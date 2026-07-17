use crate::space::ACT_PATH;
use crate::{expr, pure};
use core::f64;
use eval::EvalScope;
use eval_ffi::{ExprSink, ExprSource};
use futures::StreamExt;
use log::*;
use mork_expr::macros::SerializableExpr;
use mork_expr::{
    Expr, ExprEnv, ExprZipper, ExtractFailure, Tag, UnificationFailure, apply, byte_item, destruct,
    item_byte, parse, serialize, traverseh, unify,
};
use mork_frontend::bytestring_parser::{Context, Parser, ParserError};
use mork_frontend::json_parser::Transcriber;
use mork_interning::{SharedMapping, SharedMappingHandle, WritePermit};
use pathmap::PathMap;
use pathmap::morphisms::Catamorphism;
use pathmap::ring::{AlgebraicStatus, Lattice};
use pathmap::utils::{BitMask, ByteMask};
use pathmap::zipper::*;
use std::any::Any;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;
use std::fs::File;
use std::hint::unreachable_unchecked;
use std::io::{BufRead, Read, Write};
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::ops::{AddAssign, Coroutine, CoroutineState, MulAssign};
use std::pin::Pin;
use std::ptr::{addr_of, null, null_mut, slice_from_raw_parts, slice_from_raw_parts_mut};
use std::sync::LazyLock;
use std::task::Poll;
use std::time::Instant;
use std::{mem, process, ptr};

#[derive(Eq, PartialEq, Debug)]
pub enum WriteResourceRequest {
    BTM(&'static [u8]),
    ACT(&'static str),
    Z3(&'static str),
}

impl WriteResourceRequest {
    pub(crate) fn pjoin(&self, other: &Self) -> Option<Self> {
        match self {
            WriteResourceRequest::BTM(s) => {
                match other {
                    WriteResourceRequest::BTM(o) => {
                        // be tightened to only happen when one strictly subsumes the other?
                        // no: partial compare checks for inclusion (or a/\b == a)
                        Some(WriteResourceRequest::BTM(
                            &s[..pathmap::utils::find_prefix_overlap(s, o)],
                        ))
                    }
                    _ => None,
                }
            }
            WriteResourceRequest::ACT(s) => match other {
                WriteResourceRequest::ACT(o) if s == o => Some(WriteResourceRequest::ACT(s)),
                _ => None,
            },
            WriteResourceRequest::Z3(s) => match other {
                WriteResourceRequest::Z3(o) if s == o => Some(WriteResourceRequest::Z3(s)),
                _ => None,
            },
        }
    }
}

impl PartialOrd for WriteResourceRequest {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self {
            WriteResourceRequest::BTM(s) => {
                if let WriteResourceRequest::BTM(o) = other {
                    s.partial_cmp(o)
                } else {
                    None
                }
            }
            WriteResourceRequest::ACT(s) => {
                if let WriteResourceRequest::ACT(o) = other {
                    if s == o { Some(Ordering::Equal) } else { None }
                } else {
                    None
                }
            }
            WriteResourceRequest::Z3(s) => {
                if let WriteResourceRequest::Z3(o) = other {
                    if s == o { Some(Ordering::Equal) } else { None }
                } else {
                    None
                }
            }
        }
    }
}

pub(crate) enum WriteResource<'w, 'a, 'k> {
    BTM(&'w mut WriteZipperTracked<'a, 'k, ()>),
    ACT(()),
    Z3(&'w mut subprocess::Popen),
}

// trait JoinLattice  {
//     fn join(x: Self, y: Self) -> Self;
// }
//
// impl JoinLattice for WriteResourceRequest {
//     fn join(x: Self, y: Self) -> Self {
//         match (x, y) {
//             (WriteResourceRequest::BTM(x), WriteResourceRequest::BTM(y)) => {
//                 let i = pathmap::utils::find_prefix_overlap(x, y);
//                 &x[..i] // equiv &y[..i]
//             }
//         }
//     }
// }
//
// impl std::cmp::PartialEq for JoinLattice {
//     fn eq(&self, other: &Self) -> bool {
//         Self::is_bottom(self.meet(other))
//     }
//
// }
//
// impl std::cmp::PartialOrd for JoinLattice {
//     fn lteq(x: Self, y: Self) -> bool {
//         x.join(y).eq(y)
//     }
// }

pub(crate) trait Sink {
    fn new(e: Expr) -> Self;
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest>;
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w;
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w;
}

pub struct CompatSink {
    e: Expr,
    changed: bool,
}

impl Sink for CompatSink {
    fn new(e: Expr) -> Self {
        CompatSink { e, changed: false }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        let p = &unsafe {
            self.e
                .prefix()
                .unwrap_or_else(|x| self.e.span())
                .as_ref()
                .unwrap()
        }[..];
        trace!(target: "sink", "+ (compat) requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let mpath = &path[wz.root_prefix_path().len()..];
        trace!(target: "sink", "+ (compat) at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "+ (compat) sinking '{}'", serialize(mpath));
        wz.move_to_path(mpath);
        self.changed |= wz.set_val(()).is_none();
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        trace!(target: "sink", "+ (compat) finalizing");
        self.changed
    }
}

pub struct AddSink {
    e: Expr,
    changed: bool,
}
impl Sink for AddSink {
    fn new(e: Expr) -> Self {
        AddSink { e, changed: false }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        let p = &unsafe {
            self.e
                .prefix()
                .unwrap_or_else(|x| self.e.span())
                .as_ref()
                .unwrap()
        }[3..];
        trace!(target: "sink", "+ requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let mpath = &path[3 + wz.root_prefix_path().len()..];
        trace!(target: "sink", "+ at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "+ sinking '{}'", serialize(mpath));
        wz.move_to_path(mpath);
        self.changed |= wz.set_val(()).is_none();
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        trace!(target: "sink", "+ finalizing");
        self.changed
    }
}

// (U <expr>)
pub struct USink {
    e: Expr,
    buf: Option<*mut u8>,
    tmp: Option<*mut u8>,
    conflict: bool,
    tmp_expr_env: Vec<(ExprEnv, ExprEnv)>,
    tmp_stack: Vec<(u8, u8)>,
    tmp_assignments: Vec<(u8, u8)>,
    last_len: usize,
}
impl Sink for USink {
    fn new(e: Expr) -> Self {
        USink {
            e,
            buf: None,
            tmp: None,
            conflict: false,
            tmp_expr_env: Vec::new(),
            tmp_stack: Vec::new(),
            tmp_assignments: Vec::new(),
            last_len: usize::MAX,
        }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        let p = &unsafe {
            self.e
                .prefix()
                .unwrap_or_else(|x| self.e.span())
                .as_ref()
                .unwrap()
        }[3..];
        trace!(target: "sink", "U requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        // we could be way more parsimonious not unifying the prefix over and over again
        // let mpath = &path[3+wz.root_prefix_path().len()..];
        trace!(target: "sink", "U new expr '{}'", serialize(&path[3..]));
        if self.conflict {
            return;
        }
        if let Some(e) = self.buf {
            let mut tmp = self.tmp.unwrap();
            let eau = Expr { ptr: e };

            let mut cursor =
                std::io::Cursor::new(unsafe { core::slice::from_raw_parts_mut(tmp, 1 << 32) });

            if !mork_expr::unifies_reuse_state(
                eau,
                Expr {
                    ptr: path[3..].as_ptr().cast_mut(),
                },
                &mut cursor,
                &mut self.tmp_expr_env,
                &mut self.tmp_stack,
                &mut self.tmp_assignments,
            ) {
                self.conflict = true;
                return;
            }

            self.last_len = cursor.position() as usize;

            std::mem::swap(&mut self.buf, &mut self.tmp);
        } else {
            self.buf = Some(unsafe {
                std::alloc::alloc(std::alloc::Layout::array::<u8>(1 << 32).unwrap())
            });
            self.tmp = Some(unsafe {
                std::alloc::alloc(std::alloc::Layout::array::<u8>(1 << 32).unwrap())
            });
            unsafe {
                std::ptr::copy_nonoverlapping(
                    path[3..].as_ptr(),
                    self.buf.unwrap(),
                    path[3..].len(),
                )
            }
            self.last_len = path[3..].len();
        }
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        trace!(target: "sink", "U finalizing");
        if self.conflict {
            trace!(target: "sink", "U conflict");
            return false;
        }
        match self.buf.take() {
            None => {
                trace!(target: "sink", "U empty");
                false
            }
            Some(buf) => {
                let buf_slice = unsafe {
                    slice_from_raw_parts(buf as *const u8, self.last_len)
                        .as_ref()
                        .unwrap()
                };
                trace!(target: "sink", "U unified expression '{}'", serialize(buf_slice));
                let WriteResource::BTM(wz) = it.next().unwrap() else {
                    unreachable!()
                };
                wz.move_to_path(&buf_slice[wz.root_prefix_path().len()..]);
                wz.set_val(());
                true
            }
        }
    }
}

// (AU <expr>)
pub struct AUSink {
    e: Expr,
    buf: Option<Box<[u8]>>,
    tmp: Option<Box<[u8]>>,
    last: usize,
}
impl Sink for AUSink {
    fn new(e: Expr) -> Self {
        AUSink {
            e,
            buf: None,
            tmp: None,
            last: usize::MAX,
        }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        let p = &unsafe {
            self.e
                .prefix()
                .unwrap_or_else(|x| self.e.span())
                .as_ref()
                .unwrap()
        }[4..];
        trace!(target: "sink", "AU requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        // we could be way more parsimonious not anti-unifying the prefix over and over again
        // let mpath = &path[4+wz.root_prefix_path().len()..];
        trace!(target: "sink", "AU new expr '{}'", serialize(&path[4..]));
        if let Some(mut e) = self.buf.as_mut() {
            let mut tmp = self.tmp.as_mut().unwrap();
            let eau = Expr {
                ptr: (*e).as_mut_ptr(),
            };
            let mut wz = ExprZipper::new(Expr {
                ptr: (*tmp).as_mut_ptr(),
            });
            eau.anti_unify(
                Expr {
                    ptr: path[4..].as_ptr().cast_mut(),
                },
                &mut wz,
            )
            .unwrap();
            std::mem::swap(&mut self.buf, &mut self.tmp);
            self.last = wz.loc;
        } else {
            self.buf = Some(path[4..].to_vec().into_boxed_slice());
            self.tmp = self.buf.clone();
        }
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        trace!(target: "sink", "AU finalizing");
        match self.buf.take() {
            None => {
                trace!(target: "sink", "AU empty");
                false
            }
            Some(buf) => {
                trace!(target: "sink", "AU anti-unified expression '{}'", serialize(&buf[..self.last]));
                let WriteResource::BTM(wz) = it.next().unwrap() else {
                    unreachable!()
                };
                wz.move_to_path(&buf[wz.root_prefix_path().len()..self.last]);
                wz.set_val(());
                true
            }
        }
    }
}

pub struct ACTSink {
    e: Expr,
    file: &'static str,
    tmp: PathMap<()>,
}
impl Sink for ACTSink {
    fn new(e: Expr) -> Self {
        destruct!(e, ("ACT" {act: &str} se), {
            return ACTSink { e, file: act, tmp: PathMap::new() }
        }, _err => { panic!("act not the right shape") });
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        trace!(target: "sink", "ACT requesting {}", self.file);
        std::iter::once(WriteResourceRequest::ACT(self.file))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        trace!(target: "sink", "ACT sinking '{}'", serialize(&path[1+1+3+1+self.file.len()..]));
        self.tmp
            .insert(&path[1 + 1 + 3 + 1 + self.file.len()..], ());
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        trace!(target: "sink", "ACT finalizing");
        let _ = it.next().unwrap() else {
            unreachable!()
        };
        pathmap::arena_compact::ArenaCompactTree::dump_from_zipper(
            self.tmp.read_zipper(),
            |_v| 0,
            format!("{}{}.act", ACT_PATH, self.file),
        )
        .map(|_tree| ());
        true
    }
}

pub struct RemoveSink {
    e: Expr,
    remove: PathMap<()>,
}
// perhaps more performant to graft, remove*, and graft back?
impl Sink for RemoveSink {
    fn new(e: Expr) -> Self {
        RemoveSink {
            e,
            remove: PathMap::new(),
        }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        // !! we're never grabbing the full expression path, because then we don't have the ability to remove the root value
        let p = &unsafe {
            self.e
                .prefix()
                .unwrap_or_else(|x| {
                    let s = self.e.span();
                    slice_from_raw_parts(self.e.ptr, s.len() - 1)
                })
                .as_ref()
                .unwrap()
        }[3..];
        trace!(target: "sink", "- requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let mpath = &path[3 + wz.root_prefix_path().len()..];
        trace!(target: "sink", "- at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "- sinking '{}'", serialize(mpath));
        self.remove.insert(mpath, ());
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();
        trace!(target: "sink", "- finalizing by subtracting {} at '{}'", self.remove.val_count(), serialize(wz.origin_path()));
        // match self.remove.remove(&[]) {
        //     None => {}
        //     Some(s) => {
        //         println!("has root");
        //         wz.remove_val(true);
        //         println!("val not removed");
        //     }
        // }
        match wz.subtract_into(&self.remove.read_zipper(), true) {
            AlgebraicStatus::Element => true,
            AlgebraicStatus::Identity => false,
            AlgebraicStatus::None => true, // GOAT maybe not?
        }
    }
}

pub struct HeadTailSink<const head: bool> { e: Expr, extrema: PathMap<()>, skip: usize, count: usize, max: usize, extremum: Vec<u8> }
impl <const head: bool> Sink for HeadTailSink<head> {
    fn new(e: Expr) -> Self {
        let mut ez = ExprZipper::new(e);
        ez.next();
        ez.next();
        let max_s = ez
            .item()
            .err()
            .expect("cnt can not be an expression or variable");
        let max: usize = str::from_utf8(max_s)
            .expect("string encoded numbers for now")
            .parse()
            .expect("a number");
        assert_ne!(max, 0);
        Self { e, extrema: PathMap::new(), skip: 1 + 1+4 + 1+max_s.len(), count: 0, max, extremum: vec![] }
    }
    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        let p = &unsafe { self.e.prefix().unwrap_or_else(|x| { let s = self.e.span(); slice_from_raw_parts(self.e.ptr, s.len() - 1) }).as_ref().unwrap() }[self.skip..];
        trace!(target: "sink", "head/tail requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        let mpath = &path[self.skip+wz.root_prefix_path().len()..];
        trace!(target: "sink", "head/tail at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        if self.count == self.max {
            if (if head { &self.extremum[..] <= mpath } else { &self.extremum[..] >= mpath }) {
                trace!(target: "sink", "head/tail at max capacity ignoring '{}'", serialize(mpath));
                // doesn't displace any path
            } else {
                trace!(target: "sink", "head/tail at max capacity replacing '{}' with '{}'", serialize(&self.extremum[..]), serialize(mpath));
                assert!(self.extrema.insert(mpath, ()).is_none());
                self.extrema.remove(&self.extremum[..]);
                let mut rz = self.extrema.read_zipper();
                if head { rz.descend_last_path(); }
                else { rz.to_next_val(); }
                self.extremum.clear();
                self.extremum.extend_from_slice(rz.path()); // yikes, throwing away our needless allocation
            }
        } else {
            if self.extrema.insert(mpath, ()).is_none() {
                trace!(target: "sink", "head/tail adding '{}'", serialize(mpath));
                self.count += 1;
                let update = self.extremum.is_empty()
                    || if head { &self.extremum[..] < mpath } else { mpath < &self.extremum[..] };
                if update {
                    self.extremum.clear();
                    self.extremum.extend_from_slice(mpath);
                }
            }
        }
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();
        trace!(target: "sink", "head/tail finalizing by joining {} at '{}'", self.count, serialize(wz.origin_path()));

        match wz.join_into(&self.extrema.read_zipper()) {
            AlgebraicStatus::Element => { true }
            AlgebraicStatus::Identity => { false }
            AlgebraicStatus::None => { true } // GOAT maybe not?
        }
    }
}

#[derive(Default)]
struct ProofGroup {
    proofs: BTreeSet<ProofRow>,
    existing_proofs: BTreeSet<ProofRow>,
    old_facts: BTreeSet<(Vec<u8>, Vec<u8>)>,
}

type ProofRow = (Vec<u8>, Vec<u8>, Vec<u8>);

pub struct ReviseProofsSink {
    groups: BTreeMap<Vec<u8>, ProofGroup>,
}

fn symbol_bytes(s: &str) -> Vec<u8> {
    let mut out = vec![item_byte(Tag::SymbolSize(s.len() as u8))];
    out.extend_from_slice(s.as_bytes());
    out
}

fn push_expr(out: &mut Vec<u8>, name: &str, args: &[&[u8]]) {
    out.push(item_byte(Tag::Arity((args.len() + 1) as u8)));
    out.extend_from_slice(&symbol_bytes(name));
    for arg in args {
        out.extend_from_slice(arg);
    }
}

fn push_raw_expr(out: &mut Vec<u8>, args: &[&[u8]]) {
    out.push(item_byte(Tag::Arity(args.len() as u8)));
    for arg in args {
        out.extend_from_slice(arg);
    }
}

fn expr_len(bytes: &[u8]) -> usize {
    match byte_item(bytes[0]) {
        Tag::Arity(arity) => {
            let mut pos = 1;
            for _ in 0..arity {
                pos += expr_len(&bytes[pos..]);
            }
            pos
        }
        Tag::SymbolSize(size) => 1 + size as usize,
        _ => 1,
    }
}

fn expr_args(bytes: &[u8]) -> Vec<&[u8]> {
    let Tag::Arity(arity) = byte_item(bytes[0]) else {
        panic!("expected expression, got {}", serialize(bytes));
    };
    let mut args = Vec::with_capacity(arity as usize);
    let mut pos = 1;
    for _ in 0..arity {
        let len = expr_len(&bytes[pos..]);
        args.push(&bytes[pos..pos + len]);
        pos += len;
    }
    args
}

fn symbol_str(bytes: &[u8]) -> &str {
    let Tag::SymbolSize(size) = byte_item(bytes[0]) else {
        panic!("expected symbol, got {}", serialize(bytes));
    };
    str::from_utf8(&bytes[1..1 + size as usize]).expect("utf8 symbol")
}

fn is_symbol(bytes: &[u8], name: &str) -> bool {
    let Tag::SymbolSize(size) = byte_item(bytes[0]) else {
        return false;
    };
    size as usize == name.len() && &bytes[1..1 + size as usize] == name.as_bytes()
}

fn stv_parts(stv: &[u8]) -> (f64, f64) {
    let args = expr_args(stv);
    assert_eq!(args.len(), 2, "stv must have strength and confidence");
    (stv_f64(args[0], "strength"), stv_f64(args[1], "confidence"))
}

fn stv_f64(symbol: &[u8], field: &str) -> f64 {
    try_f64_symbol(symbol).unwrap_or_else(|| panic!("{field} must be textual or binary f64"))
}

fn try_f64_symbol(symbol: &[u8]) -> Option<f64> {
    let Tag::SymbolSize(size) = byte_item(symbol[0]) else { return None };
    try_f64_bytes(&symbol[1..1 + size as usize])
}

fn try_f64_bytes(bytes: &[u8]) -> Option<f64> {
    if let Ok(text) = str::from_utf8(bytes) {
        if let Ok(value) = text.parse::<f64>() {
            return value.is_finite().then_some(if value == 0.0 { 0.0 } else { value });
        }
    }
    let value = f64::from_be_bytes(bytes.try_into().ok()?);
    value.is_finite().then_some(if value == 0.0 { 0.0 } else { value })
}

fn binary_f64_bytes(value: f64, field: &str) -> Vec<u8> {
    assert!(value.is_finite(), "{field} must be finite");
    let value = if value == 0.0 { 0.0 } else { value };
    let mut out = vec![item_byte(Tag::SymbolSize(8))];
    out.extend_from_slice(&value.to_be_bytes());
    out
}

fn stv_bytes(strength: f64, confidence: f64) -> Vec<u8> {
    let strength_s = binary_f64_bytes(strength, "strength");
    let confidence_s = binary_f64_bytes(confidence, "confidence");
    let mut out = Vec::new();
    out.push(item_byte(Tag::Arity(2)));
    out.extend_from_slice(&strength_s);
    out.extend_from_slice(&confidence_s);
    out
}

fn confidence_to_count(confidence: f64) -> f64 {
    (confidence * 800.0) / (1.0 - confidence.min(0.9999))
}

fn revise_stv(old: &[u8], new: &[u8]) -> Vec<u8> {
    let (old_s, old_c) = stv_parts(old);
    let (new_s, new_c) = stv_parts(new);
    let old_count = confidence_to_count(old_c);
    let new_count = confidence_to_count(new_c);
    let total_count = old_count + new_count;
    let strength = if total_count == 0.0 {
        0.0
    } else {
        ((old_s * old_count) + (new_s * new_count)) / total_count
    };
    let confidence = total_count / (total_count + 800.0);
    stv_bytes(strength, confidence)
}

fn collect_evidence(bytes: &[u8], out: &mut BTreeSet<Vec<u8>>) {
    if is_symbol(bytes, "pnil") {
        return;
    }
    if let Tag::Arity(_) = byte_item(bytes[0]) {
        let args = expr_args(bytes);
        if args.len() == 3 && is_symbol(args[0], "pcons") {
            collect_evidence(args[1], out);
            collect_evidence(args[2], out);
            return;
        }
    }
    out.insert(bytes.to_vec());
}

fn evidence_set(bytes: &[u8]) -> BTreeSet<Vec<u8>> {
    let mut out = BTreeSet::new();
    collect_evidence(bytes, &mut out);
    out
}

fn is_variable_expr(bytes: &[u8]) -> bool {
    match byte_item(bytes[0]) {
        Tag::NewVar | Tag::VarRef(_) => true,
        Tag::SymbolSize(size) => size > 0 && bytes[1] == b'$',
        _ => false,
    }
}

fn alpha_equiv_inner(
    left: &[u8],
    right: &[u8],
    left_to_right: &mut BTreeMap<Vec<u8>, Vec<u8>>,
    right_to_left: &mut BTreeMap<Vec<u8>, Vec<u8>>,
) -> bool {
    match (byte_item(left[0]), byte_item(right[0])) {
        (Tag::Arity(left_arity), Tag::Arity(right_arity)) if left_arity == right_arity => {
            let left_args = expr_args(left);
            let right_args = expr_args(right);
            left_args
                .iter()
                .zip(right_args.iter())
                .all(|(l, r)| alpha_equiv_inner(l, r, left_to_right, right_to_left))
        }
        (_, _) if is_variable_expr(left) && is_variable_expr(right) => {
            match (left_to_right.get(left), right_to_left.get(right)) {
                (Some(mapped), Some(reverse)) => mapped == right && reverse == left,
                (Some(mapped), None) => mapped == right,
                (None, Some(reverse)) => reverse == left,
                (None, None) => {
                    left_to_right.insert(left.to_vec(), right.to_vec());
                    right_to_left.insert(right.to_vec(), left.to_vec());
                    true
                }
            }
        }
        (Tag::SymbolSize(_), Tag::SymbolSize(_))
            if !is_variable_expr(left) && !is_variable_expr(right) =>
        {
            left == right
        }
        _ => false,
    }
}

fn alpha_equiv(left: &[u8], right: &[u8]) -> bool {
    alpha_equiv_inner(left, right, &mut BTreeMap::new(), &mut BTreeMap::new())
}

fn pattern_instance_inner(
    pattern: &[u8],
    value: &[u8],
    bindings: &mut BTreeMap<Vec<u8>, Vec<u8>>,
) -> bool {
    if is_variable_expr(pattern) {
        return match bindings.get(pattern) {
            Some(bound) => bound == value,
            None => {
                bindings.insert(pattern.to_vec(), value.to_vec());
                true
            }
        };
    }
    match (byte_item(pattern[0]), byte_item(value[0])) {
        (Tag::Arity(pattern_arity), Tag::Arity(value_arity))
            if pattern_arity == value_arity =>
        {
            expr_args(pattern)
                .iter()
                .zip(expr_args(value).iter())
                .all(|(p, v)| pattern_instance_inner(p, v, bindings))
        }
        (Tag::SymbolSize(_), Tag::SymbolSize(_)) => pattern == value,
        _ => false,
    }
}

fn pattern_instance(pattern: &[u8], value: &[u8]) -> bool {
    pattern_instance_inner(pattern, value, &mut BTreeMap::new())
}

fn evidence_contains_rule(evidence: &[u8], rule: &[u8], allow_instance: bool) -> bool {
    evidence_set(evidence).iter().any(|item| {
        if let Tag::Arity(_) = byte_item(item[0]) {
            let args = expr_args(item);
            args.len() == 2
                && is_symbol(args[0], "rule-ev")
                && (alpha_equiv(args[1], rule)
                    || (allow_instance && pattern_instance(rule, args[1])))
        } else {
            false
        }
    })
}

fn evidence_list(set: &BTreeSet<Vec<u8>>) -> Vec<u8> {
    let mut out = symbol_bytes("pnil");
    for item in set.iter().rev() {
        let mut next = Vec::new();
        push_expr(&mut next, "pcons", &[item, &out]);
        out = next;
    }
    out
}

fn evidence_union(left: &[u8], right: &[u8]) -> Vec<u8> {
    let mut set = evidence_set(left);
    set.extend(evidence_set(right));
    evidence_list(&set)
}

fn is_expr_head(bytes: &[u8], name: &str) -> bool {
    if let Tag::Arity(_) = byte_item(bytes[0]) {
        let args = expr_args(bytes);
        !args.is_empty() && is_symbol(args[0], name)
    } else {
        false
    }
}

fn evidence_dependent(left: &[u8], right: &[u8]) -> bool {
    let left = evidence_set(left);
    evidence_set(right)
        .iter()
        .any(|item| left.contains(item) && is_expr_head(item, "rule-ev"))
}

fn evidence_equal(left: &[u8], right: &[u8]) -> bool {
    evidence_set(left) == evidence_set(right)
}

fn evidence_alpha_equal(left: &[u8], right: &[u8]) -> bool {
    let left = evidence_set(left);
    let right = evidence_set(right);
    left.len() == right.len()
        && left
            .iter()
            .all(|item| right.iter().any(|candidate| alpha_equiv(item, candidate)))
}

fn inversion_proof_parts(proof_id: &[u8]) -> Option<(&[u8], &[u8], &[u8])> {
    if !matches!(byte_item(proof_id[0]), Tag::Arity(_)) {
        return None;
    }
    let args = expr_args(proof_id);
    if args.len() != 4 {
        return None;
    }
    if is_symbol(args[0], "scheduledInvN") {
        return Some((args[1], args[2], args[3]));
    }
    if is_symbol(args[0], "scheduledN") {
        let rule = expr_args(args[2]);
        if rule.len() == 3 && is_symbol(rule[0], "inv") {
            return Some((args[1], rule[1], args[3]));
        }
    }
    None
}

fn is_scoped_inheritance_goal(goal: &[u8]) -> bool {
    if !matches!(byte_item(goal[0]), Tag::Arity(_)) {
        return false;
    }
    let scoped = expr_args(goal);
    scoped.len() == 2 && is_expr_head(scoped[1], "Inheritance")
}

fn is_inheritance_cycle_proof(proof_id: &[u8]) -> bool {
    if !matches!(byte_item(proof_id[0]), Tag::Arity(_)) {
        return false;
    }
    let args = expr_args(proof_id);
    if args.is_empty() {
        return false;
    }
    if is_symbol(args[0], "scheduledInvN") && args.len() >= 2 {
        return is_scoped_inheritance_goal(args[1]);
    }
    if is_symbol(args[0], "scheduledN") && args.len() >= 3 {
        return is_scoped_inheritance_goal(args[1])
            && (is_expr_head(args[2], "stv-prior") || is_expr_head(args[2], "inv"));
    }
    false
}

fn is_generated_inheritance_view_proof(proof_id: &[u8]) -> bool {
    if !matches!(byte_item(proof_id[0]), Tag::Arity(_)) {
        return false;
    }
    let args = expr_args(proof_id);
    if args.is_empty() {
        return false;
    }
    if is_symbol(args[0], "scheduledInvN") {
        return true;
    }
    is_symbol(args[0], "scheduledN")
        && args.len() >= 3
        && (is_expr_head(args[2], "stv-prior") || is_expr_head(args[2], "inv"))
}

fn is_inheritance_refutation_proof(proof_id: &[u8]) -> bool {
    if !matches!(byte_item(proof_id[0]), Tag::Arity(_)) {
        return false;
    }
    let args = expr_args(proof_id);
    args.len() >= 3
        && is_symbol(args[0], "scheduledN")
        && is_expr_head(args[2], "mp-conclusion-not")
}

fn proof_identity_equal(left: &ProofRow, right: &ProofRow) -> bool {
    let same_proof = match (
        inversion_proof_parts(&left.1),
        inversion_proof_parts(&right.1),
    ) {
        (Some(left), Some(right)) => {
            alpha_equiv(left.0, right.0)
                && alpha_equiv(left.1, right.1)
                && alpha_equiv(left.2, right.2)
        }
        _ => alpha_equiv(&left.1, &right.1),
    };
    same_proof && evidence_alpha_equal(&left.2, &right.2)
}

fn is_inversion_snapshot_proof(proof_id: &[u8]) -> bool {
    is_expr_head(proof_id, "scheduledInvN")
}

// Re-running a logical derivation after a premise or base-rate refinement
// replaces its previous snapshot. Proof terms may contain freshly allocated
// variables, so identity is alpha-equivalent proof structure plus evidence,
// not byte equality. Keep the strongest current snapshot deterministically.
fn select_current_snapshot_proofs(rows: &BTreeSet<ProofRow>) -> BTreeSet<ProofRow> {
    let mut selected = Vec::<ProofRow>::new();
    for row in rows {
        if let Some(current) = selected
            .iter_mut()
            .find(|current| proof_identity_equal(current, row))
        {
            let (strength, confidence) = stv_parts(&row.0);
            let (current_strength, current_confidence) = stv_parts(&current.0);
            if confidence
                .total_cmp(&current_confidence)
                .then_with(|| strength.total_cmp(&current_strength))
                .is_gt()
            {
                *current = row.clone();
            }
        } else {
            selected.push(row.clone());
        }
    }
    selected.into_iter().collect()
}

#[derive(Clone)]
struct ProjectionEvidence {
    source: Vec<u8>,
    target: Vec<u8>,
    marginal: bool,
}

fn projection_evidence(ev: &[u8]) -> Vec<ProjectionEvidence> {
    evidence_set(ev)
        .into_iter()
        .filter_map(|item| {
            let args = expr_args(&item);
            if args.len() != 5 || !is_symbol(args[0], "projection-ev") {
                return None;
            }
            let proj_args = expr_args(args[1]);
            Some(ProjectionEvidence {
                source: args[2].to_vec(),
                target: args[4].to_vec(),
                marginal: proj_args.len() >= 3 && is_symbol(proj_args[0], "marginal-proj"),
            })
        })
        .collect()
}

fn related_projection_choice(
    old_stv: &[u8],
    old_ev: &[u8],
    new_stv: &[u8],
    new_ev: &[u8],
) -> Option<(Vec<u8>, Vec<u8>)> {
    let old_projection = projection_evidence(old_ev);
    let new_projection = projection_evidence(new_ev);
    for old in &old_projection {
        for new in &new_projection {
            if old.source == new.source && old.target == new.target {
                if old.marginal && !new.marginal {
                    return Some((old_stv.to_vec(), old_ev.to_vec()));
                }
                if new.marginal && !old.marginal {
                    return Some((new_stv.to_vec(), new_ev.to_vec()));
                }
                if stv_parts(new_stv).1 < stv_parts(old_stv).1 {
                    return Some((new_stv.to_vec(), new_ev.to_vec()));
                }
                return Some((old_stv.to_vec(), old_ev.to_vec()));
            }
        }
    }
    None
}

fn merge_evidenced_stv(
    old_stv: &[u8],
    old_ev: &[u8],
    new_stv: &[u8],
    new_ev: &[u8],
) -> (Vec<u8>, Vec<u8>) {
    if let Some(choice) = related_projection_choice(old_stv, old_ev, new_stv, new_ev) {
        return choice;
    }
    if evidence_equal(old_ev, new_ev) || evidence_dependent(old_ev, new_ev) {
        if stv_parts(new_stv).1 > stv_parts(old_stv).1 {
            (new_stv.to_vec(), new_ev.to_vec())
        } else {
            (old_stv.to_vec(), old_ev.to_vec())
        }
    } else {
        (revise_stv(old_stv, new_stv), evidence_union(old_ev, new_ev))
    }
}

#[derive(Clone)]
struct ScheduledCtvProof {
    stv: Vec<u8>,
    evset: Vec<u8>,
    pos: Vec<u8>,
    neg: Vec<u8>,
    premises: Vec<Vec<u8>>,
}

fn collect_pcons(bytes: &[u8], out: &mut Vec<Vec<u8>>) -> bool {
    if is_symbol(bytes, "pnil") {
        return true;
    }
    if let Tag::Arity(_) = byte_item(bytes[0]) {
        let args = expr_args(bytes);
        if args.len() == 3 && is_symbol(args[0], "pcons") {
            out.push(args[1].to_vec());
            return collect_pcons(args[2], out);
        }
    }
    false
}

fn parse_scheduled_ctv_proof(row: &ProofRow) -> Option<ScheduledCtvProof> {
    let (stv, proof_id, evset) = row;
    if !matches!(byte_item(proof_id[0]), Tag::Arity(_)) {
        return None;
    }
    let proof_args = expr_args(proof_id);
    if proof_args.len() != 4 || !is_symbol(proof_args[0], "scheduledN") {
        return None;
    }
    if !matches!(byte_item(proof_args[2][0]), Tag::Arity(_)) {
        return None;
    }
    let rule_args = expr_args(proof_args[2]);
    if rule_args.len() != 3 || !is_symbol(rule_args[0], "ctv") {
        return None;
    }

    let mut premises = Vec::new();
    if !collect_pcons(proof_args[3], &mut premises) || premises.is_empty() {
        return None;
    }

    Some(ScheduledCtvProof {
        stv: stv.clone(),
        evset: evset.clone(),
        pos: rule_args[1].to_vec(),
        neg: rule_args[2].to_vec(),
        premises,
    })
}

fn fact_evidence_key(item: &[u8]) -> Option<Vec<u8>> {
    if !matches!(byte_item(item[0]), Tag::Arity(_)) {
        return None;
    }
    let args = expr_args(item);
    if args.len() != 3 || !is_symbol(args[0], "fact-ev") {
        None
    } else if matches!(byte_item(args[1][0]), Tag::Arity(_)) {
        let source = expr_args(args[1]);
        // Only fact-key evidence expands through proved rows.  A proof-id
        // source names exact provenance and must remain an atomic item.
        if source.len() == 2 && is_symbol(source[0], "fact-key") && source[1] == args[2] {
            Some(args[2].to_vec())
        } else {
            None
        }
    } else {
        None
    }
}

fn fact_evidence_keys(evset: &[u8]) -> BTreeSet<Vec<u8>> {
    evidence_set(evset)
        .into_iter()
        .filter_map(|item| fact_evidence_key(&item))
        .collect()
}

fn expanded_fact_evidence_key(
    key: &[u8],
    proved: &BTreeMap<Vec<u8>, BTreeSet<ProofRow>>,
    stack: &mut BTreeSet<Vec<u8>>,
) -> BTreeSet<Vec<u8>> {
    if !stack.insert(key.to_vec()) {
        return BTreeSet::from([key.to_vec()]);
    }
    let expanded: BTreeSet<_> = proved
        .get(key)
        .into_iter()
        .flat_map(|rows| rows.iter())
        .filter_map(parse_scheduled_ctv_proof)
        .flat_map(|proof| expanded_fact_evidence_keys_with_stack(&proof.evset, proved, stack))
        .collect();
    stack.remove(key);
    if expanded.is_empty() {
        BTreeSet::from([key.to_vec()])
    } else {
        expanded
    }
}

fn expanded_fact_evidence_keys_with_stack(
    evset: &[u8],
    proved: &BTreeMap<Vec<u8>, BTreeSet<ProofRow>>,
    stack: &mut BTreeSet<Vec<u8>>,
) -> BTreeSet<Vec<u8>> {
    evidence_set(evset)
        .into_iter()
        .filter_map(|item| fact_evidence_key(&item))
        .flat_map(|key| expanded_fact_evidence_key(&key, proved, stack))
        .collect()
}

fn expanded_fact_evidence_keys(
    evset: &[u8],
    proved: &BTreeMap<Vec<u8>, BTreeSet<ProofRow>>,
) -> BTreeSet<Vec<u8>> {
    expanded_fact_evidence_keys_with_stack(evset, proved, &mut BTreeSet::new())
}

fn evidence_depends_on_fact(
    evset: &[u8],
    fact: &[u8],
    proved: &BTreeMap<Vec<u8>, BTreeSet<ProofRow>>,
) -> bool {
    evidence_set(evset)
        .into_iter()
        .filter_map(|item| fact_evidence_key(&item))
        .any(|key| fact_evidence_key_depends_on(&key, fact, proved, &mut BTreeSet::new()))
}

fn fact_evidence_key_depends_on(
    key: &[u8],
    fact: &[u8],
    proved: &BTreeMap<Vec<u8>, BTreeSet<ProofRow>>,
    stack: &mut BTreeSet<Vec<u8>>,
) -> bool {
    if key == fact {
        return true;
    }
    if !stack.insert(key.to_vec()) {
        return false;
    }
    let depends = proved
        .get(key)
        .into_iter()
        .flat_map(|rows| rows.iter())
        .filter(|(_stv, proof_id, _evset)| is_inheritance_cycle_proof(proof_id))
        .any(|(_stv, _proof_id, evset)| {
            evidence_depends_on_fact_with_stack(evset, fact, proved, stack)
        });
    stack.remove(key);
    depends
}

fn evidence_depends_on_fact_with_stack(
    evset: &[u8],
    fact: &[u8],
    proved: &BTreeMap<Vec<u8>, BTreeSet<ProofRow>>,
    stack: &mut BTreeSet<Vec<u8>>,
) -> bool {
    evidence_set(evset)
        .into_iter()
        .filter_map(|item| fact_evidence_key(&item))
        .any(|key| fact_evidence_key_depends_on(&key, fact, proved, stack))
}

fn residual_evidence(evset: &[u8], shared: &BTreeSet<Vec<u8>>) -> BTreeSet<Vec<u8>> {
    evidence_set(evset)
        .into_iter()
        .filter(|item| match fact_evidence_key(item) {
            Some(key) => !shared.contains(&key),
            None => true,
        })
        .collect()
}

fn expanded_residual_evidence(
    evset: &[u8],
    shared: &BTreeSet<Vec<u8>>,
    proved: &BTreeMap<Vec<u8>, BTreeSet<ProofRow>>,
) -> BTreeSet<Vec<u8>> {
    let mut residual = BTreeSet::new();
    for item in evidence_set(evset) {
        match fact_evidence_key(&item) {
            Some(key) => {
                for expanded in expanded_fact_evidence_key(&key, proved, &mut BTreeSet::new()) {
                    if !shared.contains(&expanded) {
                        residual.insert(expanded);
                    }
                }
            }
            None => {
                residual.insert(item);
            }
        }
    }
    residual
}

fn evidence_sets_pairwise_disjoint(sets: &[BTreeSet<Vec<u8>>]) -> bool {
    for (idx, left) in sets.iter().enumerate() {
        for right in &sets[idx + 1..] {
            if left.iter().any(|item| right.contains(item)) {
                return false;
            }
        }
    }
    true
}

fn and_stv(left: &[u8], right: &[u8]) -> Vec<u8> {
    let (left_s, left_c) = stv_parts(left);
    let (right_s, right_c) = stv_parts(right);
    let strength = left_s * right_s;
    let confidence = if left_c <= 0.0 || right_c <= 0.0 {
        0.0
    } else {
        OrStvSink::ideal_prod_confidence(
            left_s,
            OrStvSink::ideal_var(left_s, left_c),
            right_s,
            OrStvSink::ideal_var(right_s, right_c),
            strength,
        )
    };
    stv_bytes(strength, confidence)
}

fn repeated_and_stv(count: usize, strength: f64, confidence: f64) -> Vec<u8> {
    let leaf = stv_bytes(strength, confidence);
    let mut acc = leaf.clone();
    for _ in 1..count {
        acc = and_stv(&acc, &leaf);
    }
    acc
}

fn stv_strength_close(left: &[u8], right: &[u8]) -> bool {
    let (left_s, _) = stv_parts(left);
    let (right_s, _) = stv_parts(right);
    (left_s - right_s).abs() < 0.000001
}

fn proof_matches_certain_shared_conj(proof: &ScheduledCtvProof) -> bool {
    let expected = OrStvSink::mp_stv(
        &repeated_and_stv(proof.premises.len(), 1.0, 1.0),
        &proof.pos,
        &proof.neg,
    );
    stv_strength_close(&proof.stv, &expected)
}

fn fold_stvs(mut stvs: impl Iterator<Item = Vec<u8>>) -> Option<Vec<u8>> {
    let mut acc = stvs.next()?;
    for stv in stvs {
        acc = and_stv(&acc, &stv);
    }
    Some(acc)
}

fn union_proof_evidence(proofs: &[ScheduledCtvProof]) -> Vec<u8> {
    proofs.iter().fold(symbol_bytes("pnil"), |acc, proof| {
        evidence_union(&acc, &proof.evset)
    })
}

fn factor_merge_all_shared_proofs(rows: &BTreeSet<ProofRow>) -> Option<(Vec<u8>, Vec<u8>)> {
    if rows.len() < 2 {
        return None;
    }
    let proofs: Vec<_> = rows
        .iter()
        .map(parse_scheduled_ctv_proof)
        .collect::<Option<Vec<_>>>()?;

    let mut shared = fact_evidence_keys(&proofs.first()?.evset);
    for proof in proofs.iter().skip(1) {
        let keys = fact_evidence_keys(&proof.evset);
        shared = shared.intersection(&keys).cloned().collect();
    }
    if shared.is_empty() {
        return None;
    }

    let premise_count = proofs.first()?.premises.len();
    if !proofs.iter().all(|proof| {
        proof.premises.len() == premise_count
            && proof
                .premises
                .iter()
                .all(|premise| shared.contains(premise))
            && proof_matches_certain_shared_conj(proof)
    }) {
        return None;
    }

    let residuals: Vec<_> = proofs
        .iter()
        .map(|proof| residual_evidence(&proof.evset, &shared))
        .collect();
    if !evidence_sets_pairwise_disjoint(&residuals) {
        return None;
    }

    let override_true = repeated_and_stv(premise_count, 1.0, 1.0);
    let override_false = repeated_and_stv(premise_count, 0.0, 1.0);
    let mut revised_pos: Option<Vec<u8>> = None;
    let mut revised_neg: Option<Vec<u8>> = None;
    for proof in &proofs {
        let pos = OrStvSink::mp_stv(&override_true, &proof.pos, &proof.neg);
        let neg = OrStvSink::mp_stv(&override_false, &proof.pos, &proof.neg);
        revised_pos = Some(match revised_pos {
            Some(ref old) => revise_stv(old, &pos),
            None => pos,
        });
        revised_neg = Some(match revised_neg {
            Some(ref old) => revise_stv(old, &neg),
            None => neg,
        });
    }

    let merged = OrStvSink::mp_stv(&override_true, &revised_pos?, &revised_neg?);
    Some((merged, union_proof_evidence(&proofs)))
}

fn packed_stv(bytes: &[u8]) -> Option<Vec<u8>> {
    if !matches!(byte_item(bytes[0]), Tag::Arity(2)) {
        return None;
    }
    let args = expr_args(bytes);
    if args.iter().all(|arg| try_f64_symbol(arg).is_some()) {
        Some(bytes.to_vec())
    } else {
        None
    }
}

fn fact_row(path: &[u8]) -> Option<(Vec<u8>, Vec<u8>)> {
    if !matches!(byte_item(path[0]), Tag::Arity(_)) {
        return None;
    }
    let args = expr_args(path);
    if args.len() == 3 && is_symbol(args[0], "fact") {
        Some((args[1].to_vec(), packed_stv(args[2])?))
    } else {
        None
    }
}

fn proved_row(path: &[u8]) -> Option<(Vec<u8>, ProofRow)> {
    if !matches!(byte_item(path[0]), Tag::Arity(_)) {
        return None;
    }
    let args = expr_args(path);
    if args.len() == 5 && is_symbol(args[0], "proved") {
        Some((
            args[1].to_vec(),
            (args[2].to_vec(), args[3].to_vec(), args[4].to_vec()),
        ))
    } else {
        None
    }
}

fn expr_prefix(name: &str, arity: u8, args: &[&[u8]]) -> Vec<u8> {
    let mut prefix = Vec::new();
    prefix.push(item_byte(Tag::Arity(arity)));
    prefix.extend_from_slice(&symbol_bytes(name));
    for arg in args {
        prefix.extend_from_slice(arg);
    }
    prefix
}

fn collect_fact_stvs<Z>(root: &Z) -> BTreeMap<Vec<u8>, Vec<u8>>
where
    Z: ZipperForking<()>,
{
    let prefix = expr_prefix("fact", 3, &[]);
    let mut rz = root.fork_read_zipper();
    if rz.descend_to_existing(&prefix) != prefix.len() {
        return BTreeMap::new();
    }
    let mut facts: BTreeMap<Vec<u8>, Vec<u8>> = BTreeMap::new();
    while rz.to_next_val() {
        if let Some((goal, stv)) = fact_row(rz.origin_path()) {
            match facts.get(&goal) {
                Some(old) if stv_parts(old).1 >= stv_parts(&stv).1 => {}
                _ => {
                    facts.insert(goal, stv);
                }
            }
        }
    }
    facts
}

fn collect_proved_rows<Z>(root: &Z) -> BTreeMap<Vec<u8>, BTreeSet<ProofRow>>
where
    Z: ZipperForking<()>,
{
    let prefix = expr_prefix("proved", 5, &[]);
    let mut rz = root.fork_read_zipper();
    if rz.descend_to_existing(&prefix) != prefix.len() {
        return BTreeMap::new();
    }
    let mut proved: BTreeMap<Vec<u8>, BTreeSet<ProofRow>> = BTreeMap::new();
    while rz.to_next_val() {
        if let Some((goal, row)) = proved_row(rz.origin_path()) {
            proved.entry(goal).or_default().insert(row);
        }
    }
    proved
}

fn eval_scheduled_proof_with(
    proof: &ScheduledCtvProof,
    shared: &BTreeSet<Vec<u8>>,
    facts: &BTreeMap<Vec<u8>, Vec<u8>>,
    proved: &BTreeMap<Vec<u8>, BTreeSet<ProofRow>>,
    shared_override: &[u8],
    stack: &mut BTreeSet<Vec<u8>>,
) -> Option<Vec<u8>> {
    let aggregate = fold_stvs(
        proof
            .premises
            .iter()
            .map(|premise| eval_goal_with(premise, shared, facts, proved, shared_override, stack))
            .collect::<Option<Vec<_>>>()?
            .into_iter(),
    )?;
    Some(OrStvSink::mp_stv(&aggregate, &proof.pos, &proof.neg))
}

fn merge_proof_results(rows: Vec<(Vec<u8>, Vec<u8>)>) -> Option<Vec<u8>> {
    let mut rows = rows.into_iter();
    let (mut merged_stv, mut merged_evset) = rows.next()?;
    for (stv, evset) in rows {
        let (next_stv, next_evset) = merge_evidenced_stv(&merged_stv, &merged_evset, &stv, &evset);
        merged_stv = next_stv;
        merged_evset = next_evset;
    }
    Some(merged_stv)
}

fn eval_goal_with(
    goal: &[u8],
    shared: &BTreeSet<Vec<u8>>,
    facts: &BTreeMap<Vec<u8>, Vec<u8>>,
    proved: &BTreeMap<Vec<u8>, BTreeSet<ProofRow>>,
    shared_override: &[u8],
    stack: &mut BTreeSet<Vec<u8>>,
) -> Option<Vec<u8>> {
    if shared.contains(goal) {
        return Some(shared_override.to_vec());
    }
    if !stack.insert(goal.to_vec()) {
        return facts.get(goal).cloned();
    }
    let result = proved.get(goal).and_then(|rows| {
        merge_proof_results(
            rows.iter()
                .filter_map(|row| {
                    let proof = parse_scheduled_ctv_proof(row)?;
                    let stv = eval_scheduled_proof_with(
                        &proof,
                        shared,
                        facts,
                        proved,
                        shared_override,
                        stack,
                    )?;
                    Some((stv, proof.evset))
                })
                .collect(),
        )
    });
    stack.remove(goal);
    result.or_else(|| facts.get(goal).cloned())
}

fn actual_proof_stv(
    proof: &ScheduledCtvProof,
    facts: &BTreeMap<Vec<u8>, Vec<u8>>,
    proved: &BTreeMap<Vec<u8>, BTreeSet<ProofRow>>,
) -> Option<Vec<u8>> {
    let aggregate = fold_stvs(
        proof
            .premises
            .iter()
            .map(|premise| {
                eval_goal_with(
                    premise,
                    &BTreeSet::new(),
                    facts,
                    proved,
                    &stv_bytes(1.0, 1.0),
                    &mut BTreeSet::new(),
                )
            })
            .collect::<Option<Vec<_>>>()?
            .into_iter(),
    )?;
    Some(OrStvSink::mp_stv(&aggregate, &proof.pos, &proof.neg))
}

fn shared_conjunction_stv(
    shared: &BTreeSet<Vec<u8>>,
    facts: &BTreeMap<Vec<u8>, Vec<u8>>,
) -> Option<Vec<u8>> {
    fold_stvs(
        shared
            .iter()
            .map(|premise| facts.get(premise).cloned())
            .collect::<Option<Vec<_>>>()?
            .into_iter(),
    )
}

fn factor_merge_with_fact_stvs(
    rows: &BTreeSet<ProofRow>,
    facts: &BTreeMap<Vec<u8>, Vec<u8>>,
    proved: &BTreeMap<Vec<u8>, BTreeSet<ProofRow>>,
) -> Option<(Vec<u8>, Vec<u8>)> {
    if rows.len() < 2 {
        return None;
    }
    let proofs: Vec<_> = rows
        .iter()
        .map(parse_scheduled_ctv_proof)
        .collect::<Option<Vec<_>>>()?;

    let mut shared = expanded_fact_evidence_keys(&proofs.first()?.evset, proved);
    for proof in proofs.iter().skip(1) {
        let keys = expanded_fact_evidence_keys(&proof.evset, proved);
        shared = shared.intersection(&keys).cloned().collect();
    }
    if shared.is_empty() || !shared.iter().all(|key| facts.contains_key(key)) {
        return None;
    }

    let residuals: Vec<_> = proofs
        .iter()
        .map(|proof| expanded_residual_evidence(&proof.evset, &shared, proved))
        .collect();
    if !evidence_sets_pairwise_disjoint(&residuals) {
        return None;
    }

    if !proofs.iter().all(|proof| {
        actual_proof_stv(proof, facts, proved)
            .map(|actual| stv_strength_close(&proof.stv, &actual))
            .unwrap_or(false)
    }) {
        return None;
    }

    let override_true = stv_bytes(1.0, 1.0);
    let override_false = stv_bytes(0.0, 1.0);
    let mut revised_pos: Option<Vec<u8>> = None;
    let mut revised_neg: Option<Vec<u8>> = None;
    for proof in &proofs {
        let pos = eval_scheduled_proof_with(
            proof,
            &shared,
            facts,
            proved,
            &override_true,
            &mut BTreeSet::new(),
        )?;
        let neg = eval_scheduled_proof_with(
            proof,
            &shared,
            facts,
            proved,
            &override_false,
            &mut BTreeSet::new(),
        )?;
        revised_pos = Some(match revised_pos {
            Some(ref old) => revise_stv(old, &pos),
            None => pos,
        });
        revised_neg = Some(match revised_neg {
            Some(ref old) => revise_stv(old, &neg),
            None => neg,
        });
    }

    let shared_stv = shared_conjunction_stv(&shared, facts)?;
    let merged = OrStvSink::mp_stv(&shared_stv, &revised_pos?, &revised_neg?);
    Some((merged, union_proof_evidence(&proofs)))
}

fn all_scheduled_ctv_proof_rows(rows: &BTreeSet<ProofRow>) -> bool {
    rows.iter()
        .all(|row| parse_scheduled_ctv_proof(row).is_some())
}

#[derive(Default)]
struct BaseRateGroup {
    fact_stvs_by_old: BTreeMap<Vec<u8>, Vec<(f64, f64)>>,
    guarded_proofs_by_old: BTreeMap<Vec<u8>, BTreeSet<ProofRow>>,
}

/// Maintains `(base-rate $patQ $stv)` facts from `(fold-base-rate $patQ $old $stv)`
/// rows. `$patQ` is an uninstantiated pattern copy that keys the group, `$old` is
/// the current value, and each row's `$stv` is one matching fact's truth value.
/// Guarded rows use `(fold-base-rate $patQ $old $stv $guard)`, where the guard
/// payload is `(base-rate-guard $kind $rule $proof $evset)`.
/// Application-local folds use `without-rule-instance`, which also recognizes
/// grounded instances of a schematic rule ID.
/// They skip recursive evidence and supersede alpha-equivalent proof snapshots.
/// The weighted base rate follows PeTTaChainer's BaseRateAcc/BaseRateTv:
/// strength = sum(s*c)/sum(c), confidence = count-confidence(sum(c)).
pub struct BaseRateSink {
    groups: BTreeMap<Vec<u8>, BaseRateGroup>,
    skipped_rows: bool,
}

impl Sink for BaseRateSink {
    fn new(_e: Expr) -> Self {
        BaseRateSink {
            groups: BTreeMap::new(),
            skipped_rows: false,
        }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        std::iter::once(WriteResourceRequest::BTM([].as_slice()))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let mpath = &path[wz.root_prefix_path().len()..];
        let args = expr_args(mpath);
        assert!(
            args.len() == 4 || args.len() == 5,
            "fold-base-rate expects 3 or 4 payload args"
        );
        assert_eq!(symbol_str(args[0]), "fold-base-rate");
        if args.len() == 5 {
            let guard = expr_args(args[4]);
            assert_eq!(guard.len(), 5, "base-rate-guard expects four arguments");
            assert_eq!(symbol_str(guard[0]), "base-rate-guard");
            let guard_kind = symbol_str(guard[1]);
            assert!(
                guard_kind == "without-rule" || guard_kind == "without-rule-instance",
                "unsupported base-rate recursion guard"
            );
            if evidence_contains_rule(
                guard[4],
                guard[2],
                guard_kind == "without-rule-instance",
            ) {
                self.skipped_rows = true;
                return;
            }
            self.groups
                .entry(args[1].to_vec())
                .or_default()
                .guarded_proofs_by_old
                .entry(args[2].to_vec())
                .or_default()
                .insert((args[3].to_vec(), guard[3].to_vec(), guard[4].to_vec()));
            return;
        }

        self.groups
            .entry(args[1].to_vec())
            .or_default()
            .fact_stvs_by_old
            .entry(args[2].to_vec())
            .or_default()
            .push(stv_parts(args[3]));
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();
        let mut remove = PathMap::new();
        let mut add = PathMap::new();

        for (pattern, group) in &self.groups {
            // Several rounds can leave fold rows based on different snapshots.
            // Evaluate only the most authoritative snapshot; mixing their rows
            // double-counts the same facts and can let a stale computed value
            // overwrite a higher-confidence manual value.
            let best_old = group
                .fact_stvs_by_old
                .keys()
                .chain(group.guarded_proofs_by_old.keys())
                .max_by(|left, right| {
                    let (_, left_c) = stv_parts(left);
                    let (_, right_c) = stv_parts(right);
                    left_c.total_cmp(&right_c).then_with(|| left.cmp(right))
                });
            let Some(old) = best_old else {
                continue;
            };
            let fact_stvs = group.fact_stvs_by_old.get(old).cloned().unwrap_or_default();
            let guarded = group
                .guarded_proofs_by_old
                .get(old)
                .map(select_current_snapshot_proofs)
                .unwrap_or_default();
            let mut wsum = 0.0;
            let mut csum = 0.0;
            for (s, c) in fact_stvs
                .into_iter()
                .chain(guarded.iter().map(|row| stv_parts(&row.0)))
            {
                wsum += s * c;
                csum += c;
            }
            let new = if csum <= 0.0 {
                stv_bytes(0.0, 0.0)
            } else {
                stv_bytes(wsum / csum, csum / (csum + 800.0))
            };
            if new == *old {
                continue;
            }
            let (_, old_c) = stv_parts(old);
            let (_, new_c) = stv_parts(&new[..]);
            if new_c < old_c {
                continue;
            }
            let mut old_fact = Vec::new();
            push_expr(&mut old_fact, "base-rate", &[pattern, old]);
            remove.insert(&old_fact[..], ());
            let mut new_fact = Vec::new();
            push_expr(&mut new_fact, "base-rate", &[pattern, &new[..]]);
            add.insert(&new_fact[..], ());
        }

        let removed = match wz.subtract_into(&remove.read_zipper(), true) {
            AlgebraicStatus::Element => true,
            AlgebraicStatus::Identity => false,
            AlgebraicStatus::None => true,
        };
        wz.reset();
        let added = match wz.join_into(&add.read_zipper()) {
            AlgebraicStatus::Element => true,
            AlgebraicStatus::Identity => false,
            AlgebraicStatus::None => true,
        };
        self.skipped_rows || removed || added
    }
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd)]
struct PriorRuleKey {
    goal: Vec<u8>,
    premise_stv: Vec<u8>,
    rule_stv: Vec<u8>,
    kb: Vec<u8>,
    antecedent: Vec<u8>,
    consequent: Vec<u8>,
    proof_id: Vec<u8>,
    evset: Vec<u8>,
    mass: Vec<u8>,
    antecedent_prior: Vec<u8>,
    consequent_prior: Vec<u8>,
    divisor: Vec<u8>,
}

#[derive(Default)]
struct PriorRuleGroup {
    antecedent_rows: BTreeMap<Vec<u8>, BTreeSet<ProofRow>>,
    consequent_rows: BTreeMap<Vec<u8>, BTreeSet<ProofRow>>,
}

/// Computes a plain-STV inheritance rule against the proof-aware, prior-
/// weighted marginals visible to that grounded application.  Unlike a global
/// cache, this can exclude both recursive rule evidence and the current
/// subject, matching FoldAll's cycle behavior in PeTTaChainer.
pub struct PriorRuleStvSink {
    groups: BTreeMap<PriorRuleKey, PriorRuleGroup>,
}

fn inheritance_subject(goal: &[u8]) -> Option<&[u8]> {
    if !matches!(byte_item(goal[0]), Tag::Arity(_)) {
        return None;
    }
    let scoped = expr_args(goal);
    if scoped.len() != 2 || !matches!(byte_item(scoped[1][0]), Tag::Arity(_)) {
        return None;
    }
    let inheritance = expr_args(scoped[1]);
    (inheritance.len() == 3 && is_symbol(inheritance[0], "Inheritance")).then_some(inheritance[1])
}

fn prior_candidate_goal<'a>(wrapped: &'a [u8], proof: &[u8]) -> Option<(&'a [u8], bool)> {
    if is_symbol(proof, "no-prior-proof") {
        return None;
    }
    let args = expr_args(wrapped);
    (args.len() == 4 && is_symbol(args[0], "prior-candidate"))
        .then_some((args[2], is_symbol(args[3], "forward-observed")))
}

fn prior_candidate_allowed(proof: &[u8]) -> bool {
    if !matches!(byte_item(proof[0]), Tag::Arity(_)) {
        return true;
    }
    let args = expr_args(proof);
    if args.is_empty() {
        return true;
    }
    if is_symbol(args[0], "scheduledN") && args.len() >= 3 {
        // PeTTa's one-pass forward marginal observes asserted inheritance
        // links and explicit refutations.  Positive derived links are rule
        // consequences, not new population observations; admitting them here
        // recreates the obsolete warm-up/two-pass base-rate feedback.
        return is_expr_head(args[2], "mp-conclusion-not");
    }
    !is_symbol(args[0], "scheduledInvN")
}

fn merge_current_goal_rows(rows: &BTreeSet<ProofRow>) -> Option<Vec<u8>> {
    let mut current = select_current_snapshot_proofs(rows).into_iter();
    let (mut stv, _proof, mut evset) = current.next()?;
    for (next_stv, _next_proof, next_evset) in current {
        let (merged, merged_evset) = merge_evidenced_stv(&stv, &evset, &next_stv, &next_evset);
        stv = merged;
        evset = merged_evset;
    }
    Some(stv)
}

fn prior_weighted_base_rate(
    rows: &BTreeMap<Vec<u8>, BTreeSet<ProofRow>>,
    mass: &[u8],
    prior: &[u8],
    divisor: f64,
) -> Vec<u8> {
    let (mass_s, mass_c) = stv_parts(mass);
    let mut wsum = 0.0;
    let mut msum = 0.0;
    for rows in rows.values() {
        let Some(stv) = merge_current_goal_rows(rows) else {
            continue;
        };
        let (strength, confidence) = stv_parts(&stv);
        let weighted_mass = mass_s * mass_c * confidence;
        wsum += strength * weighted_mass;
        msum += weighted_mass;
    }
    if msum <= 0.0 {
        return prior.to_vec();
    }
    let evidence = stv_bytes(wsum / msum, (msum / divisor).min(1.0));
    let (_, prior_c) = stv_parts(prior);
    if prior_c <= 0.0 {
        evidence
    } else {
        revise_stv(prior, &evidence)
    }
}

fn prior_proof_signature(group: &PriorRuleGroup) -> Vec<u8> {
    fn current_proof_ids(rows: &BTreeMap<Vec<u8>, BTreeSet<ProofRow>>) -> Vec<Vec<u8>> {
        let mut proof_ids = Vec::new();
        for goal_rows in rows.values() {
            proof_ids.extend(
                select_current_snapshot_proofs(goal_rows)
                    .into_iter()
                    .map(|(_stv, proof_id, _evset)| proof_id),
            );
        }
        proof_ids.sort();
        proof_ids.dedup();
        proof_ids
    }

    let antecedent_ids = current_proof_ids(&group.antecedent_rows);
    let consequent_ids = current_proof_ids(&group.consequent_rows);
    let antecedent_refs: Vec<&[u8]> = antecedent_ids.iter().map(Vec::as_slice).collect();
    let consequent_refs: Vec<&[u8]> = consequent_ids.iter().map(Vec::as_slice).collect();
    let mut antecedent = Vec::new();
    let mut consequent = Vec::new();
    push_expr(&mut antecedent, "antecedent-proofs", &antecedent_refs);
    push_expr(&mut consequent, "consequent-proofs", &consequent_refs);
    let mut signature = Vec::new();
    push_expr(
        &mut signature,
        "prior-proof-set",
        &[&antecedent, &consequent],
    );
    signature
}

impl Sink for PriorRuleStvSink {
    fn new(_e: Expr) -> Self {
        Self {
            groups: BTreeMap::new(),
        }
    }

    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        std::iter::once(WriteResourceRequest::BTM([].as_slice()))
    }

    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let args = expr_args(&path[wz.root_prefix_path().len()..]);
        assert_eq!(args.len(), 21, "prior-rule-stv expects 20 payload args");
        assert_eq!(symbol_str(args[0]), "prior-rule-stv");

        let key = PriorRuleKey {
            goal: args[1].to_vec(),
            premise_stv: args[2].to_vec(),
            rule_stv: args[3].to_vec(),
            kb: args[4].to_vec(),
            antecedent: args[5].to_vec(),
            consequent: args[6].to_vec(),
            proof_id: args[7].to_vec(),
            evset: args[8].to_vec(),
            mass: args[9].to_vec(),
            antecedent_prior: args[10].to_vec(),
            consequent_prior: args[11].to_vec(),
            divisor: args[12].to_vec(),
        };
        let Some(subject) = inheritance_subject(&key.goal) else {
            return;
        };
        let mut is_forward_observed = |goal: &[u8], proof: &[u8]| {
            let mode = symbol_bytes("forward-observed");
            let mut marker = Vec::new();
            push_expr(
                &mut marker,
                "forward-prior-observation",
                &[goal, proof, &mode],
            );
            wz.reset();
            wz.move_to_path(&marker);
            let exists = wz.path_exists();
            wz.reset();
            exists
        };
        let antecedent_candidate = prior_candidate_goal(args[13], args[15]);
        let antecedent_forward = antecedent_candidate
            .map(|(goal, mode)| mode || is_forward_observed(goal, args[15]))
            .unwrap_or(false);
        let consequent_candidate = prior_candidate_goal(args[17], args[19]);
        let consequent_forward = consequent_candidate
            .map(|(goal, mode)| mode || is_forward_observed(goal, args[19]))
            .unwrap_or(false);
        drop(is_forward_observed);
        let group = self.groups.entry(key.clone()).or_default();

        let add_candidate =
            |goal: &[u8],
             stv: &[u8],
             proof: &[u8],
             evset: &[u8],
             exclude_current_subject: bool,
             forward_observed: bool,
             target: &mut BTreeMap<Vec<u8>, BTreeSet<ProofRow>>| {
                if !forward_observed
                    && ((exclude_current_subject && inheritance_subject(goal) == Some(subject))
                        || !prior_candidate_allowed(proof)
                        || evidence_dependent(&key.evset, evset))
                {
                    return;
                }
                target.entry(goal.to_vec()).or_default().insert((
                    stv.to_vec(),
                    proof.to_vec(),
                    evset.to_vec(),
                ));
            };
        if let Some((goal, _mode)) = antecedent_candidate {
            add_candidate(
                goal,
                args[14],
                args[15],
                args[16],
                false,
                antecedent_forward,
                &mut group.antecedent_rows,
            );
        }
        if let Some((goal, _mode)) = consequent_candidate {
            add_candidate(
                goal,
                args[18],
                args[19],
                args[20],
                true,
                consequent_forward,
                &mut group.consequent_rows,
            );
        }
    }

    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();
        let mut add = PathMap::new();

        for (key, group) in &self.groups {
            let signature = prior_proof_signature(group);
            let mut snapshot = Vec::new();
            push_expr(
                &mut snapshot,
                "prior-stv-snapshot",
                &[&key.goal, &key.premise_stv, &key.proof_id, &signature],
            );
            wz.reset();
            wz.move_to_path(&snapshot[wz.root_prefix_path().len()..]);
            if wz.path_exists() {
                continue;
            }
            add.insert(&snapshot, ());

            let divisor = stv_f64(&key.divisor, "divisor").max(f64::EPSILON);
            let antecedent = prior_weighted_base_rate(
                &group.antecedent_rows,
                &key.mass,
                &key.antecedent_prior,
                divisor,
            );
            let consequent = prior_weighted_base_rate(
                &group.consequent_rows,
                &key.mass,
                &key.consequent_prior,
                divisor,
            );
            let (ante_s, ante_c) = stv_parts(&antecedent);
            let (cons_s, cons_c) = stv_parts(&consequent);
            let (rule_s, rule_c) = stv_parts(&key.rule_stv);
            let neg_s = if ante_s >= 1.0 {
                cons_s
            } else {
                ((cons_s - ante_s * rule_s) / (1.0 - ante_s)).clamp(0.0, 1.0)
            };
            let neg_c = 0.25 * ante_c.min(cons_c).min(rule_c);
            let negative = stv_bytes(neg_s, neg_c);
            let proof_stv = OrStvSink::mp_stv(&key.premise_stv, &key.rule_stv, &negative);

            let mut open_proof = Vec::new();
            push_expr(
                &mut open_proof,
                "open-proof",
                &[&key.goal, &proof_stv, &key.proof_id, &key.evset],
            );
            add.insert(&open_proof, ());
        }

        // Keep the grounded application active.  Its FoldAll marginals are
        // late-bound: proofs discovered by another rule in a later step must
        // be able to replace this rule's earlier prior-only snapshot.  The
        // A prior-stv-snapshot marker makes this event-driven: a stable
        // application does not keep producing floating-point refinements.
        wz.reset();
        let added = !matches!(wz.join_into(&add.read_zipper()), AlgebraicStatus::Identity);
        added
    }
}

pub struct PairCountsSink {
    unique: PathMap<()>,
}

impl PairCountsSink {
    fn pair_counts_from_values(values: &BTreeMap<Vec<u8>, u64>) -> Vec<u8> {
        let mut pairs = Vec::new();
        let one = symbol_bytes("1.0");
        let mut pairs_by_value: Vec<_> = values.iter().collect();
        pairs_by_value.sort_by(|(a, _), (b, _)| serialize(a).cmp(&serialize(b)));

        for (value, count) in pairs_by_value {
            let mass = if *count == 1 {
                one.clone()
            } else {
                symbol_bytes(&format!("{count}.0"))
            };
            let mut pair = Vec::new();
            push_raw_expr(&mut pair, &[value, &mass]);
            pairs.push(pair);
        }

        let mut pair_list = Vec::new();
        pair_list.push(item_byte(Tag::Arity(pairs.len() as u8)));
        for pair in &pairs {
            pair_list.extend_from_slice(pair);
        }

        let mut out = Vec::new();
        push_expr(&mut out, "PairCounts", &[&pair_list]);
        out
    }
}

impl Sink for PairCountsSink {
    fn new(_e: Expr) -> Self {
        PairCountsSink {
            unique: PathMap::new(),
        }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        std::iter::once(WriteResourceRequest::BTM([].as_slice()))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let mpath = &path[wz.root_prefix_path().len()..];
        let args = expr_args(mpath);
        assert_eq!(args.len(), 4, "pair-counts expects 3 payload args");
        assert_eq!(symbol_str(args[0]), "pair-counts");
        self.unique.insert(mpath, ());
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();

        let mut groups: BTreeMap<Vec<u8>, BTreeMap<Vec<u8>, u64>> = BTreeMap::new();
        let mut outputs: BTreeMap<Vec<u8>, Vec<u8>> = BTreeMap::new();
        let mut output_vars: BTreeMap<Vec<u8>, Vec<u8>> = BTreeMap::new();

        for (path, ()) in self.unique.iter() {
            let args = expr_args(&path);
            let output = args[1].to_vec();
            let output_var = args[2].to_vec();
            let value = args[3].to_vec();
            let mut key = output.clone();
            key.extend_from_slice(&output_var);
            outputs.entry(key.clone()).or_insert(output);
            output_vars.entry(key.clone()).or_insert(output_var);
            *groups.entry(key).or_default().entry(value).or_default() += 1;
        }
        self.unique = PathMap::new();

        let mut changed = false;
        let mut buffer: Vec<u8> = Vec::with_capacity(1 << 20);
        for (key, values) in groups {
            let output = outputs.get(&key).unwrap();
            let output_var = output_vars.get(&key).unwrap();
            let pair_counts = PairCountsSink::pair_counts_from_values(&values);

            match byte_item(output_var[0]) {
                Tag::VarRef(k) => {
                    let ie = Expr {
                        ptr: output.as_ptr().cast_mut(),
                    };
                    let mut replacement = pair_counts;
                    let mut oz = ExprZipper::new(Expr {
                        ptr: buffer.as_mut_ptr(),
                    });
                    ie.substitute_one_de_bruijn(
                        k,
                        Expr {
                            ptr: replacement.as_mut_ptr(),
                        },
                        &mut oz,
                    );
                    unsafe { buffer.set_len(oz.loc) }
                    wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                    changed |= wz.set_val(()).is_none();
                    buffer.clear();
                }
                Tag::NewVar => {
                    wz.move_to_path(output);
                    changed |= wz.set_val(()).is_none();
                }
                _ => {
                    if output_var == &pair_counts[..] {
                        wz.move_to_path(output);
                        changed |= wz.set_val(()).is_none();
                    }
                }
            }
        }

        changed
    }
}

#[derive(Default)]
struct OrderedCollectGroup {
    output: Vec<u8>,
    output_var: Vec<u8>,
    descending: bool,
    rows: Vec<(Vec<u8>, Vec<u8>)>,
}

/// `(group-collect $output $result $group asc|desc $order $item)` gathers all
/// rows for each grounded group, orders them deterministically by `$order` and
/// then `$item`, builds a canonical pcons list, substitutes it for `$result` in
/// `$output`, and emits one output atom per group during sink finalization.
pub struct OrderedCollectSink {
    groups: BTreeMap<Vec<u8>, OrderedCollectGroup>,
}

#[derive(Default)]
struct VectorFloatSumGroup {
    output: Vec<u8>,
    output_var: Vec<u8>,
    rows: Vec<(Vec<u8>, Vec<f64>)>,
}

/// `(vfsum $output $result ($value ...) $order)` sums numeric vectors per
/// output group in explicit order and substitutes a tuple of component sums.
pub struct VectorFloatSumSink {
    groups: BTreeMap<Vec<u8>, VectorFloatSumGroup>,
}

impl Sink for VectorFloatSumSink {
    fn new(_e: Expr) -> Self {
        Self {
            groups: BTreeMap::new(),
        }
    }

    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        std::iter::once(WriteResourceRequest::BTM([].as_slice()))
    }

    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let row = &path[wz.root_prefix_path().len()..];
        let args = expr_args(row);
        assert_eq!(args.len(), 5, "vfsum expects 4 payload arguments");
        assert!(is_symbol(args[0], "vfsum"));
        let values = expr_args(args[3])
            .into_iter()
            .map(|value| str::parse::<f64>(symbol_str(value)).unwrap())
            .collect();
        let output = args[1].to_vec();
        let output_var = args[2].to_vec();
        let mut key = output.clone();
        key.extend_from_slice(&output_var);
        let group = self
            .groups
            .entry(key)
            .or_insert_with(|| VectorFloatSumGroup {
                output,
                output_var,
                rows: Vec::new(),
            });
        group.rows.push((args[4].to_vec(), values));
    }

    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();
        let mut groups = BTreeMap::new();
        std::mem::swap(&mut groups, &mut self.groups);
        let mut changed = false;
        let mut buffer = Vec::with_capacity(1 << 20);

        for (_, mut group) in groups {
            group.rows.sort_by(|left, right| left.0.cmp(&right.0));
            let width = group.rows.first().map_or(0, |row| row.1.len());
            let mut totals = vec![0.0; width];
            for (_, values) in group.rows {
                assert_eq!(
                    values.len(),
                    width,
                    "vfsum vector width differs within group"
                );
                for (total, value) in totals.iter_mut().zip(values) {
                    *total += value;
                }
            }
            let mut tuple = vec![item_byte(Tag::Arity(width as u8))];
            for total in totals {
                tuple.extend_from_slice(&symbol_bytes(&total.to_string()));
            }

            match byte_item(group.output_var[0]) {
                Tag::VarRef(k) => {
                    let output = Expr {
                        ptr: group.output.as_ptr().cast_mut(),
                    };
                    buffer.push(item_byte(Tag::NewVar));
                    let mut oz = ExprZipper::new(Expr {
                        ptr: buffer.as_mut_ptr(),
                    });
                    output.substitute_one_de_bruijn(
                        k,
                        Expr {
                            ptr: tuple.as_mut_ptr(),
                        },
                        &mut oz,
                    );
                    unsafe { buffer.set_len(oz.loc) }
                    wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                    changed |= wz.set_val(()).is_none();
                    buffer.clear();
                }
                Tag::NewVar => {
                    wz.move_to_path(&group.output);
                    changed |= wz.set_val(()).is_none();
                }
                _ if group.output_var == tuple => {
                    wz.move_to_path(&group.output);
                    changed |= wz.set_val(()).is_none();
                }
                _ => {}
            }
        }
        changed
    }
}

impl OrderedCollectSink {
    fn pcons_list(items: impl DoubleEndedIterator<Item = Vec<u8>>) -> Vec<u8> {
        let mut out = symbol_bytes("pnil");
        for item in items.rev() {
            let mut next = Vec::new();
            push_expr(&mut next, "pcons", &[&item, &out]);
            out = next;
        }
        out
    }
}

impl Sink for OrderedCollectSink {
    fn new(_e: Expr) -> Self {
        Self {
            groups: BTreeMap::new(),
        }
    }

    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        std::iter::once(WriteResourceRequest::BTM([].as_slice()))
    }

    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let row = &path[wz.root_prefix_path().len()..];
        let args = expr_args(row);
        assert_eq!(args.len(), 7, "group-collect expects 6 payload arguments");
        assert!(is_symbol(args[0], "group-collect"));

        let descending = if is_symbol(args[4], "asc") {
            false
        } else if is_symbol(args[4], "desc") {
            true
        } else {
            panic!("group-collect direction must be asc or desc");
        };
        let group = self.groups.entry(args[3].to_vec()).or_default();
        if group.output.is_empty() {
            group.output = args[1].to_vec();
            group.output_var = args[2].to_vec();
            group.descending = descending;
        } else {
            assert_eq!(group.output, args[1], "group-collect output differs within group");
            assert_eq!(
                group.output_var, args[2],
                "group-collect result slot differs within group"
            );
            assert_eq!(
                group.descending, descending,
                "group-collect direction differs within group"
            );
        }
        group.rows.push((args[5].to_vec(), args[6].to_vec()));
    }

    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();
        let mut groups = BTreeMap::new();
        std::mem::swap(&mut groups, &mut self.groups);
        let mut changed = false;
        let mut buffer = Vec::with_capacity(1 << 20);

        for (_, mut group) in groups {
            group
                .rows
                .sort_by(|left, right| left.0.cmp(&right.0).then_with(|| left.1.cmp(&right.1)));
            if group.descending {
                group.rows.reverse();
            }
            let list = Self::pcons_list(group.rows.into_iter().map(|(_, item)| item));
            match byte_item(group.output_var[0]) {
                Tag::VarRef(k) => {
                    let output = Expr {
                        ptr: group.output.as_ptr().cast_mut(),
                    };
                    let mut replacement = list;
                    buffer.push(item_byte(Tag::NewVar));
                    let mut oz = ExprZipper::new(Expr {
                        ptr: buffer.as_mut_ptr(),
                    });
                    output.substitute_one_de_bruijn(
                        k,
                        Expr {
                            ptr: replacement.as_mut_ptr(),
                        },
                        &mut oz,
                    );
                    unsafe { buffer.set_len(oz.loc) }
                    wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                    changed |= wz.set_val(()).is_none();
                    buffer.clear();
                }
                Tag::NewVar => {
                    wz.move_to_path(&group.output);
                    changed |= wz.set_val(()).is_none();
                }
                _ if group.output_var == list => {
                    wz.move_to_path(&group.output);
                    changed |= wz.set_val(()).is_none();
                }
                _ => {}
            }
        }
        changed
    }
}

pub struct DistAverageSink {
    groups: BTreeMap<Vec<u8>, BTreeMap<Vec<u8>, Vec<(f64, f64)>>>,
}

fn write_dist_convolution(
    groups: &BTreeMap<Vec<u8>, BTreeMap<Vec<u8>, Vec<(f64, f64)>>>,
    average: bool,
) -> PathMap<()> {
    let mut add = PathMap::new();
    for (result_pid, sources) in groups {
        if sources.is_empty() {
            continue;
        }

        let mut sums = vec![(0.0, 1.0)];
        for pairs in sources.values() {
            let mut next = Vec::with_capacity(sums.len() * pairs.len());
            for (sum, mass) in &sums {
                for (x, w) in pairs {
                    next.push((sum + x, mass * w));
                }
            }
            sums = next;
        }

        let divisor = if average { sources.len() as f64 } else { 1.0 };
        let mut values: BTreeMap<String, f64> = BTreeMap::new();
        for (sum, mass) in sums {
            let value = (sum / divisor).to_string();
            *values.entry(value).or_default() += mass;
        }

        for (value, mass) in values {
            if mass == 0.0 {
                continue;
            }
            let value_bytes = symbol_bytes(&value);
            let mass_bytes = symbol_bytes(&mass.to_string());
            let mut atom = Vec::new();
            push_expr(
                &mut atom,
                "dist-pair",
                &[result_pid, &value_bytes[..], &mass_bytes[..]],
            );
            add.insert(&atom[..], ());
        }
    }
    add
}

impl Sink for DistAverageSink {
    fn new(_e: Expr) -> Self {
        DistAverageSink {
            groups: BTreeMap::new(),
        }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        std::iter::once(WriteResourceRequest::BTM([].as_slice()))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let mpath = &path[wz.root_prefix_path().len()..];
        let args = expr_args(mpath);
        assert_eq!(args.len(), 5, "dist-average expects 4 payload args");
        assert_eq!(symbol_str(args[0]), "dist-average");

        let result_pid = args[1].to_vec();
        let source = args[2].to_vec();
        let x = stv_f64(args[3], "distribution value");
        let w = stv_f64(args[4], "distribution weight");
        self.groups
            .entry(result_pid)
            .or_default()
            .entry(source)
            .or_default()
            .push((x, w));
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();

        let add = write_dist_convolution(&self.groups, true);
        self.groups.clear();

        match wz.join_into(&add.read_zipper()) {
            AlgebraicStatus::Element => true,
            AlgebraicStatus::Identity => false,
            AlgebraicStatus::None => true,
        }
    }
}

pub struct DistSumSink {
    groups: BTreeMap<Vec<u8>, BTreeMap<Vec<u8>, Vec<(f64, f64)>>>,
}

impl Sink for DistSumSink {
    fn new(_e: Expr) -> Self {
        DistSumSink {
            groups: BTreeMap::new(),
        }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        std::iter::once(WriteResourceRequest::BTM([].as_slice()))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let mpath = &path[wz.root_prefix_path().len()..];
        let args = expr_args(mpath);
        assert_eq!(args.len(), 5, "dist-sum expects 4 payload args");
        assert_eq!(symbol_str(args[0]), "dist-sum");

        let result_pid = args[1].to_vec();
        let source = args[2].to_vec();
        let x = stv_f64(args[3], "distribution value");
        let w = stv_f64(args[4], "distribution weight");
        self.groups
            .entry(result_pid)
            .or_default()
            .entry(source)
            .or_default()
            .push((x, w));
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();

        let add = write_dist_convolution(&self.groups, false);
        self.groups.clear();

        match wz.join_into(&add.read_zipper()) {
            AlgebraicStatus::Element => true,
            AlgebraicStatus::Identity => false,
            AlgebraicStatus::None => true,
        }
    }
}

pub struct OrStvSink {
    unique: PathMap<()>,
}

type OrStvKey = (Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>);
type OrStvRow = (Vec<u8>, Vec<u8>, Vec<u8>);

impl OrStvSink {
    fn ideal_clip(strength: f64) -> f64 {
        strength.clamp(0.000001, 0.999999)
    }

    fn ideal_var(strength: f64, confidence: f64) -> f64 {
        let clipped = Self::ideal_clip(strength);
        clipped * (1.0 - clipped) / (confidence_to_count(confidence) + 1.0)
    }

    fn ideal_conf_from_var(strength: f64, var: f64) -> f64 {
        if var <= 0.0 {
            return 0.9999;
        }
        let clipped = Self::ideal_clip(strength);
        let maxvar = clipped * (1.0 - clipped);
        let n = maxvar / var.min(maxvar) - 1.0;
        (n / (n + 800.0)).max(0.000001)
    }

    fn ideal_prod_confidence(s1: f64, v1: f64, s2: f64, v2: f64, strength: f64) -> f64 {
        let var = (v1 * v2) + ((v1 * (s2 * s2)) + ((s1 * s1) * v2));
        Self::ideal_conf_from_var(strength, var)
    }

    fn or_stv(left: &[u8], right: &[u8]) -> Vec<u8> {
        let (left_s, left_c) = stv_parts(left);
        let (right_s, right_c) = stv_parts(right);
        let strength = left_s + right_s - (left_s * right_s);
        let confidence = if left_c <= 0.0 || right_c <= 0.0 {
            0.0
        } else {
            Self::ideal_prod_confidence(
                1.0 - left_s,
                Self::ideal_var(left_s, left_c),
                1.0 - right_s,
                Self::ideal_var(right_s, right_c),
                strength,
            )
        };
        stv_bytes(strength, confidence)
    }

    fn mp_stv(premise: &[u8], pos: &[u8], neg: &[u8]) -> Vec<u8> {
        let (premise_s, premise_c) = stv_parts(premise);
        let (pos_s, pos_c) = stv_parts(pos);
        let (neg_s, neg_c) = stv_parts(neg);
        let strength = pos_s * premise_s + neg_s * (1.0 - premise_s);
        let confidence = {
            let v_pos = Self::ideal_var(pos_s, pos_c);
            let v_neg = Self::ideal_var(neg_s, neg_c);
            let v_premise = Self::ideal_var(premise_s, premise_c);
            let var = ((premise_s * premise_s) * v_pos)
                + ((((1.0 - premise_s) * (1.0 - premise_s)) * v_neg)
                    + ((((pos_s - neg_s) * (pos_s - neg_s)) * v_premise)
                        + (v_premise * (v_pos + v_neg))));
            Self::ideal_conf_from_var(strength, var)
        };
        stv_bytes(strength, confidence)
    }

    fn proof_id(rule_id: &[u8], proof_ids: &[Vec<u8>]) -> Vec<u8> {
        let proof_refs: Vec<&[u8]> = proof_ids.iter().map(Vec::as_slice).collect();
        let mut disjunction = Vec::new();
        push_expr(&mut disjunction, "disjunction", &proof_refs);

        let mut proof = Vec::new();
        push_raw_expr(&mut proof, &[rule_id, &disjunction[..]]);
        proof
    }
}

impl Sink for OrStvSink {
    fn new(_e: Expr) -> Self {
        OrStvSink {
            unique: PathMap::new(),
        }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        std::iter::once(WriteResourceRequest::BTM([].as_slice()))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let mpath = &path[wz.root_prefix_path().len()..];
        let args = expr_args(mpath);
        assert_eq!(args.len(), 8, "or-stv expects 7 payload args");
        assert_eq!(symbol_str(args[0]), "or-stv");
        self.unique.insert(mpath, ());
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();

        let mut groups: BTreeMap<OrStvKey, Vec<OrStvRow>> = BTreeMap::new();
        for (path, ()) in self.unique.iter() {
            let args = expr_args(&path);
            let key = (
                args[1].to_vec(),
                args[2].to_vec(),
                args[3].to_vec(),
                args[4].to_vec(),
            );
            groups.entry(key).or_default().push((
                args[5].to_vec(),
                args[6].to_vec(),
                args[7].to_vec(),
            ));
        }
        self.unique = PathMap::new();

        let mut add = PathMap::new();
        for ((goal, rule_id, pos, neg), mut rows) in groups {
            rows.sort_by(|(left_stv, left_proof, _), (right_stv, right_proof, _)| {
                let (left_s, _) = stv_parts(left_stv);
                let (right_s, _) = stv_parts(right_stv);
                right_s
                    .partial_cmp(&left_s)
                    .unwrap_or(Ordering::Equal)
                    .then_with(|| serialize(left_proof).cmp(&serialize(right_proof)))
            });
            let mut acc = stv_bytes(0.0, 1.0);
            let mut proof_ids = Vec::new();
            let mut evidence = symbol_bytes("pnil");
            for (stv, proof_id, evset) in rows {
                acc = OrStvSink::or_stv(&acc, &stv);
                proof_ids.push(proof_id);
                evidence = evidence_union(&evidence, &evset);
            }
            let proof_stv = OrStvSink::mp_stv(&acc, &pos, &neg);
            let proof_id = OrStvSink::proof_id(&rule_id, &proof_ids);

            let mut open_proof = Vec::new();
            push_expr(
                &mut open_proof,
                "open-proof",
                &[&goal[..], &proof_stv[..], &proof_id[..], &evidence[..]],
            );
            add.insert(&open_proof[..], ());
        }

        match wz.join_into(&add.read_zipper()) {
            AlgebraicStatus::Element => true,
            AlgebraicStatus::Identity => false,
            AlgebraicStatus::None => true,
        }
    }
}

pub struct TotalEvidenceMpSink {
    unique: PathMap<()>,
}

type TotalEvidenceMpKey = (Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>);
type TotalEvidenceMpRow = (Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>);

impl TotalEvidenceMpSink {
    fn fold_or(rows: &mut [TotalEvidenceMpRow]) -> Vec<u8> {
        rows.sort_by(
            |(_, left_stv, left_proof, _), (_, right_stv, right_proof, _)| {
                let (left_s, _) = stv_parts(left_stv);
                let (right_s, _) = stv_parts(right_stv);
                right_s
                    .partial_cmp(&left_s)
                    .unwrap_or(Ordering::Equal)
                    .then_with(|| serialize(left_proof).cmp(&serialize(right_proof)))
            },
        );

        let mut acc: Option<Vec<u8>> = None;
        for (_, stv, _, _) in rows {
            acc = Some(match acc {
                Some(ref current) => OrStvSink::or_stv(current, stv),
                None => stv.clone(),
            });
        }
        acc.unwrap_or_else(|| stv_bytes(0.0, 0.0))
    }

    fn proof_id(proof_id: &[u8], rows: &[TotalEvidenceMpRow]) -> Vec<u8> {
        let proof_ids: Vec<&[u8]> = rows
            .iter()
            .map(|(_, _, proof, _)| proof.as_slice())
            .collect();
        let mut foldall = Vec::new();
        push_expr(&mut foldall, "foldall-proof", &proof_ids);

        let mut proof = Vec::new();
        push_expr(
            &mut proof,
            "total-evidence-proof",
            &[proof_id, &foldall[..]],
        );
        proof
    }
}

impl Sink for TotalEvidenceMpSink {
    fn new(_e: Expr) -> Self {
        TotalEvidenceMpSink {
            unique: PathMap::new(),
        }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        std::iter::once(WriteResourceRequest::BTM([].as_slice()))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let mpath = &path[wz.root_prefix_path().len()..];
        let args = expr_args(mpath);
        assert_eq!(args.len(), 11, "total-evidence-mp expects 11 payload args");
        assert_eq!(symbol_str(args[0]), "total-evidence-mp");
        self.unique.insert(mpath, ());
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();

        let mut groups: BTreeMap<TotalEvidenceMpKey, Vec<TotalEvidenceMpRow>> = BTreeMap::new();
        for (path, ()) in self.unique.iter() {
            let args = expr_args(&path);
            if args[4] == args[5] {
                continue;
            }
            let key = (
                args[1].to_vec(),
                args[2].to_vec(),
                args[3].to_vec(),
                args[4].to_vec(),
                args[5].to_vec(),
                args[10].to_vec(),
            );
            groups.entry(key).or_default().push((
                args[6].to_vec(),
                args[7].to_vec(),
                args[8].to_vec(),
                args[9].to_vec(),
            ));
        }
        self.unique = PathMap::new();

        let mut add = PathMap::new();
        for ((goal, proof_id, ante_stv, _p1, _p2, ante_evset), rows) in groups {
            let mut pos_rows = Vec::new();
            let mut neg_rows = Vec::new();
            let mut evidence = ante_evset;

            for row in rows {
                evidence = evidence_union(&evidence, &row.3);
                if is_symbol(&row.0, "pos") {
                    pos_rows.push(row);
                } else if is_symbol(&row.0, "neg") {
                    neg_rows.push(row);
                }
            }

            let pos = Self::fold_or(&mut pos_rows);
            let neg = Self::fold_or(&mut neg_rows);
            let proof_stv = OrStvSink::mp_stv(&ante_stv, &pos, &neg);

            let mut proof_rows = pos_rows;
            proof_rows.extend(neg_rows);
            let proof = Self::proof_id(&proof_id, &proof_rows);

            let mut open_proof = Vec::new();
            push_expr(
                &mut open_proof,
                "open-proof",
                &[&goal[..], &proof_stv[..], &proof[..], &evidence[..]],
            );
            add.insert(&open_proof[..], ());
        }

        match wz.join_into(&add.read_zipper()) {
            AlgebraicStatus::Element => true,
            AlgebraicStatus::Identity => false,
            AlgebraicStatus::None => true,
        }
    }
}

impl Sink for ReviseProofsSink {
    fn new(_e: Expr) -> Self {
        ReviseProofsSink {
            groups: BTreeMap::new(),
        }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        std::iter::once(WriteResourceRequest::BTM([].as_slice()))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let mpath = &path[wz.root_prefix_path().len()..];
        let args = expr_args(mpath);
        assert!(
            args.len() == 4 || args.len() == 5 || args.len() == 6 || args.len() == 7,
            "revise-proofs expects 3, 4, 5, or 6 payload args"
        );
        assert_eq!(symbol_str(args[0]), "revise-proofs");

        let group = self.groups.entry(args[1].to_vec()).or_default();
        let empty_evidence = symbol_bytes("pnil");
        match args.len() {
            4 => {
                group
                    .proofs
                    .insert((args[3].to_vec(), args[2].to_vec(), empty_evidence));
            }
            5 => {
                group
                    .proofs
                    .insert((args[3].to_vec(), args[2].to_vec(), args[4].to_vec()));
            }
            6 => {
                assert_eq!(symbol_str(args[2]), "existing");
                group.existing_proofs.insert((
                    args[4].to_vec(),
                    args[3].to_vec(),
                    args[5].to_vec(),
                ));
            }
            7 => {
                group
                    .proofs
                    .insert((args[3].to_vec(), args[2].to_vec(), args[4].to_vec()));
                group.old_facts.insert((args[5].to_vec(), args[6].to_vec()));
            }
            _ => unreachable!(),
        }
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();
        let mut remove = PathMap::new();
        let mut add = PathMap::new();
        let mut fact_stvs = None;
        let mut proved_rows = None;

        for (goal, group) in &self.groups {
            let current_proofs = select_current_snapshot_proofs(&group.proofs);
            let existing_goal_proofs = proved_rows
                .get_or_insert_with(|| collect_proved_rows(wz))
                .get(goal)
                .cloned()
                .unwrap_or_default();
            // Generated inheritance views remain backward proof alternatives,
            // but they do not revise a primary asserted/ordinary positive
            // proof into a different canonical forward premise. A refutation
            // is different: it must still revise with a generated positive
            // view (Flying Raven's Penguin counter-evidence), independent of
            // which proof happens to reach this sink first.
            let has_primary_positive_proof = current_proofs
                .iter()
                .chain(existing_goal_proofs.iter())
                .any(|(_stv, proof_id, _evset)| {
                    !is_generated_inheritance_view_proof(proof_id)
                        && !is_inheritance_refutation_proof(proof_id)
                });
            let canonical_current_proofs: BTreeSet<_> = current_proofs
                .iter()
                .filter(|(_stv, proof_id, _evset)| {
                    !has_primary_positive_proof || !is_generated_inheritance_view_proof(proof_id)
                })
                .cloned()
                .collect();
            let mut factor_rows = BTreeSet::new();
            if group.old_facts.is_empty() {
                factor_rows.extend(canonical_current_proofs.iter().cloned());
            } else {
                factor_rows.extend(
                    group
                        .existing_proofs
                        .iter()
                        .filter(|(_stv, proof_id, _evset)| {
                            !has_primary_positive_proof
                                || !is_generated_inheritance_view_proof(proof_id)
                        })
                        .cloned(),
                );
                factor_rows.extend(
                    existing_goal_proofs
                        .iter()
                        .filter(|stored| {
                            (!has_primary_positive_proof
                                || !is_generated_inheritance_view_proof(&stored.1))
                                && !canonical_current_proofs
                                    .iter()
                                    .any(|current| proof_identity_equal(stored, current))
                        })
                        .cloned(),
                );
                if !factor_rows.is_empty() {
                    factor_rows.extend(canonical_current_proofs.iter().cloned());
                }
            }
            let factored = if factor_rows.len() >= 2 {
                factor_merge_all_shared_proofs(&factor_rows).or_else(|| {
                    if all_scheduled_ctv_proof_rows(&factor_rows) {
                        let facts = fact_stvs.get_or_insert_with(|| collect_fact_stvs(wz));
                        let proved = proved_rows.get_or_insert_with(|| collect_proved_rows(wz));
                        factor_merge_with_fact_stvs(&factor_rows, facts, proved)
                    } else {
                        None
                    }
                })
            } else {
                None
            };
            let mut merged = if factor_rows.len() == 1 {
                factor_rows
                    .iter()
                    .next()
                    .map(|(stv, _proof_id, evset)| (stv.clone(), evset.clone()))
            } else {
                factored
                    .clone()
                    .or_else(|| group.old_facts.iter().next().cloned())
            };
            for (old_stv, old_ev) in &group.old_facts {
                let mut fact = Vec::new();
                push_expr(&mut fact, "fact", &[goal, old_stv]);
                remove.insert(&fact[..], ());

                let mut fact_evidence = Vec::new();
                push_expr(
                    &mut fact_evidence,
                    "fact-evidence",
                    &[goal, old_stv, old_ev],
                );
                remove.insert(&fact_evidence[..], ());
            }
            for (stv, proof_id, evset) in &current_proofs {
                let mut open_proof = Vec::new();
                push_expr(&mut open_proof, "open-proof", &[goal, stv, proof_id, evset]);
                remove.insert(&open_proof[..], ());

                // A refined snapshot supersedes its alpha-equivalent stored
                // proof before revision, for ordinary and inversion rules.
                let current = (stv.clone(), proof_id.clone(), evset.clone());
                for (old_stv, old_proof_id, old_evset) in &existing_goal_proofs {
                    let old = (old_stv.clone(), old_proof_id.clone(), old_evset.clone());
                    if proof_identity_equal(&old, &current) {
                        let mut old_proved = Vec::new();
                        push_expr(
                            &mut old_proved,
                            "proved",
                            &[goal, old_stv, old_proof_id, old_evset],
                        );
                        remove.insert(&old_proved[..], ());
                    }
                }

                let mut proved = Vec::new();
                push_expr(&mut proved, "proved", &[goal, stv, proof_id, evset]);
                add.insert(&proved[..], ());

                // Query-local lift producers are private frontier goals. A
                // producer embeds its public target and all downstream goals,
                // so publish every revised proof snapshot here while the sink
                // is already iterating the complete proof group. Doing this at
                // proof revision avoids first-match exec ordering entirely.
                if matches!(byte_item(goal[0]), Tag::Arity(_)) {
                    let producer = expr_args(goal);
                    if producer.len() == 5 && is_symbol(producer[0], "mm2-query-producer") {
                        let mut published_proof = Vec::new();
                        push_expr(&mut published_proof, "query-producer", &[proof_id]);
                        let mut published = Vec::new();
                        push_expr(
                            &mut published,
                            "open-proof",
                            &[producer[2], stv, &published_proof, evset],
                        );
                        add.insert(&published, ());

                        let mut downstreams = Vec::new();
                        if collect_pcons(producer[4], &mut downstreams) {
                            for downstream in downstreams {
                                let mut downstream_goal = Vec::new();
                                push_expr(&mut downstream_goal, "Goal", &[&downstream]);
                                let mut token = Vec::new();
                                push_expr(&mut token, ",", &[&downstream_goal]);
                                add.insert(&token, ());
                            }
                        }
                    }
                }

                if factored.is_none() && canonical_current_proofs.contains(&current) {
                    let depends_on_goal = if group.old_facts.is_empty() {
                        false
                    } else {
                        let proved = proved_rows.get_or_insert_with(|| collect_proved_rows(wz));
                        evidence_depends_on_fact(evset, goal, proved)
                    };
                    merged = Some(match merged {
                        Some((ref old_stv, ref old_ev)) if depends_on_goal => {
                            (old_stv.clone(), old_ev.clone())
                        }
                        Some((ref old_stv, ref old_ev))
                            if is_inversion_snapshot_proof(proof_id)
                                && evidence_equal(old_ev, evset) =>
                        {
                            (stv.clone(), evset.clone())
                        }
                        Some((ref old_stv, ref old_ev)) => {
                            merge_evidenced_stv(old_stv, old_ev, stv, evset)
                        }
                        None => (stv.clone(), evset.clone()),
                    });
                }
            }
            if let Some((stv, evset)) = merged {
                let mut fact = Vec::new();
                push_expr(&mut fact, "fact", &[goal, &stv[..]]);
                add.insert(&fact[..], ());

                let mut fact_evidence = Vec::new();
                push_expr(
                    &mut fact_evidence,
                    "fact-evidence",
                    &[goal, &stv[..], &evset[..]],
                );
                add.insert(&fact_evidence[..], ());
            }
        }

        let removed = match wz.subtract_into(&remove.read_zipper(), true) {
            AlgebraicStatus::Element => true,
            AlgebraicStatus::Identity => false,
            AlgebraicStatus::None => true,
        };
        wz.reset();
        let added = match wz.join_into(&add.read_zipper()) {
            AlgebraicStatus::Element => true,
            AlgebraicStatus::Identity => false,
            AlgebraicStatus::None => true,
        };
        removed || added
    }
}

#[cfg(feature = "wasm")]
pub struct WASMSink {
    e: Expr,
    skip: usize,
    changed: bool,
    module: wasmtime::Module,
    store: wasmtime::Store<()>,
    instance: wasmtime::Instance,
}

#[cfg(feature = "wasm")]
static ENGINE_LINKER: LazyLock<(wasmtime::Engine, wasmtime::Linker<()>)> = LazyLock::new(|| {
    let mut config = wasmtime::Config::new();
    config.wasm_multi_memory(true);
    config.strategy(wasmtime::Strategy::Cranelift);
    config.signals_based_traps(true);
    config.memory_reservation(1 << 32);
    config.memory_guard_size(1 << 32);
    #[cfg(all(target_feature = "avx2"))]
    unsafe {
        config.cranelift_flag_enable("has_sse3");
        config.cranelift_flag_enable("has_ssse3");
        config.cranelift_flag_enable("has_sse41");
        config.cranelift_flag_enable("has_sse42");
        config.cranelift_flag_enable("has_avx");
        config.cranelift_flag_enable("has_avx2");
        config.cranelift_flag_enable("has_bmi1");
        config.cranelift_flag_enable("has_bmi2");
        config.cranelift_flag_enable("has_lzcnt");
        config.cranelift_flag_enable("has_popcnt");
        config.cranelift_flag_enable("has_fma");
    }
    #[cfg(all(target_feature = "avx512"))]
    unsafe {
        config.cranelift_flag_enable("has_avx512bitalg");
        config.cranelift_flag_enable("has_avx512dq");
        config.cranelift_flag_enable("has_avx512vl");
        config.cranelift_flag_enable("has_avx512vbmi");
        config.cranelift_flag_enable("has_avx512f");
    }

    let engine = wasmtime::Engine::new(&config).unwrap();

    let mut linker = wasmtime::Linker::new(&engine);

    linker
        .func_wrap("", "i32.bswap", |param: i32| param.to_be())
        .unwrap();
    linker
        .func_wrap("", "i64.bswap", |param: i64| param.to_be())
        .unwrap();

    (engine, linker)
});

#[cfg(feature = "wasm")]
static mut LINKER: Option<wasmtime::Linker<()>> = None;
macro_rules! wasm_ctx {
    () => {
        r#"
(module
  (import "" "i32.bswap" (func $i32.bswap (param i32) (result i32)))
  (import "" "i64.bswap" (func $i64.bswap (param i64) (result i64)))

  (memory $in 1)
  (export "in" (memory $in))
  (memory $out 1)
  (export "out" (memory $out))
  (memory $local 1)

  (func (export "_otf_grounding")
    {:?}
  )
)
"#
    };
}

#[cfg(feature = "wasm")]
impl Sink for WASMSink {
    fn new(e: Expr) -> Self {
        let mut ez = ExprZipper::new(e);
        ez.next();
        ez.next();
        let program_e = ez.subexpr();
        let wat = format!(wasm_ctx!(), program_e);
        let module = wasmtime::Module::new(&ENGINE_LINKER.0, wat).unwrap();
        let mut store = wasmtime::Store::new(&ENGINE_LINKER.0, ());
        let instance = (&ENGINE_LINKER.1).instantiate(&mut store, &module).unwrap();

        WASMSink {
            e,
            skip: 1 + 1 + 4 + program_e.span().len(),
            changed: false,
            module,
            store,
            instance,
        }
    }
    fn request(&self) -> impl Iterator<Item = &'static [u8]> {
        // let p = &unsafe { self.e.prefix().unwrap_or_else(|x| { let s = self.e.span(); slice_from_raw_parts(self.e.ptr, s.len() - 1) }).as_ref().unwrap() }[self.skip..];
        // trace!(target: "sink", "wasm requesting {}", serialize(p));
        // std::iter::once(p)
        static empty: [u8; 0] = [];
        std::iter::once(&empty[..])
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = &'w mut WriteZipperUntracked<'a, 'k, ()>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let mut wz = it.next().unwrap();
        let mpath = &path[self.skip + wz.root_prefix_path().len()..];
        trace!(target: "sink", "wasm at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "wasm input '{}'", serialize(mpath));
        let imem = self.instance.get_memory(&mut self.store, "in").unwrap();
        imem.write(&mut self.store, 0, mpath).unwrap();
        let run = self
            .instance
            .get_typed_func::<(), ()>(&mut self.store, "_otf_grounding")
            .unwrap();
        match run.call(&mut self.store, ()) {
            Ok(()) => {
                let omem = self
                    .instance
                    .get_memory(&mut self.store, "out")
                    .unwrap()
                    .data(&mut self.store);
                let ospan = unsafe {
                    Expr {
                        ptr: omem.as_ptr().cast_mut(),
                    }
                    .span()
                    .as_ref()
                    .unwrap()
                };
                trace!(target: "sink", "wasm output '{}'", serialize(ospan));
                wz.move_to_path(ospan);
                self.changed |= wz.set_val(()).is_none();
            }
            Err(e) => {
                trace!(target: "sink", "wasm error {:?}", e);
            }
        }
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = &'w mut WriteZipperUntracked<'a, 'k, ()>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        trace!(target: "sink", "wasm finalizing");
        self.changed
    }
}

// ($k $x) (f $x $y)
// (count (count of $k is $i) $i ($x $y))   unify
// (count (count of r2 is $i) $i (P Q))
// (count (count of r2 is 3) 3 ($x $y))
pub struct CountSink {
    e: Expr,
    unique: PathMap<()>,
}
impl Sink for CountSink {
    fn new(e: Expr) -> Self {
        CountSink {
            e,
            unique: PathMap::new(),
        }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        let p = &unsafe {
            self.e
                .prefix()
                .unwrap_or_else(|x| {
                    let s = self.e.span();
                    slice_from_raw_parts(self.e.ptr, s.len() - 1)
                })
                .as_ref()
                .unwrap()
        }[7..];
        trace!(target: "sink", "count requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let mpath = &path[7 + wz.root_prefix_path().len()..];
        let ctx = unsafe {
            Expr {
                ptr: mpath.as_ptr().cast_mut(),
            }
        };
        trace!(target: "sink", "count at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "count registering in ctx {:?}", serialize(mpath));
        self.unique.insert(mpath, ());
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();
        trace!(target: "sink", "count finalizing by reducing {} at '{}'", self.unique.val_count(), serialize(wz.origin_path()));

        let mut _to_swap = PathMap::new();
        std::mem::swap(&mut self.unique, &mut _to_swap);
        let mut rooted_input = PathMap::new();
        rooted_input
            .write_zipper_at_path(wz.root_prefix_path())
            .graft_map(_to_swap);

        static v: &'static [u8] = &[item_byte(Tag::NewVar)];
        let mut prz = OneFactor::new(rooted_input.into_read_zipper(&[]));
        let prz_ptr = (&prz) as *const OneFactor<_>;
        let mut changed = false;
        let mut buffer: Vec<u8> = Vec::with_capacity(1 << 32);
        crate::space::Space::query_multi_raw(
            unsafe { prz_ptr.cast_mut().as_mut().unwrap() },
            &[ExprEnv::new(
                0,
                Expr {
                    ptr: v.as_ptr().cast_mut(),
                },
            )],
            |refs_bindings, loc| {
                let cnt = prz.val_count();
                trace!(target: "sink", "'{}' and under {}", serialize(prz.path()), cnt);
                let clen = prz.path().len();
                let cnt_str = cnt.to_string();
                if prz.descend_to_existing_byte(item_byte(Tag::SymbolSize(cnt_str.len() as _))) {
                    let descended = prz.descend_to_existing(cnt_str.as_bytes());
                    if descended == cnt_str.len() {
                        let fixed = &prz.path()[..prz.path().len() - (1 + cnt_str.len())];
                        trace!(target: "sink", "fixed guard {}", serialize(fixed));
                        wz.move_to_path(fixed);
                        wz.set_val(());
                        changed |= true;
                    }
                    prz.ascend(descended + 1);
                }
                if prz.descend_to_existing_byte(item_byte(Tag::NewVar)) {
                    let ignored = &prz.path()[..prz.path().len() - 1];
                    trace!(target: "sink", "ignored guard {}", serialize(ignored));
                    wz.move_to_path(ignored);
                    wz.set_val(());
                    changed |= true;
                    prz.ascend_byte();
                }
                if prz.descend_first_byte() {
                    if let Tag::VarRef(k) = byte_item(prz.path()[prz.path().len() - 1]) {
                        let mut cntv = vec![item_byte(Tag::SymbolSize(cnt_str.len() as _))];
                        cntv.extend_from_slice(cnt_str.as_bytes());
                        let varref = &prz.path()[..prz.path().len() - 1];
                        let ie = Expr {
                            ptr: (&varref[0] as *const u8).cast_mut(),
                        };
                        let mut oz = ExprZipper::new(Expr {
                            ptr: buffer.as_mut_ptr(),
                        });
                        trace!(target: "sink", "ref guard '{}' var {:?} with '{}'", serialize(varref), k, serialize(&cntv[..]));
                        let os = ie.substitute_one_de_bruijn(
                            k,
                            Expr {
                                ptr: cntv.as_mut_ptr(),
                            },
                            &mut oz,
                        );
                        unsafe { buffer.set_len(oz.loc) }
                        trace!(target: "sink", "ref guard subs '{:?}'", serialize(&buffer[..oz.loc]));
                        wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                        wz.set_val(());
                        changed |= true
                    }
                    prz.ascend_byte();
                }
                true
            },
        );
        changed
    }
}

pub struct HashSink {
    e: Expr,
    unique: PathMap<()>,
}
impl Sink for HashSink {
    fn new(e: Expr) -> Self {
        Self {
            e,
            unique: PathMap::new(),
        }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        let p = &unsafe {
            self.e
                .prefix()
                .unwrap_or_else(|x| {
                    let s = self.e.span();
                    slice_from_raw_parts(self.e.ptr, s.len() - 1)
                })
                .as_ref()
                .unwrap()
        }[6..];
        trace!(target: "sink", "hash requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let mpath = &path[6 + wz.root_prefix_path().len()..];
        let ctx = unsafe {
            Expr {
                ptr: mpath.as_ptr().cast_mut(),
            }
        };
        trace!(target: "sink", "hash at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "hash registering in ctx {:?}", serialize(mpath));
        self.unique.insert(mpath, ());
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();
        trace!(target: "sink", "hash finalizing by reducing {} at '{}'", self.unique.val_count(), serialize(wz.origin_path()));

        let mut _to_swap = PathMap::new();
        std::mem::swap(&mut self.unique, &mut _to_swap);
        let mut rooted_input = PathMap::new();
        rooted_input
            .write_zipper_at_path(wz.root_prefix_path())
            .graft_map(_to_swap);

        static v: &'static [u8] = &[item_byte(Tag::NewVar)];
        let mut prz = OneFactor::new(rooted_input.into_read_zipper(&[]));
        let prz_ptr = (&prz) as *const OneFactor<_>;
        let mut changed = false;
        let mut buffer: Vec<u8> = Vec::with_capacity(1 << 32);
        crate::space::Space::query_multi_raw(
            unsafe { prz_ptr.cast_mut().as_mut().unwrap() },
            &[ExprEnv::new(
                0,
                Expr {
                    ptr: v.as_ptr().cast_mut(),
                },
            )],
            |refs_bindings, loc| {
                for b in prz.child_mask().and(&ByteMask(crate::space::SIZES)).iter() {
                    let Tag::SymbolSize(size) = byte_item(b) else {
                        unreachable!()
                    };
                    // if size != 16 { trace!(target: "sink", "hash guard not 16 bytes {size}"); continue }
                    prz.descend_to_byte(b);
                    debug_assert!(prz.path_exists());
                    if !prz.descend_first_k_path(size as _) {
                        unreachable!()
                    }
                    loop {
                        let clen = prz.origin_path().len();

                        let hash = prz.fork_read_zipper().hash();

                        let cnt_str = hash.to_be_bytes();
                        trace!(target: "sink", "'{}' and under {}", serialize(prz.origin_path()), hash);
                        assert_eq!(prz.origin_path().len(), clen);

                        let fixed_number =
                            &prz.origin_path()[prz.origin_path().len() - (size as usize)..];
                        if fixed_number == &cnt_str[..] {
                            let fixed =
                                &prz.origin_path()[..prz.origin_path().len() - (1 + size as usize)];
                            trace!(target: "sink", "fixed payload {}", serialize(fixed));
                            wz.move_to_path(fixed);
                            wz.set_val(());
                            changed |= true;
                        }

                        if !prz.to_next_k_path(size as _) {
                            break;
                        }
                    }
                    if !prz.ascend_byte() {
                        unreachable!()
                    }
                }

                if prz.descend_to_existing_byte(item_byte(Tag::NewVar)) {
                    let ignored = &prz.path()[..prz.path().len() - 1];
                    trace!(target: "sink", "ignored guard {}", serialize(ignored));
                    wz.move_to_path(ignored);
                    wz.set_val(());
                    changed |= true;
                    prz.ascend_byte();
                }
                if prz.descend_first_byte() {
                    if let Tag::VarRef(k) = byte_item(prz.path()[prz.path().len() - 1]) {
                        let hash = prz.fork_read_zipper().hash();
                        let cnt_str = hash.to_be_bytes();

                        let mut cntv = vec![item_byte(Tag::SymbolSize(cnt_str.len() as _))];
                        cntv.extend_from_slice(&cnt_str[..]);
                        let varref = &prz.path()[..prz.path().len() - 1];
                        let ie = Expr {
                            ptr: (&varref[0] as *const u8).cast_mut(),
                        };
                        let mut oz = ExprZipper::new(Expr {
                            ptr: buffer.as_mut_ptr(),
                        });
                        trace!(target: "sink", "hash ref guard '{}' var {:?} with '{}'", serialize(varref), k, serialize(&cntv[..]));
                        let os = ie.substitute_one_de_bruijn(
                            k,
                            Expr {
                                ptr: cntv.as_mut_ptr(),
                            },
                            &mut oz,
                        );
                        unsafe { buffer.set_len(oz.loc) }
                        trace!(target: "sink", "hash ref guard subs '{:?}'", serialize(&buffer[..oz.loc]));
                        wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                        wz.set_val(());
                        changed |= true
                    }
                    prz.ascend_byte();
                }
                true
            },
        );
        changed
    }
}

pub struct AndSink {
    e: Expr,
    unique: PathMap<()>,
}
impl Sink for AndSink {
    fn new(e: Expr) -> Self {
        Self {
            e,
            unique: PathMap::new(),
        }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        let p = &unsafe {
            self.e
                .prefix()
                .unwrap_or_else(|x| {
                    let s = self.e.span();
                    slice_from_raw_parts(self.e.ptr, s.len() - 1)
                })
                .as_ref()
                .unwrap()
        }[5..];
        trace!(target: "sink", "and requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let mpath = &path[5 + wz.root_prefix_path().len()..];
        let ctx = unsafe {
            Expr {
                ptr: mpath.as_ptr().cast_mut(),
            }
        };
        trace!(target: "sink", "and at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "and registering in ctx {:?}", serialize(mpath));
        self.unique.insert(mpath, ());
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();
        trace!(target: "sink", "and finalizing by reducing {} at '{}'", self.unique.val_count(), serialize(wz.origin_path()));

        let mut _to_swap = PathMap::new();
        std::mem::swap(&mut self.unique, &mut _to_swap);
        let mut rooted_input = PathMap::new();
        rooted_input
            .write_zipper_at_path(wz.root_prefix_path())
            .graft_map(_to_swap);

        static v: &'static [u8] = &[item_byte(Tag::NewVar)];
        let mut prz = OneFactor::new(rooted_input.into_read_zipper(&[]));
        let prz_ptr = (&prz) as *const OneFactor<_>;
        let mut changed = false;
        let mut buffer: Vec<u8> = Vec::with_capacity(1 << 32);
        crate::space::Space::query_multi_raw(
            unsafe { prz_ptr.cast_mut().as_mut().unwrap() },
            &[ExprEnv::new(
                0,
                Expr {
                    ptr: v.as_ptr().cast_mut(),
                },
            )],
            |refs_bindings, loc| {
                for b in prz.child_mask().and(&ByteMask(crate::space::SIZES)).iter() {
                    let Tag::SymbolSize(size) = byte_item(b) else {
                        unreachable!()
                    };
                    println!("and size {size}");
                    prz.descend_to_byte(b);
                    debug_assert!(prz.path_exists());
                    if !prz.descend_first_k_path(size as _) {
                        unreachable!()
                    }
                    loop {
                        let mut total = !0u8;
                        let clen = prz.origin_path().len();

                        let mut rz = prz.fork_read_zipper();
                        while rz.to_next_val() {
                            let p = rz.origin_path();
                            trace!(target: "sink", "path number {:?}", serialize(&p[clen..]));
                            total &= p[clen + 1];
                        }
                        let cnt_str = [total];
                        trace!(target: "sink", "'{}' and under {}", serialize(prz.origin_path()), total);
                        assert_eq!(prz.origin_path().len(), clen);

                        let fixed_number =
                            &prz.origin_path()[prz.origin_path().len() - (size as usize)..];
                        if fixed_number == &cnt_str[..] {
                            let fixed =
                                &prz.origin_path()[..prz.origin_path().len() - (1 + size as usize)];
                            trace!(target: "sink", "fixed payload {}", serialize(fixed));
                            wz.move_to_path(fixed);
                            wz.set_val(());
                            changed |= true;
                        }

                        if !prz.to_next_k_path(size as _) {
                            break;
                        }
                    }
                    if !prz.ascend_byte() {
                        unreachable!()
                    }
                }

                if prz.descend_to_existing_byte(item_byte(Tag::NewVar)) {
                    let ignored = &prz.path()[..prz.path().len() - 1];
                    trace!(target: "sink", "ignored guard {}", serialize(ignored));
                    wz.move_to_path(ignored);
                    wz.set_val(());
                    changed |= true;
                    prz.ascend_byte();
                }
                if prz.descend_first_byte() {
                    if let Tag::VarRef(k) = byte_item(prz.path()[prz.path().len() - 1]) {
                        let mut total = !0u8;
                        let clen = prz.path().len();
                        let mut rz = prz.fork_read_zipper();
                        while rz.to_next_val() {
                            let p = rz.origin_path();
                            trace!(target: "sink", "and path {:?}", serialize(p));
                            trace!(target: "sink", "and path {:?}", serialize(&p[clen+1..]));
                            total &= p[clen + 1];
                        }
                        let cnt_str = [total];

                        let mut cntv = vec![item_byte(Tag::SymbolSize(cnt_str.len() as _))];
                        cntv.extend_from_slice(&cnt_str[..]);
                        let varref = &prz.path()[..prz.path().len() - 1];
                        let ie = Expr {
                            ptr: (&varref[0] as *const u8).cast_mut(),
                        };
                        let mut oz = ExprZipper::new(Expr {
                            ptr: buffer.as_mut_ptr(),
                        });
                        trace!(target: "sink", "and ref guard '{}' var {:?} with '{}'", serialize(varref), k, serialize(&cntv[..]));
                        let os = ie.substitute_one_de_bruijn(
                            k,
                            Expr {
                                ptr: cntv.as_mut_ptr(),
                            },
                            &mut oz,
                        );
                        unsafe { buffer.set_len(oz.loc) }
                        trace!(target: "sink", "and ref guard subs '{:?}'", serialize(&buffer[..oz.loc]));
                        wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                        wz.set_val(());
                        changed |= true
                    }
                    prz.ascend_byte();
                }
                true
            },
        );
        changed
    }
}

pub struct SumSink {
    e: Expr,
    unique: PathMap<()>,
}
impl Sink for SumSink {
    fn new(e: Expr) -> Self {
        SumSink {
            e,
            unique: PathMap::new(),
        }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        let p = &unsafe {
            self.e
                .prefix()
                .unwrap_or_else(|x| {
                    let s = self.e.span();
                    slice_from_raw_parts(self.e.ptr, s.len() - 1)
                })
                .as_ref()
                .unwrap()
        }[5..];
        trace!(target: "sink", "sum requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let mpath = &path[5 + wz.root_prefix_path().len()..];
        let ctx = unsafe {
            Expr {
                ptr: mpath.as_ptr().cast_mut(),
            }
        };
        trace!(target: "sink", "sum at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "sum registering in ctx {:?}", serialize(mpath));
        self.unique.insert(mpath, ());
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();
        trace!(target: "sink", "sum finalizing by reducing {} at '{}'", self.unique.val_count(), serialize(wz.origin_path()));

        let mut _to_swap = PathMap::new();
        std::mem::swap(&mut self.unique, &mut _to_swap);
        let mut rooted_input = PathMap::new();
        rooted_input
            .write_zipper_at_path(wz.root_prefix_path())
            .graft_map(_to_swap);

        static v: &'static [u8] = &[item_byte(Tag::NewVar)];
        let mut prz = OneFactor::new(rooted_input.into_read_zipper(&[]));
        let prz_ptr = (&prz) as *const OneFactor<_>;
        let mut changed = false;
        let mut buffer: Vec<u8> = Vec::with_capacity(1 << 32);
        crate::space::Space::query_multi_raw(
            unsafe { prz_ptr.cast_mut().as_mut().unwrap() },
            &[ExprEnv::new(
                0,
                Expr {
                    ptr: v.as_ptr().cast_mut(),
                },
            )],
            |refs_bindings, loc| {
                for b in prz.child_mask().and(&ByteMask(crate::space::SIZES)).iter() {
                    let Tag::SymbolSize(size) = byte_item(b) else {
                        unreachable!()
                    };
                    prz.descend_to_byte(b);
                    debug_assert!(prz.path_exists());
                    if !prz.descend_first_k_path(size as _) {
                        unreachable!()
                    }
                    loop {
                        let mut total = 0u32;
                        let clen = prz.origin_path().len();

                        let mut rz = prz.fork_read_zipper();
                        while rz.to_next_val() {
                            let p = rz.origin_path();
                            trace!(target: "sink", "path number {:?}", serialize(&p[clen..]));
                            total +=
                                u32::from_str_radix(str::from_utf8(&p[clen + 1..]).unwrap(), 10)
                                    .unwrap();
                        }
                        let cnt_str = total.to_string();
                        trace!(target: "sink", "'{}' and under {}", serialize(prz.origin_path()), total);
                        assert_eq!(prz.origin_path().len(), clen);

                        let fixed_number =
                            &prz.origin_path()[prz.origin_path().len() - (size as usize)..];
                        if fixed_number == cnt_str.as_bytes() {
                            let fixed =
                                &prz.origin_path()[..prz.origin_path().len() - (1 + size as usize)];
                            trace!(target: "sink", "fixed payload {}", serialize(fixed));
                            wz.move_to_path(fixed);
                            wz.set_val(());
                            changed |= true;
                        }

                        if !prz.to_next_k_path(size as _) {
                            break;
                        }
                    }
                    if !prz.ascend_byte() {
                        unreachable!()
                    }
                }

                if prz.descend_to_existing_byte(item_byte(Tag::NewVar)) {
                    let ignored = &prz.path()[..prz.path().len() - 1];
                    trace!(target: "sink", "ignored guard {}", serialize(ignored));
                    wz.move_to_path(ignored);
                    wz.set_val(());
                    changed |= true;
                    prz.ascend_byte();
                }
                if prz.descend_first_byte() {
                    if let Tag::VarRef(k) = byte_item(prz.path()[prz.path().len() - 1]) {
                        let mut total = 0u32;
                        let clen = prz.path().len();
                        let mut rz = prz.fork_read_zipper();
                        while rz.to_next_val() {
                            let p = rz.origin_path();
                            trace!(target: "sink", "path {:?}", serialize(p));
                            trace!(target: "sink", "path {:?}", serialize(&p[clen+1..]));
                            total +=
                                u32::from_str_radix(str::from_utf8(&p[clen + 1..]).unwrap(), 10)
                                    .unwrap();
                        }
                        let cnt_str = total.to_string();

                        let mut cntv = vec![item_byte(Tag::SymbolSize(cnt_str.len() as _))];
                        cntv.extend_from_slice(cnt_str.as_bytes());
                        let varref = &prz.path()[..prz.path().len() - 1];
                        let ie = Expr {
                            ptr: (&varref[0] as *const u8).cast_mut(),
                        };
                        let mut oz = ExprZipper::new(Expr {
                            ptr: buffer.as_mut_ptr(),
                        });
                        trace!(target: "sink", "ref guard '{}' var {:?} with '{}'", serialize(varref), k, serialize(&cntv[..]));
                        let os = ie.substitute_one_de_bruijn(
                            k,
                            Expr {
                                ptr: cntv.as_mut_ptr(),
                            },
                            &mut oz,
                        );
                        unsafe { buffer.set_len(oz.loc) }
                        trace!(target: "sink", "ref guard subs '{:?}'", serialize(&buffer[..oz.loc]));
                        wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                        wz.set_val(());
                        changed |= true
                    }
                    prz.ascend_byte();
                }
                true
            },
        );
        changed
    }
}

struct Sum;
struct Min;
struct Max;
struct Prod;

trait FloatReduction {
    const NAME: &'static str;
    const ACC: f64;
    fn op(acc: &mut f64, new: f64);
}
impl FloatReduction for Sum {
    const NAME: &'static str = "fsum";
    const ACC: f64 = 0.0;
    fn op(acc: &mut f64, new: f64) {
        acc.add_assign(new);
    }
}
impl FloatReduction for Min {
    const NAME: &'static str = "fmin";
    const ACC: f64 = f64::MAX;
    fn op(acc: &mut f64, new: f64) {
        *acc = (*acc).min(new)
    }
}
impl FloatReduction for Max {
    const NAME: &'static str = "fmax";
    const ACC: f64 = f64::MIN;
    fn op(acc: &mut f64, new: f64) {
        *acc = (*acc).max(new)
    }
}
impl FloatReduction for Prod {
    const NAME: &'static str = "fprod";
    const ACC: f64 = 1.0;
    fn op(acc: &mut f64, new: f64) {
        acc.mul_assign(new)
    }
}

pub struct FloatReductionSink<Reduction> {
    e: Expr,
    unique: PathMap<()>,
    guarded_unique: BTreeSet<Vec<u8>>,
    guarded: bool,
    boo: PhantomData<Reduction>,
}
impl<Reduction: FloatReduction> Sink for FloatReductionSink<Reduction> {
    fn new(e: Expr) -> Self {
        Self {
            e,
            unique: PathMap::new(),
            guarded_unique: BTreeSet::new(),
            guarded: unsafe { *e.ptr == item_byte(Tag::Arity(5)) },
            boo: PhantomData,
        }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        if self.guarded {
            return std::iter::once(WriteResourceRequest::BTM([].as_slice()));
        }
        let p = &unsafe {
            self.e
                .prefix()
                .unwrap_or_else(|x| {
                    let s = self.e.span();
                    slice_from_raw_parts(self.e.ptr, s.len() - 1)
                })
                .as_ref()
                .unwrap()
        }[2 + Reduction::NAME.len()..];
        trace!(target: "sink", "{} requesting {}", Reduction::NAME, serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        if self.guarded {
            let mpath = &path[wz.root_prefix_path().len()..];
            let args = expr_args(mpath);
            assert_eq!(
                args.len(),
                5,
                "{} guarded form expects 4 payload args",
                Reduction::NAME
            );
            assert_eq!(symbol_str(args[0]), Reduction::NAME);
            self.guarded_unique.insert(mpath.to_vec());
            return;
        }
        let mpath = &path[2 + Reduction::NAME.len() + wz.root_prefix_path().len()..];
        let ctx = unsafe {
            Expr {
                ptr: mpath.as_ptr().cast_mut(),
            }
        };
        trace!(target: "sink", "{} at '{}' sinking raw '{}'", Reduction::NAME, serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "{} registering in ctx {:?}", Reduction::NAME, serialize(mpath));
        self.unique.insert(mpath, ());
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();
        if self.guarded {
            struct GuardedFloatGroup {
                output: Vec<u8>,
                output_var: Vec<u8>,
                rows: Vec<(Vec<u8>, f64)>,
            }

            let mut groups: BTreeMap<Vec<u8>, GuardedFloatGroup> = BTreeMap::new();
            for row in &self.guarded_unique {
                let args = expr_args(row);
                let output = args[1].to_vec();
                let output_var = args[2].to_vec();
                let value = stv_f64(args[3], "reduction value");
                let order = args[4].to_vec();
                let mut key = output.clone();
                key.extend_from_slice(&output_var);
                let group = groups.entry(key).or_insert_with(|| GuardedFloatGroup {
                    output,
                    output_var,
                    rows: Vec::new(),
                });
                group.rows.push((order, value));
            }
            self.guarded_unique.clear();

            let mut changed = false;
            let mut buffer: Vec<u8> = Vec::with_capacity(1 << 20);
            for (_key, mut group) in groups {
                group.rows.sort_by(|left, right| left.0.cmp(&right.0));
                let mut total = Reduction::ACC;
                for (_, value) in group.rows {
                    Reduction::op(&mut total, value);
                }
                let total_str = total.to_string();
                let mut total_bytes = symbol_bytes(&total_str);

                match byte_item(group.output_var[0]) {
                    Tag::VarRef(k) => {
                        let ie = Expr {
                            ptr: group.output.as_ptr().cast_mut(),
                        };
                        buffer.push(item_byte(Tag::NewVar));
                        let mut oz = ExprZipper::new(Expr {
                            ptr: buffer.as_mut_ptr(),
                        });
                        ie.substitute_one_de_bruijn(
                            k,
                            Expr {
                                ptr: total_bytes.as_mut_ptr(),
                            },
                            &mut oz,
                        );
                        unsafe { buffer.set_len(oz.loc) }
                        wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                        changed |= wz.set_val(()).is_none();
                        buffer.clear();
                    }
                    Tag::NewVar => {
                        wz.move_to_path(&group.output);
                        changed |= wz.set_val(()).is_none();
                    }
                    _ => {
                        if group.output_var == &total_bytes[..] {
                            wz.move_to_path(&group.output);
                            changed |= wz.set_val(()).is_none();
                        }
                    }
                }
            }
            return changed;
        }
        trace!(target: "sink", "{} finalizing by reducing {} at '{}'", Reduction::NAME, self.unique.val_count(), serialize(wz.origin_path()));

        let mut _to_swap = PathMap::new();
        std::mem::swap(&mut self.unique, &mut _to_swap);
        let mut rooted_input = PathMap::new();
        rooted_input
            .write_zipper_at_path(wz.root_prefix_path())
            .graft_map(_to_swap);

        static v: &'static [u8] = &[item_byte(Tag::NewVar)];
        let mut prz = OneFactor::new(rooted_input.into_read_zipper(&[]));
        let prz_ptr = (&prz) as *const OneFactor<_>;
        let mut changed = false;
        let mut buffer: Vec<u8> = Vec::with_capacity(1 << 32);
        crate::space::Space::query_multi_raw(
            unsafe { prz_ptr.cast_mut().as_mut().unwrap() },
            &[ExprEnv::new(
                0,
                Expr {
                    ptr: v.as_ptr().cast_mut(),
                },
            )],
            |refs_bindings, loc| {
                for b in prz.child_mask().and(&ByteMask(crate::space::SIZES)).iter() {
                    let Tag::SymbolSize(size) = byte_item(b) else {
                        unreachable!()
                    };
                    prz.descend_to_byte(b);
                    debug_assert!(prz.path_exists());
                    if !prz.descend_first_k_path(size as _) {
                        unreachable!()
                    }
                    loop {
                        let mut total = Reduction::ACC;
                        let clen = prz.origin_path().len();

                        let mut rz = prz.fork_read_zipper();
                        while rz.to_next_val() {
                            let p = rz.origin_path();
                            trace!(target: "sink", "path number {:?}", serialize(&p[clen..]));
                            Reduction::op(
                                &mut total,
                                try_f64_bytes(&p[clen + 1..]).expect("reduction value f64"),
                            );
                        }
                        let min_str = total.to_string();
                        trace!(target: "sink", "'{}' and under {}", serialize(prz.origin_path()), total);
                        assert_eq!(prz.origin_path().len(), clen);

                        let fixed_number =
                            &prz.origin_path()[prz.origin_path().len() - (size as usize)..];
                        if fixed_number == min_str.as_bytes() {
                            let fixed =
                                &prz.origin_path()[..prz.origin_path().len() - (1 + size as usize)];
                            trace!(target: "sink", "fixed payload {}", serialize(fixed));
                            wz.move_to_path(fixed);
                            wz.set_val(());
                            changed |= true;
                        }

                        if !prz.to_next_k_path(size as _) {
                            break;
                        }
                    }
                    if !prz.ascend_byte() {
                        unreachable!()
                    }
                }

                if prz.descend_to_existing_byte(item_byte(Tag::NewVar)) {
                    let ignored = &prz.path()[..prz.path().len() - 1];
                    trace!(target: "sink", "ignored guard {}", serialize(ignored));
                    wz.move_to_path(ignored);
                    wz.set_val(());
                    changed |= true;
                    prz.ascend_byte();
                }
                if prz.descend_first_byte() {
                    if let Tag::VarRef(k) = byte_item(prz.path()[prz.path().len() - 1]) {
                        let mut total = Reduction::ACC;
                        let clen = prz.path().len();
                        let mut rz = prz.fork_read_zipper();
                        while rz.to_next_val() {
                            let p = rz.origin_path();
                            trace!(target: "sink", "path {:?}", serialize(p));
                            trace!(target: "sink", "path {:?}", serialize(&p[clen+1..]));
                            Reduction::op(
                                &mut total,
                                try_f64_bytes(&p[clen + 1..]).expect("reduction value f64"),
                            );
                        }
                        let min_str = total.to_string();

                        let mut cntv = vec![item_byte(Tag::SymbolSize(min_str.len() as _))];
                        cntv.extend_from_slice(min_str.as_bytes());
                        let varref = &prz.path()[..prz.path().len() - 1];
                        let ie = Expr {
                            ptr: (&varref[0] as *const u8).cast_mut(),
                        };
                        let mut oz = ExprZipper::new(Expr {
                            ptr: buffer.as_mut_ptr(),
                        });
                        trace!(target: "sink", "ref guard '{}' var {:?} with '{}'", serialize(varref), k, serialize(&cntv[..]));
                        let os = ie.substitute_one_de_bruijn(
                            k,
                            Expr {
                                ptr: cntv.as_mut_ptr(),
                            },
                            &mut oz,
                        );
                        unsafe { buffer.set_len(oz.loc) }
                        trace!(target: "sink", "ref guard subs '{:?}'", serialize(&buffer[..oz.loc]));
                        wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                        wz.set_val(());
                        changed |= true
                    }
                    prz.ascend_byte();
                }
                true
            },
        );
        changed
    }
}

// (pure (result $x) $x (f32_from_string 0.2))
#[cfg(feature = "grounding")]
pub struct PureSink {
    e: Expr,
    unique: PathMap<()>,
    scope: EvalScope,
}
impl Sink for PureSink {
    fn new(e: Expr) -> Self {
        let mut scope = EvalScope::new();
        pure::register(&mut scope);
        PureSink {
            e,
            unique: PathMap::new(),
            scope,
        }
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        let p = &unsafe {
            self.e
                .prefix()
                .unwrap_or_else(|x| {
                    let s = self.e.span();
                    slice_from_raw_parts(self.e.ptr, s.len() - 1)
                })
                .as_ref()
                .unwrap()
        }[6..];
        trace!(target: "sink", "count requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        let mpath = &path[6 + wz.root_prefix_path().len()..];
        let ctx = unsafe {
            Expr {
                ptr: mpath.as_ptr().cast_mut(),
            }
        };
        trace!(target: "sink", "pure at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "pure registering in ctx {:?}", serialize(mpath));
        self.unique.insert(mpath, ());
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        let WriteResource::BTM(wz) = it.next().unwrap() else {
            unreachable!()
        };
        wz.reset();
        trace!(target: "sink", "pure finalizing by reducing {} at '{}'", self.unique.val_count(), serialize(wz.origin_path()));

        let mut _to_swap = PathMap::new();
        std::mem::swap(&mut self.unique, &mut _to_swap);
        let mut rooted_input = PathMap::new();
        rooted_input
            .write_zipper_at_path(wz.root_prefix_path())
            .graft_map(_to_swap);

        static v: &'static [u8] = &[item_byte(Tag::NewVar)];
        let mut prz = OneFactor::new(rooted_input.into_read_zipper(&[]));
        let prz_ptr = (&prz) as *const OneFactor<_>;
        let mut changed = false;
        let mut buffer: Vec<u8> = Vec::with_capacity(1 << 32);
        crate::space::Space::query_multi_raw(
            unsafe { prz_ptr.cast_mut().as_mut().unwrap() },
            &[ExprEnv::new(
                0,
                Expr {
                    ptr: v.as_ptr().cast_mut(),
                },
            )],
            |refs_bindings, loc| {
                for b in prz.child_mask().and(&ByteMask(crate::space::SIZES)).iter() {
                    let Tag::SymbolSize(size) = byte_item(b) else {
                        unreachable!()
                    };
                    prz.descend_to_byte(b);
                    debug_assert!(prz.path_exists());
                    if !prz.descend_first_k_path(size as _) {
                        unreachable!()
                    }
                    loop {
                        let clen = prz.origin_path().len();

                        let mut rz = prz.fork_read_zipper();
                        'vals: while rz.to_next_val() {
                            let p = rz.origin_path();
                            trace!(target: "sink", "path number {:?}", serialize(&p[clen..]));
                            todo!();
                        }

                        if !prz.to_next_k_path(size as _) {
                            break;
                        }
                    }
                    if !prz.ascend_byte() {
                        unreachable!()
                    }
                }

                for b in prz
                    .child_mask()
                    .and(&ByteMask(crate::space::ARITIES))
                    .iter()
                {
                    todo!();
                }

                if prz.descend_to_existing_byte(item_byte(Tag::NewVar)) {
                    let ignored = &prz.path()[..prz.path().len() - 1];
                    trace!(target: "sink", "ignored guard {}", serialize(ignored));
                    wz.move_to_path(ignored);
                    wz.set_val(());
                    changed |= true;
                    prz.ascend_byte();
                }
                if prz.descend_first_byte() {
                    if let Tag::VarRef(k) = byte_item(prz.path()[prz.path().len() - 1]) {
                        let clen = prz.path().len();
                        let mut rz = prz.fork_read_zipper();
                        'vals: while rz.to_next_val() {
                            let p = rz.origin_path();
                            trace!(target: "sink", "path {:?}", serialize(p));
                            trace!(target: "sink", "path {:?}", serialize(&p[clen..]));

                            let mut res = match self.scope.eval(ExprSource::new(&p[clen])) {
                                Ok(res) => res,
                                Err(er) => {
                                    trace!(target: "pure", "err {}", er);
                                    continue 'vals;
                                }
                            };

                            trace!(target: "sink", "result {:?}", serialize(&res[..]));

                            let varref = &prz.path()[..prz.path().len() - 1];
                            let ie = Expr {
                                ptr: (&varref[0] as *const u8).cast_mut(),
                            };
                            let mut oz = ExprZipper::new(Expr {
                                ptr: buffer.as_mut_ptr(),
                            });
                            trace!(target: "sink", "ref guard '{}' var {:?} with '{}'", serialize(varref), k, serialize(&res[..]));
                            let os = ie.substitute_one_de_bruijn(
                                k,
                                Expr {
                                    ptr: res.as_mut_ptr(),
                                },
                                &mut oz,
                            );
                            unsafe { buffer.set_len(oz.loc) }
                            trace!(target: "sink", "ref guard subs '{:?}'", serialize(&buffer[..oz.loc]));
                            wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                            wz.set_val(());
                            changed |= true;
                            self.scope.return_alloc(res);
                        }
                    }
                    prz.ascend_byte();
                }
                true
            },
        );
        changed
    }
}

// (z3 <instance> <declaration or assertion>)
#[cfg(feature = "z3")]
pub struct Z3Sink {
    e: Expr,
    buffer: Vec<u8>,
    ins: &'static str,
}
#[cfg(feature = "z3")]
impl Sink for Z3Sink {
    fn new(e: Expr) -> Self {
        destruct!(e, ("z3" {instance: &str} {decl: Expr}), {
            trace!(target: "sink", "z3 requesting instance {instance}");
            Z3Sink { e, buffer: vec![], ins: instance }
        }, _err => { unreachable!() })
    }
    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        return std::iter::once(WriteResourceRequest::Z3(self.ins));
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        let spath = &path[1 + 1 + 2 + 1 + self.ins.bytes().len()..];
        trace!(target: "sink", "z3 sinking '{}'", serialize(spath));
        let e = Expr {
            ptr: spath.as_ptr().cast_mut(),
        };
        e.serialize(&mut self.buffer, |e| std::str::from_utf8(e).unwrap());
        self.buffer.push(b'\n');
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        mut it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        trace!(target: "sink", "z3 writing buffer {:?}", std::str::from_utf8(&self.buffer[..]).unwrap());
        let WriteResource::Z3(ref mut p) = it.next().unwrap() else {
            unreachable!()
        };
        let mut stdin = p.stdin.as_mut().unwrap();
        stdin.write(&self.buffer[..]).unwrap();
        stdin.flush().unwrap();
        true
    }
}

pub enum ASink {
    AddSink(AddSink),
    RemoveSink(RemoveSink),
    HeadSink(HeadTailSink<true>),
    TailSink(HeadTailSink<false>),
    ReviseProofsSink(ReviseProofsSink),
    BaseRateSink(BaseRateSink),
    PriorRuleStvSink(PriorRuleStvSink),
    PairCountsSink(PairCountsSink),
    DistAverageSink(DistAverageSink),
    DistSumSink(DistSumSink),
    OrStvSink(OrStvSink),
    TotalEvidenceMpSink(TotalEvidenceMpSink),
    CountSink(CountSink),
    OrderedCollectSink(OrderedCollectSink),
    VectorFloatSumSink(VectorFloatSumSink),
    HashSink(HashSink),
    SumSink(SumSink),
    AndSink(AndSink),
    ACTSink(ACTSink),
    #[cfg(feature = "wasm")]
    WASMSink(WASMSink),
    #[cfg(feature = "grounding")]
    PureSink(PureSink),
    #[cfg(feature = "z3")]
    Z3Sink(Z3Sink),
    AUSink(AUSink),
    USink(USink),
    CompatSink(CompatSink),
    FSumSink(FloatReductionSink<Sum>),
    FMinSink(FloatReductionSink<Min>),
    FMaxSink(FloatReductionSink<Max>),
    FProdSink(FloatReductionSink<Prod>),
}

impl ASink {
    pub fn compat(e: Expr) -> Self {
        ASink::CompatSink(CompatSink::new(e))
    }
}

impl Sink for ASink {
    fn new(e: Expr) -> Self {
        if unsafe {
            *e.ptr == item_byte(Tag::Arity(2))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(1))
                && *e.ptr.offset(2) == b'-'
        } {
            ASink::RemoveSink(RemoveSink::new(e))
        } else if unsafe {
            *e.ptr == item_byte(Tag::Arity(2))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(1))
                && *e.ptr.offset(2) == b'+'
        } {
            ASink::AddSink(AddSink::new(e))
        } else if unsafe {
            *e.ptr == item_byte(Tag::Arity(2))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(1))
                && *e.ptr.offset(2) == b'U'
        } {
            ASink::USink(USink::new(e))
        } else if unsafe {
            *e.ptr == item_byte(Tag::Arity(2))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(2))
                && *e.ptr.offset(2) == b'A'
                && *e.ptr.offset(3) == b'U'
        } {
            ASink::AUSink(AUSink::new(e))
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(3)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(4)) &&
            *e.ptr.offset(2) == b'h' && *e.ptr.offset(3) == b'e' && *e.ptr.offset(4) == b'a' && *e.ptr.offset(5) == b'd' } {
            ASink::HeadSink(HeadTailSink::new(e))
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(3)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(4)) &&
            *e.ptr.offset(2) == b't' && *e.ptr.offset(3) == b'a' && *e.ptr.offset(4) == b'i' && *e.ptr.offset(5) == b'l' } {
            ASink::TailSink(HeadTailSink::new(e))
        } else if cfg!(feature = "pln") && unsafe {
            (*e.ptr == item_byte(Tag::Arity(4))
                || *e.ptr == item_byte(Tag::Arity(5))
                || *e.ptr == item_byte(Tag::Arity(6))
                || *e.ptr == item_byte(Tag::Arity(7)))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(13))
                && *e.ptr.offset(2) == b'r'
                && *e.ptr.offset(3) == b'e'
                && *e.ptr.offset(4) == b'v'
                && *e.ptr.offset(5) == b'i'
                && *e.ptr.offset(6) == b's'
                && *e.ptr.offset(7) == b'e'
                && *e.ptr.offset(8) == b'-'
                && *e.ptr.offset(9) == b'p'
                && *e.ptr.offset(10) == b'r'
                && *e.ptr.offset(11) == b'o'
                && *e.ptr.offset(12) == b'o'
                && *e.ptr.offset(13) == b'f'
                && *e.ptr.offset(14) == b's'
        } {
            ASink::ReviseProofsSink(ReviseProofsSink::new(e))
        } else if cfg!(feature = "pln") && unsafe {
            (*e.ptr == item_byte(Tag::Arity(4)) || *e.ptr == item_byte(Tag::Arity(5)))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(14))
                && &*slice_from_raw_parts(e.ptr.offset(2), 14) == b"fold-base-rate"
        } {
            ASink::BaseRateSink(BaseRateSink::new(e))
        } else if cfg!(feature = "pln") && unsafe {
            *e.ptr == item_byte(Tag::Arity(21))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(14))
                && &*slice_from_raw_parts(e.ptr.offset(2), 14) == b"prior-rule-stv"
        } {
            ASink::PriorRuleStvSink(PriorRuleStvSink::new(e))
        } else if cfg!(feature = "pln") && unsafe {
            *e.ptr == item_byte(Tag::Arity(4))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(11))
                && &*slice_from_raw_parts(e.ptr.offset(2), 11) == b"pair-counts"
        } {
            ASink::PairCountsSink(PairCountsSink::new(e))
        } else if cfg!(feature = "pln") && unsafe {
            *e.ptr == item_byte(Tag::Arity(5))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(12))
                && &*slice_from_raw_parts(e.ptr.offset(2), 12) == b"dist-average"
        } {
            ASink::DistAverageSink(DistAverageSink::new(e))
        } else if cfg!(feature = "pln") && unsafe {
            *e.ptr == item_byte(Tag::Arity(5))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(8))
                && &*slice_from_raw_parts(e.ptr.offset(2), 8) == b"dist-sum"
        } {
            ASink::DistSumSink(DistSumSink::new(e))
        } else if cfg!(feature = "pln") && unsafe {
            *e.ptr == item_byte(Tag::Arity(8))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(6))
                && &*slice_from_raw_parts(e.ptr.offset(2), 6) == b"or-stv"
        } {
            ASink::OrStvSink(OrStvSink::new(e))
        } else if cfg!(feature = "pln") && unsafe {
            *e.ptr == item_byte(Tag::Arity(11))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(17))
                && &*slice_from_raw_parts(e.ptr.offset(2), 17) == b"total-evidence-mp"
        } {
            ASink::TotalEvidenceMpSink(TotalEvidenceMpSink::new(e))
        } else if unsafe {
            *e.ptr == item_byte(Tag::Arity(4))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(5))
                && *e.ptr.offset(2) == b'c'
                && *e.ptr.offset(3) == b'o'
                && *e.ptr.offset(4) == b'u'
                && *e.ptr.offset(5) == b'n'
                && *e.ptr.offset(6) == b't'
        } {
            ASink::CountSink(CountSink::new(e))
        } else if unsafe {
            let args = expr_args(e.span().as_ref().unwrap());
            args.len() == 7 && is_symbol(args[0], "group-collect")
        } {
            ASink::OrderedCollectSink(OrderedCollectSink::new(e))
        } else if unsafe {
            let args = expr_args(e.span().as_ref().unwrap());
            args.len() == 5 && is_symbol(args[0], "vfsum")
        } {
            ASink::VectorFloatSumSink(VectorFloatSumSink::new(e))
        } else if unsafe {
            *e.ptr == item_byte(Tag::Arity(4))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(4))
                && *e.ptr.offset(2) == b'h'
                && *e.ptr.offset(3) == b'a'
                && *e.ptr.offset(4) == b's'
                && *e.ptr.offset(5) == b'h'
        } {
            ASink::HashSink(HashSink::new(e))
        } else if unsafe {
            *e.ptr == item_byte(Tag::Arity(4))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(3))
                && *e.ptr.offset(2) == b's'
                && *e.ptr.offset(3) == b'u'
                && *e.ptr.offset(4) == b'm'
        } {
            return ASink::SumSink(SumSink::new(e));
        } else if unsafe {
            (*e.ptr == item_byte(Tag::Arity(4)) || *e.ptr == item_byte(Tag::Arity(5)))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(4))
                && *e.ptr.offset(2) == b'f'
                && *e.ptr.offset(3) == b's'
                && *e.ptr.offset(4) == b'u'
                && *e.ptr.offset(5) == b'm'
        } {
            return ASink::FSumSink(FloatReductionSink::new(e));
        } else if unsafe {
            (*e.ptr == item_byte(Tag::Arity(4)) || *e.ptr == item_byte(Tag::Arity(5)))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(4))
                && *e.ptr.offset(2) == b'f'
                && *e.ptr.offset(3) == b'm'
                && *e.ptr.offset(4) == b'i'
                && *e.ptr.offset(5) == b'n'
        } {
            return ASink::FMinSink(FloatReductionSink::new(e));
        } else if unsafe {
            (*e.ptr == item_byte(Tag::Arity(4)) || *e.ptr == item_byte(Tag::Arity(5)))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(4))
                && *e.ptr.offset(2) == b'f'
                && *e.ptr.offset(3) == b'm'
                && *e.ptr.offset(4) == b'a'
                && *e.ptr.offset(5) == b'x'
        } {
            return ASink::FMaxSink(FloatReductionSink::new(e));
        } else if unsafe {
            (*e.ptr == item_byte(Tag::Arity(4)) || *e.ptr == item_byte(Tag::Arity(5)))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(5))
                && *e.ptr.offset(2) == b'f'
                && *e.ptr.offset(3) == b'p'
                && *e.ptr.offset(4) == b'r'
                && *e.ptr.offset(5) == b'o'
                && *e.ptr.offset(6) == b'd'
        } {
            return ASink::FProdSink(FloatReductionSink::new(e));
        } else if unsafe {
            *e.ptr == item_byte(Tag::Arity(4))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(3))
                && *e.ptr.offset(2) == b'a'
                && *e.ptr.offset(3) == b'n'
                && *e.ptr.offset(4) == b'd'
        } {
            return ASink::AndSink(AndSink::new(e));
        } else if unsafe {
            *e.ptr == item_byte(Tag::Arity(3))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(3))
                && *e.ptr.offset(2) == b'A'
                && *e.ptr.offset(3) == b'C'
                && *e.ptr.offset(4) == b'T'
        } {
            return ASink::ACTSink(ACTSink::new(e));
        } else if unsafe {
            *e.ptr == item_byte(Tag::Arity(3))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(4))
                && *e.ptr.offset(2) == b'w'
                && *e.ptr.offset(3) == b'a'
                && *e.ptr.offset(4) == b's'
                && *e.ptr.offset(5) == b'm'
        } {
            #[cfg(feature = "wasm")]
            return ASink::WASMSink(WASMSink::new(e));
            #[cfg(not(feature = "wasm"))]
            panic!(
                "MORK was not built with the wasm feature, yet trying to call {:?}",
                e
            );
        } else if unsafe {
            *e.ptr == item_byte(Tag::Arity(4))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(4))
                && *e.ptr.offset(2) == b'p'
                && *e.ptr.offset(3) == b'u'
                && *e.ptr.offset(4) == b'r'
                && *e.ptr.offset(5) == b'e'
        } {
            #[cfg(feature = "grounding")]
            return ASink::PureSink(PureSink::new(e));
            #[cfg(not(feature = "grounding"))]
            panic!(
                "MORK was not built with the grounding feature, yet trying to call {:?}",
                e
            );
        } else if unsafe {
            *e.ptr == item_byte(Tag::Arity(3))
                && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(2))
                && *e.ptr.offset(2) == b'z'
                && *e.ptr.offset(3) == b'3'
        } {
            #[cfg(feature = "z3")]
            return ASink::Z3Sink(Z3Sink::new(e));
            #[cfg(not(feature = "z3"))]
            panic!(
                "MORK was not built with the z3 feature, yet trying to call {:?}",
                e
            );
        } else {
            panic!("unrecognized sink {}", serialize(unsafe { e.span().as_ref().unwrap() }))
        }
    }

    fn request(&self) -> impl Iterator<Item = WriteResourceRequest> {
        gen move {
            match self {
                ASink::AddSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::USink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::AUSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::RemoveSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::HeadSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::TailSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::ReviseProofsSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::BaseRateSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::PriorRuleStvSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::PairCountsSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::DistAverageSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::DistSumSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::OrStvSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::TotalEvidenceMpSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::CountSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::OrderedCollectSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::VectorFloatSumSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::HashSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::SumSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::AndSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::ACTSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                #[cfg(feature = "wasm")]
                ASink::WASMSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                #[cfg(feature = "grounding")]
                ASink::PureSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                #[cfg(feature = "z3")]
                ASink::Z3Sink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::CompatSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::FSumSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::FMinSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::FMaxSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
                ASink::FProdSink(s) => {
                    for i in s.request().into_iter() {
                        yield i
                    }
                }
            }
        }
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        it: It,
        path: &[u8],
    ) where
        'a: 'w,
        'k: 'w,
    {
        match self {
            ASink::AddSink(s) => s.sink(it, path),
            ASink::USink(s) => s.sink(it, path),
            ASink::AUSink(s) => s.sink(it, path),
            ASink::RemoveSink(s) => s.sink(it, path),
            ASink::HeadSink(s) => s.sink(it, path),
            ASink::TailSink(s) => s.sink(it, path),
            ASink::ReviseProofsSink(s) => s.sink(it, path),
            ASink::BaseRateSink(s) => s.sink(it, path),
            ASink::PriorRuleStvSink(s) => s.sink(it, path),
            ASink::PairCountsSink(s) => s.sink(it, path),
            ASink::DistAverageSink(s) => s.sink(it, path),
            ASink::DistSumSink(s) => s.sink(it, path),
            ASink::OrStvSink(s) => s.sink(it, path),
            ASink::TotalEvidenceMpSink(s) => s.sink(it, path),
            ASink::CountSink(s) => s.sink(it, path),
            ASink::OrderedCollectSink(s) => s.sink(it, path),
            ASink::VectorFloatSumSink(s) => s.sink(it, path),
            ASink::HashSink(s) => s.sink(it, path),
            ASink::SumSink(s) => s.sink(it, path),
            ASink::AndSink(s) => s.sink(it, path),
            ASink::ACTSink(s) => s.sink(it, path),
            #[cfg(feature = "wasm")]
            ASink::WASMSink(s) => s.sink(it, path),
            #[cfg(feature = "grounding")]
            ASink::PureSink(s) => s.sink(it, path),
            #[cfg(feature = "z3")]
            ASink::Z3Sink(s) => s.sink(it, path),
            ASink::CompatSink(s) => s.sink(it, path),
            ASink::FSumSink(s) => s.sink(it, path),
            ASink::FMinSink(s) => s.sink(it, path),
            ASink::FMaxSink(s) => s.sink(it, path),
            ASink::FProdSink(s) => s.sink(it, path),
        }
    }

    fn finalize<'w, 'a, 'k, It: Iterator<Item = WriteResource<'w, 'a, 'k>>>(
        &mut self,
        it: It,
    ) -> bool
    where
        'a: 'w,
        'k: 'w,
    {
        match self {
            ASink::AddSink(s) => s.finalize(it),
            ASink::USink(s) => s.finalize(it),
            ASink::AUSink(s) => s.finalize(it),
            ASink::RemoveSink(s) => s.finalize(it),
            ASink::HeadSink(s) => s.finalize(it),
            ASink::TailSink(s) => s.finalize(it),
            ASink::ReviseProofsSink(s) => s.finalize(it),
            ASink::BaseRateSink(s) => s.finalize(it),
            ASink::PriorRuleStvSink(s) => s.finalize(it),
            ASink::PairCountsSink(s) => s.finalize(it),
            ASink::DistAverageSink(s) => s.finalize(it),
            ASink::DistSumSink(s) => s.finalize(it),
            ASink::OrStvSink(s) => s.finalize(it),
            ASink::TotalEvidenceMpSink(s) => s.finalize(it),
            ASink::CountSink(s) => s.finalize(it),
            ASink::OrderedCollectSink(s) => s.finalize(it),
            ASink::VectorFloatSumSink(s) => s.finalize(it),
            ASink::HashSink(s) => s.finalize(it),
            ASink::SumSink(s) => s.finalize(it),
            ASink::AndSink(s) => s.finalize(it),
            ASink::ACTSink(s) => s.finalize(it),
            #[cfg(feature = "wasm")]
            ASink::WASMSink(s) => s.finalize(it),
            #[cfg(feature = "grounding")]
            ASink::PureSink(s) => s.finalize(it),
            #[cfg(feature = "z3")]
            ASink::Z3Sink(s) => s.finalize(it),
            ASink::CompatSink(s) => s.finalize(it),
            ASink::FSumSink(s) => s.finalize(it),
            ASink::FMinSink(s) => s.finalize(it),
            ASink::FMaxSink(s) => s.finalize(it),
            ASink::FProdSink(s) => s.finalize(it),
        }
    }
}
