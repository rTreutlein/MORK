//! Safe, string-oriented boundary for native applications embedding MORK.
//!
//! Parsing buffers and process-global execution counters remain internal to
//! this module. Callers own one [`NativeSpace`] and never handle raw MORK
//! expression pointers.

use crate::space::{
    ParDataParser, Space, fused_rule_candidates, fused_rule_rows, fused_rule_unifications,
    head_source_candidates, head_source_rows, transitions, unifications, writes,
};
use crate::sinks::{reset_sink_profiling, take_sink_timings};
use mork_expr::{Expr, ExprZipper};
use mork_frontend::bytestring_parser::{Context, Parser};
use std::sync::Mutex;
use std::time::Instant;

static EXECUTION_LOCK: Mutex<()> = Mutex::new(());

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct StageTiming {
    pub stage: String,
    pub phase: String,
    pub calls: usize,
    pub elapsed_ns: u128,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExecutionStats {
    pub steps: usize,
    pub unifications: usize,
    pub writes: usize,
    pub transitions: usize,
    pub fused_rule_candidates: usize,
    pub fused_rule_unifications: usize,
    pub fused_rule_rows: usize,
    pub head_source_candidates: usize,
    pub head_source_rows: usize,
    pub elapsed_ns: u128,
    pub sink_timings: Vec<StageTiming>,
}

pub struct NativeSpace {
    space: Space,
}

impl Default for NativeSpace {
    fn default() -> Self {
        Self::new()
    }
}

impl NativeSpace {
    pub fn new() -> Self {
        Self {
            space: Space::new(),
        }
    }

    pub fn add_batch(&mut self, source: &[u8]) -> Result<usize, String> {
        self.space.add_all_sexpr(source)
    }

    pub fn remove_batch(&mut self, source: &[u8]) -> Result<usize, String> {
        self.space.remove_all_sexpr(source)
    }

    pub fn set_timing(&mut self, enabled: bool) {
        self.space.timing = enabled;
    }

    pub fn execute(&mut self, step_budget: usize) -> ExecutionStats {
        let _guard = EXECUTION_LOCK
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        let before = unsafe {
            (
                unifications,
                writes,
                transitions,
                fused_rule_candidates,
                fused_rule_unifications,
                fused_rule_rows,
                head_source_candidates,
                head_source_rows,
            )
        };
        let started = Instant::now();
        reset_sink_profiling(self.space.timing);
        let steps = self.space.metta_calculus(step_budget);
        let sink_timings = take_sink_timings()
            .into_iter()
            .map(|timing| StageTiming {
                stage: timing.sink.to_owned(),
                phase: timing.phase.to_owned(),
                calls: timing.calls,
                elapsed_ns: timing.elapsed_ns,
            })
            .collect();
        let elapsed_ns = started.elapsed().as_nanos();
        let after = unsafe {
            (
                unifications,
                writes,
                transitions,
                fused_rule_candidates,
                fused_rule_unifications,
                fused_rule_rows,
                head_source_candidates,
                head_source_rows,
            )
        };
        ExecutionStats {
            steps,
            unifications: after.0.saturating_sub(before.0),
            writes: after.1.saturating_sub(before.1),
            transitions: after.2.saturating_sub(before.2),
            fused_rule_candidates: after.3.saturating_sub(before.3),
            fused_rule_unifications: after.4.saturating_sub(before.4),
            fused_rule_rows: after.5.saturating_sub(before.5),
            head_source_candidates: after.6.saturating_sub(before.6),
            head_source_rows: after.7.saturating_sub(before.7),
            elapsed_ns,
            sink_timings,
        }
    }

    /// Read only matches of `pattern`, rendering each with `template`.
    ///
    /// Both expressions are parsed in one variable context so variables in
    /// the template refer to bindings introduced by the pattern.
    pub fn read_matching(&self, pattern: &[u8], template: &[u8]) -> Result<Vec<u8>, String> {
        let mut joined = Vec::with_capacity(pattern.len() + template.len() + 1);
        joined.extend_from_slice(pattern);
        joined.push(b' ');
        joined.extend_from_slice(template);

        let mut context = Context::new(&joined);
        let symbols = self.space.sym_table();
        let mut parser = ParDataParser::new(&symbols);
        let capacity = joined.len().saturating_mul(8).max(4096);
        let mut pattern_buf = vec![0_u8; capacity];
        let mut template_buf = vec![0_u8; capacity];
        let mut pattern_zipper = ExprZipper::new(Expr {
            ptr: pattern_buf.as_mut_ptr(),
        });
        parser
            .sexpr(&mut context, &mut pattern_zipper)
            .map_err(|error| format!("{error:?}"))?;
        let mut template_zipper = ExprZipper::new(Expr {
            ptr: template_buf.as_mut_ptr(),
        });
        parser
            .sexpr(&mut context, &mut template_zipper)
            .map_err(|error| format!("{error:?}"))?;

        let mut output = Vec::new();
        self.space.dump_sexpr(
            Expr {
                ptr: pattern_buf.as_mut_ptr(),
            },
            Expr {
                ptr: template_buf.as_mut_ptr(),
            },
            &mut output,
        );
        Ok(output)
    }

    pub fn dump_all(&self) -> Result<Vec<u8>, String> {
        let mut output = Vec::new();
        self.space.dump_all_sexpr(&mut output)?;
        Ok(output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn filtered_readback_shares_variable_bindings() {
        let mut space = NativeSpace::new();
        space.add_batch(b"(row a 1)\n(row b 2)").unwrap();

        let output = space
            .read_matching(b"(row $name $value)", b"(result $name $value)")
            .unwrap();
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("(result a 1)"), "{output}");
        assert!(output.contains("(result b 2)"), "{output}");
    }

    #[test]
    fn batch_removal_and_execution_stats_are_safe() {
        let mut space = NativeSpace::new();
        space
            .add_batch(b"(seed a)\n(exec 0 (, (seed $x)) (O (+ (seen $x))))")
            .unwrap();
        space.set_timing(true);
        let stats = space.execute(1);
        assert_eq!(stats.steps, 1);
        assert!(stats.transitions > 0);
        assert!(stats.sink_timings.iter().any(|timing| {
            timing.stage == "add"
                && timing.phase == "consume"
                && timing.calls == 1
                && timing.elapsed_ns > 0
        }));
        assert!(stats.sink_timings.iter().any(|timing| {
            timing.stage == "runtime"
                && timing.phase == "multi-output"
                && timing.calls == 1
                && timing.elapsed_ns > 0
        }));
        space.remove_batch(b"(seed a)").unwrap();
        let output = String::from_utf8(space.dump_all().unwrap()).unwrap();
        assert!(!output.contains("(seed a)"), "{output}");
        assert!(output.contains("(seen a)"), "{output}");
    }
}
