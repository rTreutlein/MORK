// use std::future::Future;
// use std::task::Poll;
use std::time::Instant;
use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::{Zipper, ZipperAbsolutePath, ZipperIteration, ZipperMoving};
use mork_frontend::bytestring_parser::Parser;
use mork::{expr, prefix, sexpr};
use mork::prefix::Prefix;
use mork::space::Space;
use mork_bytestring::{item_byte, Tag};
use mork_frontend::rosetta_parser::{SExp, ParseContext};

fn bc0() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
    ((step base)
      (, (goal (: $proof $conclusion)) (kb (: $proof $conclusion)))
      (, (ev (: $proof $conclusion) ) ))

    ((step abs)
      (, (goal (: $proof $conclusion)))
      (, (goal (: $lhs (-> $synth $conclusion)) ) ))

    ((step rev)
      (, (ev (: $lhs (-> $a $r)))  (goal (: $k $r)) )
      (, (goal (: $rhs $a) ) ))

    ((step app)
      (, (ev (: $lhs (-> $a $r)))  (ev (: $rhs $a))  )
      (, (ev (: (@ $lhs $rhs) $r) ) ))

    (exec zealous
            (, ((step $x) $p0 $t0)
               (exec zealous $p1 $t1) )
            (, (exec $x $p0 $t0)
               (exec zealous $p1 $t1) ))
    "#;

    const KB_EXPRS: &str = r#"
    (kb (: a A))
    (kb (: ab (R A B)))
    (kb (: bc (R B C)))
    (kb (: MP (-> (R $p $q) (-> $p $q))))

    (goal (: $proof C))
    "#;

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();
    s.load_all_sexpr(KB_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(47);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_sexpr(expr!(s, "[2] ev [3] : $ C"), expr!(s, "_1"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("result: {res}");
}


fn skolemize_sexp(premise_src: &str, conclusion_src: &str, f_name: &str) -> Result<String, String> {
    // Keep parse contexts alive while SExp borrows from them.
    let mut pctx = ParseContext::new(premise_src);
    let premise = SExp::parse(&mut pctx).map_err(|e| format!("{:?}", e))?;
    let mut cctx = ParseContext::new(conclusion_src);
    let conclusion = SExp::parse(&mut cctx).map_err(|e| format!("{:?}", e))?;

    // Collect universals: atoms starting with '&' that appear as arguments in the premise.
    let mut universals: Vec<&str> = Vec::new();
    match &premise {
        SExp::List(items) if items.len() >= 1 => {
            for arg in &items[1..] {
                if let SExp::Str(s) = arg {
                    if s.starts_with('&') {
                        universals.push(*s);
                    }
                }
            }
        }
        _ => return Err("premise must be a non-empty list".into()),
    }

    // Transform the conclusion by replacing any existential (var not in universals)
    // with f(universals...).
    let (head, args_out): (&str, Vec<String>) = match &conclusion {
        SExp::List(items) if !items.is_empty() => {
            let head = match &items[0] {
                SExp::Str(s) => *s,
                _ => return Err("conclusion head must be an atom".into()),
            };
            let mut out = Vec::with_capacity(items.len().saturating_sub(1));
            for arg in &items[1..] {
                match arg {
                    SExp::Str(s) => {
                        if s.starts_with('&') && !universals.iter().any(|u| u == s) {
                            if universals.is_empty() {
                                out.push(format!("({})", f_name));
                            } else {
                                out.push(format!("({} {})", f_name, universals.join(" ")));
                            }
                        } else {
                            out.push((*s).to_string());
                        }
                    }
                    _ => return Err("only atomic arguments supported in conclusion".into()),
                }
            }
            (head, out)
        }
        _ => return Err("conclusion must be a non-empty list".into()),
    };

    let result = if args_out.is_empty() {
        format!("({})", head)
    } else {
        format!("({} {})", head, args_out.join(" "))
    };

    Ok(result)
}

fn skolemize_test() {
    let mut s = Space::new();

    const SPACE_EXPRS: &str = r#"
    (premise (Pred1 &a &c))
    (conclusion (Pred2 &a &b))

    ((step tospace)
      (, (premise ($x $a)))
      (, (ps $a)))

    ((step tospace)
      (, (premise ($x $a $b)))
      (, (ps $a) (ps $b)))

    ((step tospace)
      (, (conclusion ($x $a $b)))
      (, (cl $a) (cl $b)))

    (not &a &b)
    (not &a &c)
    (not &c &b)

    ((step map)
     (, (ps $a) (cl $a))
     (, (out $a $a))
    )

    ((step map2)
     (, (ps $u1) (ps $u2) (cl $b) (not $u1 $b) (not $u2 $b) (not $u1 $u2))
     (, (out $b (f $u1 $u2)))
    )

    ((step fs)
      (, (conclusion ($x $a $b)) (out $a $na) (out $b $nb))
      (, (fcls ($x $na $nb)))
    )

    (exec zealous
            (, ((step $x) $p0 $t0)
               (exec zealous $p1 $t1) )
            (, (exec $x $p0 $t0)
               (exec zealous $p1 $t1) ))
    "#;

    s.load_all_sexpr(SPACE_EXPRS.as_bytes()).unwrap();

    let mut t0 = Instant::now();
    let steps = s.metta_calculus(102);
    println!("elapsed {} steps {} size {}", t0.elapsed().as_millis(), steps, s.btm.val_count());

    let mut v = vec![];
    s.dump_sexpr(expr!(s, "[2] fcls $"), expr!(s, "_1"), &mut v);
    let res = String::from_utf8(v).unwrap();

    println!("result:\n{res}");

}

fn main() {
    env_logger::init();

    //skolemize_test();

    //sexpr!("(Hello (A B))");
    //
    // Compare with pure-Rust Skolemization using SExp (no Space involved)
    let pure = skolemize_sexp("(Pred1 &a &c)", "(Pred2 &a &b)", "f").expect("skolemize_sexp");
    println!("pure-result:\n{pure}");
}
