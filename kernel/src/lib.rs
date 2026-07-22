#![feature(gen_blocks)]
#![feature(coroutine_trait)]
#![feature(coroutines)]
#![feature(stmt_expr_attributes)]
#![feature(more_float_constants)]

pub mod space;
mod sources;
mod sinks;
mod pure;

pub use sinks::WriteResourceRequest;
pub use sources::ResourceRequest;

#[cfg(test)]
mod tests {
    use crate::space::Space;

    #[test]
    fn head_and_tail_select_encoded_extrema() {
        let mut space = Space::new();
        space.add_all_sexpr(br#"
            (item 3)
            (item 1)
            (item 4)
            (item 2)
            (exec 0 (I (head 2 (item $x))) (O (+ (head-picked $x))))
            (exec 1 (I (tail 2 (item $x))) (O (+ (tail-picked $x))))
        "#).unwrap();

        assert_eq!(space.metta_calculus(2), 2);

        let mut output = Vec::new();
        space.dump_all_sexpr(&mut output).unwrap();
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("(head-picked 1)\n"));
        assert!(output.contains("(head-picked 2)\n"));
        assert!(!output.contains("(head-picked 3)\n"));
        assert!(output.contains("(tail-picked 3)\n"));
        assert!(output.contains("(tail-picked 4)\n"));
        assert!(!output.contains("(tail-picked 2)\n"));
    }

    #[test]
    fn ordered_float_sum_groups_and_deduplicates_rows() {
        let mut space = Space::new();
        space.add_all_sexpr(br#"
            (row a z 1.5)
            (row a a 2.5)
            (row a a 2.5)
            (row b q 4.0)
            (row stable c 1)
            (row stable a 10000000000000000)
            (row stable b -10000000000000000)
            (exec 0 (, (row $group $order $value))
                (O (fsum (total $group $sum) $sum $value $order)))
        "#).unwrap();

        assert_eq!(space.metta_calculus(1), 1);

        let mut output = Vec::new();
        space.dump_all_sexpr(&mut output).unwrap();
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("(total a 4)\n"));
        assert!(output.contains("(total b 4)\n"));
        assert!(output.contains("(total stable 1)\n"));
    }

    #[test]
    fn one_of_projects_alternative_shapes_to_one_relation() {
        let mut space = Space::new();
        space.add_all_sexpr(br#"
            (exec 0
                (I (BTM (wanted $goal))
                   (one-of
                       (value $goal ($first $second))
                       (left $goal ($first $second))
                       (right $goal (wrapped ($first $second) $ignored))))
                (, (seen $goal ($first $second))))
            (wanted a)
            (wanted b)
            (wanted missing)
            (left a (one two))
            (right a (wrapped (one two) ignored))
            (right b (wrapped (three four) ignored))
        "#).unwrap();

        assert_eq!(space.metta_calculus(1), 1);

        let mut output = Vec::new();
        space.dump_all_sexpr(&mut output).unwrap();
        let output = String::from_utf8(output).unwrap();
        assert_eq!(output.matches("(seen a (one two))\n").count(), 1, "{output}");
        assert!(output.contains("(seen b (three four))\n"), "{output}");
        assert!(!output.contains("(seen missing"), "{output}");
    }

    #[test]
    fn contribution_sink_replaces_one_identity_and_aggregate() {
        let mut space = Space::new();
        space.add_all_sexpr(br#"
            (fact cache (0.0 0.0))
            (contribution-state (fact cache) (0.0 0.0))
            (contribution-value (fact cache) (0.0 0.0))
            (pending a 0.8 0.5 proof-a)
            (exec 0
                (, (pending $id $value $weight $proof)
                   (contribution-state (fact cache) $state)
                   (contribution-value (fact cache) $old-stv))
                (O
                    (- (pending $id $value $weight $proof))
                    (update-contribution
                        (fact cache) $id no-observation
                        (observation $value $weight $proof)
                        $state $old-stv $old-stv)))
        "#).unwrap();

        assert_eq!(space.metta_calculus(2), 1);
        space.add_all_sexpr(br#"
            (replacement a 0.6 0.75 proof-b)
            (exec 0
                (, (replacement $id $value $weight $proof)
                   (contribution-state (fact cache) $state)
                   (contribution-value (fact cache) $old-stv)
                   (contribution-observation
                       (fact cache) $id $old-value $old-weight $old-proof))
                (O
                    (- (replacement $id $value $weight $proof))
                    (update-contribution
                        (fact cache) $id
                        (observation $old-value $old-weight $old-proof)
                        (observation $value $weight $proof)
                        $state $old-stv $old-stv)))
        "#).unwrap();
        assert_eq!(space.metta_calculus(2), 1);

        let mut output = Vec::new();
        space.dump_all_sexpr(&mut output).unwrap();
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("(contribution-observation (fact cache) a 0.6 0.75 proof-b)\n"), "{output}");
        assert!(!output.contains("proof-a"), "{output}");
        assert!(output.contains("(fact cache (0.6 "), "{output}");
        assert_eq!(output.matches("(contribution-state (fact cache)").count(), 1, "{output}");
        assert_eq!(output.matches("(contribution-value (fact cache)").count(), 1, "{output}");
    }
}
