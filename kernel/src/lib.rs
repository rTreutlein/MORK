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
}
