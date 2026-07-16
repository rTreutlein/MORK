
# MeTTa Optimal Reduction Kernel

**A blazing fast hypergraph processing kernel for Hyperon**

MORK seeks to retrofit Hyperon with a state-of-the-art graph database and a specialized zipper-based multi-threaded virtual machine to provide speedy MeTTa evaluation across the full range of Space sizes and topologies.

By rearchitecting certain Hyperon bottlenecks, MORK has the potential to accelerate important use cases by thousands to millions of times.  That kind of speedup represents a qualitative jump in capabilities.  It's the difference between running a training step vs. finishing the training in the same amount of time.  It's the difference between a thousand input samples vs. millions, or a crocodile's brain vs. a human's.  Deep learning has advanced due in part to the software platforms that exposed the full capabilities of underlying hardware, and we hope Hyperon + MORK can help do that for symbolic AI.

## Wiki
[The wiki](https://github.com/trueagi-io/MORK/wiki#where-to-start) is where you find examples, tutorials, and more info about both the formalism and implementation.

## Trying it out
If you're looking for the MORK server, use the [server branch](https://github.com/trueagi-io/MORK/tree/server).

If you're looking for the MORK command line utility, run `cargo build --release` in `/kernel`; you'll need a nightly compiler `rustup toolchain install nightly`.

## MyClaw development environment

The project environment pins Rust to `nightly-2026-07-15` and includes the
native tools needed by the Cargo dependency graph. From an approved MORK task
worktree, build the image and run the default test with:

```bash
python /app/project_env.py --task TASK_ID
```

The default command is `cargo test`. Because the workspace's default member is
`kernel`, this provides a practical check of the main MORK package and its
dependency graph. Pass a command after `--` when a broader or more targeted
check is needed.

MORK's Cargo workspace depends on `../PathMap`. MyClaw must therefore register
`/nexus/Dev/OpenCog/PathMap` as a project and register MORK as depending on
PathMap. The environment runner will then mount PathMap read-only at that
canonical path, preserving Cargo's sibling path resolution. Merely having the
directory on the host is not sufficient for task containers.
