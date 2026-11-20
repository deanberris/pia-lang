# Pia

Pia is a formally verified programming language. It has an OCaml-like surface with Lisp-style metaprogramming. At compile time a solver (Z3) and cheaper formal methods such as interval analysis prove that each module is internally consistent and keeps the contracts it advertises.

The name is the second half of *Sophia*, a name associated with wisdom and logic.

The first milestone is a toy compiler, written in C++ on MLIR, that proves and compiles SIMD data-processing pipelines for Apple Silicon. The flagship demo is stream delineation over terrain heightmaps.

- [Language design](docs/design.md)
- [Compiler architecture](docs/architecture.md)
- [Grammar](docs/grammar.md)
- [Architecture Decision Records](docs/adr/README.md)

## Building

Pia builds with Bazel (bzlmod) against LLVM/MLIR at a pinned llvm-project commit and Z3 from the Bazel Central Registry. See [ADR 0017](docs/adr/0017-bazel-build.md). Install [Bazelisk](https://github.com/bazelbuild/bazelisk), which picks up `.bazelversion`, then:

```sh
bazel build //...
bazel test //...
```

The first build compiles the parts of LLVM and MLIR that Pia uses and takes a while. Later builds reuse the disk cache in `~/.cache/pia-bazel-disk`.

| Target | What it is |
| --- | --- |
| `//tools/pia-opt` | `mlir-opt` for Pia's dialects |
| `//tests/smoke:smt_to_z3_test` | smt dialect to SMT-LIB to Z3, end to end |
| `//tests/smoke:smt_roundtrip_test` | `pia-opt` round trip checked with FileCheck |
| `//tests/grammar:test_grammar` | The grammar tests ([docs/grammar.md](docs/grammar.md)) |
