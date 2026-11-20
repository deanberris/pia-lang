# Pia

Pia is a formally verified programming language. It has an OCaml-like surface with Lisp-style metaprogramming. At compile time a solver (Z3) and cheaper formal methods such as interval analysis prove that each module is internally consistent and keeps the contracts it advertises.

The name is the second half of *Sophia*, a name associated with wisdom and logic.

The first milestone is a toy compiler, written in C++ on MLIR, that proves and compiles SIMD data-processing pipelines for Apple Silicon. The flagship demo is stream delineation over terrain heightmaps.

- [Language design](docs/design.md)
- [Compiler architecture](docs/architecture.md)
- [Grammar](docs/grammar.md)
- [Architecture Decision Records](docs/adr/README.md)

Build system: Bazel (bzlmod), depending on LLVM/MLIR and Z3 as Bazel modules. See [ADR 0017](docs/adr/0017-bazel-build.md).
