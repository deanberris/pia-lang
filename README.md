# Pia

Pia is a formally verified programming language. It has an OCaml-like surface with Lisp-style metaprogramming. At compile time a solver (Z3) and cheaper formal methods such as interval analysis prove that each module is internally consistent and keeps the contracts it advertises.

The name is the second half of *Sophia*, a name associated with wisdom and logic. It also stands for **Proved In Advance**: every contract and module boundary is proved at compile time, before the program runs.

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
| `//tools/piac` | The compiler driver; `piac --dump-ast file.pia` |
| `//tests/grammar:test_grammar` | The grammar tests ([docs/grammar.md](docs/grammar.md)) |
| `//tests/parser:parser_golden_test` | `piac --dump-ast` golden tests |

### Front end without Bazel

The lexer and parser (`src/syntax`) have no LLVM dependency. For quick work on them:

```sh
clang++ -std=c++17 -Isrc src/syntax/*.cpp tools/piac/piac.cpp -o piac
./piac --dump-ast file.pia
python3 tests/parser/run_tests.py ./piac            # golden tests
python3 tests/parser/run_tests.py ./piac --update   # after an intended change
```
