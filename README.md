# Pia

Pia is a formally verified programming language. It has an OCaml-like surface with Lisp-style metaprogramming. At compile time a solver (Z3) and cheaper formal methods such as interval analysis prove that each module is internally consistent and keeps the contracts it advertises.

The name is the second half of *Sophia*, a name associated with wisdom and logic. It also stands for **Proved In Advance**: every contract and module boundary is proved at compile time, before the program runs.

The first milestone is a toy compiler, written in C++ on MLIR, that proves and compiles SIMD data-processing pipelines for Apple Silicon. The flagship demo is stream delineation over terrain heightmaps.

- [Language design](docs/design.md)
- [Compiler architecture](docs/architecture.md)
- [Grammar](docs/grammar.md)
- [Architecture Decision Records](docs/adr/README.md)

Build system: Bazel (bzlmod), depending on LLVM/MLIR and Z3 as Bazel modules. See [ADR 0017](docs/adr/0017-bazel-build.md).

### Front end without Bazel

The lexer and parser (`src/syntax`) have no LLVM dependency. For quick work on them:

```sh
clang++ -std=c++17 -Isrc src/syntax/*.cpp tools/piac/piac.cpp -o piac
./piac --dump-ast file.pia
python3 tests/parser/run_tests.py ./piac            # golden tests
python3 tests/parser/run_tests.py ./piac --update   # after an intended change
```
