# Pia

Pia is a formally verified programming language. It has an OCaml-like surface with Lisp-style metaprogramming. At compile time a solver (Z3) and cheaper formal methods such as interval analysis prove that each module is internally consistent and keeps the contracts it advertises.

The name is the second half of *Sophia*, a name associated with wisdom and logic. It also stands for **Proved In Advance**: every contract and module boundary is proved at compile time, before the program runs.

The first milestone is a toy compiler, written in C++ on MLIR, that proves and compiles SIMD data-processing pipelines for Apple Silicon. The flagship demo is stream delineation over terrain heightmaps.

- [Language design](docs/design.md)
- [Compiler architecture](docs/architecture.md)
- [Grammar](docs/grammar.md)
- [Metaprograms](docs/meta.md)
- [Architecture Decision Records](docs/adr/README.md)

## Building

Pia builds with Bazel (bzlmod) against LLVM/MLIR at a pinned llvm-project commit and Z3 from the Bazel Central Registry. See [ADR 0017](docs/adr/0017-bazel-build.md). Install [Bazelisk](https://github.com/bazelbuild/bazelisk), which picks up `.bazelversion`, then:

```sh
bazel build //...
bazel test //...
```

The first build compiles the parts of LLVM and MLIR that Pia uses and takes a while. Later builds reuse the disk cache in `~/.cache/pia-bazel-disk`.

CI ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)) runs `bazel build //...` and `bazel test //...` on a GitHub-hosted Apple Silicon macOS runner for every pull request and every push to `main`. A run saves the Bazel disk cache once per set of dependencies, so only the first run builds LLVM, MLIR and Z3. A run that fails or times out saves what it built under its own key, and a failed run uploads its test logs.

| Target | What it is |
| --- | --- |
| `//tools/pia-opt` | `mlir-opt` for Pia's dialects |
| `//tests/smoke:smt_to_z3_test` | smt dialect to SMT-LIB to Z3, end to end |
| `//tests/smoke:smt_roundtrip_test` | `pia-opt` round trip checked with FileCheck |
| `//src/dialect` | The `pia`, `pia_contract` and `pia_par` dialects |
| `//tests/dialect:dialect_tests` | Dialect round-trip, folding and verifier tests |
| `//tests/irgen:irgen_tests` | `piac --emit=mlir` tests checked with FileCheck |
| `//tests/verify:verify_tests` | `piac --verify` reports checked with FileCheck |
| `//tests/codegen:codegen_tests` | `piac --emit=core` and `--emit=llvm` checked with FileCheck |
| `//tests/codegen:saturate_test` | Compiled Pia linked with a C harness and compared with C reference code (arm64 macOS only) |
| `//tools/piac` | The compiler driver: `piac --verify file.pia` proves the program's goals ([docs/verifier.md](docs/verifier.md)), `--emit=mlir` lowers to the pia dialects ([docs/irgen.md](docs/irgen.md)), `--emit=obj -o f.o` compiles for Apple Silicon ([docs/codegen.md](docs/codegen.md)), `--dump-ast` prints the syntax tree and `--dump-expanded` the tree after metaprograms run ([docs/meta.md](docs/meta.md)) |
| `//tests/grammar:test_grammar` | The grammar tests ([docs/grammar.md](docs/grammar.md)) |
| `//tests/parser:parser_golden_test` | `piac --dump-ast` golden tests |
| `//tools/pia-lsp` | The language server ([ADR 0021](docs/adr/0021-language-server.md)): syntax errors, failed goals with counterexamples, hover with proofs, definitions, outline and completion over LSP. `//tools/pia-lsp:pia-lsp-frontend` is the same without MLIR |
| `//tests/lsp:lsp_test` | `pia-lsp` end to end over pipes; `lsp_frontend_test` runs it on the front-end build |

### Editor support

[`editors/vscode`](editors/vscode/README.md) is a VS Code extension that runs `pia-lsp`: build `//tools/pia-lsp`, then `npm install && npx vsce package` in that folder and install the `.vsix`. Any other LSP client can start `pia-lsp` too.

### Front end without Bazel

The lexer and parser (`src/syntax`) have no LLVM dependency. For quick work on them:

```sh
clang++ -std=c++17 -DPIA_NO_MLIR -Isrc src/syntax/*.cpp tools/piac/piac.cpp -o piac
./piac --dump-ast file.pia
python3 tests/parser/run_tests.py ./piac            # golden tests
python3 tests/parser/run_tests.py ./piac --update   # after an intended change
```
