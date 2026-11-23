# Codemap

A map of the repository, so that you can find the code you need without reading the code around it. Read sections 1 to 3 first, which fit on one screen, and after that only the section for the area you are changing. Use `tools/codemap/outline.py` on any large file before opening it.

`tools/codemap/check.py` checks this file on every pull request (`.github/workflows/codemap.yml`): every source file needs a line here, and every path written here must exist. When you add, move or delete a file, update its line in the same PR.

## 1. The pipeline

```
.pia / .pia.md ─ syntax/Lexer ─ syntax/Parser (AST: syntax/Syntax.h, comments kept)
  ─ meta/Expand (prelude operators, @derive, metaprograms, to a fixed point)
  ─ sema/Sema (types, signatures, concepts, deduction)
  ─ irgen/IRGen (AST → pia + pia_contract dialects; generics instantiated here)
  ─ transforms/ScalarizeRecords
  ─ verify/Verifier (intervals → Presburger → smt dialect → Z3, counterexamples)
  ─ codegen/Codegen (contracts erased → arith/scf/memref/vector → LLVM → arm64 or x86_64 object)
```

The `piac` driver (`tools/piac/piac.cpp`) runs this pipeline, with flags that stop it at each stage (`--dump-tokens`, `--dump-ast`, `--dump-expanded`, `--emit=mlir`, `--verify`, `--dump-smt`, `--emit=core|llvm|asm|obj|interface`). `pia repl` and `pia mcp` (`src/repl`) run the same pipeline one cell at a time, with a JIT. `pia-lsp` (`src/lsp`) runs it up to the verifier.

Design: [docs/design.md](docs/design.md) covers the language and [docs/architecture.md](docs/architecture.md) covers the compiler components, dialects and milestones. Each stage has its own page: [irgen.md](docs/irgen.md), [verifier.md](docs/verifier.md), [codegen.md](docs/codegen.md) and [meta.md](docs/meta.md).

## 2. Build, test, run

| What | Command | Where |
| --- | --- | --- |
| everything | `bazel build //... && bazel test //...` | the iMac (arm64 macOS), or CI (macOS arm64 and Linux x86_64, `.github/workflows/ci.yml`). Cloud sessions cannot fetch Bazel's dependencies. |
| one test file | `bazel test //tests/verify:loops_test` (the target is `<stem>_test`) | |
| a suite | `bazel test //tests/verify:verify_tests` (also `irgen_tests`, `std_tests`, …) | |
| prove a file | `bazel-bin/tools/piac/piac --verify f.pia` | see the `piac-verify` and `pia-fast-proofs` skills |
| doc examples | `bazel test //tests/docs:doc_examples_test //tests/docs:case_studies_test //tests/docs:skills_test` | every `ocaml` block in the listed pages is proved |
| proof cost gate | `python3 tools/bench/proof_bench.py --piac bazel-bin/tools/piac/piac` | fails on a Z3 cost regression of more than 10% against `tools/bench/baseline.json` |
| quick C++ check without Bazel | `g++ -std=c++17 -Isrc -fsyntax-only src/syntax/Lint.cpp` | works for `src/syntax`, `src/lsp`, `src/meta`, and the parts of `src/repl` that do not use LLVM |
| format | `git clang-format origin/main` | CI checks only the lines you changed (`.github/workflows/style.yml`, [docs/style.md](docs/style.md)) |
| grammar corpus | `python3 tests/grammar/test_grammar.py` | pure Python |
| docs site | `pip install -r tools/docs/requirements.txt && mkdocs build --strict` | `.github/workflows/docs.yml` |
| this map | `python3 tools/codemap/check.py` | pure Python, in CI (`.github/workflows/codemap.yml`) |

**Test format.** Most tests are lit files run by `tests/lit/run_lit.sh`. A `.pia` test keeps its `// RUN:` and `// CHECK:` lines inside a `(* ... *)` comment, because `//` does not start a comment in Pia. `tests/verify/update_expected.py <piac> <test>` rewrites the expected report at the end of a verify test. Run it on the iMac and read the diff before you commit.

## 3. To change X, look in Y

| Task | Start in | Then |
| --- | --- | --- |
| new syntax | `docs/grammar.md`, `grammar/pia.lark` | `src/syntax/Lexer.cpp`, `Parser.cpp`, `Syntax.h`; tests in `tests/parser`, `tests/grammar` |
| an operator or a core builtin | `src/syntax/Prelude.cpp` (operators, `derive_eq`, `machine`) | `isCoreBuiltin` in `src/sema/Sema.cpp`, the lowering in `IRGen.cpp` (`genBinary`, `genBitBuiltin`) |
| the memory model, litmus tests (ADR 0052) | `src/irgen/Memory.pia`, `litmus` in `src/syntax/Prelude.cpp` | `tests/memory`; docs/theories.md, "The memory model" |
| atomics: cells, orders, overflow modes (ADR 0052) | `genAtomic` in `src/irgen/IRGen.cpp`, the `pia.atomic.*` ops in `src/dialect/Pia.td` | the `Atomic*Lowering` patterns in `src/codegen/Codegen.cpp`; tests in `tests/verify/atomics.pia`, `tests/irgen/atomic_errors.pia`, `tests/codegen/atomics.pia` |
| a metaprogram builtin or expansion | `src/meta/Interpreter.cpp`, `Expand.cpp` | `docs/meta.md`; tests in `tests/meta` |
| type checking, overloads, concepts, deduction | `src/sema/Sema.{h,cpp}` | `IRGen.cpp`: `genCall`, `genGenericCall`, `--explain-overloads` |
| a new kind of expression or statement | `IRGen.cpp`: `genExprOf` dispatches | `tests/irgen`, then `tests/verify` |
| a new proof goal, or why a goal fails | `IRGen.cpp`, where the `pia_contract.obligation` op is created | `src/verify/Verifier.cpp` (the `Encoder` class); `tests/verify` |
| solver encodings, theories, triggers | `src/verify/Verifier.cpp`, `Triggers.cpp`, `Strategy.cpp` | `src/irgen/Theories.cpp`; `docs/theories.md` |
| a lint | `src/syntax/Lint.{h,cpp}` | `docs/idioms.md` table; `tests/lint` |
| modules, `.piai`, imports | `src/syntax/Interfaces.cpp` | `tools/piac/pia.bzl` (`pia_library`, `pia_binary`); `tests/modules` |
| codegen or the C ABI | `src/codegen/Codegen.cpp` | `docs/codegen.md`, `docs/abi.md`; `tests/codegen` |
| a target platform | `tools/piac/targets.bzl`, `--target`/`--cpu` in `piac.cpp` | ADR 0049, `docs/adr/0049-targets-are-theories.md` |
| the dialects | `src/dialect/*.td` | `tests/dialect` (round trips through `pia-opt`) |
| REPL or MCP | `src/repl/Session.cpp`, `Mcp.cpp` | `docs/repl.md`; `tests/repl` |
| the language server | `src/lsp/Server.cpp`, `Analysis.cpp` | `tests/lsp`, `editors/vscode` |
| a standard library module | `lib/Pia/...`, with `docs/cpp-std.md` as the status page | `tests/std` (a goal-count test, an importer and a run test for each module) |
| an image or compression codec | `lib/Pia/Image`, ADR 0054 | `tests/std/image_*`, `tests/std/gif_*` |
| memory, allocators, `box`, `vec` | `lib/Pia/Mem/{Alloc,Box,Vec}.pia`; pools, pages and `vec (box t)` are still prototypes in `tests/verify/{arena,pool,vec_boxes}.pia` | `tests/std/mem*.pia`, `src/irgen/Boxes.cpp`, `Regions.cpp` |
| user docs or an example | `docs/*.md`, listed in `mkdocs.yml` | a page under test is listed in `tests/docs/BUILD.bazel` |
| an agent skill | `skills/<name>/SKILL.md`, linked from `.claude/skills` | add it to `SKILLS` in `tests/docs/BUILD.bazel` |

**A working example of almost every feature** is in `tests/verify/<feature>.pia`, for example `handlers.pia`, `defer.pia`, `lambda_captures.pia`, `concepts.pia`, `models.pia` and `vec_boxes.pia`. Run `ls tests/verify` and copy from the closest one.

## 4. Source files

Line counts are as of 2026-11-23. For a file over 1,500 lines, run `outline.py` first.

### src/syntax: front end (no MLIR, builds with plain g++)

- `src/syntax/Token.h` lists the token kinds. `src/syntax/Lexer.{h,cpp}` is the lexical grammar, including nested comments.
- `src/syntax/Syntax.{h,cpp}` is the AST: a `Node` with a `kind`, `kids`, text and location.
- `src/syntax/Parser.{h,cpp}` (1.8k lines) is recursive descent with precedence climbing over the prelude's operator table.
- `src/syntax/Prelude.cpp` is the prelude source as a Pia string: the operators, `fold_and`, `derive_eq` and `machine`.
- `src/syntax/Comments.{h,cpp}` attaches comments to nodes (ADR 0029). It also reads literate `.pia.md`.
- `src/syntax/Diagnostics.h` holds the diagnostics, printed with a caret under the column.
- `src/syntax/Interfaces.{h,cpp}` holds module headers, `.piai` interface artifacts and import resolution (ADR 0039).
- `src/syntax/Lint.{h,cpp}` holds the ADR 0037 lints. They run before expansion, and piac and pia-lsp share them.

### src/meta: metaprograms

- `src/meta/Interpreter.{h,cpp}` is the tree-walking evaluator for `let meta`: quotes, splices and builtins (`listing`, `doc`, `concat`, `fold` and others).
- `src/meta/Expand.{h,cpp}` is the expansion loop to a fixed point, with hygiene (ADR 0022) and the `--meta-cycles` limit.
- `src/meta/Totality.{h,cpp}` proves that type-level metaprograms terminate (ADR 0035).

### src/sema: semantic analysis

- `src/sema/Sema.{h,cpp}` handles type resolution, `FuncSig`, range types and their joins, variants as tagged records, `isCoreBuiltin`, concepts and overload ranking.

### src/irgen: AST to MLIR (the largest area)

- `src/irgen/IRGen.{h,cpp}` (9.7k lines, one class `Gen`). Its main entry points are `run`, `genFunction`, `genExprOf`, `genBinary`, `genCall`, `genGenericCall`, `genMatch`, `liftLambda`, `coerce` and `checkFresh` (no shadowing). Run `python3 tools/codemap/outline.py --grep <word> src/irgen/IRGen.cpp` to find the rest.
- `src/irgen/Theories.{h,cpp}` flattens theories and models (ADR 0036) and detects `@trusted`.
- `src/irgen/Target.{h,cpp}` adds the built-in theory `Target` (ADR 0049), written in `src/irgen/Target.pia` and compiled in, with the model of the target being compiled for. `tests/verify/target_theory.pia` proves its models.
- `src/irgen/Memory.{h,cpp}` adds the built-in theory `Memory`, RC11 (ADR 0052), written in `src/irgen/Memory.pia` and compiled in, to a program that names it. `tests/memory/theory.pia` proves its model.
- `src/irgen/Boxes.{h,cpp}` expands `box` over a concept (ADR 0046).
- `src/irgen/Regions.{h,cpp}` erases region parameters (ADR 0042).

### src/dialect: MLIR dialects (ODS)

- `src/dialect/Pia.td` and `src/dialect/PiaDialect.{h,cpp}` define `pia`: range integers, arrays, slices, records, `dyn` and scalar ops.
- `src/dialect/Contract.td` and `src/dialect/ContractDialect.{h,cpp}` define `pia_contract`: requires, ensures, invariant, `obligation`, quantifiers and `old`.
- `src/dialect/Par.td` and `src/dialect/ParDialect.{h,cpp}` define `pia_par`: tiled grids, `spread` and collectives. They are not lowered yet.

### src/transforms, src/verify, src/codegen

- `src/transforms/ScalarizeRecords.{h,cpp}` replaces each record value with its fields.
- `src/verify/Verifier.{h,cpp}` (4.7k lines) holds the obligations, interval and Presburger discharge, the `Encoder` that builds the smt dialect, Z3 per goal (`--jobs`), the proof cache, slicing and counterexamples.
- `src/verify/Triggers.{h,cpp}` picks the triggers for axiom instantiation (ADR 0036).
- `src/verify/Strategy.{h,cpp}` holds the `@solver(...)` strategies and the `@by` tactics.
- `src/codegen/Codegen.{h,cpp}` erases contracts and lowers to LLVM, and from there to objects, assembly and the C ABI (the record out-pointer and one buffer per field). It also writes each object's witness symbols and certificate section.
- `src/codegen/SliceBuffers.{h,cpp}` splits each buffer of slices into a buffer of addresses and one of lengths before lowering (ADR 0048, step 3).
- `src/cert/Certificate.{h,cpp}` is the proof certificate an object carries (the interfaces it provides and imports, with their hashes), how to read one from an object file, and the link check (docs/abi.md).

### src/repl, src/lsp: tools on top of the pipeline

- `src/repl/Session.{h,cpp}` (2.1k lines) holds the persistent verified environment, `:redef`, the JIT and background tasks.
- `src/repl/State.{h,cpp}` holds REPL state with invariants and `old` migration.
- `src/repl/Kernel.{h,cpp}` is an asynchronous job front for a session. `src/repl/Mcp.{h,cpp}` is the MCP server with the two tools `execute` and `poll`.
- `src/repl/Guide.{h,cpp}` is the language guide `pia mcp` teaches with: its instructions, `:help <topic>`, `pia://guide/` resources and hints on failed cells. `src/repl/embed_guide.py` cuts it from the skills at build time, with the primer in `skills/pia-mcp/instructions.md`.
- `src/repl/LineEditor.{h,cpp}` is the terminal line editor.
- `src/lsp/Server.{h,cpp}` is the LSP over a byte stream. `src/lsp/Analysis.{h,cpp}` analyses one document: symbols, hover, rename and lints. `src/lsp/Proofs.{h,cpp}` runs the deep proof check. `src/lsp/Json.{h,cpp}` is a small JSON library.

### tools: binaries and Bazel rules

- `tools/piac/piac.cpp` is the compiler driver, where every flag is parsed.
- `tools/piac/pia.bzl` defines `pia_library` and `pia_binary`. `tools/piac/targets.bzl` defines `PIA_TARGETS` and the flags for each platform.
- `tools/pia/pia.cpp` is the `pia` tool (`pia repl`, `pia mcp`).
- `tools/pia-cert/pia-cert.cpp` is `pia-cert dump` and `pia-cert check`, which read and check the certificates in Pia objects.
- `tools/pia-lsp/pia-lsp.cpp` is the language server binary. `tools/pia-opt/pia-opt.cpp` is the MLIR opt driver for the dialects.
- `tools/link.bzl` holds the link options for the tool binaries, which link LLVM, MLIR and Z3 statically.
- `tools/bench/proof_bench.py`, `tools/bench/corpus.txt` and `tools/bench/baseline.json` make up the proof-cost benchmark (ADR 0032).
- `tools/docs/hooks.py` and `tools/docs/requirements.txt` are the MkDocs hook (source links to GitHub, OCaml highlighting) and its pinned version.
- `tools/codemap/outline.py` outlines a file. `tools/codemap/check.py` checks this map.
- `tools/bindings/gen.py` writes `lib/Pia/Sys/Gen/<target>.pia` from the host's C headers, for the names in `tools/bindings/posix.toml` (ADR 0051, section 6). `--check` is the drift check that `.github/workflows/bindings.yml` runs on both targets.

### lib: the standard library, written in Pia (ADR 0023, ADR 0040)

Each module is a `pia_library` in the `BUILD.bazel` next to it, with its tests in `tests/std/<module>.pia` and `tests/std/Inputs/<module>_run.pia`. Its mapping from C++ and its status are in `docs/cpp-std.md`.

- `lib/Pia/Fn.pia` holds the laws of function arguments as spec functions, such as `strict_weak_order` (ADR 0044).
- `lib/Pia/Core/Ascii.pia` is `<cctype>` for ASCII bytes. `lib/Pia/Core/Charconv.pia` is `<charconv>`'s `from_chars` and `to_chars` for integers. `lib/Pia/Core/Digits.pia` is the lemma library for digit strings (`dval`, `pow`, `prepend`, `frame`, `divmod`), which importers call as facts. `lib/Pia/Core/Hash.pia` is `std::hash`: the Hash concept, integer instances and FNV-1a. `lib/Pia/Core/Bit.pia` is `<bit>`. `lib/Pia/Core/Int.pia` holds the integer utilities: gcd, midpoint, abs, div and saturating arithmetic.
- `lib/Pia/Core/Order.pia` is `<compare>`, with the `Eq` and `Ord` concepts and `ordering`. `lib/Pia/Core/Option.pia` is `<optional>`. `lib/Pia/Core/Result.pia` is `<expected>`, its instances stamped out by the `result_family` metaprogram. `lib/Pia/Core/Utf8.pia` is UTF-8: decode, encode and validate, with both round trips proved.
- `lib/Pia/Core/Algo/Search.pia` holds the non-modifying sequence algorithms. `lib/Pia/Core/Algo/Modify.pia` holds the modifying ones. `lib/Pia/Core/Algo/Remove.pia` is `remove`.
- `lib/Pia/Core/Algo/Sort.pia`, `lib/Pia/Core/Algo/Heap.pia` and `lib/Pia/Core/Algo/BinarySearch.pia` hold sorting, the heap operations and the binary search family. `lib/Pia/Core/Algo/Permutation.pia` holds the multiset spec functions the sorts use.
- `lib/Pia/Core/Algo/PartialSort.pia` holds `partial_sort` and `nth_element`. `lib/Pia/Core/Algo/Partition.pia` holds `is_partitioned`, `partition_point` and `partition`.
- `lib/Pia/Core/Algo/Merge.pia` holds `merge`, from two sorted ranges into an out slice.
- `lib/Pia/Mem/Alloc.pia` holds `oom`, the `Allocator` concept and the bump allocator. `lib/Pia/Mem/Box.pia` is `box t r` over any allocator, and `lib/Pia/Mem/Vec.pia` is `vec t a r`, a growable vector that holds its allocator.
- `lib/Pia/Core/Algo/Set.pia` holds `includes`, `set_intersection` and `set_difference`. `lib/Pia/Core/Algo/SetUnion.pia` holds `set_union`.
- `lib/Pia/Core/Algo/SetSymmetric.pia` holds `set_symmetric_difference`, in its own module so it proves in parallel with `set_union`.
- `lib/Pia/Core/Algo/Numeric.pia` is `<numeric>`.
- `lib/Pia/Text/Json/Spec.pia` is the RFC 8259 token grammar as spec functions. `lib/Pia/Text/Json/Lex.pia` is a tokenizer proved against it, `lib/Pia/Text/Json/Write.pia` a writer proved to produce its tokens, and `lib/Pia/Text/Json/Read.pia` the token readers `@derive(json)` builds on (ADR 0045); the derive itself is in `src/syntax/Prelude.cpp`.
- `lib/Pia/Sys/Gen/arm64_macos.pia` and `lib/Pia/Sys/Gen/x86_64_linux.pia` are generated by `tools/bindings/gen.py`: POSIX constants, struct layouts and contract-free `extern` declarations, all `@target`. Never edit them by hand. `tests/irgen/sys_gen.pia` proves they compile.
- `lib/Pia/Image/Bits.pia` reads and writes LSB-first bit fields over a byte slice, for GIF and deflate. `lib/Pia/Image/Raster.pia` holds image dimensions, sample indices and rectangles (ADR 0054).
- `lib/Pia/Image/Gif/Spec.pia` is GIF89a as spec functions, starting with the LZW dictionary. `lib/Pia/Image/Gif/Lzw.pia` is the LZW decoder proved against it.

### Elsewhere

- `examples/edges` (`edges.pia`, `edges_buggy.pia` and the C harness) is the edge detection demo, and `docs/demo.md` describes it. `examples/streams` is the C harness for `docs/streams.pia.md`, the stream delineation demo, and `docs/sediment.pia.md`, its sediment transport stage.
- `grammar/pia.lark`, `grammar/pia_lexer.py` and `grammar/pia_grammar.py` are the reference grammar in Lark, checked against the C++ parser.
- `editors/vscode` is the VS Code extension: TextMate grammars and an LSP client.
- `skills/` holds the agent skills, listed in `skills/README.md`. Claude Code finds them through `.claude/skills/*`, which are symlinks. They are `skills/pia-language` (writing Pia), `skills/pia-contracts` (fixing failed goals), `skills/piac-verify` and `skills/pia-fast-proofs` (running the prover), `skills/pia-repl` and `skills/pia-mcp` (cell by cell), and `skills/pia-proof-debugging` (is this C++ correct?).
- `CLAUDE.md` holds the instructions every agent session loads: this map, the skills and the house rules.
- `third_party/rules_foreign_cc` holds the patches for the Z3 build.

## 5. Tests

| Directory | What it checks | Notes |
| --- | --- | --- |
| `tests/verify` | `piac --verify` reports, one feature per file | the best source of examples |
| `tests/irgen` | `--emit=mlir` | |
| `tests/codegen` | lowering lit tests and C harnesses | the run tests need arm64 macOS or a matching host |
| `tests/meta` | `--dump-expanded` and proofs of expanded code | |
| `tests/modules` | interfaces and imports across files | inputs in `tests/modules/Inputs` |
| `tests/memory` | the litmus battery for `Pia.Memory`, one file per family (MP, SB, LB, coherence, rmw, races, multi) | `theory.pia` proves the theory's model |
| `tests/std` | the `lib/` modules | build the `.piai` files first in local runs |
| `tests/lint` | lint text and fixes | |
| `tests/parser`, `tests/grammar` | AST goldens and the shared grammar corpus | |
| `tests/dialect` | ODS round trips | |
| `tests/repl`, `tests/lsp` | end to end over pipes | `tests/repl` runs in shards |
| `tests/docs` | `doc_examples_test.py`: every doc, case study and skill example | its markers are `<!-- example: -->`, `<!-- expect: fail -->` and `<!-- untested: -->` |
| `tests/smoke` | the tools start | |
| `tests/lit` | `run_lit.sh` and `lit.bzl`, the lit runner | |

## 6. Docs and ADRs

User docs (the site, `mkdocs.yml`): `docs/index.md`, `getting-started.md`, `tour.md`, `idioms.md`, `verification.md`, `theories.md`, `repl.md`, `repl-debugging.md`, `agents.md`, `status.md`, `demo.md`, `streams.pia.md`, `sediment.pia.md` and `cases/`. Internals: `design.md`, `architecture.md`, `grammar.md`, `irgen.md`, `verifier.md`, `codegen.md`, `meta.md`, `abi.md`, `concurrency.md`, `stdlib.md`, `cpp-std.md`, `init.md` and `style.md`.

ADRs are in `docs/adr/NNNN-title.md`. The index is `docs/adr/README.md`. By topic:

- **Syntax and bindings:** 0002 (single `let`), 0019 (grammar), 0059 (digit separators, `min t`/`max t`), 0022 (hygiene, no shadowing), 0029 (comments, literate), 0039 (modules and interfaces).
- **Types:** 0003 (`dyn`), 0005 (parameter modifiers), 0009 (generics, concepts), 0034 (overloads), 0035 (SFINAE, type `match`), 0043 (generics proved once), 0044 (lambdas), 0046 (`box`), 0047 (recursive types), 0048 (buffers of slices), 0051 (tuples, variadic packs, `one_of`, generated foreign bindings), 0057 (`Pia.Sys.Posix` per target behind one interface).
- **Proof:** 0004 (strongest guarantee by default), 0006 (contracts, module state), 0020 (Presburger), 0032 (parallel, sliced, cached proving), 0036 (library theories), 0037 (idioms and lints), 0038 (floats against real theories), 0049 (targets as theories), 0058 (ghost buffers).
- **Errors and memory:** 0026 (memory manager), 0028 (`?`, handlers, `defer`), 0041 (allocators), 0042 (lifetimes).
- **Metaprograms:** 0007 (fixed-point expansion), 0008 (operators).
- **Modules, ABI and trust:** 0010 (interfaces, certificates), 0024 (published certificates), 0030 (layouts), 0033 (initialisation).
- **Compiler and tools:** 0001 (ADRs), 0011 (MLIR and Z3), 0017 (Bazel), 0018 (dialects), 0021 (LSP), 0025 (sanitizers), 0031 (REPL), 0056 (tests generated from contracts and theories).
- **Performance and parallelism:** 0012 (FP reassociation), 0013 (auto-vectorisation), 0014 (concurrency), 0015 (device placement), 0027 (coroutines, race freedom), 0050 (senders and receivers, io_uring and kqueue), 0052 (atomics), 0053 (protocols checked by Z3 and CHC).
- **Library and demos:** 0016 (streams demo), 0023 (minimal core, self-hosted stdlib), 0040 (C++23 std), 0045 (JSON), 0054 (GIF and inflate codecs), 0055 (sediment transport in fixed point).

## 7. Keeping this map current

- A PR that adds, renames or deletes a file in `src/`, `lib/`, `tools/`, `tests/` (directories only), `examples/` or `skills/`, or adds an ADR, updates this file in the same PR. `python3 tools/codemap/check.py` says what is missing.
- Keep each entry to one line that says what the file is for, not how it works. The file's own header comment holds the detail.
- Section 3 is the part that earns its keep. When a task took you a while to locate, add a row for it.
