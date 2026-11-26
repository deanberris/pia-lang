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
| prebuilt `pia` and `piac` | `gh release download latest -R deanberris/pia-lang --pattern 'pia-linux-x86_64.tar.gz'` (or `pia-macos-arm64.tar.gz`) | moving `latest` prerelease on [GitHub Releases](https://github.com/deanberris/pia-lang/releases/tag/latest) (plus `SHA256SUMS.txt`), updated on green `main` runs (`.github/workflows/ci.yml`) |
| one test file | `bazel test //tests/verify:loops_test` (the target is `<stem>_test`) | |
| a suite | `bazel test //tests/verify:verify_tests` (also `irgen_tests`, `std_tests`, …) | |
| build queue (iMac) | `bazelq --status`; `bazelq --exec -- <command>` for heavy non-Bazel runs | `tools/imac/install.sh` makes plain `bazel` queue machine-wide with 4 jobs per build |
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
| `spread`: parallel loops, ownership goals, the async runtime (ADR 0060) | `genSpread`, `ownedHere`, `footprintScope` and `checkFootprintCall` in `src/irgen/IRGen.cpp`; `HavocOthersOp` in `src/dialect/Contract.td` and the verifier; `reads` frames: `ReadsOp`, `addFrameLemmas` in `src/meta/Expand.cpp`, `frameLink` in `src/verify/Verifier.cpp` | `lowerSpreads` and the async passes in `src/codegen/Codegen.cpp`; tests in `tests/verify/spread.pia`, `tests/verify/spread_ensures.pia`, `tests/verify/frames.pia`, `tests/irgen/spread_errors.pia`, `tests/codegen/spread.pia` (run by `spread_test`) |
| opaque spec functions: `@opaque` and `with f` (ADR 0063) | `reveal` in `src/syntax/Parser.cpp`; `genReveal`, `revealed` and `@opaque` in `genAttributes`, in `src/irgen/IRGen.cpp`; `RevealOp` in `src/dialect/Contract.td` | `specCall` (the opaque check), the `RevealOp` step and `walkBlock`'s scope in `src/verify/Verifier.cpp`; tests in `tests/verify/opaque.pia`, `tests/modules/opaque.pia` |
| spec state: `let spec` locals, spec parameters and spec fields (ADR 0058) | `genLetIn`, `genName` and `genField` (the read checks), `genAssign` and `genRecordLit` (spec writes) and the spec arguments in `genCall`, in `src/irgen/IRGen.cpp`; `RecordType`'s `specFields` in `src/dialect/Pia.td` | `leafSpec` in `src/transforms/ScalarizeRecords.cpp`, `eraseSpecState` in `src/codegen/Codegen.cpp`; tests in `tests/verify/spec_locals.pia`, `tests/verify/spec_fields.pia`, `tests/irgen/spec_local_errors.pia`, `tests/irgen/spec_field_errors.pia`, `tests/codegen/spec_state.pia` |
| atomics: cells, orders, overflow modes (ADR 0052) | `genAtomic` in `src/irgen/IRGen.cpp`, the `pia.atomic.*` ops in `src/dialect/Pia.td` | the `Atomic*Lowering` patterns in `src/codegen/Codegen.cpp`; tests in `tests/verify/atomics.pia`, `tests/irgen/atomic_errors.pia`, `tests/codegen/atomics.pia` |
| a metaprogram builtin or expansion | `src/meta/Interpreter.cpp`, `Expand.cpp` | `docs/meta.md`; tests in `tests/meta` |
| type checking, overloads, concepts, deduction | `src/sema/Sema.{h,cpp}` | `IRGen.cpp`: `genCall`, `genGenericCall`, `--explain-overloads` |
| a new kind of expression or statement | `IRGen.cpp`: `genExprOf` dispatches | `tests/irgen`, then `tests/verify` |
| a new proof goal, or why a goal fails | `IRGen.cpp`, where the `pia_contract.obligation` op is created | `src/verify/Verifier.cpp` (the `Encoder` class); `tests/verify` |
| solver encodings, theories, triggers | `src/verify/Verifier.cpp`, `Triggers.cpp`, `Strategy.cpp` | `src/irgen/Theories.cpp`; `docs/theories.md` |
| a lint | `src/syntax/Lint.{h,cpp}` | `docs/idioms.md` table; `tests/lint` |
| modules, `.piai`, imports | `src/syntax/Interfaces.cpp` | `tools/piac/pia.bzl` (`pia_library`, `pia_binary`); `tests/modules` |
| a lowering to MLIR (`@lower`, ADR 0065) | `markLowering` in `src/irgen/IRGen.cpp` (the rules), `src/codegen/Lowerings.cpp` (splice, parse, replace the body, the linalg passes) | `--lower` and the trust report in `tools/piac/piac.cpp`, `trusted` lines in `src/cert/Certificate.cpp`; tests in `tests/codegen/lower_linalg.pia` (run by `lower_linalg_run_test` and `lower_linalg_body_run_test`), `tests/codegen/lower_invalid.pia`, `tests/irgen/lower.pia`, `tests/irgen/lower_errors.pia`, `tests/irgen/lower_untrusted.pia` |
| codegen or the C ABI | `src/codegen/Codegen.cpp` | `docs/codegen.md`, `docs/abi.md`; `tests/codegen` |
| a target platform | `tools/piac/targets.bzl`, `--target`/`--cpu` in `piac.cpp` | ADR 0049, `docs/adr/0049-targets-are-theories.md` |
| the dialects | `src/dialect/*.td` | `tests/dialect` (round trips through `pia-opt`) |
| REPL or MCP | `src/repl/Session.cpp`, `Mcp.cpp` | `docs/repl.md`; `tests/repl` |
| the language server | `src/lsp/Server.cpp`, `Analysis.cpp` | `tests/lsp`, `editors/vscode` |
| a standard library module | `lib/Pia/...`, with `docs/cpp-std.md` as the status page | `tests/std` (a goal-count test, an importer and a run test for each module) |
| an image or compression codec | `lib/Pia/Image`, `lib/Pia/Compress`, ADR 0054 | `tests/std/image_*`, `tests/std/gif_*`, `tests/std/inflate.pia`, `tests/std/zlib_*` |
| a file format (safetensors) | `lib/Pia/Format`, ADR 0067 | `tests/std/safetensors*`; `tools/llm/export.py` converts a llama2.c checkpoint |
| memory, allocators, `box`, `vec` | `lib/Pia/Mem/{Alloc,Box,Vec}.pia`; pools, pages and `vec (box t)` are still prototypes in `tests/verify/{arena,pool,vec_boxes}.pia` | `tests/std/mem*.pia`, `src/irgen/Boxes.cpp`, `Regions.cpp` |
| user docs or an example | `docs/*.md`, listed in `mkdocs.yml` | a page under test is listed in `tests/docs/BUILD.bazel` |
| an agent skill | `skills/<name>/SKILL.md`, linked from `.claude/skills` | add it to `SKILLS` in `tests/docs/BUILD.bazel` and the tables in `skills/README.md` and `docs/agents.md`; `python3 tools/skills/check.py` lists what is missing |

**A working example of almost every feature** is in `tests/verify/<feature>.pia`, for example `handlers.pia`, `defer.pia`, `lambda_captures.pia`, `concepts.pia`, `models.pia` and `vec_boxes.pia`. Run `ls tests/verify` and copy from the closest one.

## 4. Source files

Line counts are as of 2026-11-23. For a file over 1,500 lines, run `outline.py` first.

### src/syntax: front end (no MLIR, builds with plain g++)

- `src/syntax/Token.h` lists the token kinds. `src/syntax/Lexer.{h,cpp}` is the lexical grammar, including nested comments.
- `src/syntax/Syntax.{h,cpp}` is the AST: a `Node` with a `kind`, `kids`, text and location.
- `src/syntax/Parser.{h,cpp}` (1.8k lines) is recursive descent with precedence climbing over the prelude's operator table.
- `src/syntax/Prelude.cpp` is the prelude source as a Pia string: the operators, `fold_and`, `derive_eq` and `machine`.
- `src/syntax/Comments.{h,cpp}` attaches comments to nodes (ADR 0029). It also reads literate `.pia.md`.
- `src/syntax/RecTypes.{h,cpp}` finds the type items that refer to themselves, alone or in cycles, for sema's `let rec` checks and the `needless_rec` lint (ADR 0047).
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
- `src/codegen/ArrayResults.{h,cpp}` turns each array result into a buffer the caller makes, and each return into a copy into it, so arrays are returned by value.
- `src/codegen/Lowerings.{h,cpp}` puts each `@lower` function's MLIR in place of its body after `lowerToCore`, and adds the passes that take `linalg` to loops (ADR 0065).
- `src/codegen/SliceBuffers.{h,cpp}` splits each buffer of slices into a buffer of addresses and one of lengths before lowering (ADR 0048, step 3).
- `src/gpu/Spirv.{h,cpp}` is the GPU path's lowering (ADR 0068, step 1): it registers the `gpu` and `spirv` dialects, lowers a `gpu.module` to a `spirv.module` with upstream MLIR passes, and serialises it to a SPIR-V binary. `piac --emit=spirv` and `pia-opt` use it. `tools/gpu/metal.bzl` builds a `.metallib` from MSL with Xcode's Metal toolchain and embeds it in a `cc_library`. `third_party/spirv_cross` builds SPIRV-Cross, which translates SPIR-V to MSL; SPIRV-Tools comes from the Bazel Central Registry. `tests/gpu` takes a hand-written kernel through all of it.
- `src/cert/Certificate.{h,cpp}` is the proof certificate an object carries (the interfaces it provides and imports, with their hashes, and its trusted lowerings), how to read one from an object file, and the link check (docs/abi.md).

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
- `tools/bench/proof_bench.py`, `tools/bench/corpus.txt` and `tools/bench/baseline.json` make up the proof-cost benchmark (ADR 0032); `tools/bench/needs_bench.py` decides from the changed paths whether CI runs it.
- `tools/bench/solver_compare.py` splits a `--dump-smt` into queries and compares solvers on them: Z3 bit-blasting, Z3 int-blasting, cvc5, Bitwuzla (ADR 0066).
- `tools/docs/hooks.py` and `tools/docs/requirements.txt` are the MkDocs hook (source links to GitHub, OCaml highlighting) and its pinned version.
- `tools/imac/bazelq` is the machine-wide FIFO build queue for the shared iMac, and `tools/imac/install.sh` installs it with a `bazel` shim and the 4-job limits in `~/.bazelrc`.
- `tools/codemap/outline.py` outlines a file. `tools/codemap/check.py` checks this map.
- `tools/llm/export.py` converts a llama2.c checkpoint (karpathy/tinyllamas) to safetensors with the config in `__metadata__` (ADR 0067). It is not run by the build.
- `tools/bindings/gen.py` writes `lib/Pia/Sys/Gen/<target>.pia` from the host's C headers, for the names in `tools/bindings/posix.toml` and the rows of `lib/Pia/Sys/Posix.pia`, which it checks against the headers (ADRs 0051 and 0057). `--check` is the drift check that `.github/workflows/bindings.yml` runs on both targets.

### lib: the standard library, written in Pia (ADR 0023, ADR 0040)

Each module is a `pia_library` in the `BUILD.bazel` next to it, with its tests in `tests/std/<module>.pia` and `tests/std/Inputs/<module>_run.pia`. Its mapping from C++ and its status are in `docs/cpp-std.md`.

- `lib/Pia/Fn.pia` holds the laws of function arguments as spec functions, such as `strict_weak_order` (ADR 0044).
- `lib/Pia/Core/Ascii.pia` is `<cctype>` for ASCII bytes. `lib/Pia/Core/Charconv.pia` is `<charconv>`'s `from_chars` and `to_chars` for integers. `lib/Pia/Core/Digits.pia` is the lemma library for digit strings (`dval`, `pow`, `prepend`, `frame`, `divmod`), which importers call as facts. `lib/Pia/Core/Hash.pia` is `std::hash`: the Hash concept, integer instances and FNV-1a. `lib/Pia/Core/Ratio.pia` is `<ratio>`, as exported metaprograms that fold ratios at compile time. `lib/Pia/Time.pia` is `<chrono>`'s durations, made by metaprograms over Ratio, time points over them, and the civil calendar with both round trips proved. `lib/Pia/Core/Bit.pia` is `<bit>`. `lib/Pia/Core/Int.pia` holds the integer utilities: gcd, midpoint, abs, div and saturating arithmetic.
- `lib/Pia/Core/Order.pia` is `<compare>`, with the `Eq` and `Ord` concepts and `ordering`. `lib/Pia/Core/Option.pia` is `<optional>`. `lib/Pia/Core/Result.pia` is `<expected>`, its instances stamped out by the `result_family` metaprogram. `lib/Pia/Core/Utf8.pia` is UTF-8: decode, encode and validate, with both round trips proved.
- `lib/Pia/Core/Algo/Search.pia` holds the non-modifying sequence algorithms. `lib/Pia/Core/Algo/Modify.pia` holds the modifying ones. `lib/Pia/Core/Algo/Remove.pia` is `remove`.
- `lib/Pia/Core/Algo/Sort.pia`, `lib/Pia/Core/Algo/Heap.pia` and `lib/Pia/Core/Algo/BinarySearch.pia` hold sorting, the heap operations and the binary search family. `lib/Pia/Core/Algo/Permutation.pia` holds the multiset spec functions the sorts use.
- `lib/Pia/Core/Algo/PartialSort.pia` holds `partial_sort` and `nth_element`. `lib/Pia/Core/Algo/Partition.pia` holds `is_partitioned`, `partition_point` and `partition`.
- `lib/Pia/Core/Algo/Merge.pia` holds `merge`, from two sorted ranges into an out slice.
- `lib/Pia/Mem/Alloc.pia` holds `oom`, the `Allocator` concept and the bump allocator. `lib/Pia/Mem/Box.pia` is `box t r` over any allocator, and `lib/Pia/Mem/Vec.pia` is `vec t a r`, a growable vector that holds its allocator.
- `lib/Pia/Core/Algo/Set.pia` holds `includes`, `set_intersection` and `set_difference`. `lib/Pia/Core/Algo/SetUnion.pia` holds `set_union`.
- `lib/Pia/Core/Algo/SetSymmetric.pia` holds `set_symmetric_difference`, in its own module so it proves in parallel with `set_union`.
- `lib/Pia/Core/Algo/Numeric.pia` is `<numeric>`.
- `lib/Pia/Text/Json/Spec.pia` is the RFC 8259 token grammar as spec functions. `lib/Pia/Text/Json/Lex.pia` is a tokenizer proved against it, `lib/Pia/Text/Json/Write.pia` a writer proved to produce its tokens, and `lib/Pia/Text/Json/Read.pia` the token readers `@derive(json)` builds on, and `lib/Pia/Text/Json/Derive.pia` exports `@derive(json)` itself with the concept `Json`, `Json.read` and `json_errors` (ADR 0045).
- `lib/Pia/Sys/Posix.pia` is the `Posix` interface, the contract overlay: one row per POSIX function or constant (ADR 0057). `lib/Pia/Sys/Gen/arm64_macos.pia` and `lib/Pia/Sys/Gen/x86_64_linux.pia` are the module `Pia.Sys.Posix` for each target, generated by `tools/bindings/gen.py` from the headers and that interface: constants, struct layouts, the rows as contracted externs, and the other functions as private externs. Never edit them by hand. `//lib/Pia/Sys:posix` picks one by platform. `tests/irgen/sys_gen.pia` proves both, and `tests/std/posix_import.pia` imports one.
- `lib/Pia/Sys/Fs.pia` is files over `Pia.Sys.Posix`, written once for both targets: a decoded `errno` variant, a `@linear` `file`, `open_read`, `create`, `read_some`, `write_all` and `close` (#57). `tests/std/fs.pia`, `tests/std/fs_edges.pia` and `:fs_run_test` test it.
- `lib/Pia/Image/Bits.pia` reads and writes LSB-first bit fields over a byte slice, for GIF and deflate. `lib/Pia/Image/Raster.pia` holds image dimensions, sample indices and rectangles (ADR 0054).
- `lib/Pia/Image/Gif/Spec.pia` is GIF89a as spec functions: the LZW dictionary and the block grammar. `lib/Pia/Image/Gif/Lzw.pia` is the LZW decoder proved against it. `lib/Pia/Image/Gif/Decode.pia` is the container: `info`, proved to accept exactly what the grammar accepts, and `decode_frame`, which composites frames.
- `lib/Pia/Image/Gif/LzwEncode.pia` is the LZW encoder and the sub-block writer. `lib/Pia/Image/Gif/Encode.pia` is the animated GIF encoder, `encode_animation`, with its proved size bound.
- `lib/Pia/Image/Gif/Quantise.pia` maps RGB to a palette of at most 256 colours (exact when the input has few enough, else median cut), and holds `encode_rgb_animation`.
- `lib/Pia/Compress/Huffman.pia` builds and decodes canonical Huffman codes. `lib/Pia/Compress/Inflate/Spec.pia` is RFC 1951's block parts as spec functions, `lib/Pia/Compress/Inflate.pia` decodes deflate, and `lib/Pia/Compress/Zlib.pia` is RFC 1950 with Adler-32 (ADR 0054).
- `lib/Pia/Format/Safetensors.pia` reads the safetensors container the LLM demo's weights load from: the header's tensor table into a caller's buffer, proved total, with every tensor placed in the data region and the tensors tiling it in order (ADR 0067, M1). Its fixture and run test come from `tests/std/Inputs/safetensors_gen.py`.

### Elsewhere

- `examples/edges` (`edges.pia`, `edges_buggy.pia` and the C harness) is the edge detection demo, and `docs/demo.md` describes it. `examples/streams` is the C harness for `docs/streams.pia.md`, the stream delineation demo, `docs/sediment.pia.md`, its sediment transport stage, `docs/basins.pia.md`, sediment by basin in parallel, and `docs/pull.pia.md`, sediment in pull form, waves of a `spread`, proved equal to the sequential step; `examples/streams/gif.pia` is the C entry point for the animated GIF of the evolving landscape. `examples/streams/srtm.c` runs the pipeline on a real SRTM tile, which `examples/streams/fetch_srtm.sh` downloads; `examples/streams/demo_io.c` is the image and file I/O both programs share, and `examples/streams/testdata` holds a 256 × 256 crop of a tile for the tests, with its source and attribution.
- `grammar/pia.lark`, `grammar/pia_lexer.py` and `grammar/pia_grammar.py` are the reference grammar in Lark, checked against the C++ parser.
- `editors/vscode` is the VS Code extension: TextMate grammars and an LSP client.
- `skills/` holds the agent skills, listed in `skills/README.md`. Claude Code finds them through `.claude/skills/*`, which are symlinks. They are `skills/pia-language` (writing Pia), `skills/pia-porting` (a feature map from C, C++, Rust, OCaml, Zig and Go), `skills/pia-idioms` (acting on lints), `skills/pia-contracts` (fixing failed goals), `skills/piac-verify` and `skills/pia-fast-proofs` (running the prover), `skills/piac-build` (compiling, linking, trust reports, certificates), `skills/pia-repl` and `skills/pia-mcp` (cell by cell), and `skills/pia-proof-debugging` (is this C, C++ or Rust correct?).
- `.claude-plugin/marketplace.json` and `.claude-plugin/plugin.json` make the repository a Claude Code plugin marketplace: the `pia` plugin installs the skills, `pia-lsp` as a language server and `pia mcp` as an MCP server (docs/agents.md).
- `tools/skills/check.py` checks the pack is complete: each skill wired into tests, tables and links, the manifests, and every lexer keyword and piac flag taught by some skill. `.github/workflows/skills.yml` runs it.
- `wip/huffman-kraft/` (`README.md`, `kraft.pia`) is unfinished work on Huffman's Kraft lemma (ADR 0054 step 5), not built by Bazel; its README says what is proved.
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

User docs (the site, `mkdocs.yml`): `docs/index.md`, `getting-started.md`, `tour.md`, `idioms.md`, `verification.md`, `theories.md`, `repl.md`, `repl-debugging.md`, `agents.md`, `comparison.md`, `status.md`, `demo.md`, `streams.pia.md`, `sediment.pia.md`, `basins.pia.md` and `cases/`; `docs/images/` holds images the pages show (`sediment-evolution.gif`, the demo's animation). Internals: `design.md`, `architecture.md`, `grammar.md`, `irgen.md`, `verifier.md`, `codegen.md`, `meta.md`, `abi.md`, `concurrency.md`, `stdlib.md`, `cpp-std.md`, `init.md` and `style.md`.

ADRs are in `docs/adr/NNNN-title.md`. The index is `docs/adr/README.md`. By topic:

- **Syntax and bindings:** 0002 (single `let`), 0019 (grammar), 0059 (digit separators, `min t`/`max t`), 0022 (hygiene, no shadowing), 0029 (comments, literate), 0039 (modules and interfaces).
- **Types:** 0003 (`dyn`), 0005 (parameter modifiers), 0009 (generics, concepts), 0034 (overloads), 0035 (SFINAE, type `match`), 0043 (generics proved once), 0044 (lambdas), 0046 (`box`), 0047 (recursive types), 0048 (buffers of slices), 0051 (tuples, variadic packs, `one_of`, generated foreign bindings), 0057 (`Pia.Sys.Posix` per target behind one interface), 0064 (distinct types: `type` always makes a new type).
- **Proof:** 0004 (strongest guarantee by default), 0006 (contracts, module state), 0020 (Presburger), 0032 (parallel, sliced, cached proving), 0036 (library theories), 0037 (idioms and lints), 0038 (floats against real theories), 0049 (targets as theories), 0058 (spec buffers), 0061 (Lean-proved lemmas and models, asymptotics), 0062 (cost bounds in contracts), 0063 (opaque spec functions), 0066 (int-blasting for nonlinear goals), 0069 (pure and impure functions).
- **Errors and memory:** 0026 (memory manager), 0028 (`?`, handlers, `defer`), 0041 (allocators), 0042 (lifetimes).
- **Metaprograms:** 0007 (fixed-point expansion), 0008 (operators).
- **Modules, ABI and trust:** 0010 (interfaces, certificates), 0024 (published certificates), 0030 (layouts), 0033 (initialisation).
- **Compiler and tools:** 0001 (ADRs), 0011 (MLIR and Z3), 0017 (Bazel), 0018 (dialects), 0065 (lowerings written in Pia: `@lower`, `@schedule`, linalg to SPIR-V), 0021 (LSP), 0025 (sanitizers), 0031 (REPL), 0056 (tests generated from contracts and theories), 0070 (raw binary embedding via `@embed`).
- **Performance and parallelism:** 0012 (FP reassociation), 0013 (auto-vectorisation), 0014 (concurrency), 0015 (device placement), 0068 (GPU compute: SPIR-V, SPIRV-Cross, Metal shim, `@place(gpu)`), 0027 (coroutines, race freedom), 0050 (senders and receivers, io_uring and kqueue), 0052 (atomics), 0053 (protocols checked by Z3 and CHC), 0060 (`spread` v0: ownership and runtime).
- **Library and demos:** 0016 (streams demo), 0023 (minimal core, self-hosted stdlib), 0040 (C++23 std), 0045 (JSON), 0054 (GIF and inflate codecs), 0055 (sediment transport in fixed point), 0067 (0.1.0: a proved small LLM on the M3).

## 7. Keeping this map current

- A PR that adds, renames or deletes a file in `src/`, `lib/`, `tools/`, `tests/` (directories only), `examples/` or `skills/`, or adds an ADR, updates this file in the same PR. `python3 tools/codemap/check.py` says what is missing.
- Keep each entry to one line that says what the file is for, not how it works. The file's own header comment holds the detail.
- Section 3 is the part that earns its keep. When a task took you a while to locate, add a row for it.
