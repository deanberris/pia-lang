---
name: piac-build
description: Build Pia beyond a single proof - compile to objects and assembly, build modules against interfaces, call Pia from C and C from Pia, use the Bazel rules, read the trust report and check proof certificates with pia-cert, and pick targets. Use when compiling, linking or packaging Pia code, auditing what a build trusts, or choosing piac flags.
---

# Building Pia with `piac`

`piac` proves a file and then compiles it; it never generates code for a program with a failed goal. Proving and reading the report are in `piac-verify`, and making proofs fast is in `pia-fast-proofs`. This skill is everything after that.

```sh
bazel build //tools/piac //tools/pia //tools/pia-lsp //tools/pia-cert
piac=bazel-bin/tools/piac/piac
```

## The pipeline, and where each flag stops it

| Command | Stops after |
| --- | --- |
| `piac --check f.pia` | parsing and the lints |
| `piac --dump-tokens`, `--dump-ast`, `--dump-expanded f.pia` | lexing, parsing, metaprogram expansion (`--comments` keeps comment nodes, `--meta-cycles=N` caps expansion) |
| `piac --emit=mlir f.pia` | the Pia dialects; with `--verify`, proved ops are marked `pia.proved` |
| `piac --verify f.pia` | the proof, with a report |
| `piac --emit=core\|llvm\|asm f.pia` | the proof, then the core MLIR dialects, LLVM IR or assembly |
| `piac --emit=obj -o f.o f.pia` | the proof, then an object file |
| `piac --emit=interface -o DIR m.pia` | a module's interface artifacts (`.piai`), from the source alone, with no proof |

A `.pia.md` file is literate (only its ` ```pia ` blocks are code); `--literate` forces that for another name. `--fragment=contracts` parses a file of contract clauses alone.

## Code generation

- `--target=<triple>` and `--cpu=<name>`: arm64 macOS (`arm64-apple-macosx14.0.0`, `apple-m1`) is the default, and `x86_64-unknown-linux-gnu` is the second target (ADR 0049). The target is also a theory (`Pia.Target`), so code can prove facts that hold only on one target.
- `-O0` to `-O3`.
- `@lower("...")` on a function in a `@trusted` file gives it an MLIR form, such as `linalg.matmul`, that codegen compiles in place of its Pia body (ADR 0065). The body is still proved, and `--trust-report` lists the lowering as a trusted item. `--lower=off` compiles the Pia bodies instead, so a test can compare the two forms. `@lower(gen args)` takes the string a `let meta` computes, with the parameters passed as names; the MLIR is parsed, and checked to write only `out` and `inout` buffers, before anything is proved, so a bad lowering fails fast in `--verify` too.
- Each Pia function becomes a C function of the same name, and an `@abi(c)` interface keeps C names for a module's exports. Records and slices pass as documented in [docs/codegen.md](../../docs/codegen.md#c-abi): a slice is a pointer and a length.

To call C from Pia, give the C function a contract; its preconditions are proved at each call and its postconditions are trusted:

<!-- example: ffi.pia -->
```ocaml
let clamp (x : i32) : i32
  ensures result >= 0 && result <= 100
= extern "clamp_c"

let pct (x : i32) : i32
  ensures result <= 100
= clamp x
```

An `extern` with no contract can only be called as `unsafe f x`, and nothing is known about its result.

## Modules

One file is one module, with a `module M : I` header; only what an interface lists is visible outside. Build the dependency's interfaces first, then the importer against them:

```sh
piac --emit=interface -o ifaces dep.pia
piac --verify --iface-path=ifaces main.pia
```

Importers are checked against the interfaces' contracts, never the bodies, so a change to a body or a private item leaves the `.piai` files byte-identical and rebuilds nothing downstream.

## Bazel rules

`load("//tools/piac:pia.bzl", "pia_object", "pia_library", "pia_binary")`:

| Rule | Builds | Notes |
| --- | --- | --- |
| `pia_object(name, src)` | `<name>.o` from one file with no imports | put it in a `cc_library`'s `srcs` to call it from C |
| `pia_library(name, src, deps)` | a module: its objects and `<name>.piai/` | `deps` are other `pia_library` targets; each `import` must be provided by a direct dep. Also checks the certificates link |
| `pia_binary(name, src, deps)` | a program whose `main` is in `src` | a `pia_library` plus a `cc_binary` |

`load("//tools/lean:lean.bzl", "pia_lean_proof")`: `pia_lean_proof(name, src, proofs)` checks the Lean proofs in `proofs` of the lemmas of `src` proved in Lean and writes `<name>.receipt`, for `piac --lean-receipt=` (ADR 0061, the `pia-lean` skill).

All three take `allow_unproved = [...]` (each becomes `--allow-unproved=`), `solver_rlimit` and `solver_timeout_ms`, with the same deterministic defaults as `piac`, so a proof does not depend on how loaded the build machine is.

## What a build trusts

`--trust-report` lists the trusted items the proofs rest on: axioms of theories with no model, `assume`s (only allowed in a `@trusted` file), contracts of `extern` functions and `unsafe` calls. `--why` adds, for each trusted item, the goals whose proofs used it, and the report ends with how many proved goals rest on one. Lemmas proved in Lean (`= by lean T`, the `pia-lean` skill) are not trusted, but have a section of their own after the count: each with its theorem, Lean toolchain, axioms and statement hash, and with `--why` the goals that use it, since they rest on Lean's kernel and on piac's translation of the statement. A Lean proof by `native_decide` trusts Lean's compiler, so it is allowed only in a `@trusted` file and listed as a trusted item. `--check-vacuity` re-solves each goal proved from a trusted axiom or an `assume` without its negation, and fails it if its hypotheses contradict each other.

```sh
piac --verify --trust-report --why f.pia
piac --verify --check-vacuity f.pia
```

Read the trust report before shipping: everything in it is something a person has to believe.

## Proof certificates

Every object `piac` writes carries a certificate in the `__TEXT,__pia_cert` section: the module, the interfaces it provides and the interfaces it requires, each with the hash it was proved against, its trusted items (`trusted lowering ...`, `trusted native_decide ...`) and its lemmas proved in Lean (`proved lean <lemma> <statement hash> by <theorem> (<toolchain>; axioms ...)`), plus a witness symbol per interface, so a stale library fails to link instead of running against contracts it was never proved with ([docs/abi.md](../../docs/abi.md), ADR 0024).

```sh
pia-cert dump f.o                          # print the certificate
pia-cert check a.o b.o main.o              # every required interface is provided, with the same hash
pia-cert check --stamp=ok.txt a.o b.o      # also write the result, for a build step to depend on
```

`pia_library` runs `pia-cert check` as a validation action. Exit status: 0 when the objects link, 1 when they do not, 2 for bad usage or an unreadable object.

## Other tools

| Tool | Use |
| --- | --- |
| `pia repl`, `pia repl --json`, `pia mcp` | cell-by-cell sessions with a JIT (`pia-repl`, `pia-mcp`) |
| `pia-lsp` | the language server, over stdio: diagnostics, lints with quick fixes, hover, definitions, rename and a deep proof check (`--timeout-ms=N` per goal, default 10000) |
| `pia-opt` | `mlir-opt` with the Pia dialects registered, for compiler work |

## Diagnosing overloads and metaprograms

- `--explain-overloads=f.pia:L` prints, for each overloaded or generic call on line L, the candidates, why each was removed, and which one won.
- `--dump-expanded` shows the program after metaprograms run: the place to look when a `@derive` or an operator does something surprising.
