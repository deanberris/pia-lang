# Status and roadmap

Pia is an experimental language under active development. The compiler works end to end for a small subset, and much of the language is designed but not built. Nothing is stable yet: syntax, flags and the compiled ABI can all change before a 0.1 release.

## What works today

| Area | Status |
| --- | --- |
| Parser | The whole grammar in [grammar.md](grammar.md), including the parts the later stages do not handle yet |
| Types | Bounded integers, range types `int{lo..hi}`, `bool`, fixed arrays `[T; n]`, slices `[T]`, records, variants, type aliases |
| Code | Functions, `let rec`, `let ... in`, mutable locals and buffers, `if`, `for`, `while`, parameter modifiers |
| Overflow | `@overflow(proof)` by default, plus `wrap`, `saturate` and `trap`, and saturating operators |
| Contracts | `requires`, `ensures`, `assert`, `assume`, `old`, `forall` and `exists`, loop `invariant` and `decreases`, spec functions and lemmas, the spec-only types `int` (unbounded) and `real`, theories (sorts, abstract functions and axioms with triggers) and their models, which prove the axioms and are sealed from clients, `where` refinements on record fields, consistency checks of trusted theories, and `--trust-report --why` with the axioms each goal used ([verifier.md](verifier.md#theories)) |
| Verification | Overflow, nonzero divisors, bounds, preconditions at calls, postconditions and assertions, by intervals and Z3, with counterexamples |
| Metaprograms | `let meta` functions, quotes and splices, hygiene, operators defined in the prelude and by programs, `@derive(eq)`, expansion to a fixed point |
| Comments | `(* *)`, `\` line and `(** *)` doc comments, kept in the syntax tree for metaprograms and hover; literate `.pia.md` files |
| Modules | one module per file with a `module` header; everything is private unless an interface the module claims lists it; each listed item is checked against the module, with contracts proved; `@abi(c)` interfaces keep C names; `piac --emit=interface` writes canonical `.piai` artifacts, `import M.I` finds them on `--iface-path` and checks callers against their contracts, modules link through `__pia$M$f` symbols, and the `pia_library` and `pia_binary` Bazel rules build modules separately with strict dependencies ([ADR 0039](adr/0039-module-and-interface-syntax.md), steps 1 and 2 of 7; imported types, `as` and `{ }` come in step 3) |
| Codegen | arm64 for Apple Silicon through MLIR and LLVM: object files, assembly and LLVM IR, a C ABI for exported functions, saturating NEON instructions and vectorised loops |
| Demo | [Edge detection](demo.md): a Pia image pipeline, proved and compiled into a program you can run with `bazel run //examples/edges`; [stream delineation](streams.pia.md), a literate program with sink filling, D8 directions, flow accumulation and watersheds, run with `bazel run //examples/streams` |
| Tools | `piac`, `pia-opt`, the `pia-lsp` language server and a VS Code extension, and [`pia repl`](repl.md), a verified REPL with a JIT, a JSON mode, an MCP server (`pia mcp`), proved live redefinition of code that background tasks are running, and state with invariants and verified migration |

## Known limitations

- **Loops need invariants.** After a loop, only its invariant is known, so a goal after the loop that depends on what it did needs an invariant that says so.
- **Termination is checked for loops and direct recursion only.** A `while` loop or a recursive call without `decreases` is a skipped goal, which `piac` refuses unless `--allow-unproved` accepts it. Mutual recursion is not checked.
- **Calls inside contracts** are unknown values, so a contract cannot rely on what another function computes.
- **Counterexamples do not show array contents** yet, only lengths and scalar values.
- **Not compiled yet:** function values and lambdas outside metaprograms, recursive types, `dyn`, floats, `vec<T, k>`, refinement types and `where` on values, imports, separate compilation and nested modules, `spread` and the concurrency runtime. `piac` reports these as "not supported yet" at their source location.
- **One target.** Code generation targets arm64 macOS. The compiler itself builds on Linux and cross-compiles.

## Roadmap

The plan is a sequence of milestones, each a GitHub issue, building towards the flagship demo: stream delineation and sediment transport over a terrain heightmap, proved correct and running across the CPU and GPU ([ADR 0016](adr/0016-stream-delineation-flagship-demo.md)).

| Milestone | Scope | |
| --- | --- | --- |
| M0 to M7 | Bazel build, grammar, parser, MLIR dialects, IRGen, verifier, arm64 codegen, records and the metaprogram engine | done |
| [M8](https://github.com/deanberris/pia-lang/issues/9) | Modules, explicit interface imports, proof certificates and a link check | next |
| [M9](https://github.com/deanberris/pia-lang/issues/10) | Generic types, concepts with laws, adapters and call-site deduction | generic types and functions, overloading, concepts, the definition check, adapters, ranking by constraints and choosing by preconditions done (ADR 0034 complete); ADR 0035: type-level metaprograms in types and `where` predicates, their totality check, and soft failure with `--explain-overloads` done (ADR 0035 complete) |
| [M10](https://github.com/deanberris/pia-lang/issues/11) | Vectorisation driven by proved facts, and `vec<T, k>` | |
| [M11](https://github.com/deanberris/pia-lang/issues/12) | Floats: strict IEEE, and three ways to allow reassociation | |
| [M12](https://github.com/deanberris/pia-lang/issues/13) | Concurrency: `spread`, collectives, and compile-time checks that collectives match | |
| [M13](https://github.com/deanberris/pia-lang/issues/14) | PNG and GIF decoding and encoding, written in Pia | |
| [M14](https://github.com/deanberris/pia-lang/issues/15) | The stream delineation demo: delineation [done](streams.pia.md), sediment transport and Pia image codecs next | |

Alongside these, a Presburger stage will decide affine goals such as aliasing and loop-carried dependence ([ADR 0020](adr/0020-presburger-for-affine-goals.md)). After a 0.1 release, Pia will be offered to [Compiler Explorer](https://github.com/deanberris/pia-lang/issues/30).

## Following along

The [Architecture Decision Records](adr/README.md) record every design decision and why it was made. The [compiler architecture](architecture.md) describes the pipeline and the milestones in more detail.
