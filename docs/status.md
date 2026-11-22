# Status and roadmap

Pia is an experimental language under active development. The compiler works end to end for a small subset, and much of the language is designed but not built. Nothing is stable yet: syntax, flags and the compiled ABI can all change before a 0.1 release.

## What works today

| Area | Status |
| --- | --- |
| Parser | The whole grammar in [grammar.md](grammar.md), including the parts the later stages do not handle yet |
| Types | Bounded integers, range types `int{lo..hi}`, `bool`, fixed arrays `[T; n]`, slices `[T]`, records, variants, type aliases |
| Code | Functions, `let rec`, `let ... in`, mutable locals and buffers, `if`, `for`, `while`, parameter modifiers |
| Overflow | `@overflow(proof)` by default, plus `wrap`, `saturate` and `trap`, and saturating operators |
| Contracts | `requires`, `ensures`, `assert`, `assume` (only in a file marked `@trusted`), `old`, `forall` and `exists`, loop `invariant` and `decreases`, spec functions and lemmas, the spec-only types `int` (unbounded) and `real`, theories (sorts, abstract functions and axioms with triggers) and their models, which prove the axioms and are sealed from clients, `where` refinements on record fields, consistency checks of trusted theories, `--trust-report --why` with the axioms and `assume`s each goal used, theories built by metaprograms, such as the prelude's `machine` ([verifier.md](verifier.md#theories)), and solver strategies (`@solver`) and tactics (`@by`), metaprograms that write proof steps ([verifier.md](verifier.md#solver-strategies-and-tactics)), and `--check-vacuity`, which fails a goal proved from contradictory hypotheses |
| Verification | Overflow, nonzero divisors, bounds, preconditions at calls, postconditions and assertions, by intervals and Z3, with counterexamples |
| Metaprograms | `let meta` functions, quotes and splices, hygiene, operators defined in the prelude and by programs, `@derive(eq)`, expansion to a fixed point |
| Comments | `(* *)`, `\` line and `(** *)` doc comments, kept in the syntax tree for metaprograms and hover; literate `.pia.md` files |
| Modules | one module per file with a `module` header; everything is private unless an interface the module claims lists it; each listed item is checked against the module, with contracts proved; `@abi(c)` interfaces keep C names; `piac --emit=interface` writes canonical `.piai` artifacts, `import M.I` finds them on `--iface-path` and checks callers against their contracts (an overloaded function comes in as its whole overload set, each overload checked against its own definition), modules link through `__pia$M$f` symbols, and the `pia_library` and `pia_binary` Bazel rules build modules separately with strict dependencies ([ADR 0039](adr/0039-module-and-interface-syntax.md), steps 1 and 2 of 7, and step 3 in part: interfaces show records, variants and generic types, which importers use as `M.t` with the variants' constructors in scope, and list concepts, generic functions and spec functions, which come with their definitions, and state postconditions of functions that write their parameters, and `import M.I as X { a, b }`; step 4 in part: values, shown with `=` or known only by type; qualified quotes and module state follow) |
| Codegen | arm64 for Apple Silicon through MLIR and LLVM: object files, assembly and LLVM IR, a C ABI for exported functions, saturating NEON instructions and vectorised loops |
| Demo | [Edge detection](demo.md): a Pia image pipeline, proved and compiled into a program you can run with `bazel run //examples/edges`; [stream delineation](streams.pia.md), a literate program with sink filling, D8 directions, flow accumulation and watersheds, run with `bazel run //examples/streams` |
| Tools | `piac`, `pia-opt`, the `pia-lsp` language server and a VS Code extension, and [`pia repl`](repl.md), a verified REPL with a JIT, a JSON mode, an MCP server (`pia mcp`), proved live redefinition of code that background tasks are running, and state with invariants and verified migration |

## Known limitations

- **Loops need invariants.** After a loop, only its invariant is known, so a goal after the loop that depends on what it did needs an invariant that says so.
- **Termination is checked for loops and direct recursion only.** A `while` loop or a recursive call without `decreases` is a skipped goal, which `piac` refuses unless `--allow-unproved` accepts it. Mutual recursion is not checked.
- **Calls inside contracts** to functions other than spec functions and pure functions of scalars are unknown values, so a contract cannot rely on what such a function computes.
- **Counterexamples do not show array contents** yet, only lengths and scalar values.
- **Function values are partly compiled.** Typed lambdas without captures, and top-level functions, can be passed to a parameter of function type, which may carry a contract, and a lambda can be bound by a `let` and applied ([ADR 0044](adr/0044-function-values-and-lambdas.md), steps 1 and 2). So can function objects, any record or variant with an `apply`, which `g x` calls. `Function` is a standard concept, and an overload set may mix functions that take values with functions that take functions. Each call with a function argument is proved and compiled as its own specialisation. Lambdas that capture, untyped and generic lambdas, and storing or returning functions come later.
- **Not compiled yet:** other function values, recursive types, `dyn`, floats, `vec<T, k>`, refinement types and `where` on values, imports, separate compilation and nested modules, `spread` and the concurrency runtime. `piac` reports these as "not supported yet" at their source location.
- **One target.** Code generation targets arm64 macOS. The compiler itself builds on Linux and cross-compiles.

## Roadmap

The plan is a sequence of milestones, each a GitHub issue, building towards the flagship demo: stream delineation and sediment transport over a terrain heightmap, proved correct and running across the CPU and GPU ([ADR 0016](adr/0016-stream-delineation-flagship-demo.md)).

| Milestone | Scope | |
| --- | --- | --- |
| M0 to M7 | Bazel build, grammar, parser, MLIR dialects, IRGen, verifier, arm64 codegen, records and the metaprogram engine | done |
| [M8](https://github.com/deanberris/pia-lang/issues/9) | Modules, explicit interface imports, proof certificates and a link check | next |
| [M9](https://github.com/deanberris/pia-lang/issues/10) | Generic types, concepts with laws, adapters and call-site deduction | generic types and functions, overloading, concepts, the definition check, adapters, ranking by constraints and choosing by preconditions done (ADR 0034 complete); generic bodies proved once over their type parameters as well as at each instance (ADR 0043, step 1 of 5); ADR 0035: type-level metaprograms in types and `where` predicates, their totality check, and soft failure with `--explain-overloads` done (ADR 0035 complete) |
| [M10](https://github.com/deanberris/pia-lang/issues/11) | Vectorisation driven by proved facts, and `vec<T, k>` | |
| [M11](https://github.com/deanberris/pia-lang/issues/12) | Floats: strict IEEE, and three ways to allow reassociation | |
| [M12](https://github.com/deanberris/pia-lang/issues/13) | Concurrency: `spread`, collectives, and compile-time checks that collectives match | |
| [M13](https://github.com/deanberris/pia-lang/issues/14) | PNG and GIF decoding and encoding, written in Pia | |
| [M14](https://github.com/deanberris/pia-lang/issues/15) | The stream delineation demo: delineation [done](streams.pia.md), sediment transport and Pia image codecs next | |

Alongside these, a Presburger stage will decide affine goals such as aliasing and loop-carried dependence ([ADR 0020](adr/0020-presburger-for-affine-goals.md)). After a 0.1 release, Pia will be offered to [Compiler Explorer](https://github.com/deanberris/pia-lang/issues/30).

## Following along

The [Architecture Decision Records](adr/README.md) record every design decision and why it was made. The [compiler architecture](architecture.md) describes the pipeline and the milestones in more detail.
