# Architecture Decision Records

Each file records one decision: its context, the decision, and its consequences. See [ADR 0001](0001-record-architecture-decisions.md) for the process, and [`../design.md`](../design.md) for the readable overview.

| ADR | Decision | Status |
| --- | --- | --- |
| [0001](0001-record-architecture-decisions.md) | Record architecture decisions | Accepted |
| [0002](0002-single-let-binding-form.md) | `let` is the only binding form | Accepted |
| [0003](0003-static-typing-with-tagged-dyn.md) | Strong static typing; dynamic typing only through tagged values | Accepted |
| [0004](0004-strongest-guarantee-by-default.md) | The strongest guarantee is always the default | Accepted |
| [0005](0005-parameter-modifiers.md) | Parameters carry ownership, access and modifiability modifiers | Accepted |
| [0006](0006-contracts-and-module-state.md) | Contracts, refinement types, and module state as exported symbols | Accepted |
| [0007](0007-metaprogramming-fixed-point-expansion.md) | Metaprogramming from day one, expanded to a fixed point | Accepted |
| [0008](0008-operators-via-metaprograms.md) | Operators are defined only through metaprograms | Accepted |
| [0009](0009-generics-concepts-adapters.md) | User-defined generics, checked concepts with laws, and adapters | Accepted |
| [0010](0010-modules-interfaces-and-proof-certificates.md) | Modules export interfaces; imports name them; proofs carry certificates | Accepted |
| [0011](0011-mlir-and-z3-implementation.md) | Compiler in C++ on MLIR, verifying with interval analysis then Z3 | Accepted |
| [0012](0012-floating-point-reassociation.md) | Three ways to license float reassociation and FMA | Accepted |
| [0013](0013-auto-vectorisation.md) | Auto-vectorise as much as possible; keep `vec<T, k>` for explicit control | Accepted |
| [0014](0014-concurrency-model.md) | Concurrent by default: collectives, task graphs, futures; collectives proved to match | Accepted |
| [0015](0015-device-placement.md) | Device placement: compiler cost model, explicit, or overridable | Accepted |
| [0016](0016-stream-delineation-flagship-demo.md) | Stream delineation on Apple Silicon is the flagship demo | Accepted |
| [0017](0017-bazel-build.md) | Build with Bazel; depend on LLVM/MLIR and Z3 as Bazel modules | Accepted |
| [0018](0018-dialect-layering.md) | Three Pia dialects over upstream MLIR, with `smt` for solving | Accepted |
| [0019](0019-grammar-disambiguation.md) | Grammar disambiguation rules: contracts before bodies, layout, adjacency | Accepted |
| [0020](0020-presburger-for-affine-goals.md) | Decide affine aliasing and dependence goals with MLIR's Presburger library | Accepted |
| [0021](0021-language-server.md) | A language server, `pia-lsp`, with a VS Code client first | Accepted |
| [0022](0022-metaprogram-hygiene.md) | Hygiene and name lookup: no shadowing, renamed quote binders, qualified names, ADL | Accepted |
| [0023](0023-minimal-core-self-hosted-stdlib.md) | A minimal core, with the standard library written and proved in Pia | Accepted |
| [0024](0024-published-proof-certificates.md) | Shared libraries publish interfaces and proof certificates; loaders check them | Accepted |
| [0025](0025-sanitizers.md) | Sanitizers check the edges of the proof | Accepted |
| [0026](0026-memory-manager.md) | A memory manager of explicit allocators, with no garbage collection | Accepted |
| [0027](0027-coroutines-and-race-freedom.md) | Stackless coroutines, structured tasks, and race freedom proved from permissions | Accepted |
| [0028](0028-error-propagation-and-cleanup.md) | Errors propagate with `?` to a scope's handler; cleanup runs at scope end | Accepted |
| [0029](0029-comments-as-syntax-and-literate-pia.md) | Comments are syntax: `\` line comments, doc comments, and literate `.pia.md` files | Accepted |
| [0030](0030-published-object-layouts.md) | Optimised object layouts are published, and a changed layout fails to load until relinked | Proposed |
| [0031](0031-verified-repl-and-live-environment.md) | A verified REPL over a reusable session, with proved live redefinition | Proposed |
| [0032](0032-parallel-sliced-cached-proving.md) | Proofs run in parallel, one goal per solver, sliced, cached and selectable | Accepted |
| [0033](0033-module-initialisation-and-registries.md) | Module initialisation: registries, proved `@init` hooks, and opt-in dynamic registration | Accepted |
| [0034](0034-concepts-and-overload-resolution.md) | Concepts are checked signatures with laws; overloads are chosen by type, by constraint entailment and by proved preconditions | Accepted |
| [0035](0035-substitution-failure-and-total-constraints.md) | Substitution failure removes an overload candidate; constraint metaprograms are proved to terminate | Accepted (with type `match`) |
| [0036](0036-library-theories.md) | Libraries extend the solver with theories, proved consistent by a model or listed as trusted | Accepted |
| [0037](0037-idiomatic-pia-and-lints.md) | Idiomatic Pia: facts in types first, written as opinions and checked by lints | Accepted |
| [0038](0038-float-kernels-against-real-theories.md) | Float kernels are proved against real-valued specifications by rounding-error bounds | Accepted |
| [0039](0039-module-and-interface-syntax.md) | Modules are private by default: one module per file, interfaces list every export, imports name interfaces | Accepted |
| [0040](0040-cpp23-standard-library-in-pia.md) | The C++23 standard library is mapped onto Pia by capability, with every component proved | Accepted |
| [0041](0041-allocator-semantics-as-a-theory.md) | Allocator semantics are a theory, and allocators prove they refine it through spec-only state | Accepted |
| [0042](0042-lifetimes-liveness-and-escape-analysis.md) | Lifetimes are checked by liveness, marked where values cross boundaries, and escape analysis places memory | Accepted |
| [0043](0043-generic-definitions-proved-once.md) | Generic definitions are proved once, against their concepts, and instances are discharged by that proof | Accepted |
| [0044](0044-function-values-and-lambdas.md) | Function values: every lambda has its own type, arrow parameters are constrained by a Function concept, and proofs go through function arguments | Proposed |
| [0045](0045-json-derived-codecs-and-conforming-dom.md) | JSON: derived streaming codecs, typed construction by passing the type, and a recursive DOM over the input proved to conform to a type | Accepted |
| [0046](0046-box-over-a-type-or-a-concept.md) | A box holds a type or any type meeting a concept, and what it holds is proved to have the concept's shape | Accepted |
| [0047](0047-recursive-sum-types-and-shared-references.md) | Recursive sum types are explicit (`let rec`), recurse through an `Indirect` owning type, and share through `ref` and `weak`, mutated only under leases proved exclusive across threads | Accepted |
