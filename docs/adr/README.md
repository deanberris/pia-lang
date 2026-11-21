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
| [0021](0021-language-server.md) | A language server, `pia-lsp`, with a VS Code client first | Proposed |
| [0022](0022-metaprogram-hygiene.md) | Hygiene and name lookup: no shadowing, renamed quote binders, qualified names, ADL | Accepted |
| [0023](0023-minimal-core-self-hosted-stdlib.md) | A minimal core, with the standard library written and proved in Pia | Proposed |
| [0024](0024-published-proof-certificates.md) | Shared libraries publish interfaces and proof certificates; loaders check them | Proposed |
| [0025](0025-sanitizers.md) | Sanitizers check the edges of the proof | Accepted |
| [0026](0026-memory-manager.md) | A memory manager of explicit allocators, with no garbage collection | Accepted |
| [0027](0027-coroutines-and-race-freedom.md) | Stackless coroutines, structured tasks, and race freedom proved from permissions | Proposed |
| [0028](0028-error-propagation-and-cleanup.md) | Errors propagate with `?` to a scope's handler; cleanup runs at scope end | Accepted |
| [0029](0029-comments-as-syntax-and-literate-pia.md) | Comments are syntax: `\` line comments, doc comments, and literate `.pia.md` files | Accepted |
| [0030](0030-published-object-layouts.md) | Optimised object layouts are published, and a changed layout fails to load until relinked | Proposed |
| [0031](0031-verified-repl-and-live-environment.md) | A verified REPL over a reusable session, with proved live redefinition | Proposed |
| [0032](0032-parallel-sliced-cached-proving.md) | Proofs run in parallel, one goal per solver, sliced, cached and selectable | Proposed |
