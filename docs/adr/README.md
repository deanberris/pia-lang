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
| [0018](0018-dialect-layering.md) | Three Pia dialects over upstream MLIR, with `smt` for solving | Proposed |
