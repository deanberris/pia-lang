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
| [0030](0030-published-object-layouts.md) | Optimised object layouts are published, and a changed layout fails to load until relinked | Accepted |
| [0031](0031-verified-repl-and-live-environment.md) | A verified REPL over a reusable session, with proved live redefinition | Accepted |
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
| [0044](0044-function-values-and-lambdas.md) | Function values: every lambda has its own type, arrow parameters are constrained by a Function concept, and proofs go through function arguments | Accepted |
| [0045](0045-json-derived-codecs-and-conforming-dom.md) | JSON: derived streaming codecs, typed construction by passing the type, and a recursive DOM over the input proved to conform to a type | Accepted |
| [0046](0046-box-over-a-type-or-a-concept.md) | A box holds a type or any type meeting a concept, and what it holds is proved to have the concept's shape | Accepted |
| [0047](0047-recursive-sum-types-and-shared-references.md) | Recursive sum types are explicit (`let rec`), recurse through an `Indirect` owning type, and share through `ref` and `weak`, mutated only under leases proved exclusive across threads | Accepted |
| [0048](0048-buffers-whose-elements-hold-slices.md) | Buffers may hold slices: owned slices are written through, shared ones only read | Accepted |
| [0049](0049-targets-are-theories.md) | Linux x86_64 is a second target, tested in Linux CI, and each target is a model of a built-in `Pia.Target` theory | Accepted |
| [0050](0050-senders-and-receivers.md) | Asynchronous work is senders and receivers whose completion rules are proved, over io_uring on Linux and a kqueue completion adapter on macOS | Accepted |
| [0051](0051-variadic-generics-and-foreign-varargs.md) | Variadic functions and types take a pack that is called and partially applied like any argument list, walked by metaprograms and proved once; sums over a pack are matched by type; foreign bindings are generated from headers | Accepted |
| [0052](0052-atomics.md) | Atomics are a core cell type with checked orders and stated overflow, modelled by RC11 with a litmus battery before tasks exist, and lowered per target by a table proved against each hardware model | Accepted |
| [0053](0053-protocols-checked-by-z3.md) | Protocols and deadlock are checked in Z3, as transition systems proved by constrained Horn clauses; explicit search stays for atomics, and TLA+ is an export format | Accepted |
| [0054](0054-proved-gif-and-inflate-codecs.md) | GIF and inflate are proved total on every input, decode to a written specification, and GIF round-trips exactly; JPEG is deferred | Accepted |
| [0055](0055-sediment-transport-in-fixed-point.md) | Sediment transport is integer mass moved downhill in height order, with conservation proved exactly | Accepted |
| [0056](0056-tests-generated-from-contracts-and-theories.md) | Tests are generated by metaprograms from contracts, types and theories; a case the verifier can decide is proved, and only the rest is run | Accepted |
| [0057](0057-posix-module-per-target-behind-one-interface.md) | `Pia.Sys.Posix` is one generated module per target behind one hand-written interface, and the generator joins the contract overlay | Accepted |
| [0058](0058-spec-buffers.md) | Spec buffers: spec-only arrays that code writes, contracts read and codegen erases | Accepted |
| [0059](0059-digit-separators-and-type-bounds.md) | Digits group with `'` or `_`; `min t` and `max t` are an integer type's bounds, folded to literals | Accepted |
| [0060](0060-spread-v0-ownership-and-runtime.md) | `spread` v0: iterations own the cells they write, proved one iteration at a time; MLIR's async runtime runs them | Accepted |
| [0061](0061-lean-proved-facts.md) | Lean proves the facts Z3 cannot: lemmas and theory models proved in Lean against generated statements, recorded by statement hash, checked outside the edit loop; cost bounds proved by Z3, their asymptotics in Lean | Accepted |
| [0062](0062-cost-bounds-in-contracts.md) | Cost bounds are contracts: `costs c <= e` bounds what a function spends on a named counter, tracked by a spec-only `spent c` and proved by Z3 | Accepted |
| [0063](0063-opaque-spec-functions.md) | Opaque spec functions: a spec function marked `@opaque` keeps its definition out of every goal until a proof reveals it | Accepted |
| [0064](0064-distinct-types.md) | `type` always makes a new type: `let length = type u32` is distinct from `u32`, converts only by applying a type to a value, and inherits only what it derives | Accepted |
| [0065](0065-lowerings-written-in-pia.md) | Pia code extends the compiler's lowering: `@lower` gives a function an MLIR form and a type an MLIR type, the Pia definition stays the specification, and each lowering is proved to refine it or is listed as trusted | Accepted |
| [0066](0066-int-blasting-for-nonlinear-goals.md) | Nonlinear goals are tried first with Z3's int-blasting solver; cvc5 is deferred, and nothing GPL is used | Accepted |
| [0067](0067-release-0-1-0-a-proved-small-llm.md) | Release 0.1.0 is a small Llama-architecture LLM ported from PyTorch to Pia, proved where a proof means something, running inference on an M3 on CPU SIMD and on the GPU through linalg | Accepted |
| [0068](0068-gpu-compute-through-spirv-and-metal.md) | GPU compute: a proved `spread` placed on the GPU, lowered through SPIR-V and SPIRV-Cross to Metal, launched by a small trusted shim, with an Apple GPU float model; section 9 adds a placed sequence of spreads as one command buffer | Accepted |
| [0069](0069-pure-and-impure-functions.md) | Pure and impure functions: computed purity, `@pure` assertions, and `@impure` interface boundaries | Accepted |
| [0070](0070-raw-binary-embedding.md) | Raw binary embedding: `@embed` for compile-time fixed byte blobs, hermetic roots, opaque verification and direct LLVM emission | Accepted |
| [0071](0071-function-references.md) | Function references: a function is a value that travels by reference, checked against its arrow where the reference is made | Accepted |
| [0072](0072-drops-run-in-constant-stack.md) | A drop never grows the stack: every drop is one walk, proved against the recursive drop, with a fixed stack bound per type | Accepted |
| [0073](0073-prover-identity-abi-version-and-advisories.md) | Certificates record the piac, solvers and proof engines that proved a module and the Pia ABI version; advisories revoke trust in faulty provers; every breaking change ships a migration rule run by piac and `piac migrate` | Accepted |
| [0074](0074-library-types-tensors.md) | Library types: a type written in Pia gets an MLIR type, ops and proofs from its library, and `Pia.Tensor` over MLIR `tensor` is the proof point | Accepted |
| [0075](0075-codegen-benchmarks-against-c-cpp-rust-zig.md) | Codegen is benchmarked against C, C++, Rust and Zig on public problems, same algorithm first, counted in instructions on Linux and timed on Apple Silicon | Accepted |
| [0076](0076-transparent-exports.md) | Transparent exports: an exported function the verifier can unfold is exported with its body, so a module boundary never changes what proves; `@opaque` keeps one contract-only | Proposed |
| [0077](0077-definitions-inherit-interface-contracts.md) | A definition that states no contract takes the contract of the interface that lists it, so a module writes each contract once | Accepted |
| [0078](0078-pia-lib-ops-with-proved-substitutions.md) | Library functions lower to `pia_lib.call`, a Pia-owned op whose meaning is its Pia body; a late pass expands it or substitutes an upstream op through a rule proved against the body | Proposed |
| [0079](0079-pia-module-format.md) | Pia IR: a versioned op schema Pia controls, in lock-step with piac, encoding every op piac uses, with deprecations and migrations, not MLIR bytecode | Proposed |
| [0080](0080-release-0-1-0-gates.md) | Releases ship their libraries in .0 and finish their demo in patches; tracking labels; the gates for 0.1.0 | Proposed |
| [0081](0081-release-0-2-0-gates.md) | Release 0.2.0: an embeddable REPL and proved networking (HTTP/2, TLS through BoringSSL, gRPC) | Proposed |
| [0082](0082-release-0-3-0-gates.md) | Release 0.3.0: a SQL DSL and a proved embedded database | Proposed |
| [0083](0083-release-0-4-0-gates.md) | Release 0.4.0: an FFI to C++ and a proof that Pia subsumes C++ interfaces | Proposed |
| [0084](0084-release-0-5-0-gates.md) | Release 0.5.0: a SAT and SMT solver written in Pia, beside Z3 | Proposed |
| [0085](0085-release-1-0-gates.md) | Release 1.0: a Pia front end in Pia over Pia IR | Proposed |
| [0086](0086-spread-collectives.md) | Collectives in a `spread`: `all_reduce` and `halo_exchange`, proved to match by uniform control flow, run as phases on the async runtime | Proposed |
| [0087](0087-simd-vectors-as-a-library-type.md) | SIMD vectors are a library type, `simd t k` in `Pia.Simd`, lowered to MLIR `vector` values | Proposed |
