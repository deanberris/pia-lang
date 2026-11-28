# 83. Release 0.4.0: an FFI to C++ and a proof that Pia subsumes C++ interfaces, and its gates

Date: 2026-11-28

Status: Proposed

## Context

The [roadmap](../roadmap.md) (Dean, 2026-11-27, agreed 2026-11-28; 0.4.0 and 0.5.0 swapped the same day) makes 0.4.0 the release where Pia binds to any C++ interface, and shows that Pia's features are a superset of what a C++ interface can express. It comes before the solver so that a self-hosted front end can call MLIR, LLVM and Z3 early.

Dean's decisions that shape it (2026-11-27):

- **"Superset" is shown both ways**: formally, a translation from a core model of C++ interfaces to Pia with a soundness theorem in Lean; and in practice, a test suite that binds real headers and checks every declaration maps.
- **Start with what MLIR's and LLVM's public headers use**, since the self-hosted compiler binds those first; then the C++ standard library and popular libraries.
- **Templates are an exercise in equivalence.** A template becomes a Pia metaprogram that generates the Pia code evaluating it at each use. Each instantiation must give the same layout, overload choice and mangled symbol as Clang's. Prove as much as possible: a Lean model of instantiation for a defined fragment with a correspondence theorem, and outside it, a check per instantiation.
- **Exceptions are boxed errors**: an error set stays closed, and one constructor carries a box of a concept, such as `Cxx of box exception`. A generated shim catches at each bound call and rethrows a Pia error crossing back into C++. This needs boxes of a concept, which land before 0.1.0.

## Decision

The release policy of [ADR 0080](0080-release-0-1-0-gates.md) applies.

### Libraries, which gate the 0.4.0 tag

1. **A C++ binding generator**, the successor of [ADR 0051](0051-variadic-generics-and-foreign-varargs.md)'s C header generator: reads headers through Clang and writes Pia declarations for classes, overloads, namespaces, enums, constants and templates.
2. **The feature map from C++ to Pia**: constructors and destructors, copy and move, references and value categories, `const` and `mutable`, virtual dispatch, overloading, default arguments, exceptions at the boundary, templates and concepts. Each has its Pia construct, and a construct with none gets one through its own ADR.
3. **Ownership across the boundary**: RAII objects as `@linear` values with `drop`, `unique_ptr` as `box`, and `shared_ptr` and raw pointers as trusted items until their contracts are written.
4. **Exceptions as boxed errors**, with the generated catch and rethrow shims, and handlers that match on the concept's operations or downcast to a known type.
5. **Templates as metaprograms**, with the equivalence check against Clang (layout, overload, mangled symbol) for every instantiation a binding uses.
6. **Contracts on bound APIs**: an overlay of contracts over generated declarations, as for POSIX ([ADR 0057](0057-posix-module-per-target-behind-one-interface.md)).
7. **The C++23 standard library in Pia** ([ADR 0040](0040-cpp23-standard-library-in-pia.md)), far enough that Pia and bound C++ code share strings, vectors and maps.

### The proofs, which also gate the tag

- **The Lean model of C++ interfaces** for the features MLIR's and LLVM's public headers use, with the soundness theorem for its translation to Pia.
- **The Lean model of template instantiation** for a defined fragment, with the correspondence theorem against the metaprogram's expansion.
- **The header test suite** over MLIR's and LLVM's public headers: every declaration maps, or the suite names the construct that does not, and the release notes list them.

### The demo, which closes the 0.4.x series

Pia code that, through MLIR's and LLVM's C++ APIs, builds a module, runs a pass pipeline and emits an object file that links and runs, with contracts on every call it makes and the trust report listing only the bound calls without proved contracts. The header suite then grows to the C++ standard library and a published list of popular libraries.

## Consequences

- The binding generator links Clang's libraries, which grows the build; the release measures by how much.
- Templates outside the proved fragment are checked, not proved, and the trust report says which ones.
- 0.5.0 and 1.0 depend on this release to reach Z3, MLIR and LLVM from Pia.
