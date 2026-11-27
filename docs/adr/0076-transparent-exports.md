# 76. Transparent exports: an importer proves against an exported function's body, as a caller in its own module does

Date: 2026-11-27

Status: Proposed

## Context

Indigo (actuals.com) put a claim to Dean (2026-11-27). Building modules separately against exported contracts may cost callers two things: proofs that let the optimiser remove branches, and proofs of the callers' own contracts. Some of those losses could even be soundness problems. Dean asked for the property to be proved in Lean against the current implementation, and for the compiler to be changed if it falls short. The change he named was grafting in shipped Pia bodies, the standard library's first, so that "all the contracts and branches are visible to the prover".

The claim mixes two properties, and they come out differently:

- **Soundness.** Nothing proved against a contract is false for an implementation that meets it.
- **Precision.** What a caller cannot prove because the contract says less than the body does.

### What the call rule is today

`stepCall` in `src/verify/Verifier.cpp` (docs/verifier.md, "Calls") takes a call on its callee's contract. The precondition is a goal at the arguments, the result is fresh, and the postcondition is assumed about it. There are three exceptions:

- **Pure functions of scalars in the same module** (`definesValue`, "Pure functions of scalars"). One with no loop, buffer, `abort` or recursion is unfolded at every call: `pre(a) ==> F a = body(a)`.
- **Spec functions, generics and metaprograms.** These are exported with their definitions (`inlinedSig` in `src/syntax/Interfaces.cpp`), and importers unfold the spec functions.
- **Imported ordinary functions.** These are only their contracts: "An imported function of scalars is, to the verifier, an uninterpreted function that meets its interface contract".

So a module boundary changes what proves. A call that the body settles in its own module fails across the boundary. This happens on today's `latest` piac:

```ocaml
module Clamp : C
interface C = sig
  let clamp_to : (x : u8) -> (hi : u8) -> u8
    ensures result <= hi
end
let clamp_to (x : u8) (hi : u8) : u8
  ensures result <= hi
= if x > hi then hi else x
let three_here (k : u8) : u8 ensures result = 3 = clamp_to 3 10    (* proved *)
```

```ocaml
module Use : U
import Clamp.C
let three (k : u8) : u8 ensures result = 3 = Clamp.clamp_to 3 10   (* failed, k = 0 *)
let dead (x : u8) : u8 ensures result = x
= if Clamp.clamp_to x 255 <> x then 0 else x                       (* failed, x = 127 *)
```

`dead` is the optimisation half of the claim. Its `then` branch is dead, but nothing outside `Clamp` can know that. Codegen sees the same boundary. Contracts are erased (docs/codegen.md, step 1), and an imported function is a declaration in the importer's object, so LLVM cannot inline it or fold the branch either. Within a module, private functions have internal linkage and LLVM inlines them.

### What Lean proves about the rule

`tests/lean/CallRule.lean` (checked by `//tests/lean:call_rule_test`) models the rule over a small language: each function has one integer parameter and result, bodies are trees of calls, and an erased call stands for a lemma call or a call in a contract. It proves, with Lean's own axioms only:

| Theorem | Says |
| --- | --- |
| `partial_sound` | For code that runs, the rule is sound with no termination argument at all: every run that returns meets its contract, mutual recursion included |
| `ghost_unsound` | For calls that never run, it is **not** sound without termination: two lemmas that call each other prove `False`, and a caller that returns 3 is proved to return 7 |
| `verifier_sound`, `verifier_partial`, `lex_descends` | With the goals the verifier now raises, it is sound, erased calls included. Calls between the call graph's cycles go down the DAG, and calls within a cycle make a measure go down |
| `modular` | A caller's proof holds for every implementation of its callees that is verified against their contracts, which is what separate compilation and the certificate check rely on |
| `refine_preserves` | A weaker precondition and a stronger postcondition (ADR 0024's evolution rule) keep every caller's proof |
| `precision_gap` | Some property of the real program cannot be proved from a contract weaker than its body |
| `strongest_complete` | Using each callee's exact behaviour as its contract (inlining it) proves everything that holds |
| `strongest_not_modular` | A proof made by inlining does not survive a change to the callee's body that keeps its contract |

`ghost_unsound` was a real bug in the verifier, not just a property of the model. Termination was checked for direct recursion only, so this program proved and compiled, and returned 3:

```ocaml
let lemma a (x : int) : unit ensures false = b x
let lemma b (x : int) : unit ensures false = a x
let seven (x : u8) : u8 ensures result = 7 = a 0; 3
```

PR #496 fixes it: each call within a cycle of the call graph is now a termination goal (tests/verify/mutual_recursion.pia). That is the `Descends` relation the Lean proof assumes, so the theorems describe the verifier as it now is.

So the answer to the claim:

1. **Soundness.** With PR #496, modular verification is sound. Proving against contracts loses no soundness, and `modular` says why separate builds are safe. The unsoundness was in termination, not in modularity.
2. **Precision.** Precision really is lost, but only at module boundaries, and only for functions whose bodies the verifier would otherwise unfold. Inlining wins it back (`strongest_complete`), and the price is that the body becomes part of what callers depend on (`strongest_not_modular`).

## Decision

### 1. An exported function the verifier can unfold is exported with its body

An exported ordinary function that `definesValue` accepts is **transparent**: a pure function of scalars, or a spec-only projection such as `held`. Its definition goes into the interface's inline surface, as a spec function's or a generic's already does. An importer encodes a call to it exactly as a caller in its own module does: `pre(a) ==> F a = body(a)`, with the callee's own goals proved once, in its module, as for imported spec functions (ADR 0039). That makes a module boundary proof-neutral for these functions: `three` and `dead` above prove.

This needs no new keyword. The rule for what unfolds is the one the verifier already applies within a module, so moving a function into another module never changes what proves.

Functions with loops, buffers, `abort`, recursion, atomics or foreign calls stay contract-only. For them, the body's strongest fact is its loop invariants and its `ensures`, which the contract already is.

### 2. `@opaque` on an ordinary function keeps it contract-only

`@opaque` already means "the definition is not a fact here" for spec functions (ADR 0063). On an exported ordinary function it keeps the body out of the interface and out of importers' goals, and `with f` reveals it in a proof inside the module. A library whose body must change without rebuilding its importers marks the function `@opaque`.

### 3. A transparent body is part of the interface hash

The interface hash is the SHA-256 of the `.piai` text (`interfaceHash` in `src/cert/Certificate.cpp`), which already holds the inline surface. So a changed transparent body is a changed interface. Importers re-verify and relink, and the witness symbols make the linker and dyld refuse a mismatch. That is `strongest_not_modular` turned into a rule: a proof made with a body depends on that body. docs/abi.md already describes a separate *inline surface hash*, so that a change to a body breaks only the importers that used it. Building that split is a later step (step 5), and nothing here depends on it.

### 4. Codegen gets the body too (Dean, 2026-11-27)

An importer compiles each transparent function it calls as an LLVM `available_externally` definition. LLVM may inline it and fold the branches it decides, and the symbol still comes from the defining module's object, so no code is duplicated in the link. This is the optimisation half of the claim, and it is sound for the same reason the proof is: the hash ties the importer to the body it inlined.

### 5. An LTO mode links modules into one optimisation unit (Dean, 2026-11-27)

Transparent bodies reach importers only for loop-free functions of scalars. A link-time mode covers everything else: `piac --lto` emits LLVM bitcode rather than machine code, and `pia_binary(lto = True)` links a program's Pia objects, and C objects compiled with `-flto`, through LLVM's LTO (ThinLTO by default, full LTO as an option). LLVM can then inline across modules, fold branches and run its peephole passes over the whole program, loops and buffers included. This is #490 in the codegen benchmark plan (#485), "LTO across Pia objects and their C callers", so the two land as one change.

LTO changes no proof. Each module is still proved against its imports' contracts and its certificate still names the interface hashes it used, so `modular` covers whatever LLVM links. LLVM only uses what the IR says, and since contracts are erased first, it cannot assume anything a proof did not establish. What LTO gives up is the separate shipping of objects: a module whose code was inlined into another under LTO is part of that binary, so a shared library is never built this way, and the witness symbols are still emitted so the certificate check runs at link time as it does now.

### 6. Steps

1. Export transparent definitions in `.piai` and unfold them at importers. Prove `tests/modules/transparent.pia` (the `Clamp` example), and record the change in the Linux proof-cost shards.
2. `@opaque` on ordinary functions, `with f` across them, and the docs (verifier.md "Calls", tour, features).
3. `available_externally` bodies in codegen, with a test that `dead`'s branch is gone from the importer's assembly.
4. A lint, `opaque_export`, for an exported function that is not transparent and whose `ensures` does not determine its result, pointing at the precision it gives up.
5. The inline surface hash split from the interface hash (docs/abi.md), recorded per importer in its certificate.
6. `piac --lto` (bitcode objects) and `pia_binary(lto = True)` through LLVM ThinLTO, with C objects built `-flto`, measured on the codegen benchmark (#485, #490).

## Consequences

- **Soundness is unchanged.** An importer assumes about the body only what the body's module proved: its precondition-guarded definition, which `strongest_complete` shows is exact. The certificate check keeps the body the importer used equal to the one it links, since the body is hashed.
- **Proof cost.** A goal that mentions a call to a transparent function carries its body, and the bodies of the transparent functions it calls, the same cost in-module callers already pay. These are loop-free bodies of scalars, so the terms are small, but transitive unfolding can add up: `Pia.Core.Ascii`'s classifiers call `between`, so `is_alnum` unfolds three `between`s. The Linux proof bench gates every PR, so step 1 reports the change per file, and `@opaque` is there for any function that turns out costly.
- **Rebuild invalidation.** Changing a transparent body re-verifies its importers. The proof cache keys each goal on its query, so only the goals whose query contained the body are solved again, and the rest are cache hits. Changing an `@opaque` body, or any function with a loop, still re-verifies nothing outside its module.
- **ABI (ADR 0030, 0073).** A transparent body is inline surface, like a C++ inline function or a generic: a shared library that changes one breaks its importers' certificates until they rebuild, and `pia-cert check` says which interface changed. Layout hashes are unaffected. ADR 0073's migration rules apply to changed interfaces as they do now.
- **What stays modular.** Loops, recursion, buffers and anything `@opaque` are still proved once against their contracts, and `modular` still covers those calls, so separate builds and the proof cache keep working where they matter most.
- **Not covered here.** Calls through function references (ADR 0071) are calls the verifier cannot see the callee of. They stay contract-only, and they need their own termination rule before a lemma can be called through one.
