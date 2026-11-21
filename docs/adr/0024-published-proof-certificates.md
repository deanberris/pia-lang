# 24. Shared libraries publish interfaces and proof certificates; loaders check them

Date: 2026-11-21

Status: Proposed

## Context

[ADR 0010](0010-modules-interfaces-and-proof-certificates.md) makes verification assume-guarantee across modules and has the static linker refuse a module whose certificate names an interface hash that does not match. Shared libraries can be rebuilt, upgraded or replaced after an importer was linked, so a static check is not enough: a program could run against a library that no longer guarantees what the program assumed, and since contracts leave no trace in machine code, nothing would notice.

Prior art splits in two. Proof-carrying code (Necula) and foundational PCC ship proofs that the consumer re-checks, which removes trust in the producer but is too slow for a loader and needs a stable proof format. Practical systems (OCaml interface CRCs and `Dynlink`, Rust's crate hash, WebAssembly import checks, ELF symbol versions) compare identities at link or load time and leave re-checking to offline tools. dyld has no pre-bind hook, but it does refuse to launch a program with a missing non-weak symbol, and all macOS arm64 code is signed page by page.

The full design, prior art and trade-offs are in [docs/abi.md](../abi.md).

## Decision

- **Interface hash.** Each exported interface is hashed (SHA-256) over a canonical serialisation of its type-checked form: a domain prefix with the Pia ABI version and target, then every exported symbol with its type, parameter modifiers, contract (normalised `pia_contract` terms with numbered binders), and trust marks. Bodies, private symbols and proof details are not hashed. Memory layout is not in the interface hash either: it is published and checked separately ([ADR 0030](0030-published-object-layouts.md)), so a layout change forces a relink but not a re-proof. Foldable values and inline bodies get a separate **inline surface hash**.
- **Certificate in the image.** Each image carries one certificate in `__TEXT,__pia_cert` (macOS) listing, per module, the interfaces it provides (with every older version it is proved to refine), the interfaces it requires with the hashes it was proved against, and its own trusted items: `extern` contracts, `@assume`, `--allow-unproved` goals and `unsafe` call sites. The canonical interfaces are embedded in `__TEXT,__pia_iface`, so `piac` can import from a `.dylib`. Code signing protects both.
- **Three layers of checking.**
  1. **Witness symbols**: a library exports `_pia$w$<module>$<interface>$<hash>` per provided interface version, and importers reference the one they were proved against, so dyld itself refuses a mismatch before any code runs.
  2. **Certificate check** at static link (`piac link`, Bazel rules), at launch (Pia runtime, before `main`) and in `Pia.Dl.open`: ABI version, inline surfaces, trust policy, compiler identity. Pia images never contain static initializers, so checking after `dlopen` is sound.
  3. **Offline audit** (`pia-cert audit`): recompute hashes, re-prove refinements and optionally replay a proof bundle. The loader never runs a solver.
- **ABI evolution by proved refinement.** A library keeps baselines of the interfaces it has published. At build time `piac` proves the current interface refines each baseline: same types and layout, no removed symbols, weaker `requires`, stronger `ensures` and invariants, identical foldable values. Proved baselines are listed in the certificate and get witnesses, so old importers keep working. Breaking changes drop a baseline and bump the dylib major version.
- **Trust model.** Certificates make honest-but-buggy builds safe to combine. Integrity and provenance come from code signing. Correctness of the library rests on the producer's compiler plus the trusted items its certificate lists. The transitive trusted base is computed by walking certificates (`--trust-report`), not copied into each one.
- **macOS/arm64 first**, then ELF (`.pia.cert` note, witnesses or GNU symbol versions, optional `LD_AUDIT` module).

## Consequences

- A stale or swapped library fails at launch or `dlopen` with no runtime cost beyond one bind per imported interface.
- Library authors can ship compatible updates without recompiling importers, and every compatible change is a proof, not a diff.
- Any Pia binary can report the exact set of trusted contracts it depends on, including libSystem `extern`s from the standard library.
- Pia code cannot rely on static initializers. Module-level state must be constant or set up from `main`.
- The canonical serialisation and the Pia ABI version become compatibility promises: changing either changes every hash.
- A malicious, signed producer can still ship code that does not match its certificate. Closing that needs re-checkable proof objects (for example cvc5 Alethe proofs) and translation validation, left for later; the format reserves room for them.
