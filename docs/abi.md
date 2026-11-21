# Shared libraries and published proof certificates

Status: proposed, 2026-11-21. Decision record: [ADR 0024](adr/0024-published-proof-certificates.md). Builds on [ADR 0010](adr/0010-modules-interfaces-and-proof-certificates.md) (modules, interfaces and certificates) and on the trusted-contract rules proposed in `docs/stdlib.md` ([PR #37](https://github.com/deanberris/pia-lang/pull/37)).

A Pia shared library carries, inside the binary, the interfaces it exports, their contracts and a proof certificate. Before a Pia program binds to that library, something checks that the library still provides exactly the interfaces the program was proved against. This page says what the certificate contains, what is hashed and what is re-checked, how a library can evolve without breaking its importers, how the check works on macOS/arm64 first, and what the certificate does and does not let you trust.

## The problem

[ADR 0010](adr/0010-modules-interfaces-and-proof-certificates.md) makes verification assume-guarantee: module `B` is proved while *assuming* the contracts of the interfaces it imports from `A`, and `A` is proved to *guarantee* them. The two halves only compose if the `A` that runs is an `A` that was proved against the same interface `B` assumed.

With static linking, the link checker sees both halves at once and refuses a mismatch. A shared library breaks that: `libA.dylib` can be rebuilt, upgraded or swapped after `B` was linked. If the new `A` weakened a postcondition, `B` is still running on a proof that no longer holds, and nothing tells anyone. Every C and C++ ABI has this problem with types (the symbol still resolves, the struct layout changed). Pia has it with contracts too, which is worse, because a contract change is invisible in the machine code.

The goal: **a proof made against an interface is never used with a library that does not provide that interface**, and the check costs about as much as symbol binding.

## Prior art

| System | What travels with the binary | What the consumer checks | What Pia takes |
| --- | --- | --- | --- |
| Proof-carrying code (Necula and Lee, 1996-97) | Native code plus a proof, in LF, that it meets a safety policy | Regenerates the verification condition from the code and checks the proof with a small LF checker. No trust in the producer | The ideal end state: re-checkable evidence. Too costly for a loader, and needs a proof format Z3 does not stably produce |
| Foundational PCC (Appel, 2001) | Proof down to machine semantics | Same, with a smaller trusted base | Shows that "how much must the consumer trust" is a dial, not a yes/no |
| Typed assembly language (Morrisett et al., 1998) | Type annotations on assembly | Linear-time type checking of the annotations | Certificates that are cheap to *check* even if expensive to *find*. Pia's hash check is the degenerate case |
| JVM bytecode verifier and `StackMapTable` | Type state at branch targets | Linear-time verification at class load | Ship the hard part (the invariants), check the easy part at load |
| WebAssembly | Module with typed imports and exports | Validation is a linear type check; instantiation checks each import against the provider's export type | The import-matches-export check at bind time, on interface identity instead of structural types |
| OCaml `.cmi` CRCs and `Dynlink` | Each compilation unit records a digest of every interface it was compiled against | The linker and `Dynlink` refuse "inconsistent assumptions over interface" | Closest match. Pia does the same with contract-aware hashes, and also at dyld load |
| Rust crate metadata (SVH) | A hash of the crate's public surface in `rlib` metadata | `rustc` refuses a dependency whose hash changed | Hash the exported surface, not the whole crate, so private changes do not force rebuilds |
| Swift library evolution, `.swiftinterface`, ABI checker | A textual interface plus a baseline of the published ABI | The ABI checker diffs the new interface against the baseline at library build time | Compatible evolution through a checked-in baseline, proved instead of diffed |
| ELF symbol versioning (`VERDEF`/`VERNEED`) | Version names on exported symbols, required versions in importers | `ld.so` refuses a missing version before any code runs | Make the system loader enforce the check by turning interface hashes into symbols it must bind |
| Mach-O code signing | Hashes of every page, in `LC_CODE_SIGNATURE`, signed | The kernel checks pages as they are paged in; library validation checks the signer | Integrity of the certificate comes free if it lives in a signed segment |
| glibc `LD_AUDIT` (`la_objopen`), dyld `_dyld_register_func_for_add_image` | Nothing | Callbacks when an image loads | Hooks for richer policy checks. dyld has no pre-bind hook, so Pia cannot depend on one |

Two lessons decide the design:

1. **Every system that works at load time checks identity, not proofs.** OCaml, Rust, Wasm and ELF versioning all compare names or digests. Re-checking proofs is done once, offline, if at all. Pia does the same: the loader compares hashes, and re-verification is an audit tool.
2. **The cheapest reliable enforcement is the one the system loader already does.** dyld refuses to start a program with a missing non-weak symbol. If a mismatched interface means a missing symbol, the check needs no hook, no runtime, and no cooperation from the program.

## Design overview

The check runs in three layers. Each catches everything the layer below it catches, and more.

| Layer | When | Who | What it checks | Cost |
| --- | --- | --- | --- | --- |
| 1. Witness symbols | Launch, `dlopen` | dyld (or `ld.so`) | Each imported interface's hash is provided by the library actually loaded | One symbol bind per imported interface |
| 2. Certificate check | Static link, launch, `Pia.Dl.open` | `piac link`, the Pia runtime | Layer 1, plus folded constants, ABI version, trusted-base policy, compiler identity | Reads a small section per image |
| 3. Audit | Any time, offline | `pia-cert audit` | Layers 1 and 2, plus recomputes every hash from the embedded interfaces, re-proves interface refinements and optionally replays the proofs | Seconds to minutes. Never on the load path |

Layer 1 alone already gives the core guarantee for programs launched normally. Layers 2 and 3 add policy and assurance.

## What is hashed

### The interface hash

Each exported interface gets an **interface hash**: SHA-256 over a canonical serialisation of the interface. "Canonical" means two interfaces that mean the same thing hash the same, whatever their source formatting, and two that differ in anything an importer could rely on hash differently.

The serialisation is built from the type-checked interface, after metaprogram expansion and monomorphisation, never from source text. It contains, in this order:

1. **Domain prefix**: the string `pia-iface`, the **Pia ABI version** (below) and the target triple (`arm64-apple-macos`). A change to calling convention or layout rules changes every hash.
2. **Interface identity**: the fully qualified module and interface name.
3. **Every exported symbol**, sorted by name. For each:
   - its kind: function, type, fixed value, state symbol;
   - its type, with range types (`int{0..255}`), parameter modifiers (ownership, access, modifiability), and the target **layout** of every type that crosses the boundary (size, alignment, field offsets, `dyn` tag encoding);
   - its contract: `requires`, `ensures`, refinements and state invariants, as `pia_contract` terms. Bound variables are numbered (de Bruijn style), names are module-qualified as in [ADR 0022](adr/0022-metaprogram-hygiene.md), and terms are simplified only by a fixed, versioned set of rewrites so the hash does not depend on optimiser changes;
   - trust marks that are part of the interface: an `@assume` that [design.md](design.md#contracts) says "is a visible note in the interface", and whether the symbol is an `extern` with a trusted contract.
4. Concept instances and adapters the interface exports, by concept and type.

What is **not** in the interface hash: function bodies, private symbols, proof details, which solver proved what, source locations and comments. A module can be rewritten, re-optimised or re-proved without changing its interface hash, so its importers neither rebuild nor relink.

### The inline surface hash

An interface may export fixed values and `let inline` or `const` symbols whose *values* importers fold into their own code ([ADR 0010](adr/0010-modules-interfaces-and-proof-certificates.md)). Importers prove against the symbol's type and refinement, which is in the interface hash, but once they fold the value, they also depend on the value itself.

These values get a second hash per interface, the **inline surface hash**, over the canonical IR of every foldable value and inline body. It is separate so that a library can change an inline body and break only the importers that actually folded something, which the importer's certificate records.

### Proof and build identity

Not hashed into anything an importer depends on, but recorded in the certificate for policy and audit: the compiler version and a hash of the `piac` binary, the Z3 version and options, and the hash of the module's optional proof bundle (below).

## The certificate format

Each Pia image (an executable, a `.dylib`, a `.o`) holds one **image certificate**. It is a small binary blob, little-endian, versioned, with no pointers, so it needs no relocations and can live in a read-only, signed section.

```text
header       magic "PIAC", format version, Pia ABI version, target triple
image        flags (has_trusted, allowed_unproved), compiler identity, proof bundle hash
modules[]    one per Pia module linked into the image:
  name         fully qualified module name
  provides[]   interface name, interface hash, inline surface hash,
               and the hashes of every older interface version it also provides (see ABI evolution)
  requires[]   interface name, interface hash it was proved against,
               inline surface hash if any value was folded, else zero
  trusted[]    this module's own trusted items: kind (extern contract, @assume,
               allowed-unproved goal, unsafe call site), symbol, source location,
               hash of the trusted contract or goal
strings      string table for the names above
```

Decisions behind the format:

- **One certificate per image, with one entry per module.** An image can contain several Pia modules. The static link step merges the modules' object-file certificates into one image certificate and checks the requires against the provides it can already see.
- **Trusted items are listed per module, not transitively.** A module's certificate records only its own trusted items. The whole trusted base of a program is computed by walking the certificates of every image it loads: `piac link --trust-report` at link time, and `pia-cert trust-report` on a built program. If a dependency replaces a proved body with an `@assume` behind an unchanged interface, the importer's proof is still valid by assume-guarantee, so its certificate should not go stale, but the report must still show the new trusted item. This answers the open question in `docs/stdlib.md` ([PR #37](https://github.com/deanberris/pia-lang/pull/37)): yes, certificates list trusted contracts, and the linker and the trust report read them.
- **Four kinds of trusted item.** An `extern` declaration's contract and an `@assume`, both allowed only in `@trusted` modules; an obligation accepted with `--allow-unproved`; and each `unsafe f x` call site, the required spelling for a call to a foreign function declared without a contract. The certificate also flags a module as `@trusted`.
- **`--allow-unproved` goals are trusted items.** An obligation accepted with `--allow-unproved` ([verifier.md](verifier.md)) is recorded the same way as an `@assume`, so "this library has unproved goals" is visible to anyone who loads it.
- **Fixed-size hashes in the certificate, short ones in symbols.** The certificate holds full 32-byte SHA-256 hashes. Witness symbols use the first 128 bits, base32-encoded, which keeps symbol names short while leaving accidental collisions out of reach.

### Where it lives on macOS/arm64

| Mach-O location | Contents | Loaded | Signed |
| --- | --- | --- | --- |
| `__TEXT,__pia_cert` | The image certificate | Yes, read-only | Yes, by the code signature's page hashes |
| `__TEXT,__pia_iface` | The canonical serialised interfaces the image provides (the `.piai` contents) | Yes, read-only | Yes |
| `__PIA_PROOF,__bundle` (optional) | Proof bundle: the module's obligations as `pia_contract` MLIR bytecode, plus solver settings | No (stripped by default, or a sidecar `.piap` file) | If present |

Putting the certificate in `__TEXT` means every arm64 macOS image already protects it: all code on Apple Silicon must be signed (ad-hoc at least), and the kernel checks each page against the code directory as it pages it in. Tampering with the certificate of a signed library makes the page fail validation. No Pia-specific signature is needed for integrity.

Embedding the interfaces in `__pia_iface` means `piac` can import directly from a `.dylib`, with no separate `.piai` file to ship or keep in sync. The interface hash is recomputed from these bytes by the audit tool, so the embedded interface and the certificate cannot silently disagree.

## Layer 1: witness symbols

For every interface `I` a library provides, it exports one data symbol, a **witness**:

```text
_pia$w$<module>$<interface>$<hash128>          interface hash
_pia$i$<module>$<interface>$<hash128>          inline surface hash (only if the interface has one)
```

Every image that imports `I` emits a non-weak reference to the witness for the hash it was proved against, and to the inline surface witness if it folded anything. The witnesses are one byte each and nothing reads them. They exist only so that the system loader must bind them.

- On macOS, binding is two-level: the reference names both the symbol and the library's install name. With chained fixups (macOS 12 and later), all non-lazy binds are resolved at launch, before any initializer runs. A library that does not provide the hash makes dyld stop the program with `Symbol not found: _pia$w$...`. No Pia code, in the program or the library, has run.
- On `dlopen`, the same bind happens at open time, and `dlopen` fails.
- A library that provides several versions of an interface (see below) exports one witness per version, so old importers keep binding.
- Exported function symbols keep plain, stable names (module-qualified, without the hash). Debuggers, profilers, crash reports and C callers see readable names, and the hash lives only in the witnesses.

The cost of Layer 1 is one extra bind per imported interface, which is a rounding error next to the binds for the functions themselves. The error message is cryptic, so the Pia runtime and `pia-cert` turn `_pia$w$...` into a readable explanation: which interface, which hash the program wanted, which hashes the library provides.

The same scheme ports to ELF with one symbol per witness, or with the hash as a GNU symbol version (`PIA_<hash128>`) on the interface's symbols, so `ld.so` reports `version 'PIA_...' not found`.

## Layer 2: the certificate check

Witnesses prove that the right interfaces are present. The certificate check adds what a symbol bind cannot express:

- the image's Pia ABI version and target match the program's;
- the trust policy holds: for example "no library with allowed-unproved goals", or "the only trusted items allowed are `extern` contracts in `@trusted` modules of `Pia.*`";
- the compiler identity is in an allowed set, when a deployment asks for that;
- every requires entry in every loaded image is met by a provides entry in the image the loader actually bound to (a belt-and-braces repeat of Layer 1 that also produces good errors).

It runs at three points:

1. **Static link** (`piac link`, and the `pia_library`/`pia_binary` Bazel rules from M8). Reads the certificates of the objects being linked and of every `.dylib` on the link line, and refuses mismatches. This is the check [ADR 0010](adr/0010-modules-interfaces-and-proof-certificates.md) already requires, extended to shared libraries.
2. **Launch.** The Pia runtime library runs a check before `main`. It walks the loaded images with `_dyld_image_count`/`_dyld_get_image_header`, reads each `__pia_cert` with `getsectiondata`, and checks every Pia image. It registers `_dyld_register_func_for_add_image` so later loads are checked as well.
3. **`Pia.Dl.open`**, the Pia library's `dlopen` wrapper, used for plugins. It opens with `RTLD_NOW | RTLD_LOCAL`, checks the new image's certificate against the interfaces the caller names, and only then hands back symbols. On a failed check it closes the image and returns an error, with the reason.

**Pia images have no static initializers.** `piac` never emits `__mod_init_func` entries for Pia code: module-level values are constants resolved at compile time, and anything else must be explicit in `main`. This is what makes checking after `dlopen` sound: opening a Pia library runs none of its code, so the check happens before anything the certificate guards can execute. The certificate check rejects a Pia image that contains initializers. Non-Pia libraries (libSystem, C dependencies) can still have initializers. They are outside the proof anyway, and enter the trusted base through `extern` contracts.

dyld has no hook that runs before binding, and with the hardened runtime `DYLD_INSERT_LIBRARIES` is disabled, so Pia does not rely on either. Layer 1 covers the window before the runtime's check runs.

## Layer 3: audit and re-checking

The loader never runs a solver. Proof search can take minutes ([verifier.md](verifier.md)), and a loader that runs Z3 would make startup time depend on solver heuristics. But hashes alone only say "some compiler said so". `pia-cert audit` closes as much of that gap as is practical, offline:

1. **Recompute** every interface hash and inline surface hash from `__pia_iface` and compare with `__pia_cert`. Catches a buggy or tampered certificate in an unsigned image.
2. **Re-prove refinements.** For every older interface version a library claims to provide, check the refinement obligations (below) with Z3 from the embedded interfaces alone. This needs no source.
3. **Replay proofs** when a proof bundle is present: reload the module's obligations from the bundle and run the verifier on them, then check that the bundle's hash matches the certificate. This re-checks that the obligations are valid. It does not check that the obligations were generated faithfully from the machine code. That would need translation validation or a proof-producing code generator, which is out of scope.
4. **Report** the full trusted base, transitively.

A future step toward real proof-carrying code is to store checkable proof objects instead of obligations, for example Alethe proofs from cvc5 checked by an independent checker such as Carcara, so a consumer can re-check without trusting the solver. Z3's proof output is not stable enough to ship today. The format reserves a section kind for proof objects so this can be added without a format change.

## ABI evolution

Exact hash matching would mean every change to a library breaks every importer. Pia allows compatible changes, proved compatible at library build time.

A library keeps **ABI baselines**: the canonical interfaces of every version it has published, checked into the repository (for example `abi/Pixels.PixelOps.v1.piai`). The library declares which baselines it still provides. When it builds, `piac` proves the current interface **refines** each declared baseline:

| Element | Compatible change (refinement) |
| --- | --- |
| Symbol set | New symbols may be added. No baseline symbol may be removed |
| Types and layout | Identical for every baseline symbol. Layout changes always break |
| `requires` | May get weaker: prove `requires_old ⇒ requires_new` |
| `ensures` | May get stronger: prove `requires_old ∧ ensures_new ⇒ ensures_old` |
| Refinement on a result or fixed value | May get stronger, same rule as `ensures` |
| State symbol invariants | May get stronger: prove `invariant_new ⇒ invariant_old` |
| Foldable values and inline bodies | Must be identical. A changed value changes the inline surface hash, which breaks importers that folded it (by design, per ADR 0010) |

These are behavioural subtyping rules: anything a caller proved against the old interface still holds against the new one. Each one is an ordinary verifier obligation, so they get counterexamples like any other goal. When every refinement is proved, the certificate's provides entry lists the baselines' hashes, and the library exports a witness for each. Old importers bind to their witness and keep working without recompiling. New importers prove against the current interface.

To make a breaking change, the library drops the baseline from its declared set and bumps its install name's major version (`libpixels.2.dylib`), the usual dylib practice. Dropping a baseline is visible in review because the baseline file is deleted.

**The Pia ABI version** is a single integer in the compiler covering calling convention, layout rules, `dyn` tag encoding, the certificate format and the canonical hash serialisation. Bumping it changes every hash, so it is bumped rarely and on purpose, and the release notes say so.

## Trust model

What a valid certificate tells you depends on what you trust. The design is explicit about each part.

| You trust | You get |
| --- | --- |
| Nothing | The witness and certificate check still stop *accidental* mismatches: stale libraries, wrong versions, partial upgrades. This is the main failure the design targets |
| The code signature (Apple's chain, a Team ID) | The certificate and interfaces are exactly what that signer shipped. With the hardened runtime's library validation, only libraries signed by the same team (or Apple) can load at all |
| The signer's compiler | The library's exported contracts were proved, except for the trusted items it lists |
| The signer's compiler, plus the trusted items in the report | The program as a whole meets its top-level contracts, by assume-guarantee over every image |
| Only `pia-cert audit` and your own Z3 | Interface hashes, refinements and (with a bundle) the obligations re-checked independently. The compiler that generated obligations and machine code is still trusted |

What the certificate does **not** protect against: a malicious producer who signs a library whose code does not match its certificate. Hashes cannot catch that, only a re-check of the machine code can. Pia's position is the same as OCaml's and Rust's: certificates make honest-but-buggy builds safe to combine, and code signing decides whose builds you accept. Reproducible builds let anyone rebuild a library from source and compare it with the shipped one, which is the practical way to stop trusting a specific signer.

## Platforms

- **macOS/arm64 first.** Everything above. Tested on the iMac and on the `macos-15` CI runners.
- **Linux/ELF next.** Certificate in a `.pia.cert` section inside a `PT_NOTE` segment (or an `SHT_NOTE` note with owner `Pia`), witnesses as symbols or GNU symbol versions, the launch check through the runtime with `dl_iterate_phdr`, and an optional `LD_AUDIT` module that checks each object in `la_objopen` before its symbols are bound. ELF images are not signed by default, so Layer 3's recompute step matters more there.
- **Static archives and objects** carry per-module certificates. Only images (executables and shared libraries) carry merged image certificates and witnesses.

## Relation to the minimal core and stdlib

The standard library (`docs/stdlib.md` and ADR 0023, [PR #37](https://github.com/deanberris/pia-lang/pull/37)) is the first big user. `Pia.Core`, `Pia.Mem` and `Pia.Io` can ship as one shared `libpia.dylib`, versioned by ABI baselines like any other library. Its `extern` POSIX contracts and `@assume`s appear as trusted items under `@trusted` modules, so `pia-cert trust-report` of any Pia program lists exactly which libSystem contracts it rests on.

## Implementation plan

Each step is a GitHub issue, tracked from M8 ([#9](https://github.com/deanberris/pia-lang/issues/9)) and the follow-up milestones.

1. Canonical interface serialisation and the interface and inline surface hashes.
2. The certificate format: a small C++ reader and writer, and `pia-cert dump`.
3. Emit `__pia_cert` and `__pia_iface` in objects and merge them into image certificates at link.
4. Witness symbols: export them from libraries and reference them from importers.
5. The link checker for objects and `.dylib` inputs, including `--trust-report`.
6. Pia images without static initializers, the runtime's launch check, and `Pia.Dl.open`.
7. ABI baselines and refinement proofs.
8. `pia-cert audit`: recompute, re-prove refinements, replay proof bundles.
9. The ELF port.

## References

- G. Necula, P. Lee. *Safe Kernel Extensions Without Run-Time Checking*, OSDI 1996, and G. Necula, *Proof-Carrying Code*, POPL 1997.
- A. Appel. *Foundational Proof-Carrying Code*, LICS 2001.
- G. Morrisett, D. Walker, K. Crary, N. Glew. *From System F to Typed Assembly Language*, POPL 1998.
- WebAssembly Core Specification, sections on validation and module instantiation.
- OCaml manual, the `Dynlink` library and "inconsistent assumptions over interface".
- Swift library evolution and the Swift ABI checker (`swift-api-digester`).
- Apple, *Code Signing Guide* and `TN3125: Inside Code Signing`; `dyld` and `mach-o/getsect.h`.
- Ulrich Drepper, *How To Write Shared Libraries* (ELF symbol versioning); glibc `rtld-audit(7)`.
- H. Barbosa et al., *Flexible Proof Production in an Industrial-Strength SMT Solver* (cvc5, Alethe), IJCAR 2022.
