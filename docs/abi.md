# Shared libraries and published proof certificates

Status: certificates accepted, 2026-11-21; object layout proposed. Decision records: [ADR 0024](adr/0024-published-proof-certificates.md) (certificates, accepted) and [ADR 0030](adr/0030-published-object-layouts.md) (object layout). Builds on [ADR 0010](adr/0010-modules-interfaces-and-proof-certificates.md) (modules, interfaces and certificates) and on the trusted-contract rules proposed in [docs/stdlib.md](stdlib.md).

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
| 1. Witness symbols | Launch, `dlopen` | dyld (or `ld.so`) | Each imported interface's hash, and each imported type's shape or layout hash, is provided by the library actually loaded | One symbol bind per imported interface and type |
| 2. Certificate check | Static link, launch, `Pia.Dl.open` | `piac link`, the Pia runtime | Layer 1, plus folded constants, ABI version, trusted-base policy, compiler identity | Reads a small section per image |
| 3. Audit | Any time, offline | `pia-cert audit` | Layers 1 and 2, plus recomputes every hash from the embedded interfaces, re-proves interface refinements and optionally replays the proofs | Seconds to minutes. Never on the load path |

Layer 1 alone already gives the core guarantee for programs launched normally. Layers 2 and 3 add policy and assurance.

## What is hashed

### The interface hash

Each exported interface gets an **interface hash**: SHA-256 over a canonical serialisation of the interface. "Canonical" means two interfaces that mean the same thing hash the same, whatever their source formatting, and two that differ in anything an importer could rely on hash differently.

The serialisation is built from the type-checked interface, after metaprogram expansion and monomorphisation, never from source text. It contains, in this order:

1. **Domain prefix**: the string `pia-iface`, the **Pia ABI version** (below) and the target triple (`arm64-apple-macos`). A change to the calling convention changes every hash.
2. **Interface identity**: the fully qualified module and interface name.
3. **Every exported symbol**, sorted by name. For each:
   - its kind: function, type, fixed value, state symbol;
   - its type, with range types (`int{0..255}`) and parameter modifiers (ownership, access, modifiability). Memory layout is **not** part of the interface hash: it has its own shape and layout hashes, so a layout change forces a relink but never a re-proof (see [Object layout](#object-layout));
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
  layouts[]    shape and layout hash of every type the module defines and exports
               (descriptors themselves are in __pia_layout)
  uses[]       type name, and the shape or layout hash this module's code was
               compiled against, with a flag if a proof depended on it
  trusted[]    this module's own trusted items: kind (extern contract, @assume,
               allowed-unproved goal, unsafe call site, lowering), symbol,
               source location, hash of the trusted contract, goal or MLIR
strings      string table for the names above
```

What is built so far is a text body (src/cert/Certificate.h): format 1 has the module and its provides and requires, format 2 its trusted lowerings, and format 3 ([ADR 0073](adr/0073-prover-identity-abi-version-and-advisories.md)) the Pia ABI version and target triple (`abi 1 arm64-apple-macos`), piac's version (`prover piac 0.0.0+512.9f3c2e1a7b04`, `dev` in a build that is not stamped) and the solver's (`solver z3 5.4.1`). `piac --version` prints the same three. The link check refuses objects for different ABI versions or targets, and objects in formats 1 and 2, which record none.

Decisions behind the format:

- **One certificate per image, with one entry per module.** An image can contain several Pia modules. The static link step merges the modules' object-file certificates into one image certificate and checks the requires against the provides it can already see.
- **Trusted items are listed per module, not transitively.** A module's certificate records only its own trusted items. The whole trusted base of a program is computed by walking the certificates of every image it loads: `piac link --trust-report` at link time, and `pia-cert trust-report` on a built program. If a dependency replaces a proved body with an `@assume` behind an unchanged interface, the importer's proof is still valid by assume-guarantee, so its certificate should not go stale, but the report must still show the new trusted item. This answers the open question in [docs/stdlib.md](stdlib.md): yes, certificates list trusted contracts, and the linker and the trust report read them.
- **Five kinds of trusted item.** An `extern` declaration's contract and an `@assume`, both allowed only in `@trusted` modules; an obligation accepted with `--allow-unproved`; each `unsafe f x` call site, the required spelling for a call to a foreign function declared without a contract; and a `lowering`, a function whose `@lower` MLIR replaced its proved body, recorded with the function, the ops its MLIR uses and the SHA-256 of the spliced text ([ADR 0065](adr/0065-lowerings-written-in-pia.md); a `schedule` joins it with `@schedule`). The certificate also flags a module as `@trusted`.
- **`--allow-unproved` goals are trusted items.** An obligation accepted with `--allow-unproved` ([verifier.md](verifier.md)) is recorded the same way as an `@assume`, so "this library has unproved goals" is visible to anyone who loads it.
- **Fixed-size hashes in the certificate, short ones in symbols.** The certificate holds full 32-byte SHA-256 hashes. Witness symbols use the first 128 bits, base32-encoded, which keeps symbol names short while leaving accidental collisions out of reach.

### Where it lives on macOS/arm64

| Mach-O location | Contents | Loaded | Signed |
| --- | --- | --- | --- |
| `__TEXT,__pia_cert` | The image certificate | Yes, read-only | Yes, by the code signature's page hashes |
| `__TEXT,__pia_layout` | Layout descriptors of every exported type (the `.pial` contents) | Yes, read-only | Yes |
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

Module initialisation still exists, but not through dyld. `@init` functions and registries are run by the Pia runtime after this check, in a proved order, and dynamic loading with `Pia.Dl.open` is provided by the opt-in `Pia.Dyn` environment, which calls each image's generated registration function ([init.md](init.md), [ADR 0033](adr/0033-module-initialisation-and-registries.md)).

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
| Types | Identical for every baseline symbol. Layout is versioned separately: an `auto` layout change relinks importers, and a `frozen` layout cannot change (see [Object layout](#object-layout)) |
| `requires` | May get weaker: prove `requires_old ⇒ requires_new` |
| `ensures` | May get stronger: prove `requires_old ∧ ensures_new ⇒ ensures_old` |
| Refinement on a result or fixed value | May get stronger, same rule as `ensures` |
| State symbol invariants | May get stronger: prove `invariant_new ⇒ invariant_old` |
| Foldable values and inline bodies | Must be identical. A changed value changes the inline surface hash, which breaks importers that folded it (by design, per ADR 0010) |

These are behavioural subtyping rules: anything a caller proved against the old interface still holds against the new one. Each one is an ordinary verifier obligation, so they get counterexamples like any other goal. When every refinement is proved, the certificate's provides entry lists the baselines' hashes, and the library exports a witness for each. Old importers bind to their witness and keep working without recompiling. New importers prove against the current interface.

To make a breaking change, the library drops the baseline from its declared set and bumps its install name's major version (`libpixels.2.dylib`), the usual dylib practice. Dropping a baseline is visible in review because the baseline file is deleted.

**The Pia ABI version** is a single integer in the compiler covering the calling convention, the certificate format and the canonical hash serialisation. The layout algorithm has its own version inside each layout descriptor, so improving layouts changes layout hashes (relink) without changing interface hashes (no re-proof). Bumping the ABI version changes every hash, so it is bumped rarely and on purpose, and the release notes say so.

## Object layout

The compiler is free to choose how every Pia type is laid out in memory: field order, packing, alignment, where sum-type tags go, and tag bits stashed in the low bits of pointers. The module that defines a type picks its layout and **publishes it**. Every importer that compiled code against that layout records a **layout hash**, and a library whose layout no longer matches cannot be loaded: dyld fails, and the importer must be relinked. Static links and rebuilds therefore always agree on how data is laid out and packed.

This is a deliberate choice against the alternatives:

| Approach | Example | Why not for Pia |
| --- | --- | --- |
| Fixed, C-like layout rules | C, C++ (the fragile base class problem) | Forbids reordering, packing and niches, which is most of the optimisation |
| Layout resolved at load time | Objective-C 2.0 non-fragile ivars (offsets are symbols that dyld binds), Swift resilience (size and offsets read from value witness tables at run time) | Offsets become run-time values: no constant folding, worse vectorisation, and proofs about sizes lose their constants |
| Unspecified layout, no dynamic ABI | Rust `repr(Rust)` | Gives the optimisation freedom, but no shared libraries across builds |
| **Published layout, fail and relink** | Pia | Full optimisation freedom, constant offsets, and a mismatch is caught at load instead of corrupting memory |

### Layout never changes a proof

Proofs are about types and contracts, not offsets. Verification runs on layout-independent IR, and layout is chosen afterwards, in codegen. That gives the property the rest of the design depends on:

- A layout change changes **layout hashes only**, never interface hashes, so importers are **relinked, not re-verified**. "Relink" means re-running layout lowering, codegen and the link from the importer's cached verified IR, against the new layout descriptors. The importer's proof certificate is reused unchanged.
- In Bazel, verification actions depend only on `.piai` interfaces, and codegen actions also depend on `.pial` layout descriptors. A layout change reruns codegen and link actions only.
- `size_of t` and `align_of t` are treated like exported fixed values ([ADR 0010](adr/0010-modules-interfaces-and-proof-certificates.md)). Proofs see them as symbols with refinements (`size_of t : int{1 .. 2^32}`, `align_of t` a power of two), and codegen folds them. A proof that needs the concrete number makes the module record a dependency on the layout hash in its requires, just as folding a constant records the inline surface hash. A layout change then makes that module re-verify, and no other.
- Layout respects the interface, never the reverse. If an interface lets importers borrow a field of an exported type, that field stays byte-addressable, so layout can never change what type-checks.

### The layout descriptor

Each module emits a descriptor for every type that is visible outside it, in a `.pial` file and in `__TEXT,__pia_layout` in the image:

```text
type          fully qualified name, monomorphised (Pixels.pixel, Pia.Mem.pool<Pixels.pixel>)
policy        auto | c | frozen | packed
shape         size, alignment, calling-convention class (integer registers, HFA, memory)
fields[]      name, bit offset, bit width, encoding (plain, biased range, niche-carrying),
              addressable flag
tags          for sum types and dyn: where the tag lives (own field, niche in a field,
              low bits of a pointer field), its bit positions and the variant-to-value map
pointer_tags  for each pointer field: which low bits carry tags, and the alignment proof
              they rely on
components    layout hashes of every field and type argument
algorithm     layout algorithm version, and the profile hash if layout used a profile
```

Two hashes are computed from it, both SHA-256 over a canonical encoding:

- **Shape hash**: size, alignment and calling-convention class. This is all an importer needs to pass a value of an **abstract** type (one whose definition the interface hides) or to embed it in its own records.
- **Layout hash**: the whole descriptor. Needed by an importer that reads or writes fields, matches on variants, or unpacks tagged pointers. Only possible for types whose definition the interface exposes.

Hashes compose through `components`. `Pia.Mem.pool<Pixels.pixel>` has a layout hash that includes `Pixels.pixel`'s, so a pool passed across a library boundary forces both sides to agree on its slot size.

An importer records, per type, the weakest hash it actually used. A library can therefore reorder or repack the fields of an abstract type freely, as long as its size, alignment and class stay the same, and importers that only hold it abstractly keep loading.

### Layout policies

- `@layout(auto)` is the default. The compiler orders fields to remove padding, packs range-typed fields into the bits they need (`int{0..9}` in 4 bits, `bool` in 1), puts sum-type tags into niches (an `option<int{0..254}>` uses 255 for `None`), and stashes tags in pointer low bits where the alignment allows. It may use a profile to place hot fields together, and then the profile's hash is part of the layout. The algorithm is deterministic: the same type, algorithm version and profile always give the same layout, so reproducible builds stay reproducible.
- `@layout(c)` follows the platform C ABI exactly, with no tags or packing. It is required for every type that crosses an `extern` boundary.
- `@layout(packed)` asks for minimum size even at the cost of unaligned access.
- `@layout(frozen)` pins the current layout with a checked-in baseline (`abi/<Module>.<type>.pial`), like Swift's `@frozen`. The compiler must reproduce the baseline exactly, and a library release cannot change it without dropping the baseline and bumping its major version. Use it for types in a library's stable ABI. Everything else stays `auto`, and changes whenever the compiler finds a better layout.

### Pointer tagging rules

A tagged pointer keeps extra information in pointer bits that are always zero for valid addresses. Pia allows it under these rules, each checked by the compiler:

1. **Low bits only.** A pointer may carry `k` tag bits only in bits `0 .. k-1`, and only if every pointer of that type is proved to be aligned to at least `2^k`. The proof comes from the pointer's provenance. `Pia.Mem.alloc` guarantees alignment of at least `max 16 (align_of t)` in its `ensures` (ADR 0026, [PR #65](https://github.com/deanberris/pia-lang/pull/65)), so any pointer from `Pia.Mem` has at least 4 free low bits. Static data gets the alignment codegen gives it. A pointer from an `extern` call has only the alignment its contract states.
2. **Never the high bits.** On Apple Silicon the top bits belong to pointer authentication (arm64e), memory tagging (MTE) and top-byte-ignore, and which of these apply varies by process and OS release. Pia does not tag there.
3. **More tag bits mean more alignment.** A layout that wants `k > 4` tag bits raises the pointee's alignment to `2^k`. That alignment is part of the pointee's shape, so it changes the shape hash and is visible to every importer.
4. **The tag encoding belongs to the containing type.** Which bits are used and what each value means is in the descriptor of the type that holds the pointer, so changing it changes that type's layout hash.
5. **Tags never cross `extern`.** `@layout(c)` types cannot hold tagged pointers, and passing a pointer to a foreign function strips its tag. A pointer received from C is never assumed to have free bits beyond its stated alignment.
6. **Tagging and untagging are checked operations.** They are `pia` dialect ops whose obligations (alignment, tag in range, address bits untouched) go to the verifier like any other goal, and they are lowered to `and`/`orr`/`bic` or folded into load offsets when the tag is known.

### Free-list reuse

Free lists are where a layout disagreement does the most damage, so they get explicit rules. `Pia.Mem` ([ADR 0026](https://github.com/deanberris/pia-lang/pull/65)) keeps its free lists as side metadata keyed by size class, so the allocator itself only ever sees sizes and alignments, never layouts.

- **Both sides of a free use the same size.** Allocation sizes come from `size_of t`, folded at codegen. If `libA` allocates a `t` and `B` frees it, both must agree on `size_of t`, or the block goes back into the wrong size class and a later allocation overlaps a live object. Both bind the same shape or layout witness for `t`, so dyld refuses the program before that can happen.
- **Typed pools compose.** `pool<t>` slabs are sized by `t`'s layout, and `pool<t>`'s own layout hash includes `t`'s. Code that shares a pool across a boundary binds one witness for both.
- **Reuse never exposes old contents or old tags.** A reused block comes back as `out` memory, so it must be fully written before it is read, and nothing of the old object's fields or pointer tags can be observed. Ownership and the borrow rules in ADR 0026 rule out a stale owner, or a stale tagged pointer, that still refers to the old object.
- **Reuse across types is by size class only.** A block freed as `t` may come back as `u` from the same size class. That is safe because the allocator guarantees size and alignment for `u`, and `u`'s layout does not depend on `t`'s.
- **Alignment survives reuse.** Every block in a size class has the class's alignment, at least 16, so the low-bit tags of any type allocated from it stay valid after reuse.

### The relink failure path

For each exported type a library makes visible, it exports one witness per hash, next to the interface witnesses:

```text
_pia$s$<module>$<type>$<hash128>               shape hash
_pia$l$<module>$<type>$<hash128>               layout hash (only for types whose definition is exported)
```

An importer references the witness for each type it depends on, at the weakest level it used.

- **Launch.** If the library's layout changed, dyld stops the program with `Symbol not found: _pia$l$Pixels$pixel$...` before any code runs. No Pia code can intercept that, so `pia-cert check <binary>` explains it: which type changed, which importer depends on it, what changed (size, field offsets, tag encoding), and that the fix is to relink, with no re-verification needed.
- **`dlopen`.** `Pia.Dl.open` turns the failure into `Err (LayoutChanged { type, wanted, found })` instead of a raw `dlerror` string.
- **Static link.** The link checker compares the layout hashes every object was compiled against with the defining module's descriptors, and reports `relink required` with the list of objects whose codegen is stale. The Bazel rules rerun exactly those codegen actions.
- **Frozen types** keep the same witness across releases. **Auto types** get a new one whenever their layout changes.

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

The standard library ([docs/stdlib.md](stdlib.md) and [ADR 0023](adr/0023-minimal-core-self-hosted-stdlib.md)) is the first big user. `Pia.Core`, `Pia.Mem` and `Pia.Io` can ship as one shared `libpia.dylib`, versioned by ABI baselines like any other library. Its `extern` POSIX contracts and `@assume`s appear as trusted items under `@trusted` modules, so `pia-cert trust-report` of any Pia program lists exactly which libSystem contracts it rests on.

## Implementation plan

Each step is a GitHub issue, tracked from M8 ([#9](https://github.com/deanberris/pia-lang/issues/9)) and the follow-up milestones.

1. Canonical interface serialisation and the interface and inline surface hashes ([#40](https://github.com/deanberris/pia-lang/issues/40)).
2. The certificate format: a small C++ reader and writer, and `pia-cert dump` ([#41](https://github.com/deanberris/pia-lang/issues/41)). Format 1 is implemented in `src/cert`, with a text body that holds the module, provides and requires. Format 2 adds `trusted` lines, so far only for lowerings (`trusted lowering matmul <hash> linalg.matmul,memref.expand_shape`), and piac writes it only for an object that has one, so every other object stays format 1; `pia-cert dump` prints them. The other fields, and the other kinds of trusted item, come later.
3. Emit `__pia_cert` and `__pia_iface` in objects and merge them into image certificates at link ([#42](https://github.com/deanberris/pia-lang/issues/42)).
4. Witness symbols: export them from libraries and reference them from importers ([#43](https://github.com/deanberris/pia-lang/issues/43)). Implemented for objects: the hash is over the whole `.piai` text until the inline surface gets its own hash, and the module path is spelled with `$`, as in `pia$w$Image$Pixels$Ops$<hash>`.
5. The link checker for objects and `.dylib` inputs, including `--trust-report` ([#44](https://github.com/deanberris/pia-lang/issues/44)). `pia-cert check` checks objects, and `pia_library` runs it as a validation action; `.dylib` inputs and the trust report come later.
6. Pia images without static initializers, the runtime's launch check, and `Pia.Dl.open` ([#46](https://github.com/deanberris/pia-lang/issues/46)).
7. ABI baselines and refinement proofs ([#49](https://github.com/deanberris/pia-lang/issues/49)).
8. `pia-cert audit`: recompute, re-prove refinements, replay proof bundles ([#51](https://github.com/deanberris/pia-lang/issues/51)).
9. The ELF port ([#53](https://github.com/deanberris/pia-lang/issues/53)).
10. Layout descriptors, shape and layout hashes, `__pia_layout` ([#89](https://github.com/deanberris/pia-lang/issues/89)).
11. Layout-independent verification and relink without re-proof ([#90](https://github.com/deanberris/pia-lang/issues/90)).
12. The `@layout(auto)` optimiser and the `c`, `packed` and `frozen` policies ([#91](https://github.com/deanberris/pia-lang/issues/91)).
13. Verified pointer tagging ([#92](https://github.com/deanberris/pia-lang/issues/92)).
14. Layout witnesses and the relink failure path ([#93](https://github.com/deanberris/pia-lang/issues/93)).
15. Free-list reuse across a library boundary ([#94](https://github.com/deanberris/pia-lang/issues/94)).

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
