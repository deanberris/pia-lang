# 30. Optimised object layouts are published, and a changed layout fails to load until relinked

Date: 2026-11-21

Status: Proposed

## Context

Dean wants the compiler free to optimise data layout: reorder fields, pack them, choose alignment, and stash information in the low bits of pointers. Modules should advertise the layout they chose, so rebuilds and static links agree on how data is laid out. When a library's layout changes, dynamic loading must fail and the importer must be relinked. Free-list reuse is a case that must stay safe.

[ADR 0024](0024-published-proof-certificates.md) publishes interfaces and proof certificates in shared libraries and makes dyld refuse a library with the wrong interface hash. Folding layout into that hash would force a re-proof on every layout change, though proofs never depend on offsets. The alternatives elsewhere are fixed C-like layout (no optimisation), layout resolved at load time (Objective-C non-fragile ivars, Swift resilience: offsets become run-time values, which blocks folding and vectorisation), or no dynamic ABI at all (Rust).

The full design is in [docs/abi.md](../abi.md#object-layout).

## Decision

- **The defining module chooses and publishes each type's layout.** It emits a layout descriptor (shape, fields with bit offsets and encodings, sum-type tag placement, pointer tag bits, component hashes, layout algorithm version, profile hash) in a `.pial` file and in `__TEXT,__pia_layout`.
- **Two hashes per type, separate from the interface hash.** The shape hash covers size, alignment and calling-convention class, which is what abstract uses need. The layout hash covers the whole descriptor, for importers that touch fields, variants or tags. Hashes compose through component types. Each importer records the weakest hash it used.
- **Layout never changes a proof.** Verification runs before layout is chosen. `size_of` and `align_of` are symbols with refinements in proofs, folded at codegen. A proof that needs a concrete size records a dependency on the layout hash. A layout change therefore means a relink: re-run codegen and link from cached verified IR, reusing the certificate.
- **Fail at load, relink to fix.** Libraries export `_pia$s$` and `_pia$l$` witness symbols per type and hash. Importers reference the ones they used. A changed layout makes dyld refuse to launch, or `Pia.Dl.open` return `LayoutChanged`. The static link checker reports which objects need their codegen rerun.
- **Policies.** `@layout(auto)` (default, optimised, deterministic), `@layout(c)` (required across `extern`), `@layout(packed)`, and `@layout(frozen)` (pinned by a checked-in baseline, for stable library ABIs).
- **Pointer tagging.** Low bits only, `k` bits only when the pointee's alignment of at least `2^k` is proved from provenance (`Pia.Mem.alloc` guarantees 16-byte alignment, so 4 bits). Never the high bits, which arm64e pointer authentication, MTE and top-byte-ignore claim. More tag bits raise the pointee's alignment, which is part of its shape. Tags are part of the containing type's layout, never cross `extern`, and tagging and untagging are verified ops.
- **Free-list reuse.** Allocator free lists see only sizes and alignments (ADR 0026). Allocating and freeing sides bind the same shape witness, so they agree on the size class. Pools compose their element's hash. Reused blocks come back as `out` memory, so old fields and tags are unobservable, and size-class alignment keeps low-bit tags valid.

## Consequences

- The compiler can reorder, pack, niche-fill and tag without any ABI promise to break, and offsets stay compile-time constants for folding, vectorisation and proofs.
- A layout change costs importers a relink, never a re-verification, and in Bazel only codegen and link actions rerun.
- Shipping a library with a stable binary layout takes an explicit `@layout(frozen)` and a checked-in baseline.
- One extra witness bind per imported type, at load.
- dyld's own error for a missing witness is cryptic, so `pia-cert check` is needed to explain it.
