# 48. Buffers may hold slices: owned slices are written through, shared ones only read

Date: 2026-11-22

Status: Proposed.

## Context

A buffer cannot hold a value that holds a slice today: `[box u16]` is "not supported yet: its elements hold a slice". That blocks Dean's priority for `box` ([ADR 0046](0046-box-over-a-type-or-a-concept.md)): a `vec (box t)`, and most of all a `vec (box c)`. It also blocks a vector of strings, the JSON DOM's arrays of nodes whose leaves are slices of the input ([ADR 0045](0045-json-derived-codecs-and-conforming-dom.md), [ADR 0047](0047-recursive-sum-types-and-shared-references.md)), and any buffer of records with a slice field.

The verifier models every buffer as an SMT array of its own. A slice taken from a buffer is a view of it, an offset and a length into the same array, and a buffer a call returns, such as an allocation, is a fresh array. That is sound because each slice knows which array it views. A slice stored in a buffer element loses that: two elements may hold views of the same memory. A write through one must then show through the other, and the encoding cannot tell when.

Rust's answer is that a mutable reference is unique. Pia already has the same fact in two places. An owning value (`@linear`, or a type with a `Drop`, such as `box`) is never copied, so the slot it owns is reached only through it. And a shared slice, such as a JSON leaf viewing its input, is only read.

## Decision

### 1. A buffer of slices is an array of arrays

A buffer whose elements hold a slice is stored, as buffers of records are, one buffer per field ([buffers of records](../irgen.md)). A slice field becomes a buffer of slices. The verifier encodes a buffer of slices of `t` as two arrays: the contents, from an index to an array of `t`, and the lengths, from an index to a length. `xs.[i]` gives element `i`'s slice, `len xs.[i]` its length, and `xs.[i].[j]` reads its contents. A write `xs.[i].[j] <- v` updates element `i`'s array and no other.

### 2. Only owned slices are written through

That encoding is sound only when no two elements share memory. So a write through a slice held in a buffer is allowed only when an owning value holds it: the element type, or the record on the path to the slice, is `@linear` or has a `Drop`. A `box` is one. Ownership is what proves the elements apart, so the user writes no apartness invariant, and the solver needs no quantifier for it.

A slice held in a buffer through anything else is read-only there: reading is sound whatever it aliases. Writing through one is an error that says the element does not own its slice, and suggests a `box` or a `@linear` record.

A slice taken out of an owning element, `let s = xs.[i].slot`, is a loan from the buffer (#70, [ADR 0042](0042-lifetimes-liveness-and-escape-analysis.md)). While it is live, the buffer cannot be written, so the element cannot be replaced under it.

### 3. Regions carry over

An element's slices borrow from what its type says: `[box u16 r]` borrows from the region `r`, as each box does ([ADR 0042](0042-lifetimes-liveness-and-escape-analysis.md), step 2). A loan in a buffer lasts as long as the buffer's own borrows.

### 4. Code generation

Each element slice is a pointer and a length. The buffer of slices becomes two buffers, one of pointers and one of lengths, so it stays struct-of-arrays like every buffer of records. A C entry point takes both, as it takes one pointer per field today.

## Implementation order

1. Sema accepts buffers whose elements hold slices; IRGen stores them as buffers of slices, with the ownership rule for writes and the loan rule for slices taken out.
2. The verifier's array-of-arrays encoding, with reads, `len`, writes through owned elements, and element replacement. (Steps 1 and 2 implemented: tests/verify/slice_buffers.pia. Spec-only fields in buffer elements, which `box`'s state needs, are proved and erased by codegen: tests/verify/spec_buffers.pia. Not yet: element lengths in callee contracts.)
3. Codegen: pointer and length buffers, and C entry points.
4. `vec (box t)` proved end to end, with `push` of boxes and `set` on an element (ADR 0046's priority test, at a concrete type).

## Consequences

- `vec (box t)`, vectors of strings and buffers of records with slice fields work, with no apartness invariants to write.
- A buffer of shared, writable slices, such as several views of one array kept in a vector, cannot be written through. Such code keeps indices into one buffer instead, which is also what a proof of it would need.
- Aliasing between an owned slot and a slice that is not in a buffer is ruled out by the borrow rules already: the owner lends it.

## Questions for Dean

1. **Writes only through owned slices?** The alternative, a region heap with explicit `apart` invariants, would allow writes through shared slices but needs quantified invariants that make proofs slower.
2. **Is `Drop` enough to count as owning**, or must the type be `@linear`? `box` has a `Drop`; a `@linear` record cannot be dropped implicitly. Both stop copies, which is what the proof needs.
