# 48. Buffers may hold slices: owned slices are written through, shared ones only read

Date: 2026-11-22

Status: Accepted (2026-11-27).

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

### 5. Inline boxes: `vec (box t)` is a specialisation of `vec`

A buffer of owning boxes need not point anywhere: each element's slot can be the element itself (Dean, 2026-11-23). A buffer whose element type is a `box t` of a sized `t` is compiled as one aligned buffer of `t`, with each box's slot the one-element slice at its own index, and its spec-only state erased. There is then no pointer, length or allocation per box, and moving boxes between buffers, as growing a vector does, copies their contents.

The proofs do not change. The verifier still sees each element as owning a slice of length one, and a box taken out of the buffer borrows its slot in place, lent from the buffer as in section 2. Inline storage changes only where the slot lives.

A box over a concept, `box c`, holds values of different sizes. Stored inline, each slot must fit the largest value it will hold. The compiler knows which those are: every `widen` into a `box c` names its type, so the types that reach a given buffer of `box c` are known statically from the specialisations the program makes (Dean, 2026-11-23). The slot size and alignment are the largest of that set, and the user writes no bound. The set is part of the buffer's layout, which the ABI advertises (ADR 0030): a module that widens a new type into it changes the layout, and dynamic loading against the old one fails and requires a relink. A `box c` outside a buffer of inline boxes is the fat pointer of ADR 0046.

### 6. Moving an owned element out

An owning element read as a value, `nb.[i] <- old_buf.[i]` or `push v xs.[i]`, moves out of its buffer, as growing a vector does. The element left behind must not still own the box's slot, or two boxes would share it while the verifier models them apart. So each element of a buffer of owning elements has a held state (Dean, 2026-11-23), and the held state is its slices' lengths: a move leaves every slice of the element behind empty. A box is held when its slot has length one, which `ok` already says, so contracts need no new spec state and no new word. Reading or writing through an element moved out is then out of bounds, and a second move gets a box with an empty slot, which owns nothing and fails `ok`.

The element left behind keeps its contents: the moved value still reads them. Codegen keeps the emptying store, so the element's length is 0 at run time too, as the proof has it, and a program that reads it sees what was proved.

A read through the element, `xs.[i].slot.[0]`, `len xs.[i].slot`, or an argument of a `borrowed` parameter, borrows it and moves nothing, as a field read of a linear local does. Moving out needs a buffer the function may write. Moving an element out of a borrowed buffer is an error, since the caller would still hold the box.

Storing a whole owning element, `xs.[i] <- b`, needs the element written over to be empty, so that no box is lost by writing over it: the verifier proves that every slice of the old element has length zero. A buffer that is `out`, as a parameter or as the buffer a function lends, holds nothing yet, so all its elements are empty. A vector says the same of its spare capacity: `good v` states that the elements past `v.len` have empty slots.

## Implementation order

1. Sema accepts buffers whose elements hold slices; IRGen stores them as buffers of slices, with the ownership rule for writes and the loan rule for slices taken out.
2. The verifier's array-of-arrays encoding, with reads, `len`, writes through owned elements, and element replacement. (Steps 1 and 2 implemented: tests/verify/slice_buffers.pia. Spec-only fields in buffer elements, which `box`'s state needs, are proved and erased by codegen: tests/verify/spec_buffers.pia. Element lengths in callee and spec-function contracts are encoded too.)
3. Codegen: pointer and length buffers, and C entry points; buffers of `box t` inline as buffers of `t` (section 5). (Pointer and length buffers and C entry points implemented: tests/codegen/slice_buffers_run.pia runs from C, and tests/codegen/vec_boxes_core.pia checks a vector of boxes' lowering. Running a vector of boxes from C waits on regions in interfaces; inline boxes are not done yet.)
4. `vec (box t)` proved end to end, with `push` of boxes and `set` on an element (ADR 0046's priority test, at a concrete type). (Implemented over a fixed buffer: tests/verify/vec_boxes.pia, `vec (box u16)`. Growing, which moves the boxes into a larger buffer, is proved too, and so is that a box is stored only where no box is (section 6).)

## Consequences

- `vec (box t)`, vectors of strings and buffers of records with slice fields work, with no apartness invariants to write.
- A buffer of shared, writable slices, such as several views of one array kept in a vector, cannot be written through. Such code keeps indices into one buffer instead, which is also what a proof of it would need.
- Aliasing between an owned slot and a slice that is not in a buffer is ruled out by the borrow rules already: the owner lends it.

## Questions for Dean


1. **Writes only through owned slices?** The alternative, a region heap with explicit `apart` invariants, would allow writes through shared slices but needs quantified invariants that make proofs slower. Answered 2026-11-27 by Dean: yes, writes only through owned slices.
2. **Is `Drop` enough to count as owning**, or must the type be `@linear`? `box` has a `Drop`; a `@linear` record cannot be dropped implicitly. Both stop copies, which is what the proof needs. Answered 2026-11-27 by Dean: `Drop` is enough.
3. **Inline `box c` slots**: should a buffer of boxes over a concept carry a slot size, `vec (box c) n`, or should such boxes always stay out of line? Answered (Dean, 2026-11-23): neither. The slot fits the set of types the program statically widens into it, found from its specialisations (section 5).
