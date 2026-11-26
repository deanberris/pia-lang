# 71. Function references: a function is a value that travels by reference

Date: 2026-11-27

Status: Proposed

## Context

[ADR 0044](0044-function-values-and-lambdas.md) made every function value static: a lambda or a named function passed to a higher-order function is a direct call in that function's instance, and "there is no function pointer and no heap allocation for a static function value, ever". A value whose function is chosen at run time was left to the library's `box` over `Function` ([ADR 0046](0046-box-over-a-type-or-a-concept.md)).

The case that needs this is a box over a concept, `box c` (Dean, 2026-11-27): what Rust's `dyn Trait` is for traits. A `Box<dyn Shape>` in Rust is a pointer to the object and a pointer to a table holding the object's drop, its size and alignment, and one function pointer per method. A `box Shape` must do the same job, ending and calling an object whose type its user does not know, and it can only do it with function references:

- **Its drop.** The amendment to ADR 0046 of 2026-11-26 gives a `box c` a direct reference to the boxed type's `drop`, "like a `unique_ptr<T>` ... but instead of a vtable we have an explicit ref to the type's drop implementation" (Dean).
- **Its requirements.** A call of a concept's requirement through a box must reach the boxed type's implementation. Step 5 of ADR 0046 does it with a switch on a tag, which works only inside the module that knows every widened type. A reference to each requirement's implementation works anywhere, including in a module that imports the box and never saw the types.

The same references then serve tables and callbacks: a table of handlers, a state machine's transitions, a C library that takes a callback (`qsort`, `pthread_create`), or C code that calls back into Pia. For a function that captures nothing, a box and an allocator are more than those need.

Dean decided on 2026-11-27 that function references are visible to programs, and that they need no address operator: "we can treat a function as a value that travels by reference (cannot be cloned or duplicated)". The function itself is never copied, and a reference to it can be (Dean, 2026-11-27).

### Prior art

- **C** has function pointers and an implicit decay from a function's name to its address. Nothing stops a call through a pointer of the wrong type.
- **C++** has the same decay, `std::function` for owning closures, and `std::function_ref` (C++26) for a borrowed callable: a code pointer and a pointer to the callable's state.
- **Rust** has `fn(A) -> R`, distinct from the `Fn` traits, to which named functions and capture-free closures coerce. It is never null; `Option<fn(...)>` is the nullable form. `dyn Trait` is a fat pointer, the data and a vtable of drop, size, alignment and one `fn` pointer per method, shared by every value of one type and trait.

## Decision

### 1. A function is a value that travels by reference

A function's name is a value of its arrow type ([ADR 0044](0044-function-values-and-lambdas.md), section 3). Wherever that value is stored or passed by reference, what travels is a reference to the function, never a copy of its code. There is no address operator and no separate reference type:

```
let succ (x : u8) : u8 requires x < 255 ensures result = x + 1 = (x + 1)

let h : (x : u8) -> u8 requires x < 255 = succ
let keys = type { on_key : (k : u8) -> unit; on_quit : unit -> unit }
let table : [(x : u8) -> u8 requires x < 100; 3] = [succ; twice; succ]
```

- The function has static lifetime, so a reference to it is a shared borrow that never ends. It may be stored in a `let`, a record field, a variant, a buffer or module state, returned, and sent to another task.
- A reference can be copied, as any shared borrow can, so one function may sit in many places. The function itself cannot be cloned or duplicated.
- A reference is a proxy for its function (Dean, 2026-11-27): wherever it is used, it behaves as the function's name would, so it is called, passed on and stored the same way. It is fixed by default, like every binding: `h` names `succ` for as long as `h` lives, and a call through it, where the compiler can see which function it was bound to, is a direct call. A place written `mutable`, such as `let h : mutable (u8 -> u8) = succ` or a `mutable` table slot, can be rebound to another function of the same arrow with `h <- twice`; a call through it is indirect unless the compiler can see the last binding.
- Semantically it is ADR 0047's `ref t` to the function (Dean, 2026-11-27): a shared, immutable value that every copy of the reference reaches. Because a function lives for the whole program, there is no count to keep and nothing to free, so it is laid out as a bare address and needs no word of its own.
- A reference is never null. `option (u8 -> u8)` is the nullable one, laid out as one address with zero as `None`.
- Function types still never meet `Eq`, `Ord` or `Hash` (ADR 0044): two references cannot be compared.

What can be referenced: a top-level function, an instance of a generic one (`sort<u32>`; an uninstantiated generic has no single body), and a lambda that captures nothing. A lambda that captures is section 4.

### 2. Parameters: inlined, or by reference

ADR 0044's parameters keep their meaning, and `borrowed` chooses the other one:

- `(f : u8 -> u8)` is any type meeting `Function` (ADR 0044, section 4). Each argument gets its own instance, and the call inlines. This stays the default, because it is the fast one.
- `(f : borrowed (u8 -> u8))` takes a reference. The function has one instance for every argument, and calls through the reference.

A stored arrow type, in a `let`, a field, a buffer or a result, is always a reference, since a stored value has one layout.

### 3. Meeting the arrow, and calling through it

Making a reference, by storing a function or passing it `borrowed`, checks the function against the arrow. Its `requires` must follow from the arrow's and its `ensures` must give the arrow's, the same check ADR 0044 makes when a named function is passed for an arrow parameter, proved once where the reference is made. When the arrow's contract differs from the function's, the reference is to a wrapper with the arrow's contract, as in ADR 0044's step 1. Modifiers must match exactly, since they are the calling convention.

A call through a reference, `h x`, knows only the arrow:

- Its goals are the arrow's `requires`, at the call.
- Its facts are the arrow's `ensures`, about `result` and any `out` or `inout` parameters, and nothing else.
- When the arrow is pure ([ADR 0069](0069-pure-and-impure-functions.md)), a call is an uninterpreted function of the reference and the arguments, so two calls through one reference on equal arguments are equal, and the call may appear in a contract. A call through an arrow that is not pure is code-only, as ADR 0044 and ADR 0046 already rule for boxes. A function referenced at a pure arrow must be pure.

### 4. Borrowed closures

A lambda that captures is a record of its captures (ADR 0044, section 6). A reference to it is two words, its code and a pointer to that record, as C++'s `function_ref` is. It is an ordinary loan ([ADR 0042](0042-lifetimes-liveness-and-escape-analysis.md)): it lasts no longer than the closure it borrows, so it can be passed `borrowed` and stored in a local, but not returned past the closure or stored where the closure does not reach. A closure that must outlive its maker, chosen at run time, is still a `box (Function a r)` with an allocator (ADR 0046).

A reference to a function that captures nothing has no environment, and is one word.

### 5. Code generation and the ABI

- A reference is the function's address: `func.constant`, then `llvm.mlir.addressof`. A call is `func.call_indirect`, then an indirect `llvm.call`. In a record or a buffer a reference is stored as a pointer, as ADR 0048's buffers of slices store addresses.
- A reference to a function with a C-compatible signature is a C function pointer at the C boundary ([ADR 0039](0039-module-and-interface-syntax.md)'s `@abi(c)`). So an `extern` may take one, and C's `qsort` can take a Pia comparator. The arrow's contract is what the `extern` declares the callback to be, trusted like every `extern` contract and listed in the trust report.
- A reference that crosses into Pia from C, as a parameter of an exported function or the result of an `extern`, is trusted to meet its arrow, and the trust report lists it. A reference made in Pia is proved where it is made.
- An interface may export a function that takes, stores or returns references. The arrow is part of the signature, so an importer checks its calls against it.

### 6. Boxes over concepts

This is what the references are for first, and what makes a `box c` work as Rust's `dyn Trait` does. When `widen` makes a `box c` from a `box t`, it stores, beside the slot and the object's size and alignment (the ADR 0046 amendment):

- **A reference to `t`'s drop**, through a thunk that takes the slot and drops the object in it, or one that does nothing for a type with no drop. Dropping the box calls it, then gives the slot back to its allocator.
- **A reference to `t`'s implementation of each of `c`'s requirements**, through a thunk that takes the slot in the receiver's place and forwards to `t`'s function. `area b` on a `box Shape` is a call through the box's `area` reference.

Each reference is checked once, where `widen` makes it, against the requirement's arrow with the receiver erased, which is exactly the check ADR 0046's section 4 already asks for: what is placed in a box must be proved to expose the concept's interface. So the verifier's view of a box does not change. A call through it has the requirement's contract and nothing else.

The references are stored in the box itself, not in a table the box points to, as Dean asked ("instead of a vtable we have an explicit ref"): a call is one load and one indirect call, and a box is one word wider for each requirement. Where the compiler can see what a box holds, such as straight after `widen`, the call is direct, as it is today. Because a reference is an address, a box made in one module can be called and dropped in another that never saw its type, so ADR 0046's step 6 needs no table layout and no thunks beyond these.

### 7. What this ADR does not decide

- Comparison of references, such as testing which handler a table holds. A program that needs it keeps a tag beside the reference.
- Owning closures chosen at run time: those are boxes (ADR 0046).
- References across dynamic libraries beyond what a symbol's address gives, which waits for [ADR 0024](0024-published-proof-certificates.md)'s loader work.

## Implementation order

Each step is a PR with lit tests in `tests/verify`, `tests/irgen` and `tests/codegen`, with `pia-language`'s syntax table and `pia-porting`'s feature map updated as it lands.

1. **References and their proofs.** Arrow types in a `let`, a field and a buffer, `borrowed` arrow parameters, the check against the arrow where a reference is made, calls through the arrow's contract, pure arrows as uninterpreted functions, and errors for a generic without arguments, a capturing lambda stored past its captures, and mismatched modifiers.
2. **Code generation.** Addresses and indirect calls, references in records, variants and buffers, `option` of an arrow as a nullable pointer, and a run test that picks handlers from a table.
3. **The C boundary.** References as parameters of `extern`s and `@abi(c)` exports, with a test of `qsort` over a Pia comparator and of C calling back into Pia, and the trust report's entries.
4. **Borrowed closures**: two-word references to capturing lambdas, with ADR 0042's loan checks.
5. **Boxes over concepts through references** (the ADR 0046 amendment, steps 2 and 3): `widen` stores the drop and each requirement's reference, calls and drops go through them, and a box made in one module is used in another.

## Consequences

- Tables of handlers and C callbacks need no allocator, no box and no new syntax. A call through one costs one indirect call.
- A function's name means the same thing everywhere, and `borrowed` is the only word that picks a reference over an instance, so no keyword or operator is added.
- What a reference can do is exactly what its arrow says, so a caller proves what it would about any function with that arrow, and the referenced function is checked once, where the reference is made.
- ADR 0044's promise still holds for functions passed without `borrowed`: they never become pointers.
- A reference from C is trusted, the same trust an `extern` already carries, and the trust report shows it.
