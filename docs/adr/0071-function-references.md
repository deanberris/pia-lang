# 71. Function references: `code (arrow)` holds a function's address, called through the arrow's contract

Date: 2026-11-27

Status: Proposed

## Context

[ADR 0044](0044-function-values-and-lambdas.md) made every function value static: a lambda or a named function passed to a higher-order function is a direct call in that function's instance, and "there is no function pointer and no heap allocation for a static function value, ever". A value whose function is chosen at run time was left to the library's `box` over `Function` ([ADR 0046](0046-box-over-a-type-or-a-concept.md)).

Two things now need a function's address as a value:

- **`box c`'s drop.** The amendment to ADR 0046 of 2026-11-26 gives a `box c` a direct reference to the boxed type's `drop`, "like a `unique_ptr<T>` ... but instead of a vtable we have an explicit ref to the type's drop implementation" (Dean). That reference is a code address stored in the box.
- **Tables and callbacks.** A table of handlers, a state machine's transitions, a C library that takes a callback (`qsort`, `pthread_create`, a GUI toolkit), or C code that calls back into Pia. For a function that captures nothing, a box and an allocator are more than the job needs: C's function pointer is the whole of it.

Dean decided on 2026-11-27 that function references are visible to programs, not internal to `box c`.

### Prior art

- **C** has function pointers: one address, no environment, no contract, and nothing stops a call through a pointer of the wrong type.
- **C++** adds pointers to members and `std::function`. A capture-free lambda converts to a function pointer.
- **Rust** has `fn(A) -> R`, a function-pointer type distinct from the `Fn` traits. Every capture-free closure and named function coerces to it. It is never null; `Option<fn(...)>` is the nullable pointer, with the same layout.
- **Zig** has `*const fn (A) R`, and **OCaml** needs none, since every closure is a value.

## Decision

### 1. The type `code (arrow)`

`code (x : u8) -> u8 requires x < 255 ensures result > x` is the type of a reference to a function with that arrow ([ADR 0044](0044-function-values-and-lambdas.md), section 3), contract included. `code` is a prelude type constructor, not a keyword, so it adds nothing to the lexer.

- A `code` value is one address wide. It is copyable, has no `drop`, and is never null. `option (code a)` is the nullable reference, laid out as one address with zero as `None`, as Rust does.
- It never meets `Eq`, `Ord` or `Hash`, as with every function type (ADR 0044).
- A function has static lifetime, so a `code` value borrows nothing. It can be stored in a record, a variant, a buffer or a module-state value, returned, and sent to another task.

### 2. Making one: `code f`

`code f` makes a reference to:

- a top-level function `f`,
- an instance of a generic one, `code sort<u32>` (an uninstantiated generic has no single address), or
- a lambda that captures nothing. A lambda with captures has an environment, and goes through `box (Function a r)` instead.

The function must meet the arrow it is used at. Its `requires` must follow from the arrow's and its `ensures` must give the arrow's. That is the same check ADR 0044 makes when a named function is passed for an arrow parameter, proved once where the `code f` is written. When the arrow has a contract the function does not meet exactly, the reference points to a wrapper with the arrow's contract, as ADR 0044's step 1 makes for function arguments. Modifiers must match exactly, since they are the calling convention: `moved t` is not `borrowed t`.

### 3. Calling through one

A `code` value is applied like any function, `c x`. The verifier knows nothing about which function it holds, only the arrow:

- The call's goals are the arrow's `requires`, at the call.
- Its facts are the arrow's `ensures`, about `result` and any `out` or `inout` parameters, and nothing else.
- When the arrow is pure ([ADR 0069](0069-pure-and-impure-functions.md)), a call is an uninterpreted function of the reference and the arguments, so two calls through one `code` value on equal arguments are equal, and the call may appear in a contract. A call through an arrow that is not pure is code-only, as ADR 0044 and ADR 0046 already rule for boxes.
- A reference's own purity is its arrow's. `code f` at a pure arrow requires `f` to be pure.

So a program that calls through a `code` value proves what it would prove about a call of any function with that arrow, and the check at `code f` is what makes that sound.

### 4. Generics and `Function`

`code (a -> r)` meets the prelude's `Function (code (a -> r)) a r`, with `apply` the call. A higher-order function instantiated at a `code` type has one instance for every function of that arrow, and it calls through the reference. This is how code size and dynamic choice are traded: a lambda passed directly still gets its own instance and inlines (ADR 0044, section 7), while a table of `code` values shares one.

### 5. Code generation and the ABI

- `code f` is the function's address: `func.constant`, then `llvm.mlir.addressof`. A call is `func.call_indirect`, then an indirect `llvm.call`. In a record or a buffer a reference is stored as a pointer (ADR 0048's buffers of slices store addresses the same way).
- A reference to a function with a C-compatible signature is a C function pointer at the C boundary ([ADR 0039](0039-module-and-interface-syntax.md)'s `@abi(c)`). So an `extern` may take a `code` parameter, and C's `qsort` can take a Pia comparator. The arrow's contract is what the `extern` declares the callback to be, and like every `extern` contract it is trusted and listed in the trust report.
- A `code` value that crosses into Pia from C, as a parameter of an exported function or the result of an `extern`, is trusted to meet its arrow, and the trust report lists it. A reference made in Pia is proved, at `code f`.
- An interface may export a `code` value or a function that takes or returns one. The arrow is part of the signature, so an importer checks its calls against it, and the referenced function's certificate ([ADR 0024](0024-published-proof-certificates.md)) covers the check made at `code f`.

### 6. `box c`'s drop

The amendment to ADR 0046 is the first user of this. A `box c` stores a `code` value for its object's drop. The compiler makes it for each widened type, as a thunk that takes the slot and drops the object in it, or a thunk that does nothing for a type with no drop. Dropping a `box c` calls it. Since the verifier sees only the arrow, the box's contract is unchanged.

### 7. What this ADR does not decide

- References to functions with captures: those are boxes, with an allocator (ADR 0046).
- Comparison of references, such as testing which handler a table holds. A program that needs it keeps a tag beside the reference.
- References across dynamic libraries, beyond what a symbol's address already gives. That waits for ADR 0024's loader work.

## Implementation order

Each step is a PR with lit tests in `tests/verify`, `tests/irgen` and `tests/codegen`, and with `pia-language`'s syntax table and `pia-porting`'s feature map updated as it lands.

1. **The type and its proofs.** `code (arrow)` in sema, `code f` with the check against the arrow, calls through the arrow's contract, pure arrows as uninterpreted functions, and errors for a generic without arguments, a lambda with captures, and mismatched modifiers.
2. **Code generation.** Addresses and indirect calls, references in records, variants and buffers, `option (code a)` as a nullable pointer, and a run test that picks handlers from a table.
3. **The C boundary.** `code` parameters of `extern`s and of `@abi(c)` exports, with a test of `qsort` over a Pia comparator and of C calling back into Pia, and the trust report's entries.
4. **`Function` for `code`**, so generic algorithms take a reference.
5. **`box c`'s drop through a reference** (the ADR 0046 amendment, steps 2 and 3).

## Consequences

- Tables of handlers and C callbacks need no allocator and no box, and a call through one costs one indirect call.
- What a reference can do is exactly what its arrow says, so a caller proves no more and no less than it would about any function with that arrow. The cost moves to `code f`, where the referenced function is checked once.
- ADR 0044's promise still holds for lambdas passed directly: they never become pointers. A reference exists only where a program writes `code`.
- A `code` value from C is trusted, which is the same trust an `extern` already carries, and the trust report shows it.

## Questions for Dean

1. **The name.** `code (arrow)` (recommended: a type name, not a keyword, and it says what the value is), `fn (arrow)` as in Rust, or a bare arrow type in a value's position with `&f` to make one.
