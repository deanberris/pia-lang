# 46. A box holds a type or any type meeting a concept, and what it holds is proved to have the concept's shape

Date: 2026-11-22

Status: Accepted (Dean, 2026-11-22), with his answers folded in: `release` and `remove` leave a box empty until it is filled again; a box over a concept forwards its interface directly, with no run-time checks; and a `vec` of boxes, above all `vec (box c)`, comes first.

## Context

C++ has three ways to own a value that lives elsewhere, and none of them says much about it:

- `unique_ptr<T>` is a pointer that may be null, plus a deleter. Its type promises only that it points to a `T`, or to nothing.
- A `unique_ptr<Base>` to a class with virtual functions holds any derived class. Whether the derived class keeps the base class's promises is a matter of documentation.
- `std::function<R(A)>` and `std::move_only_function` hold any callable of the right signature, with a hidden allocation.

Dean asked (2026-11-22) why Pia would mirror `unique_ptr`, when a box type could take a concept as its parameter, so that anything put in it is proved statically to have the right shape. [ADR 0040](0040-cpp23-standard-library-in-pia.md) section 4 took that answer: there is no `unique_ptr`, only one `box`. [ADR 0044](0044-function-values-and-lambdas.md) section 8 left dynamic function values to "a type-erased box" in `Pia.Fn`, and that box is this one at the `Function` concept. This ADR decides the core part they both need: a concept used where a type is expected.

What the language has today:

- **Concepts** ([ADR 0034](0034-concepts-and-overload-resolution.md)) are checked signatures with laws. A use check proves each type that meets a concept satisfies its requirements' contracts and laws.
- **Generic bodies** are proved once over abstract SMT sorts, with concept functions uninterpreted and constrained by their contracts and laws ([ADR 0043](0043-generic-definitions-proved-once.md)). That is the proof a call through an erased box needs.
- **`dyn`** ([ADR 0003](0003-static-typing-with-tagged-dyn.md)) is a closed sum of tagged types, which a `match` takes apart. It cannot hold a type it does not list, and it has no requirement calls.
- **Allocators** are explicit, and containers store theirs ([ADR 0026](0026-memory-manager.md), [ADR 0041](0041-allocator-semantics-as-a-theory.md)). `Drop`, `@linear` and borrows decide when a value is freed and who may see it.

### Prior art

- **Rust** has `Box<T>` and `Box<dyn Trait>`. `dyn Trait` is unsized, so it lives only behind a pointer, which is a fat pointer to the value and a vtable. Only "object-safe" traits can be `dyn`: no generic methods, and no `Self` in argument or result position other than the receiver.
- **Swift** has `any P` existentials with witness tables, and the same restriction on `Self` requirements until they are opened.
- **Haskell** has existential types over a type class dictionary.
- **Dafny** and **Verus** verify calls through traits from the trait method's specification, which is what ADR 0043 already does for generic bodies.

## Decision

### 1. One `box`, never null

`box` is a library type in `Pia.Mem.Box`. A `box t` is an owning, non-null pointer to a `t` in memory taken from an allocator the box stores.

- `box.make alloc v` moves `v` into a new allocation. It can fail, like every allocation, so its result is `result (box t) alloc_error`.
- Reading and writing the contents are borrows: `box.get b : borrowed(b) t`, and `box.get_mut` for writes, which the borrow rules of #70 and [ADR 0042](0042-lifetimes-liveness-and-escape-analysis.md) keep from outliving the box.
- **Emptying and refilling** (Dean). A box has a spec-only state `box.full b` ([ADR 0041](0041-allocator-semantics-as-a-theory.md)'s spec-only fields, erased by codegen), so there is no run-time flag:
    - `box.release b : t` (for `box t`) moves the value out and leaves `b` empty. `box.remove b` (for any box, including `box c`, whose value is unsized and cannot be returned) drops the value in place and leaves `b` empty.
    - An empty box keeps its allocation. `box.fill b v` requires `not (box.full b)` and a compatible value, and makes `b` full again: for `box t`, any `t`; for `box c`, a value of any type that meets `c` and whose size and alignment fit the allocation, which the box records from `make` (as a real field when its allocator's `give` needs the size, spec-only otherwise).
    - `get`, `get_mut` and every call through a box require `box.full b`, proved where they are used. An empty box is invalid until it is filled, and using it is a failed goal, not a run-time check. (For `box c`, the cache-line amendment replaces this: an empty box is moved from, so the compiler rejects using it, and a call through a box needs no proof.)
    - `box.free b` requires `not (box.full b)` and returns the memory without dropping anything.
- A box is `Drop`, and dropping requires it to be full: it drops the contents and then returns the memory to its allocator. A box that may be empty at scope end must be filled or freed first. A box of a `@linear` type is itself `@linear`.
- There is no deleter. A different way to free is a different allocator.
- There is no null box. A box that may be empty is `option (box t)`, and the layout ([ADR 0030](0030-published-object-layouts.md)) uses the null pointer as `None`, so it is still one pointer.
- A box stores its allocator. A default allocator from module state ([ADR 0041](0041-allocator-semantics-as-a-theory.md)) has no fields, so with one, `box t` is a single pointer.

`box t` at a concrete `t` is an ordinary generic type. It needs nothing from this ADR beyond `Pia.Mem` storing allocators (ADR 0041, step 5). Every call on its contents is direct, and every proof sees the concrete value.

### 2. A concept in place of a type

A concept applied to all of its arguments but the first names a type: the type of a value of *some* type that meets the concept. `Shape` (from `Shape (t : type) : concept`) and `Function u8 bool` (from `Function f a r`, ADR 0044) are such types. They need no keyword, so the rule adds none.

- **They are unsized.** Their size is not known when the program is compiled, so they may appear only as an argument of a type parameter marked `@unsized`. `box`'s parameter is the only one in the library at first: `let box (@unsized t : type) = ...`. Anywhere else, such as a `let`, a field, a slice element or a parameter, is a type error that suggests `box`.
- **Arrow types are sugar.** `box ((x : u8) -> u8 requires x < 255 ensures result > x)` is a box of `Function` at that arrow type, contract included. That is `Pia.Fn`'s dynamic function value: C++'s `move_only_function`, with its contract in the type.
- **Generic code at a concept.** `box Shape` is a concrete type, and it meets `Shape` itself by forwarding (section 4), so code generic over `(t : type where Shape t)` is instantiated at `box Shape` like any type that meets `Shape`.

### 3. Widening is explicit and proves the shape

`box.widen b` turns a `box t` into a `box c`, as `widen` turns a value into a wider type elsewhere in Pia. Pia has no implicit conversions (ADR 0003), so the call is written out. Writing `box.widen b` where a `box Shape` is expected deduces `c` from the expected type. (The draft called this `box.erase`; it is renamed so it is not read as removing the contents, which is `box.remove`.)

- **The use check runs there.** `t` must meet `c`, with instances found by argument-dependent lookup and adapters as ADR 0034 finds them. The requirements' contracts and the concept's laws are proved for `t` by the use check, as for any instance, once per type and not once per box.
- **The table.** The erased box stores a pointer to the instance's table, which holds the requirement functions in the concept's declaration order, then `drop`, size and alignment. There is one table per pair of type and concept, emitted as a constant.
- **Restrictions on what can be erased.** A `@linear` value cannot be erased unless the concept requires a consuming function, because the box would hide the obligation to release it. A value that borrows (`borrowed(m)`) cannot be erased, because the box could outlive its lender.

### 4. A box forwards its concept's interface, and only some requirements can be forwarded

A requirement can be called through a `box c` when its concept parameter appears exactly once among its parameters, as the receiver (`in`, `inout` or `moved`), and nowhere in its result. `area : (s : t) -> f32` qualifies. `lt : (a : t) -> (b : t) -> bool` and `clone : (s : t) -> t` do not, because two erased values may hold different types, and an erased result has no size. This is Rust's object safety. Pia has no run-time type information to check that two boxes hold the same type, and adding it would be a separate decision.

A concept whose requirements are all excluded can still be widened to. Only `drop` can then be called through the box, and a program that tries anything else gets an error naming the requirement and the reason.

**Forwarding, proved, with no run-time checks** (Dean). When every requirement of `c` can be called through a box and every law of `c` mentions one value of the concept's type, the compiler gives `box c` an instance of `c` itself. Each requirement of that instance takes the box (as `in`, `inout` or `moved`, as the requirement takes its receiver), requires `box.full b`, and calls the boxed object's function through the table with the same arguments; nothing is checked at run time. The instance is checked like any other at the use check: its contracts are the requirement's own, which hold because the table's function was proved to meet them when the box was widened, and its laws hold for the same reason. So a `box Shape` exposes `Shape`'s interface, proved to forward directly to the object. A concept with a binary requirement or a law over two values (`Ord`'s transitivity) gives `box c` no instance, and its callable requirements are still usable on the box directly.

### 5. Proofs through a box

An erased box's contents are a value of an abstract sort, one sort per box value, so two boxes never share facts about their contents. A call `area b` through a box is proved the way ADR 0043 proves a call in a generic body:

- the requirement is an uninterpreted function at that sort;
- its `requires` is a goal at the call;
- its `ensures` is assumed of the result;
- the concept's laws hold for the sort, so a law over one receiver can be used.

The proof is sound because erasing ran the use check, which proved each requirement's contract for the actual type.

- **Mutation.** A call with an `inout` receiver gives the box a fresh contents value afterwards, so facts from earlier calls are lost unless the requirement's `ensures` relates them with `old`.
- **Calls in contracts** (agreed with the lambdas design, ADR 0044 section 5). A call through a box may appear in a contract or spec function only when the requirement is pure: only `in` parameters, no module-state writes, and a contract that does not say it may fail to terminate. Otherwise an erased call is code only, and its facts come only from the requirement's contract. For `box (Function a r)` that means applying the box in a contract is allowed only when the arrow type is pure. A box that calls something effectful never makes a contract depend on which function it holds.

### 6. Relation to `dyn`

`dyn` stays a closed sum: its tags are listed, a `match` takes it apart, and the prover enumerates its cases. A `box c` is open: any module can widen a box of a new type into it, there is no `match` on what it holds, and no downcast. The two cover the two uses C++ gives `variant` and virtual base classes respectively.

### 7. Code generation and the ABI

- A `box t` is one pointer, and the allocator's fields when it has any. A `box c` adds the table pointer, so it is a fat pointer, as in Rust.
- A call through a box is an indirect call through the table, unless the optimiser can see which table it holds, for example right after `box.widen`, in which case it is a direct call.
- Tables are part of the published ABI ([ADR 0030](0030-published-object-layouts.md), [ADR 0024](0024-published-proof-certificates.md)):
  - a concept's table layout is its requirements in declaration order;
  - the concept's interface hash goes in the certificate;
  - a module whose table for a concept was built against a different version of that concept fails to load until it is relinked, as a changed object layout does.

## Implementation order

Dean's priority is a `vec` of boxes, and most of all `vec (box c)`, so steps 1 to 5 aim at one end-to-end test: a `vec (box Shape)` holding two different shapes, with a `Shape` function called on each element and proved.

1. **`box t` in `Pia.Mem.Box`**, built with the `Pia.Mem` work ("Build Pia's core up to a proved Vec") once records can hold their allocator (ADR 0042's region parameters). This covers `make`, `get`, `get_mut`, `release`, `remove`, `fill`, `free`, the spec-only `full` state, `Drop`, and `vec (box t)`. The one-pointer layout of `option (box t)` can follow with ADR 0030; a proved non-null invariant is enough at first. (Done in lib/Pia/Mem/Box.pia: `make`, `get`, `set`, `release`, `remove`, `fill`, `free` and a generic `drop` that requires a full box and drops the value with it; tests/std/mem*.pia, with mem_drop_errors.pia for a box left empty or freed full. `get_mut` is `set` for now. Still to come: `vec (box t)` in the library, which is proved as a prototype in tests/verify/vec_boxes.pia, and a box over an allocator that frees one by one.)
2. **Concepts as unsized types.** Parsing a partially applied concept in type position, `@unsized` parameters, the error everywhere else, and arrow types as `Function`.
3. **`box.widen`.** The use check at widening, tables as constants, the `@linear` and borrow restrictions.
4. **Calls through a box and forwarding.** The receiver rule, the generated forwarding instance, the verifier's one sort per box, contracts and laws as hypotheses, havoc after `inout`, and purity in contracts.
5. **Code generation, within a module.** `box C` lowers to a tagged union of the types the module widens to `C` (its closed world). A call through a box is a switch on the tag into each type's requirement, and a direct call where the tag is known. With step 1 this gives the `vec (box Shape)` test. A box may not cross a Pia module boundary yet: two modules would disagree on the union.
6. **The ABI.** Fat pointers to a function-pointer table, one per pair of type and concept, with forwarding thunks and indirect calls: the cross-module layout, with [ADR 0030](0030-published-object-layouts.md)'s published layouts, the table layout in the published interface, and the loader's check.
7. **`Pia.Fn`'s dynamic function values** as `box` at arrow types, and the library's handler tables.

## Steps 2 to 4 as built

Steps 2 to 4 are built for the verifier (src/irgen/Boxes.cpp), and step 5 for code generation within a module.

- **The type.** A type function whose first parameter is `@unsized`, `let box = let (@unsized t : type) (r : region) => type { slot : borrowed(r) mutable [t]; state : int }`, takes a concept there. `box Shape r` is then its own type, `box_Shape`: the tagged union of the types this module widens to `Shape` (step 5), found by a first pass of IRGen, so the second makes `type | Box_Shape_square of square | Box_Shape_rect of rect`. In tests/codegen/box_concept.pia that is 4 bytes, a tag and the largest field set, square's side or rect's w and h, laid out as one buffer per field. A concept anywhere else a type is expected is an error that suggests `box` (tests/irgen/box_concept_type_errors.pia).
- **The verifier's view.** Each requirement callable through a box is an uninterpreted function of the box in a generated theory `erased_Shape`, `area_of`. The union's switch is code; the verifier is told only that its result is `area_of b` (an assumption the use check at `widen` justifies), so a proof through a box sees the contract and not which types the module widens. The requirement's contract is an axiom about it, and so is each law of the concept over one value. The axioms hold because `widen` runs the use check. One sort serves every box, which is sound because only single-receiver requirements are callable, and one address is one object.
- **`widen b`** turns a full `box t` (`b.state = 1`, as for `box t`) into a `box Shape`. It is generic over `t where Shape t`, so the use check runs at each instance. It refuses a `@linear` `t` and a `t` that borrows (tests/irgen/box_concept_errors.pia).
- **Calls through a box.** `area b`, with `b : box Shape`, is a generated function: its precondition is the requirement's, and it ensures `result = erased_Shape.area_of b.slot`. Those functions are `box Shape`'s instance of `Shape`, so `box Shape` meets `Shape`, and a generic over `Shape` instantiates at it and is discharged by its generic proof. A requirement with two values of the concept's type, or one returning that type, gets a stub whose call is an error naming the reason. For now a box forwards only a receiver it lends.
- **Gaps.**
  - `widen` gives the box a fresh object, so facts about the boxed value do not carry over. A later step links them: a requirement's result on the box equals its result on the value.
  - Function-pointer tables and the cross-module layout are step 6; until then an interface may show a box only to C (`@abi(c)`), and a box over an imported concept is refused.
  - A requirement's precondition that names another requirement is not carried into the switch's call.
  - `remove` and `fill` for `box c` are not built, so a `box c` is always full, which lets the forwarding instance meet the concept without a `full` precondition.
  - Only a concept of one parameter can be boxed.
  - A program that boxes two concepts gets two `widen` overloads that differ only in their result.
- tests/verify/box_concept.pia holds a square and a rectangle in one slice of `box Shape`, proves the sum of their areas from `Shape`'s contract, calls a generic over `Shape` at `box Shape`, and fails a requirement's precondition through a box. tests/codegen/box_concept.pia compiles it, and box_concept_test.c runs it and checks the sum, 19. tests/codegen/box_direct.pia checks that a call through a box straight after `widen` has no test of the tag, and that one through a box from a slice does.

## Consequences

- C++'s `unique_ptr`, virtual base classes, `std::function` and `move_only_function` become one type with one set of rules. Whatever a box holds is proved, statically, to meet the concept it is boxed as, laws included, which C++ cannot check for a derived class.
- A box over a concept has the same proof cost as a generic body: requirement contracts and laws, proved once per type at the use check. No proof re-runs per box.
- Binary requirements such as `lt`, and requirements returning the concept's type, cannot be called through a box. Code that needs them uses generics, or a concept written for the erased use.
- Pia gains its first unsized type. The `@unsized` marker keeps unsized types out of every position that needs a size.

## Dean's answers (2026-11-22)

1. **Emptying.** Taking the contents out is `release` (or `remove`), and it leaves the box invalid until it is filled with another compatible value (section 1). Widening stays an explicit call, renamed from `erase` to `widen` (section 3).
2. **Forwarding.** Whatever is placed in a box must be proved to expose the concept's interface and forward directly to the object, with no run-time checks (section 4). So there is no run-time type check for binary requirements, which stay uncallable through a box.
3. **Where the work goes.** Yes: `box t` is built with the `Pia.Mem` work, and `vec` must hold `box t` values. A `vec (box c)` is the most valuable result, so the implementation order aims at it.


## Amendment, 2026-11-26: a `box c` knows its object's size and drop

Dean (2026-11-26): "`box<Concept> c` should have a special implementation where the size of the element placed in the tag is known, and a reference to the drop function for the item is also known. This would be like a `unique_ptr<T>` with an allocator that knows how to dispatch to the delete implementation of T, but instead of a vtable we have an explicit ref to the type's drop implementation."

So a `box c` is not a tagged union of values, as step 5 built it. It owns its object the way a `box t` does, through a slot, and carries what an owner needs to end it without knowing what it holds:

- **The object's place.** The slot that `make` allocated for the `box t`, kept by `widen`: the object is not copied into the box.
- **Its size and alignment**, in bytes, of the type `widen` was given. A container that moves or frees the object, such as an allocator that frees one by one or a `vec (box c)` that copies its slots when it grows, uses them without a switch.
- **A reference to that type's `drop`**: the instance of `drop` for the boxed type (`drop<square>`), or a function that does nothing for a type with no drop. Dropping a `box c` calls it on the object, then gives the slot back to its allocator if the allocator frees one by one.
- **A reference to each of the concept's requirements** for the boxed type, so a requirement's call through the box is an indirect call, as Rust's `dyn Trait` does through its vtable. The size, alignment, drop and requirement references live in one static table per type and concept, shared by every box of that type, and the box holds a reference to the table (Dean, 2026-11-27); [ADR 0071](0071-function-references.md), section 6, says how tables are made, consolidated and checked, and section 6a how the REPL redefines them. This replaces step 5's tag and switch; a call is still direct where the compiler can see what the box holds.

What the verifier sees does not change: the contents are still an abstract value, and a requirement's result on the box is still the erased requirement's. Dropping a `box c` requires it full, as dropping a `box t` does, and `remove` and `free` for `box c` follow, so a `box c` can be emptied (closing the gap that a `box c` is always full).

The size and drop also serve ADR 0048's inline slots: a buffer of inline `box c` slots stores each element's table reference next to it, so moving, dropping and calling elements needs no switch.

Implementation, replacing step 5's representation:

1. **Function references in code generation**: a function's address as a value, and an indirect call through it, lowered to LLVM.
2. **`box c`'s layout**: the slot and a reference to the type's table (size, alignment, drop and one reference per requirement), made by `widen` from a `box t`; requirement calls go through the table.
3. **`drop`, `remove` and `free` for `box c`**, with `drop` called through the reference; tests that a `box Shape` of a type with a drop runs that drop, from Pia and from C.
4. **Inline `box c` slots** (ADR 0048, section 5) with the size and drop kept per element.

Step 6's cross-module ABI is then the box's layout above: an importer calls a requirement or the drop through the box's table, whose layout is published with the concept ([ADR 0030](0030-published-object-layouts.md)).

## Note, 2026-11-27: a box over a concept as an error payload

Dean (2026-11-27), on the roadmap's C++ interop: "There should be a way to box an error (or have the error constructor host a concept box that then subsumes the C++ exception interface)", needed before 0.1.0.

Nothing new is decided here: this records that the rules above already give it. A constructor's payload may be any sized type, and `box c` is sized (it is the box, not what it holds), so an error set may have a case that carries one:

```ocaml
let io_error = type | Closed | Cxx of box Exception
```

- **The set stays closed** ([ADR 0028](0028-error-propagation-and-cleanup.md)). Its cases are a fixed list, so a handler still covers exactly the errors that can reach it. Only the payload of `Cxx` is open: any type that meets `Exception` can be boxed into it, from any module once boxes go through tables.
- **Raising** is `Err (Cxx (widen b))` from a full `box t`, and `widen` runs the use check for `t` (section 3), so each type's requirement contracts and one-value laws are proved once, where it is boxed.
- **Handling** binds the box, `| Cxx e -> code e`, and calls through it are proved as in section 5: from `Exception`'s contracts and laws, never from which type was boxed.
- **C++ exceptions** (0.5, with the C++ FFI) are then a library concept `exception` with `what` and the nested exception as single-receiver requirements, and a generated shim at each bound C++ call that catches, boxes what it caught into the error set's `Cxx` case, and returns it as an `Err`. It is `std::exception_ptr` with the interface checked. There is no downcast (section 6): a handler that must tell C++ types apart asks through a requirement of the concept.

As built: tests/verify/box_error_payload.pia proves an error set whose `Cxx` case holds a boxed `not_found` or `overflow`, passed on by `?` and handled through the box, and tests/codegen/box_error_payload.pia runs it from C. Within a module this uses step 5's tagged union. A payload boxed in one module and handled in another needs the amendment's tables, ADR 0071's section 6, which come next. A payload whose type has a drop is not dropped through the box until the amendment's step 3.

## Amendment, 2026-11-27: a `box c` is one cache line, with small objects inline

Dean (2026-11-27), so that a `box c` can be made in one module and used in another, which the boxed error payloads of the note above need before 0.1.0: the box holds a reference to a descriptor generated for the boxed type and hidden from the language, "the aligned storage laid out at the end of the box ... proved and computed to have the maximum bytes that fit in a cache line, and for anything bigger we have a pointer to a block that's been allocated at construction time of the object. Every box should have a lease on the allocator and the allocator must outlive the box provably. This is the small object optimisation."

**The problem it solves.** A buffer of records compiles to one buffer per field ([codegen](../codegen.md)), and a box's slot is a buffer of one record, so a boxed `rect` is two pointers, one per field. A descriptor shared by every box of a type cannot say where one box's fields are, and a box holding one pointer per field has a size that depends on what it holds. Step 5's tagged union got around this by copying the fields into the box, which works only while one module knows every type it holds.

**The layout.** A `box c` is one cache line of the target (`Target.cache_line`, ADR 0049: 64 bytes on x86_64 Linux, 128 on Apple silicon), aligned to it:

- a reference to the boxed type's **descriptor**;
- the **lease**: a borrow of the allocator the box was made from, so the borrow rules ([ADR 0042](0042-lifetimes-liveness-and-escape-analysis.md)) prove the allocator outlives the box. An allocator with no fields leases in no bytes;
- the rest, the **inline storage**. A type whose size and alignment fit is stored there, in its C layout ([ADR 0030](0030-published-object-layouts.md)'s `c`: fields in declaration order, each at its natural alignment), with offsets codegen deduces from the type. A larger type works as a C++ string's small-buffer optimisation does (Dean, 2026-11-28): the inline storage holds a pointer to the object instead. When `box.make` needs memory for it, it allocates one block through the lease, whose first part is the box's control block (the descriptor reference and the lease) and whose rest is aligned storage for the object, so the control block and the data are colocated. The object's offsets in that storage still come from the descriptor, as they do inline.

Whether a type is inline is decided by its size, so the descriptor knows it and the box has no run-time flag. `size_of t <= capacity` is a fact codegen computes per target, as `size_of` is today (ADR 0035). Nothing is written on the type, and every type can be boxed: buffers of records elsewhere stay one buffer per field, which is what vectorises.

**The descriptor** is ADR 0071's table (section 6), one link-once constant per type and concept, `pia$t$<type>$<concept>`, unreachable from Pia: the type's size and alignment, whether it is inline, a thunk that drops the object at an address (and, out of line, gives the block back through the lease), and one thunk per requirement callable through a box, taking the object's address in the receiver's place. A call through a box loads the thunk and calls it, one indirection, as Rust's `dyn` does and without C++'s hop from the object to its vtable pointer. Where the compiler can see which descriptor a box holds, as right after it is made, the call is direct. To the verifier a call through a box is a proxy carrying the requirement's contract (the `pia.proxy` pattern of ADR 0071), so proofs through a box do not change.

**Making and moving.**

- `box.make alloc v : result (box c) oom` makes a `box c` from a value of any type that meets `c`, running the use check as `widen` does (section 3). It can fail only for a type too large for the inline storage, and for one that fits it ensures `Ok`, so callers prove that case needs no handler. `widen` from a full `box t` stays, for code that already holds one.
- Moving a box copies its cache line, which is sound because a Pia value never points into itself (ADR 0042).
- Dropping a box calls the descriptor's drop, then ends the lease.
- **Taking out** (Dean, 2026-11-28). Taking the object out of a `box c` names the type expected, and fails when the box holds another, as matching a variant's case can. It always copies or moves the object into new storage of the caller's, never hands out the box's own storage, so the box's control block can be reused. An object held out of line gives its block back to the allocator through the lease when it is taken, so nothing leaks, and the box keeps a control block of the minimum size from the same allocator until it is refilled.
- **An empty box** is like a unit value: its descriptor reference points to one statically allocated control block per concept, the default state and the proxy's reference while the box is empty. A box is never left with a dangling descriptor, and filling it again swaps in the new type's.

**Across modules.** The descriptor's layout is the concept's: its requirements in declaration order after the fixed entries, published with the concept ([ADR 0030](0030-published-object-layouts.md)). So an interface may show a `box c`, a module may box values of a concept it imports, and step 5's refusals go. A `box c` is part of each target's ABI as one cache line; to C it is an opaque, aligned block of that size, and C code calls into it only through Pia.

This replaces step 5's tagged union, and ADR 0048 section 5's inline slots sized to the widest widened type: a buffer of `box c` is a buffer of cache lines.

Implementation:

1. **The layout within a module**: `box c` as a cache line with the descriptor reference, the lease and the inline storage; `make` and `widen` storing inline or out of line; calls and drops through the descriptor; direct calls where it is known. tests/codegen/box_concept.pia and box_error_payload.pia move to it, with C harnesses that treat the box as an opaque block. (Done for objects that fit inline, PR #540: the descriptor, the inline object, calls through it and direct where known. Taking out is done for objects inline, in tests/verify/box_concept.pia and tests/codegen/box_concept.pia, with the empty box (Dean, 2026-11-28): for each type the module widens, `take b d` moves the object into the caller's empty `box t`, and `consume<t> b` copies it to the stack, when the box's descriptor is that type's. Both leave `b` empty, its descriptor the concept's static control block, and IRGen treats `b` as moved from in their `Ok` arms, so it cannot be used until it is assigned again; a mismatch is `Err Mismatch` and leaves `b` full. So a `box c` is full wherever it can be used, and a call through one needs no proof that it is (Dean's choice, which replaces section 1's `box.full` requirement for `box c`). Only a local or a `moved` parameter can be left empty. Descriptors are link-once, so the address comparison holds across modules. The lease (Dean: the allocator's address and a table for its type, as `std::pmr`), objects out of line and drops through the descriptor are still to come.)
2. **Across modules**: an interface shows a `box c`, and a test boxes an error payload in one module and handles it in another. (Done, in tests/modules/box_across.pia: each module makes the box from the concept, so a module that imports a concept boxes values of its own types in it. The box's theory over the box is taken as consistent when the same axioms over a one-byte shape are, which the verifier checks, since they speak of one box at a time and never of its words (#563). Requirement types that name the concept's module's own types are not read through an import yet.)
3. **Buffers of boxes**: `vec (box c)` over cache-line elements.

## Amendment, 2026-11-28: a theory of a box's state

Dean (2026-11-28): a box needs a theory that checks an instance keeps its invariants within a scope, and makes its postcondition deterministic where it escapes. The move checker alone tracks only locals, so an empty box could not be handed through an `inout` parameter, a result or a slice element, and nothing in a proof said what state a box leaves a function in.

**The theory.** Each concept's generated theory, `erased_C`, gains a box's state as spec-only functions of the box, with no run-time cost:

- `full b`, the box holds an object, and `holds_t b` for each type `t` the module boxes: it holds a `t`.
- Axioms: `holds_t b ==> full b`, and `holds_t b ==> not holds_u b` for two types `t` and `u`, so a box holds at most one type.
- `widen` and `box.make` ensure `holds_t result`. The empty box ensures `not full result`.
- `take b d` and `consume<t> b` ensure, on `Ok`, `not full b` (and `d` full), and on `Err`, `full b = old (full b)` with every `holds` unchanged: a mismatch leaves the state as it was.
- A call through a box requires `full b`, a goal discharged from the box's stated or tracked state.

**Every contract states the state** (Dean, 2026-11-28, on a card, over a default of `full`). There is no default invariant. A function that takes a box states its state in a `requires` (`requires full b`), and one that hands a box out, as a result, an `inout` or `out` parameter, or a store into a buffer the caller sees, states the state it leaves in an `ensures` (`ensures full result`, `ensures not full b`, `ensures holds_square result`). A box in a signature with no such clause is an error that names the clause to add. So the state of every box is explicit at every boundary, and the caller learns it from the contract alone.

**The invariant in a scope.** Inside a body the verifier tracks a box's state through the theory as it does any spec function, starting from the `requires`. A box may be emptied and refilled within a scope, and each use is checked against the state at that point. The move checker keeps its error for a local used after `take` (clearer than a failed goal), and the theory covers everything else: parameters, results, fields and slice elements.

**Where it escapes, the postcondition is deterministic.** Where a box leaves a function, the verifier proves the state its `ensures` names on every path, so the state the caller receives is the one the contract names and never a "maybe". A state that differs between paths is stated as a condition, as `take` does (`match result with | Ok -> not full b | Err _ -> ...`). An empty box in a slice element is described by a quantified clause over the slice.

**Soundness.** The empty box is made only inside `take` and `consume`, whose contracts state that the box is empty, and every other function states the states it relies on and leaves, so no proof assumes a state the contracts do not give it.

**Migration.** Box signatures without a state clause were accepted before, so this is a breaking change: a migration rule (ADR 0073) adds `requires full b` for each box parameter and `ensures full result` for a box result, which is what every such program assumed.

Implementation:

1. `full` and `holds_t` in `erased_C`, with the axioms; `widen`, `take`, `consume` and the empty box state them; calls through a box require `full`.
2. The state clause required on every box in a signature, with the migration rule that adds `full`.
3. Quantified states over buffers of boxes, with `vec (box c)` (the amendment's step 3).
