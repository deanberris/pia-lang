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
    - `get`, `get_mut` and every call through a box require `box.full b`, proved where they are used. An empty box is invalid until it is filled, and using it is a failed goal, not a run-time check.
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

So a `box c` is not a tagged union of values, as step 5 built it, and not a pointer to a table, as section 7 sketched it. It owns its object the way a `box t` does, through a slot, and carries what an owner needs to end it without knowing what it holds:

- **The object's place.** The slot that `make` allocated for the `box t`, kept by `widen`: the object is not copied into the box.
- **Its size and alignment**, in bytes, of the type `widen` was given. A container that moves or frees the object, such as an allocator that frees one by one or a `vec (box c)` that copies its slots when it grows, uses them without a switch.
- **A reference to that type's `drop`**: the instance of `drop` for the boxed type (`drop<square>`), or a function that does nothing for a type with no drop. Dropping a `box c` calls it on the object, then gives the slot back to its allocator if the allocator frees one by one. It is a direct reference to one function, not a table: there is no table of the concept's functions.
- **A tag** saying which of the module's widened types it holds, for calls of the concept's requirements, which stay a switch on the tag within a module (step 5), and a direct call where the tag is known.

What the verifier sees does not change: the contents are still an abstract value, and a requirement's result on the box is still the erased requirement's. Dropping a `box c` requires it full, as dropping a `box t` does, and `remove` and `free` for `box c` follow, so a `box c` can be emptied (closing the gap that a `box c` is always full).

The size and drop also serve ADR 0048's inline slots: a buffer of inline `box c` slots stores each element's size and drop next to it, so moving and dropping elements needs no switch.

Implementation, replacing step 5's representation:

1. **Function references in code generation**: a function's address as a value, and an indirect call through it, lowered to LLVM.
2. **`box c`'s layout**: slot, size, alignment, drop and tag, made by `widen` from a `box t`; requirement calls switch on the tag as before.
3. **`drop`, `remove` and `free` for `box c`**, with `drop` called through the reference; tests that a `box Shape` of a type with a drop runs that drop, from Pia and from C.
4. **Inline `box c` slots** (ADR 0048, section 5) with the size and drop kept per element.

Step 6's cross-module ABI is then the box's layout above, plus a way for an importer to call a requirement through a box whose types it does not know. That needs a decision of its own.
