# 46. A box holds a type or any type meeting a concept, and what it holds is proved to have the concept's shape

Date: 2026-11-22

Status: Proposed

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
- `box.into b` takes the value back out and frees the allocation.
- A box is `Drop`. Dropping it drops the contents and then returns the memory to its allocator. A box of a `@linear` type is itself `@linear`.
- There is no deleter. A different way to free is a different allocator.
- There is no null box. A box that may be empty is `option (box t)`, and the layout ([ADR 0030](0030-published-object-layouts.md)) uses the null pointer as `None`, so it is still one pointer.
- A box stores its allocator. A default allocator from module state ([ADR 0041](0041-allocator-semantics-as-a-theory.md)) has no fields, so with one, `box t` is a single pointer.

`box t` at a concrete `t` is an ordinary generic type. It needs nothing from this ADR beyond `Pia.Mem` storing allocators (ADR 0041, step 5). Every call on its contents is direct, and every proof sees the concrete value.

### 2. A concept in place of a type

A concept applied to all of its arguments but the first names a type: the type of a value of *some* type that meets the concept. `Shape` (from `Shape (t : type) : concept`) and `Function u8 bool` (from `Function f a r`, ADR 0044) are such types. They need no keyword, so the rule adds none.

- **They are unsized.** Their size is not known when the program is compiled, so they may appear only as an argument of a type parameter marked `@unsized`. `box`'s parameter is the only one in the library at first: `let box (@unsized t : type) = ...`. Anywhere else, such as a `let`, a field, a slice element or a parameter, is a type error that suggests `box`.
- **Arrow types are sugar.** `box ((x : u8) -> u8 requires x < 255 ensures result > x)` is a box of `Function` at that arrow type, contract included. That is `Pia.Fn`'s dynamic function value: C++'s `move_only_function`, with its contract in the type.
- **Generic bodies at a concept.** `box Shape` is a concrete type. Code generic over `(t : type where Shape t)` is not instantiated at it, because an erased value is not a `t` that meets `Shape`: a `box Shape` has no `Shape` instance of its own unless an adapter is written for it.

### 3. Erasing is explicit and proves the shape

`box.erase b` turns a `box t` into a `box c`. Pia has no implicit conversions (ADR 0003), so the call is written out. Writing `box.erase b` where a `box Shape` is expected deduces `c` from the expected type.

- **The use check runs there.** `t` must meet `c`, with instances found by argument-dependent lookup and adapters as ADR 0034 finds them. The requirements' contracts and the concept's laws are proved for `t` by the use check, as for any instance, once per type and not once per box.
- **The table.** The erased box stores a pointer to the instance's table, which holds the requirement functions in the concept's declaration order, then `drop`, size and alignment. There is one table per pair of type and concept, emitted as a constant.
- **Restrictions on what can be erased.** A `@linear` value cannot be erased unless the concept requires a consuming function, because the box would hide the obligation to release it. A value that borrows (`borrowed(m)`) cannot be erased, because the box could outlive its lender.

### 4. Only some requirements can be called through a box

A requirement can be called through a `box c` when its concept parameter appears exactly once among its parameters, as the receiver (`in`, `inout` or `moved`), and nowhere in its result. `area : (s : t) -> f32` qualifies. `lt : (a : t) -> (b : t) -> bool` and `clone : (s : t) -> t` do not, because two erased values may hold different types, and an erased result has no size. This is Rust's object safety. Pia has no run-time type information to check that two boxes hold the same type, and adding it would be a separate decision.

A concept whose requirements are all excluded still erases. Only `drop` can then be called through the box, and a program that tries anything else gets an error naming the requirement and the reason.

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

`dyn` stays a closed sum: its tags are listed, a `match` takes it apart, and the prover enumerates its cases. A `box c` is open: any module can erase a new type into it, there is no `match` on what it holds, and no downcast. The two cover the two uses C++ gives `variant` and virtual base classes respectively.

### 7. Code generation and the ABI

- A `box t` is one pointer, and the allocator's fields when it has any. A `box c` adds the table pointer, so it is a fat pointer, as in Rust.
- A call through a box is an indirect call through the table, unless the optimiser can see which table it holds, for example right after `box.erase`, in which case it is a direct call.
- Tables are part of the published ABI ([ADR 0030](0030-published-object-layouts.md), [ADR 0024](0024-published-proof-certificates.md)):
  - a concept's table layout is its requirements in declaration order;
  - the concept's interface hash goes in the certificate;
  - a module whose table for a concept was built against a different version of that concept fails to load until it is relinked, as a changed object layout does.

## Implementation order

1. **`box t` in `Pia.Mem.Box`**, with the work on proved `Pia.Mem` ("Build Pia's core up to a proved Vec"), once allocators are stored (ADR 0041, step 5). This covers `make`, `get`, `get_mut`, `into`, `Drop`, and `option (box t)` as one pointer.
2. **Concepts as unsized types.** Parsing a partially applied concept in type position, `@unsized` parameters, the error everywhere else, and arrow types as `Function`.
3. **`box.erase`.** The use check at erasure, tables as constants, the `@linear` and borrow restrictions.
4. **Calls through a box.** The receiver rule, the verifier's one sort per box, contracts and laws as hypotheses, havoc after `inout`, and purity in contracts.
5. **Code generation.** Fat pointers, indirect calls, and devirtualising when the table is known.
6. **The ABI.** Table layout in the published interface, and the loader's check.
7. **`Pia.Fn`'s dynamic function values** as `box` at arrow types, and the library's handler tables.

## Consequences

- C++'s `unique_ptr`, virtual base classes, `std::function` and `move_only_function` become one type with one set of rules. Whatever a box holds is proved, statically, to meet the concept it is boxed as, laws included, which C++ cannot check for a derived class.
- A box over a concept has the same proof cost as a generic body: requirement contracts and laws, proved once per type at the use check. No proof re-runs per box.
- Binary requirements such as `lt`, and requirements returning the concept's type, cannot be called through a box. Code that needs them uses generics, or a concept written for the erased use.
- Pia gains its first unsized type. The `@unsized` marker keeps unsized types out of every position that needs a size.

## Questions for Dean

1. **Erasing.** Should `box.erase b` be written explicitly, as recommended, since Pia has no implicit conversions? Or should a `box t` convert to `box c` wherever a `box c` is expected?
2. **Binary requirements.** Should calls through a box be limited to requirements with one receiver, as recommended and as Rust does? The alternative is a run-time check that two boxes hold the same type, which needs a type identity in the table.
3. **Where the core work goes.** `box t` (step 1) needs stored allocators from the `Pia.Mem` work. Should it be built there, with steps 2 to 7 in the standard library work, as recommended?
