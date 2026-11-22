# 47. Recursive sum types are explicit, recurse through an owning indirection, and share through strong and weak references

Date: 2026-11-22

Status: Proposed

## Context

Pia has records, variants, generic types, and, with [ADR 0046](0046-box-over-a-type-or-a-concept.md), a non-null `box` that owns a value from an allocator it stores. It has no recursive types: a type that mentions itself is "not supported yet" ([status.md](../status.md)). Several pieces of work wait on them:

- **The JSON DOM** ([ADR 0045](0045-json-derived-codecs-and-conforming-dom.md)). Dean decided (2026-11-22) that the DOM is a recursive sum type whose leaves are slices of the input, not a flat tape.
- **Proof by reflection** ([ADR 0036](0036-library-theories.md), [verifier.md](../verifier.md)) needs a datatype of formulas.
- **Trees and lists in the library**: `shared_ptr` and `weak_ptr`, deferred in [ADR 0040](0040-cpp23-standard-library-in-pia.md) section 4 until there were atomics and "a proof that cycles cannot leak, which needs recursive types".

Dean's requirements (2026-11-22): algebraic sum types support recursion *explicitly*, and once there is a box type, there is a reference and a weak reference type that use a concept for recursive types. Earlier decisions constrain the design: no garbage collection, ever ([ADR 0026](0026-memory-manager.md)); every allocation can fail and is handled at its call site; no implicit conversions ([ADR 0003](0003-static-typing-with-tagged-dyn.md)); fewer keywords; `Drop`, `@linear` and borrows decide when memory is freed; and proofs must stay cheap ([ADR 0032](0032-parallel-sliced-cached-proving.md)).

### Prior art

- **OCaml, Haskell and F#** make every type definition recursive implicitly, and allocate constructors on a garbage-collected heap. OCaml marks recursion for values with `let rec` and for types with `type nonrec` (the opposite default).
- **Rust** rejects a type of infinite size ("recursive type has infinite size, insert some indirection") and accepts recursion through `Box`, `Vec`, `Rc` and `Arc`. `Rc<T>`/`Weak<T>` share with counts; cycles of `Rc` leak, and avoiding them is left to the programmer. `Rc::get_mut` gives a mutable reference only when the count is one.
- **Swift** has `indirect enum` (a keyword) and ARC with `weak` and `unowned`.
- **Z3 and SMT-LIB** have algebraic datatypes (`declare-datatypes`), including mutually recursive ones, with constructors, testers and accessors. **Dafny** and **F\*** encode inductive datatypes this way and prove termination by a well-founded "rank" on datatype values.
- **Koka** and **Lean 4** use reference counting with reuse ("Perceus", "counting immutable beans"): shared values are immutable, mutation in place happens when the count is one, and cycles cannot be built from immutable values.

## Decision

### 1. Recursion is explicit: `let rec` on a type

A type that refers to itself is declared with `let rec`, the form functions already use, so there is no new keyword:

```ocaml
let rec tree = type
  | Leaf
  | Node of { left : box tree; key : u32; right : box tree }

let rec json = type
  | Null | Bool of bool | Num of str | Str of str
  | Arr of vec json
  | Obj of vec (str, json)
```

- Without `rec`, a type that names itself is an error that suggests `let rec`. A `let rec` type that does not name itself is a lint (`needless_rec`).
- **Mutual recursion** is a group of `let rec` types that refer to each other. Every type in the cycle must be marked, so a reader can see which types are recursive from their declarations.
- **Generic recursive types** take type parameters as usual: `let rec list = let (t : type) => type | Nil | Cons of (t, box (list t))`. The recursive occurrence must use the same arguments in the same order (regular recursion), which is what Z3's datatypes and codegen's layouts need. Nested, non-regular recursion (`box (list (t, t))`) is an error.

### 2. Every recursive occurrence goes through an owning indirection

A recursive occurrence must sit inside a type that holds its argument behind a pointer, so every type keeps a size known when the program is compiled:

- **Indirections are recognised by a concept.** The prelude declares `Indirect`, a concept on one-argument type constructors whose layout does not depend on their argument: `box`, `vec`, `ref` and `weak` (section 5) meet it, and so does a library type that holds its argument only behind pointers and states the concept. An occurrence anywhere else, such as a field of type `tree` or a fixed array `[tree; 2]`, is an error that suggests `box`. This is the "concept for recursive types" Dean asked for.
- **Ownership is unchanged.** `box` and `vec` own their contents uniquely, so a `tree` is a tree of unique owners and is dropped exactly once, as any other value is. Moves, borrows and `@linear` work as for non-recursive types.
- **A box over a concept** (`box c`, ADR 0046) may also be an indirection, for open recursion such as an expression tree whose nodes are any type meeting `Expr`. Each such box has its own abstract sort, so the verifier knows only the concept's contracts about what it holds, and structural reasoning (section 3) does not see through it.
- **Every recursive type must be inhabited.** At least one constructor, or a path through `option` or an empty `vec`, must build a value without already having one. Since `box` is never null, `let rec l = type | Cons of (u8, box l)` has no values and is an error.

### 3. Proofs: recursive variants are datatypes

- **Encoding.** The verifier encodes a recursive variant as an SMT-LIB datatype, mutually recursive types as one `declare-datatypes` group, and generic ones per instance as today. `box t` and `vec t` are encoded by their contents (a `box t` is its `t`, a `vec t` its sequence), because they own their contents uniquely, so the proof sees a recursive value as a value, not as a heap.
- **Structural recursion terminates without a measure.** A recursive function or spec function whose recursive calls are on components of its argument (names a `match` binds below the top, an element of a `vec`) is accepted as terminating, as Dafny does, using Z3's datatype rank. Other recursion needs `decreases`, which may now use the spec builtin `depth v` or `size v` of a recursive value.
- **Spec functions unfold under fuel.** A recursive spec function over a recursive type, such as ADR 0045's `valid_dom` or `conforms`, unfolds `@fuel(n)` levels ([ADR 0036](0036-library-theories.md)), and lemmas proved by structural induction (a tactic like `induction`, [meta.md](../meta.md#tactics)) cover the rest. Goals over recursive values stay as small as their unfolding.
- **Proof by reflection** becomes possible: a datatype of formulas, a total `decide`, and a soundness lemma proved once (ADR 0036, step 6).

### 4. Code generation: layout and a drop that cannot overflow the stack

- A recursive variant is laid out like any variant ([ADR 0030](0030-published-object-layouts.md)): a tag and the largest payload, where a recursive occurrence is a pointer (`box`), a pointer and a length (`vec`), or a counted pointer (`ref`). `option (box t)` is one pointer with null as `None`.
- **Drop runs in constant stack.** The generated drop of a recursive type must not recurse once per level, since a list a million long would overflow the stack. It frees iteratively: it loops along one recursive child, and threads the other children onto a worklist built inside the memory of the nodes it is freeing (each freed node's own pointer slot links the list), so it needs neither recursion nor an allocation. The verifier proves the generated drop terminates and frees each node once, from section 3's encoding.
- **Construction and pattern matching** are as for other variants. Building a `Node` allocates its boxes explicitly (`box.make a v?`), so every allocation in a recursive structure is visible and handled at its call site.

### 5. Shared references: `ref` and `weak`

`Pia.Mem.Ref` provides shared ownership, next to `Pia.Mem.Box`:

- **`ref t`** is a counted box: one allocation holds a strong count, a weak count, the allocator and the value. `ref.make a v` can fail with the allocator's error. `ref.share r` makes another reference and increments the count; it is a function call, never an implicit copy. Dropping the last strong reference drops the value, and dropping the last reference of either kind frees the memory.
- **Shared values are immutable.** `ref.get r` is a `borrowed(r)` read. `ref.get_mut r` requires `ref.unique r` (the strong count is one and no weak reference can upgrade), which the caller proves or checks with `ref.try_unique`, as Rust's `Rc::get_mut` and Koka's reuse do. There is no interior mutability through a `ref`.
- **So strong cycles cannot exist.** A value can only be changed through a unique reference, and while it is borrowed for writing, the borrow rules ([#70](https://github.com/deanberris/pia-lang/issues/70)) stop the program from sharing it, so no reference to a value can be stored inside it, directly or through other values. Every value graph built from `ref`s is acyclic by construction, and every value is freed when its last reference goes. This is the proof ADR 0040 asked for: it follows from the rules, so no program has to prove it. It is stated as a lemma of `Pia.Mem.Ref`'s model, proved once, and the verifier keeps the counts as spec-only state ([ADR 0041](0041-allocator-semantics-as-a-theory.md)).
- **`weak t`** is a reference that does not keep the value alive: `weak.of r`, and `weak.upgrade w : option (ref t)`. Back pointers, such as a tree node's parent, are weak. A cycle that goes through a weak reference is fine, since it never keeps anything alive.
- **Over a concept.** `ref c` and `weak c` share any type meeting the concept `c`, as `box c` owns one (ADR 0046): the table pointer lives in the counted allocation, and the same single-receiver rule applies.
- **Encoding.** Since shared values are immutable, the verifier encodes `ref t` by its value, like `box t`, plus a spec-only identity that `ref.ptr_eq` compares. A `weak t` is an identity and an `option t` that `upgrade` may return.
- **One thread first.** `ref` and `weak` are not `sendable` ([ADR 0027](0027-coroutines-and-race-freedom.md)): their counts are not atomic. A `shared_ref` with atomic counts comes with atomics in M12, with the same rules.

### 6. Metaprograms over recursive types

- Inside a type-level metaprogram, a recursive occurrence appears as the type's name, as `json` appears inside `json`. `is_rec t` is true for a `let rec` type, and `rec_group t` lists its mutually recursive group.
- The totality rule of [ADR 0035](0035-substitution-failure-and-total-constraints.md) treats a recursive occurrence as a leaf: a metaprogram that recursed into it would unfold the type forever, so the checker rejects such a call. A derive that needs to handle recursion, such as `@derive(json)` or `@derive(eq)`, generates a recursive function (`let rec eq_tree ...`) that calls itself where the type recurses, and that function terminates by structural recursion (section 3).

### 7. What this ADR does not decide

- Garbage collection and cycle collection: never ([ADR 0026](0026-memory-manager.md)). Cyclic graphs use weak references, or indices into a pool, which ADR 0040 already uses for node containers.
- Interior mutability (cells inside shared values). It would allow strong cycles, so it is out until a separate ADR shows how to keep values from leaking with it.
- Lazy or infinite (codata) types.

## Implementation order

1. **`let rec` types** in the parser and Sema: the explicit-recursion rule, regular recursion, guardedness through `Indirect` types, the inhabitation check, `needless_rec`.
2. **Verifier**: recursive variants as SMT-LIB datatypes, `box` and `vec` by their contents, structural termination, `depth` and `size`.
3. **Codegen**: layouts with pointer occurrences, construction, matching, and the constant-stack drop, proved. Needs `box t` (ADR 0046 step 1, built in `Pia.Mem` after the ADR 0042 region parameter decision).
4. **Metaprograms**: `is_rec`, `rec_group`, the totality rule, and `@derive(eq)` on recursive types.
5. **`ref` and `weak`** in `Pia.Mem.Ref`, with the uniqueness rule and the acyclicity lemma; [docs/cpp-std.md](../cpp-std.md) maps `shared_ptr` and `weak_ptr` to them.
6. **`ref c` and `weak c`** over concepts, after ADR 0046's concept boxes.
7. **`shared_ref`** with atomics (M12).

The JSON DOM (ADR 0045 step 6) needs steps 1 to 3. Proof by reflection needs steps 1 and 2.

## Consequences

- Recursive types are visible in their declarations, and their memory is visible in their constructors: every node is an explicit, fallible allocation, freed exactly once.
- Recursive structures are proved as values. Shared ones are too, because sharing is immutable.
- Leak freedom of shared references is a property of the library's rules, not of each program. The cost is no interior mutability through `ref`; programs that need a mutable graph use a pool with indices, or weak back references.
- Z3 datatypes make goals over recursive values heavier than goals over flat records. Fuel and structural lemmas keep each goal to a bounded unfolding, and recursive types join the proof benchmark from step 2.

## Questions for Dean

1. **Spelling.** Mark recursive types with `let rec`, reusing the function form so there is no new keyword (recommended), or with an attribute such as `@rec`?
2. **Guards.** Allow recursion only through types meeting the `Indirect` concept (recommended: `box`, `vec`, `ref`, `weak`, and library types that state it), or only through `box`?
3. **Shared mutation.** Keep shared values immutable, with mutation only through a unique reference, so strong cycles are impossible by construction (recommended), or allow interior mutability and prove the absence of strong cycles per program?
