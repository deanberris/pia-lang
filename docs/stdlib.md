# The standard library and its core

Status: proposal, 2026-11-21. Nothing here is implemented yet. Once the open questions at the end are settled, the decisions should go into an ADR.

This page answers one question: **what is the smallest set of things the compiler has to provide, so that everything else in the standard library can be written in Pia and proved like any other Pia code?**

## Principle

A feature belongs in the core when one of these is true:

1. **Pia cannot express it.** It needs a machine instruction, an OS call, or memory that Pia has no way to describe. Examples: shifts, allocating memory, writing to a file.
2. **The verifier must know what it means.** The solver needs its semantics as axioms, not as a body to walk. Examples: `len`, `old`, wrapping arithmetic, the meaning of a buffer that has been freed.
3. **It shapes the language.** Other code cannot be written without it. Examples: modules, generics, sum types.

Everything else goes in the library, written in Pia, with contracts, and proved when the library builds. This is the same split as Rust's `core`, `alloc` and `std`. It is also how Zig and OCaml work: the library is ordinary code, and the compiler provides a short list of builtins (`@` builtins in Zig, `external` primitives in OCaml). What Pia adds is that every library function carries a contract the compiler has proved. That also asks things of the core that an unverified language does not need: specification functions and lemmas (see [Verification primitives](#verification-primitives)).

The prelude already works this way for operators ([ADR 0008](adr/0008-operators-via-metaprograms.md)). `+` is a metaprogram that expands to the core builtin `add`, and the builtin is what the verifier and codegen understand. The proposal extends that pattern to the rest of the library.

## What the core has today

| Area | Core today |
| --- | --- |
| Arithmetic builtins | `add` `sub` `mul` `div` `rem` `add_sat` `sub_sat`, with `@overflow(proof\|wrap\|saturate\|trap)` |
| Comparison and logic | `eq` `ne` `lt` `gt` `le` `ge`, `and` `or` `implies` `iff` |
| Buffers | `len`, indexing `xs.[i]`, fixed arrays `[T; n]`, slices `[T]` |
| Contracts | `requires` `ensures` `assert` `assume` `old` `forall` `exists` `invariant` `decreases` |
| Types | bounded integers, range types `int{lo..hi}`, `bool`, records, type aliases |
| Meta builtins | `map` `fold` `length` `fields` `name` `concat`, quotes and splices |
| Prelude | operator declarations, `fold_and`, `derive_eq`, held as a C++ string in `src/syntax/Prelude.cpp` |

That is enough for the edge detection demo (`examples/edges`), but not for a library. The gaps that block one, roughly in order of how much they block:

- **No modules or imports.** A library cannot be imported, so every program would have to paste it in. This is milestone M8 ([ADR 0010](adr/0010-modules-interfaces-and-proof-certificates.md)).
- **No generics.** Every function is for one concrete type. This is M9 ([ADR 0009](adr/0009-generics-concepts-adapters.md)).
- **No sum types or `match`.** So there is no `option` or `result`, and no way to return an error.
- **No bitwise operators or shifts.** Hashing, checksums, bitsets, UTF-8 and the PNG codec in M13 all need them.
- **No memory allocation, and no calls to the outside world.** All memory comes from a C caller, and there is no I/O. The edge demo needed a C `main` for this reason.
- **No calls inside contracts.** A call in a contract is an unknown value ([verifier.md](verifier.md#limits-of-v0)). So a library cannot state `ensures sorted xs`, or `ensures result = sum xs`.
- **No slicing `xs.[a .. b]`, no buffers of records, no constant arrays, no function values.**

## The proposed minimal core

The core is grouped by what each group unlocks in the library. **★** marks what the first useful library (`core`, below) cannot do without.

### 1. Modules and the prelude as a module ★

- `module`, `interface`, `import` as already designed in M8. The library is a set of modules: `Pia.Core`, `Pia.Mem`, `Pia.Io` and so on.
- The prelude becomes a real Pia module, `Pia.Prelude`, which every module imports implicitly. Today it is a C++ string. Moving it makes the operators ordinary library code, and lets the library be versioned with the compiler.
- Proof certificates ([ADR 0010](adr/0010-modules-interfaces-and-proof-certificates.md)) apply to the library like any other module. A program proved against `Pia.Core`'s interface keeps its proof until that interface changes.

### 2. Integer primitives ★

New builtins, each one or two MLIR ops, with exact SMT semantics (`bvand`, `bvshl` and so on):

| Builtin | Meaning | Goal raised |
| --- | --- | --- |
| `band` `bor` `bxor` `bnot` | bitwise logic on unsigned types | none |
| `shl` `shr` | shifts | `shift < bits t`. `shl` in proof mode also proves no bits are lost |
| `rotl` `rotr`, `clz` `ctz` `popcount` | bit counting and rotation, through LLVM intrinsics | none |
| `narrow e` | narrowing conversion, the explicit form of what assignment does now | the value fits |
| `wrap_to t e`, `sat_to t e` | conversion with a stated overflow mode | none |
| `bits` `from_bits` | reinterpret, once floats exist | none |

The operators `land` `lor` `lxor` `lsl` `lsr` (OCaml's names), or `&` `|` `^` `<<` `>>`, then go in the prelude as metaprograms, like `+` today.

Everything else about integers is library code: `min`, `max`, `clamp`, `abs`, `gcd`, `isqrt`, `ilog2`, checked or wrapping helpers, `is_power_of_two`, `align_up`.

### 3. Sum types and `match` ★

These are already designed (`let shape = type | Circle of f32 | ...`). Implementing variants and an exhaustive `match`, encoded as Z3 datatypes as [design.md](design.md#type-system) describes, unlocks `option`, `result`, `ordering`, and every API that can fail. Without them, the library can only report errors through out-parameters and flags.

### 4. Generics and concepts ★

M9 as designed: type parameters, concepts with laws, monomorphisation before verification. `Eq`, `Ord`, `Hash` and `Numeric` are then library code, and so are `@derive(ord, hash)`, written as metaprograms next to `derive_eq`.

There is a stopgap until M9 lands: metaprograms that stamp out one instance per type, for example `instantiate_sort u8`. The meta engine can already generate functions, so this works today. It gives a monomorphic library that can later be rewritten over generics without changing what callers write.

### 5. Verification primitives ★

This group has no counterpart in an unverified language's core. Without it, the library can be *safe* (in bounds, no overflow), but it cannot be *specified*. A `sort` could not promise that its result is sorted.

- **Specification functions.** `let spec sorted (xs : [i32]) : bool = forall (i in 1..len xs). xs.[i - 1] <= xs.[i]`. A spec function is pure, total and side-effect free. It may be used in contracts, and the verifier gives its definition to Z3: as a macro when it is not recursive, or as `define-fun-rec` with its `decreases` measure when it is. This removes the "calls inside contracts are unknown values" limit. Dafny, F* and SPARK (whose expression functions play this role) are built on the same idea.
- **Lemmas.** `let lemma sum_split (xs : [u8]) (k : usize) : unit requires k <= len xs ensures sum xs = sum_to xs k + sum_from xs k = ...`. A lemma is proved once, and a call to it adds its postcondition at the call site. It is what makes proofs about loops and recursion scale. The edge demo showed the need: it took `assert` stepping stones before Z3 could prove simple bounds within its timeout.
- **Ghost values**, possibly later. Locals and parameters that exist only in the proof, such as a model `seq<T>` of a vector's contents, erased by codegen like contracts are today. SPARK's formal containers use exactly this pattern: each container has a mathematical model, and its contracts are written against the model.
- **Permutation and multiset reasoning**, possibly later. `ensures permutation xs (old xs)` is the other half of a sort's specification. It can be a spec function over counts first, with a dedicated encoding only if Z3 struggles.

### 6. Buffers ★

- **Slicing** `xs.[a .. b]`, as a view with proved bounds. The library cannot split work, recurse on halves, or return part of a buffer without it.
- **Constant data**: array literals and module-level constant arrays (`let crc_table : [u32; 256] = ...`), placed in read-only data. Many library algorithms are table driven.
- **Buffers of records** in codegen, which the scalariser does not lower yet.

### 7. Memory

Pia does not allocate. The core needs one primitive, and the ownership modifiers that already exist give it a contract:

```ocaml
(* Pia.Mem, provided by the runtime *)
let alloc (t : type) (n : usize) : moved out mutable [t]   (* result: len = n, every element unwritten *)
let free  (buf : moved inout [t]) : unit                   (* buf is dead after the call *)
```

- `moved` already means that the caller cannot use the buffer after the call, so use after free and double free are type errors, not proof goals.
- `out` already means "written before it is read", so reading uninitialised memory is a proof goal.
- Running out of memory is either a trap (`@overflow(trap)` style, visible in the contract) or a `result`, once sum types exist. The library can offer both.

On top of these, `vec`, `string`, `hash_map`, a binary heap (priority-flood in the flagship demo needs one) and an arena allocator are library code. They are the first place where specification functions and ghost models (group 5) pay off: `push` ensures `model result = append (model old) x`.

### 8. The outside world

The core needs a way to call a C function, plus a policy that says what the verifier may assume about it:

```ocaml
extern "C" let write (fd : i32) (buf : [u8]) : isize
  ensures result <= len buf
```

- An `extern` contract is **trusted, not proved**. It is listed in the module's interface the way `@assume` is, so `piac` can print the trusted base of any program.
- The OS surface the library needs is small: `read`, `write`, `open`, `close`, `exit`, `clock_gettime`, `getenv`, and `malloc`/`free` behind `Pia.Mem`. `Pia.Io`, `Pia.Fs`, `Pia.Time` and `Pia.Process` wrap these in Pia, with stronger contracts proved over the trusted ones.
- `main` becomes something Pia can export, `let main (args : [[u8]]) : i32`, so a program no longer needs a C wrapper.
- `abort` and `unreachable`: `abort` has the precondition `requires false` in proof mode, so every call to it is a proof that it cannot happen, or a visible `--allow-unproved`.

### 9. Later, driven by milestones

- **Floats (M11)**: `f32` and `f64` builtins, `sqrt`, `fma`, conversions, and the three reassociation choices from [ADR 0012](adr/0012-floating-point-reassociation.md). The math library (`exp`, `log`, `sin`) is then Pia, with error-bound contracts where they can be proved.
- **Function values and closures**: `map`, `fold` and comparator-based `sort` over function values. Until then, generics plus concept instances (`Ord t`) cover most needs, which is also what lets them monomorphise and vectorise.
- **`vec<T, k>` (M10)** and its lane intrinsics: `splat`, `load`, `store`, `fma`, shuffles.
- **Concurrency (M12)**: `spread` and the collectives, which ADR 0014 already places in a library (`Pia.Par.Collectives`) on top of a few runtime primitives.

## The library, layer by layer

| Layer | Needs from the core | Contents (all Pia) |
| --- | --- | --- |
| `Pia.Prelude` | modules | operators, `derive_eq`, later `derive_ord` and `derive_hash` |
| `Pia.Core` | groups 1 to 6 | `option` `result` `ordering`; `Eq` `Ord` `Hash` `Numeric`; integer utilities; slice algorithms (`fill` `copy` `equal` `find` `reverse` `rotate` `binary_search` `sort` `partition`); fixed-capacity containers (`array_vec`, `bitset`, `ring`); `crc32` `adler32` `fnv`; UTF-8 validation; formatting integers into a buffer and parsing them |
| `Pia.Mem` | group 7 | `alloc` `free`, `vec`, `string`, `hash_map`, `heap`, `arena` |
| `Pia.Io`, `Pia.Fs`, `Pia.Time`, `Pia.Process` | group 8 | buffered reader and writer, files, clocks, `args`, `exit` |
| `Pia.Math` | floats | elementary functions with error bounds |
| `Pia.Par` | M12 | `spread`, collectives |
| `Image.Png`, `Image.Gif` | all of the above | M13: zlib/deflate, CRC, the PNG and GIF codecs |

`Pia.Core` needs no allocator and no OS, like Rust's `core`, so it can run anywhere the compiler targets, including a GPU kernel later on.

Every function in every layer has a contract that is proved when the library builds. Proved means at least the strongest-guarantee defaults (no overflow, in bounds, terminates). Where specification functions allow, it also means functional correctness: `sort` returns a sorted permutation of its input, and `binary_search` finds the element if it is there.

## Suggested order

Each step unlocks a usable slice of the library, and the order follows the roadmap:

1. **Integer primitives, slicing, constant arrays, `abort`.** Small compiler changes, and enough to write checksums, bit utilities and slice algorithms as a single-file library.
2. **Spec functions and lemmas.** So the library can be specified as it is written, and not retrofitted later. This also answers the solver-timeout problem the edge demo hit.
3. **Modules (M8)**, with the prelude moved into Pia. `Pia.Core` becomes importable.
4. **Sum types and `match`.** `option`, `result`, and fallible APIs.
5. **Generics (M9).** Rewrite `Pia.Core` generically. The metaprogram-instantiated versions from step 1 show what the generic versions must match.
6. **`extern`, `main` and `alloc`/`free`.** `Pia.Mem` and `Pia.Io`. Programs no longer need a C wrapper, and the edge demo can read and write BMP files in Pia.
7. **Floats (M11), `vec` (M10), concurrency (M12)**, then the image codecs (M13) for the flagship demo.

Steps 1 and 2 need neither M8 nor M9, so they can start now, alongside M8.

## Open questions

- **Operator spellings for bit operations**: OCaml's `land` `lor` `lsl`, or C's `&` `|` `<<`. Pia already uses `||` and `&&` for logic, so `|` and `&` would read as their bitwise forms.
- **Where trusted contracts live.** `extern` contracts and `@assume` are both trusted. Should the certificate list them, so the linker can report the whole trusted base of a binary?
- **Allocation failure**: trap by default, or `result` by default? The strongest-guarantee principle ([ADR 0004](adr/0004-strongest-guarantee-by-default.md)) suggests `result`, with a trapping variant clearly named.
- **Spec function encoding**: `define-fun-rec` lets Z3 unfold recursive definitions, but unfolding can blow up. Dafny-style fuel limits, or explicit lemmas only?
- **Is `seq<T>` a core type**, or a library type whose model is an SMT array plus a length? A core type gives the verifier one canonical encoding. A library type keeps the core smaller.
