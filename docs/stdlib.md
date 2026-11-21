# The standard library and its core

Status: proposal, 2026-11-21 ([ADR 0023](adr/0023-minimal-core-self-hosted-stdlib.md)). Nothing here is implemented yet. Code blocks show designed syntax.

This page answers one question: **what is the smallest set of things the compiler has to provide, so that everything else in the standard library can be written in Pia and proved like any other Pia code?**

It also covers two requirements that shape the answer:

- **The core calls POSIX directly** and wraps it in strongly typed, contract-constrained Pia functions. There is no C layer between a Pia program and the operating system.
- **Multiplication must be provable.** Today any `*` in a module widens the whole SMT encoding, and loop goals time out ([below](#multiplication-in-the-verifier)). A library full of `width * height` cannot live with that.

## Principle

A feature belongs in the core when one of these is true:

1. **Pia cannot express it.** It needs a machine instruction, an OS call, or memory that Pia has no way to describe. Examples: shifts, calling `read`, viewing a page that `mmap` returned.
2. **The verifier must know what it means.** The solver needs its semantics as axioms, not as a body to walk. Examples: `len`, `old`, wrapping arithmetic, the meaning of a buffer that has been freed.
3. **It shapes the language.** Other code cannot be written without it. Examples: modules, generics, sum types.

Everything else goes in the library, written in Pia, with contracts, and proved when the library builds. This is the same split as Rust's `core`, `alloc` and `std`. It is also how Zig and OCaml work: the library is ordinary code, and the compiler provides a short list of builtins (`@` builtins in Zig, `external` primitives in OCaml). What Pia adds is that every library function carries a contract the compiler has proved. That also asks things of the core that an unverified language does not need: specification functions and lemmas (see [Verification primitives](#5-verification-primitives)).

The prelude already works this way for operators ([ADR 0008](adr/0008-operators-via-metaprograms.md)). `+` is a metaprogram that expands to the core builtin `add`, and the builtin is what the verifier and codegen understand. The proposal extends that pattern to the rest of the library.

The rule from [ADR 0004](adr/0004-strongest-guarantee-by-default.md) applies throughout: the strongest guarantee is the default. The only things taken on trust are the compiler's builtins and the contracts of a short, audited list of POSIX functions. Each of those trusts is named in a proof certificate, so `piac` can print the trusted base of any program.

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

That is enough for the edge detection demo (`examples/edges`), but not for a library. The demo shows the gaps directly: `main.c` reads and writes the BMP files and allocates the buffers, because Pia has no I/O and no allocation, and grayscale is `(r + 2g + b) / 4` rather than BT.601, because one `*` makes its loop goals time out. The gaps that block a library, roughly in order of how much they block:

- **No modules or imports.** A library cannot be imported, so every program would have to paste it in. This is milestone M8 ([ADR 0010](adr/0010-modules-interfaces-and-proof-certificates.md)).
- **No generics.** Every function is for one concrete type. This is M9 ([ADR 0009](adr/0009-generics-concepts-adapters.md)).
- **No sum types or `match`.** So there is no `option` or `result`, and no way to return an error.
- **No bitwise operators or shifts.** Hashing, checksums, bitsets, UTF-8 and the PNG codec in M13 all need them.
- **No memory allocation, and no calls to the outside world.** All memory comes from a C caller, and there is no I/O.
- **Multiplication defeats the solver** once loops are involved.
- **No calls inside contracts.** A call in a contract is an unknown value ([verifier.md](verifier.md#limits-of-v0)). So a library cannot state `ensures sorted xs`, or `ensures result = sum xs`.
- **No slicing `xs.[a .. b]`, no buffers of records, no constant arrays, no function values.**

## The proposed minimal core

The core is grouped by what each group unlocks in the library. **★** marks what the first useful library (`Pia.Core`, below) cannot do without.

### 1. Modules and the prelude as a module ★

- `module`, `interface`, `import` as already designed in M8. The library is a set of modules: `Pia.Core`, `Pia.Mem`, `Pia.Sys` and so on.
- The prelude becomes a real Pia module, `Pia.Prelude`, which every module imports implicitly. Today it is a C++ string. Moving it makes the operators ordinary library code, and lets the library be versioned with the compiler.
- Proof certificates ([ADR 0010](adr/0010-modules-interfaces-and-proof-certificates.md)) apply to the library like any other module. A program proved against `Pia.Core`'s interface keeps its proof until that interface changes. Certificates also list the trusted contracts a module depends on ([group 8](#8-posix-trusted-declarations-and-typed-wrappers)).

### 2. Integer primitives ★

New builtins, each one or two MLIR ops, with exact SMT semantics (`bvand`, `bvshl` and so on):

| Builtin | Meaning | Goal raised |
| --- | --- | --- |
| `band` `bor` `bxor` `bnot` | bitwise logic on unsigned types | none |
| `shl` `shr` | shifts (`shr` is arithmetic on signed types) | `shift < bits t`. `shl` in proof mode also proves no bits are lost |
| `rotl` `rotr`, `clz` `ctz` `popcount` `bswap` | bit counting, rotation and byte swap, through LLVM intrinsics | none |
| `widen e` | to a wider type of the same signedness | none |
| `narrow e` | narrowing conversion, the explicit form of what assignment does now | the value fits |
| `wrap_to t e`, `sat_to t e` | conversion with a stated overflow mode | none |
| `mul_wide a b` | the full product in a type twice as wide, `u32 -> u32 -> u64` | none |
| `bits` `from_bits` | reinterpret, once floats exist | none |

The operators (`land` `lor` `lxor` `lsl` `lsr`, OCaml's names, or `&` `|` `^` `<<` `>>`) then go in the prelude as metaprograms, like `+` today.

Everything else about integers is library code: `min`, `max`, `clamp`, `abs`, `gcd`, `isqrt`, `ilog2`, checked or wrapping helpers, `is_power_of_two`, `align_up`, and byte-order reads such as `u32_be` (PNG is big-endian, BMP little-endian), each with a postcondition the verifier checks against the arithmetic definition.

### 3. Sum types and `match` ★

These are already designed (`let shape = type | Circle of f32 | ...`). Implementing variants and an exhaustive `match`, encoded as Z3 datatypes as [design.md](design.md#type-system) describes, unlocks `option`, `result`, `ordering`, and every API that can fail. Without them, the library can only report errors through out-parameters and flags.

### 4. Generics and concepts ★

M9 as designed: type parameters, concepts with laws, monomorphisation before verification. `Eq`, `Ord`, `Hash` and `Numeric` are then library code, and so are `@derive(ord, hash)`, written as metaprograms next to `derive_eq`.

There is a stopgap until M9 lands: metaprograms that stamp out one instance per type, for example `instantiate_sort u8`. The meta engine can already generate functions, so this works today. It gives a monomorphic library that can later be rewritten over generics without changing what callers write.

### 5. Verification primitives ★

This group has no counterpart in an unverified language's core. Without it, the library can be *safe* (in bounds, no overflow), but it cannot be *specified*. A `sort` could not promise that its result is sorted.

- **Specification functions.** `let spec sorted (xs : [i32]) : bool = forall (i in 1..len xs). xs.[i - 1] <= xs.[i]`. A spec function is pure, total and side-effect free. It may be used in contracts, and the verifier gives its definition to Z3: as a macro when it is not recursive, or as `define-fun-rec` with its `decreases` measure when it is. This removes the "calls inside contracts are unknown values" limit. Dafny, F* and SPARK (whose expression functions play this role) are built on the same idea.
- **Lemmas.** `let lemma sum_split (xs : [u8]) (k : usize) : unit requires k <= len xs ensures sum xs = sum_to xs k + sum_from xs k = ...`. A lemma is proved once, erased from code, and a call to it adds its postcondition at the call site, through the existing rule that a call is taken on its callee's contract. It is what makes proofs about loops, recursion and multiplication scale.
- **Ghost values**, possibly later. Locals and parameters that exist only in the proof, such as a model `seq<T>` of a vector's contents, erased by codegen like contracts are today. SPARK's formal containers use exactly this pattern: each container has a mathematical model, and its contracts are written against the model.
- **Permutation and multiset reasoning**, possibly later. `ensures permutation xs (old xs)` is the other half of a sort's specification. It can be a spec function over counts first, with a dedicated encoding only if Z3 struggles.

### 6. Buffers ★

- **Slicing** `xs.[a .. b]`, as a view with proved bounds. The library cannot split work, recurse on halves, or return part of a buffer without it.
- **Constant data**: array literals and module-level constant arrays (`let crc_table : [u32; 256] = ...`), placed in read-only data. Many library algorithms are table driven.
- **Buffers of records** in codegen, which the scalariser does not lower yet.

### 7. Linear resources and memory

Pia does not allocate. Two things fix that: one type rule, and allocation written in Pia over `mmap`.

**`@linear` types.** Pia already has `moved` parameters, which make a value dead in the caller after the call. A type marked `@linear` adds one rule to the type checker: a value of it must be consumed, by being passed as `moved` or returned, on every path out of its scope. File descriptors, mappings and arenas are linear, so leaking one is a type error and using one after it is closed is the existing `moved` rule. This is the idea behind ATS's and Austral's resource types, kept to one attribute and no typestate ([ADR 0006](adr/0006-contracts-and-module-state.md)).

**Allocation.** `Pia.Mem` gives the allocation interface, with the ownership modifiers that already exist as its contract:

```ocaml
(* Pia.Mem *)
let alloc (t : type) (n : usize) : result (moved out mutable [t])   (* Ok: len = n, every element unwritten *)
let free  (buf : moved inout [t]) : unit                            (* buf is dead after the call *)
```

- `moved` already means that the caller cannot use the buffer after the call, so use after free and double free are type errors, not proof goals.
- `out` already means "written before it is read", so reading uninitialised memory is a proof goal.
- Running out of memory is a `result` by default, the strongest guarantee. `alloc_or_trap` is the clearly named trapping variant, and its trap is visible in its contract.

`alloc` and `free` are Pia, not a runtime written in C. Their memory comes from `mmap` through [group 8](#8-posix-trusted-declarations-and-typed-wrappers). The first allocator is an **arena**: a `@linear` region from which slices are handed out, all freed together when the arena is consumed. That fits pipelines like the demos, which allocate a few large buffers up front. Its invariant (the bump pointer stays inside the region, handed-out slices are disjoint) is module state, proved once in `Pia.Mem`. A size-class allocator behind `alloc`/`free` follows. Zig's explicit allocators and F*'s Low* regions are the prior art.

On top of these, `vec`, `string`, `hash_map`, a binary heap (priority-flood in the flagship demo needs one) are library code. They are the first place where specification functions and ghost models (group 5) pay off: `push` ensures `model result = append (model old) x`.

### 8. POSIX: trusted declarations and typed wrappers

The core calls POSIX directly. On macOS that means libSystem, not raw system call numbers: Apple changes the syscall ABI between releases and supports only calls through libSystem, which is why Go moved to libSystem on macOS in Go 1.12. So a Pia program links against libSystem like any C program, and nothing between the two is written in C.

**FFI: foreign functions with explicit contracts.** `extern "symbol"` as a function body declares a function with the C calling convention, implemented outside Pia. It is an ordinary identifier that the core gives meaning to, like `old` and `result`, so `let` stays the only binding form ([ADR 0002](adr/0002-single-let-binding-form.md)). The declaration's parameter types, modifiers, result type and contract are Pia's:

```ocaml
let crc32_z (crc : u32) (buf : [u8]) (n : usize) : u32
  requires n <= len buf
  = extern "crc32_z"                              (* zlib; reads n bytes, writes nothing *)
```

Any module may declare foreign functions, for its own C libraries as well as POSIX. The rules:

- **An explicit contract is required to call it normally.** A contract is explicit when the declaration has at least one `requires` or `ensures` clause. `ensures true` counts: it says on purpose that nothing more is promised. Parameter modifiers carry much of an FFI contract, and their defaults are promises too: a plain `[u8]` parameter is `borrowed in fixed`, so the function only reads the buffer and keeps no pointer to it.
- **The contract is trusted, not proved.** At each call, its `requires` is a proof goal like any other, and its `ensures` is assumed. Each contracted foreign function is a trusted item in its module's certificate.
- **A foreign function without an explicit contract can only be called as `unsafe f x`.** Writing `unsafe` is the caller's statement that it has checked the call by hand. The verifier assumes nothing about the result beyond its type's range, and every buffer passed to it is treated as written with unknown contents. Each `unsafe` call site, by symbol and source location, is a trusted item in the certificate. Calling such a function without `unsafe` is a compile error that suggests writing the contract.
- **`unsafe` is not a way around proof goals.** An `unsafe` call still has its arguments checked against their types, and every goal around it is proved as usual. It only marks that the callee's behaviour is taken on trust.

`unsafe` is a core form, like `extern`, not a block: it marks one call, so the trusted surface stays as small as the call. Rust's `unsafe` blocks and Verus's `assume_specification` are the prior art. Pia's version is narrower than Rust's, since a contracted foreign call needs no `unsafe` at all.

**Raw addresses.** `addr` is a raw machine address. It has no arithmetic and cannot be dereferenced. `view (a : addr) (n : usize) : [T]` turns an address into a slice, and `addr_of (xs : [T]) : addr` goes the other way. Both are trusted, so they and `assume` may only be used in a module marked `@trusted`. `Pia.Sys.Posix` and `Pia.Rt` are the only trusted modules in the library.

**`Pia.Sys.Posix` declares, the rest of `Pia.Sys` proves.** The trusted contracts are deliberately weak. They say only what POSIX guarantees, and each cites its manual page:

```ocaml
(* Pia.Sys.Posix, @trusted *)
let read (fd : i32) (buf : out mutable [u8]) (n : usize) : isize
  requires n <= len buf
  ensures result >= -1 && result <= n
  ensures result >= 0 ==> written buf 0 result      (* read(2): no more bytes than it returns *)
  = extern "read"
```

`read` returns at most `n`, or `-1`, and writes no more than it returns. It never says what a file contains. Every stronger claim is something the untrusted layer above has to prove. That layer turns integers and errno into types:

```ocaml
(* Pia.Sys.Fs, fully proved *)
let errno = type | Again | BadFd | Interrupted | Invalid | IoError | NoSpace | NoEntry | Denied | Other of i32
let fd = type { raw : i32 } @linear where raw >= 0           (* only built from a successful open *)

let open_read (path : str) : result fd = ...
let close (f : moved fd) : result unit = ...
let read_some (f : fd) (buf : out mutable [u8]) : result usize
  ensures match result with Ok n -> n <= len buf && written buf 0 n | Err _ -> true
  = ...
let write_all (f : fd) (buf : [u8]) : result unit           (* loops over write, retrying Interrupted *)
  = ...
```

`Err` carries a decoded `errno`, never a sentinel, and `match` must handle it. `raw` is not exported, so only `Pia.Sys` can make or unwrap an `fd`. Forgetting `close` is a type error. `errno` itself is `*__error()` on macOS, which `Pia.Sys.Posix` reads through `addr`, so it is a few lines of trusted Pia rather than a C helper.

The first set of declarations, enough for files, memory, time, threads and the demos:

| Group | libSystem functions | Wrapped in |
| --- | --- | --- |
| Files | `open close read write pread pwrite lseek fstat ftruncate fsync unlink` | `Pia.Sys.Fs`, then `Pia.Io` readers and writers |
| Memory | `mmap munmap madvise` | `Pia.Sys.Mapping` (a `@linear` region of pages), then `Pia.Mem` |
| Process | `exit getpid getenv`, and `argc`/`argv` | `Pia.Sys.Process` |
| Time | `clock_gettime nanosleep` | `Pia.Sys.Clock`: a monotonic `instant` and ordered `duration` |
| Threads | `pthread_create pthread_join`, `pthread_mutex_*`, `pthread_cond_*`, `sysctlbyname` for the core count | `Pia.Sys.Thread`: `spawn` takes a `moved` closure and returns a `@linear` handle that `join` consumes |
| Errors | `__error` | `Pia.Sys.Errno` |

**`main` and `abort`.** `let main (args : [str]) : u8` is a symbol Pia can export. A small entry function in `Pia.Sys.Process` builds `args` from `argv`, calls `main`, and passes the result to `exit`. So the edge demo's `main.c` becomes Pia. `abort` has the precondition `requires false` in proof mode, so every call to it is a proof that it cannot happen, or a visible `--allow-unproved`.

**Keeping the trusted base honest.** Each trusted declaration has a test that calls it on macOS and checks its contract's claims at run time, so a wrong trust shows up as a failing test rather than an unsound proof. Each module's proof certificate lists its own trusted items: contracted foreign functions, `unsafe` call sites, `assume`s and goals accepted with `--allow-unproved`, each with a hash of what is trusted. It does not copy its dependencies' items. The transitive trusted base of a program is computed by walking the certificates at link time, and `piac --trust-report` prints it. That way a dependency that swaps a proved body for an `assume`, without changing its interface, leaves importers' proofs valid (assume-guarantee) but still shows up in the report. The certificate format is [ADR 0024](adr/0024-published-proof-certificates.md)'s ([abi.md](abi.md)).

### 9. Runtime errors

Most failures are ruled out at compile time, but a few happen at run time by design: `@overflow(trap)`, `alloc_or_trap`, `abort` reached through `--allow-unproved`, and faults inside foreign code (`SIGSEGV`, `SIGBUS`, `SIGILL`, `SIGFPE`). All of them go to one runtime error handler in `Pia.Rt`, written in Pia.

- **One entry point.** Codegen lowers every trap to a call of `pia_trap (kind, site)`, where `site` indexes a table of source locations the compiler emits into the binary. So a trap reports its Pia file, line and column, and what failed ("overflow in `a + b`, `@overflow(trap)`"), even in a binary without debug info.
- **Signals.** At start-up, `Pia.Rt` installs handlers with `sigaction` on an alternate signal stack (`sigaltstack`), so a stack overflow or a fault in foreign code also reaches the handler.
- **Stack traces.** The handler walks the frame-pointer chain, which arm64 macOS always keeps, and symbolises each return address with `dladdr`. When debug info is available (`piac -g` emits DWARF, and a `.dSYM` sits beside the binary), it adds file and line for each frame. Without it, it prints symbol names and offsets.
- **Debug info.** It also prints the trap kind, the faulting address for a signal, the thread, and for `unsafe` sites, the foreign symbol that was being called.
- **Safe in a signal handler.** The handler allocates nothing and writes with `write(2)` to standard error only, so it is async-signal-safe. It then exits with status 134, as `abort` would.
- **Replaceable.** A program can install its own handler with `Pia.Rt.on_trap`, for example to flush a log first. The default stays the strong one: print everything, then stop.

`Pia.Rt` is trusted, since it reads frames and signal contexts through `addr`, so its items appear in every program's trust report. The prior art is Rust's panic handler and `RUST_BACKTRACE`, and Go's runtime traceback on a fatal signal.

### 10. SIMD, floats and atomics

These come with milestones M10 to M12, but they are core builtins, so they are listed here.

- **Floats (M11)**: `fadd fsub fmul fdiv fneg fsqrt fma fabs fmin fmax`, comparisons, `ftoi` (with a range goal), `itof`, `is_nan`, `is_inf`, and the three reassociation choices from [ADR 0012](adr/0012-floating-point-reassociation.md). Elementary functions (`exp`, `log`, `sin`) are Pia in `Pia.Math`: range reduction and polynomials, with error bounds in their contracts. Only the sediment colour map needs them at first.
- **`vec<T, k>` (M10)**: `splat`, `lane` and `with_lane` (lane index proved), `vload xs i` and `vstore xs i v` (with `i + k <= len xs` proved), every integer and float builtin applied lane-wise with the same overflow modes, comparisons and `vselect`, constant `shuffle`, `vwiden_lo`/`vwiden_hi`/`vnarrow`, and horizontal `vreduce_add`/`vreduce_max`. They lower to MLIR's `vector` dialect, and to `arm_neon` where a pattern needs it. The verifier models a vector as `k` values.
- **Atomics (M12)**: `atomic_load atomic_store atomic_swap atomic_cas atomic_add atomic_sub atomic_and atomic_or fence` on an `atomic<T>` cell, each with a memory order (`relaxed acquire release acq_rel seq_cst`), lowering to LLVM atomics and so to `ldar`, `stlr`, `ldadd` and `cas` on arm64.

**Concurrency is then library code.** The worker pool behind `spread` is Pia in `Pia.Par`, over `Pia.Sys.Thread` and the atomics: a fixed set of threads, a work queue and a barrier. The collectives `scatter`, `gather`, `halo_exchange` and `all_reduce` are library metaprograms, as [ADR 0014](adr/0014-concurrency-model.md) already says. Race freedom stays in ownership, since tiles are `moved` to workers. The pool's own invariants (each task runs once, the barrier releases only when every worker arrives) are module-state contracts for the model checker pass. GPU placement ([ADR 0015](adr/0015-device-placement.md)) lowers through MLIR's `gpu` dialect to Metal. Metal's host API is Objective-C, not POSIX, so it is a separate trusted module later, outside this minimal core.

### 11. Metaprogram builtins

The interpreter has `map fold length fields name concat` ([meta.md](meta.md)). Derives in the library need a few more, all read-only questions about types:

| Builtin | Answer |
| --- | --- |
| `field_type t f` | the type of field `f` of record `t` |
| `variants t` | the constructors of a variant type, with their payload types |
| `kind t` | `"record"`, `"variant"`, `"int"`, `"float"`, `"array"`, `"slice"` or `"vec"` |
| `size_of t`, `align_of t` | layout, as codegen will lay it out |
| `int_bounds t` | the bounds of an integer or range type |
| `attrs x` | the attributes on an item or field, with their arguments |
| `error msg` | stop expansion with a diagnostic at the expansion site |
| `nth` `zip` `range` | list helpers the library would otherwise write recursively |

With these, `@derive(ord)`, `@derive(hash)`, `@derive(serialise)` and `@derive(deserialise)` are library metaprograms. A PNG chunk header can be declared as a record and read by a derived, bounds-proved reader.

### 12. Later

- **Function values and closures**: `map`, `fold` and comparator-based `sort` over function values. Until then, generics plus concept instances (`Ord t`) cover most needs, which is also what lets them monomorphise and vectorise.

## Multiplication in the verifier

Today every integer in a module is a 68-bit bit-vector, or 132-bit if the module multiplies anywhere ([verifier.md](verifier.md#encoding)). So one `*` makes every goal in the module wider, and loop-nest bounds goals then time out. This is a verifier change rather than a builtin, but the library cannot be written until it is done, so it is part of the core. The design is a ladder, cheapest first. Each step is tried with a short timeout before the next.

1. **Width per goal, not per module.** Each goal's width is computed from the ops it contains and the intervals of their operands. A goal with no multiplication stays at 68 bits however many `*` the module has elsewhere. This alone should fix the edge demo's timeouts.
2. **Multiplication by a constant is linear.** `3 * i` is encoded as shifts and adds, and an affine goal goes to the Presburger stage ([ADR 0020](adr/0020-presburger-for-affine-goals.md)).
3. **Intervals first.** If interval analysis bounds both operands, it bounds the product, and the goal is settled without Z3, as for addition today.
4. **Opaque products and lemmas.** A product of two variables is encoded as an uninterpreted function with its basic facts: zero, one, commutativity, sign, and monotonicity in each argument within the operands' ranges. Goals that need more call a lemma from `Pia.Core.Arith` (`mul_le_mul`, `div_mul_le`, `mul_div_cancel`, `index_2d_lt`), which are ordinary [lemmas](#5-verification-primitives) proved once. Most bounds goals in image code, such as `y * w + x < w * h` given `y < h` and `x < w`, are settled here.
5. **Exact nonlinear arithmetic, in a query of its own.** Only when the steps above fail does the goal get the exact product, at the width it needs, in a separate query. Bit-vectors and Z3's nonlinear integer solver run as a portfolio, and the first answer wins.

Verus does the same: nonlinear facts are kept out of ordinary queries, proved in small `by (nonlinear_arith)` queries, and packaged as `vstd::arithmetic` lemmas. Dafny's standard library does it with nonlinear lemmas and an option that turns nonlinear reasoning off in ordinary queries. A goal that still times out is reported with the step it reached and a suggestion: a lemma that would close it, or an `assert` that splits it. Proof decomposition stays explicit and visible in the source. The same ladder applies to `/` and `%`, which today get special-case facts for non-negative operands.

## The library, layer by layer

```mermaid
flowchart TD
  b["Core builtins (in piac)"] --> pre["Pia.Prelude"]
  pre --> core["Pia.Core: no allocation, no OS"]
  core --> posix["Pia.Sys.Posix: extern declarations, @trusted"]
  posix --> sys["Pia.Sys: Fs, Mapping, Process, Clock, Thread"]
  posix --> rt["Pia.Rt: runtime error handler, @trusted"]
  sys --> mem["Pia.Mem: arena, alloc, vec, heap"]
  mem --> io["Pia.Io: readers, writers, formatting"]
  io --> par["Pia.Par: worker pool, collectives"]
  io --> img["Image: Bmp, Png, Gif"]
```

| Layer | Needs from the core | Contents (all Pia) |
| --- | --- | --- |
| `Pia.Prelude` | modules | operators, `derive_eq`, later `derive_ord` and `derive_hash` |
| `Pia.Core` | groups 1 to 6 | `option` `result` `ordering`; `Eq` `Ord` `Hash` `Numeric`; integer utilities and `Arith` lemmas; slice algorithms (`fill` `copy` `equal` `find` `reverse` `rotate` `binary_search` `sort` `partition`); fixed-capacity containers (`array_vec`, `bitset`, `ring`); `crc32` `adler32` `fnv`; UTF-8 validation; formatting integers into a buffer and parsing them |
| `Pia.Sys.Posix` | group 8 | the trusted libSystem declarations, and nothing else |
| `Pia.Rt` | groups 8 and 9 | the trap entry point, signal handlers, stack traces |
| `Pia.Sys` | groups 7 and 8 | `fd`, `mapping`, `errno`, `args`, `exit`, clocks, threads: POSIX in strong types, fully proved |
| `Pia.Mem` | group 7 | `arena`, `alloc` `free`, `vec`, `string`, `hash_map`, `heap` |
| `Pia.Io` | `Pia.Sys`, `Pia.Mem` | `reader` and `writer` concepts with bounds-proved reads, buffered file I/O, `str` as `[u8]` refined to valid UTF-8, printing |
| `Pia.Math` | floats | elementary functions with error bounds |
| `Pia.Par` | atomics, threads | the `spread` worker pool, collectives |
| `Image.Bmp`, `Image.Png`, `Image.Gif` | all of the above | BMP first, to replace the demo's `main.c`; then zlib inflate and deflate, PNG unfiltering, GIF LZW (M13) |

`Pia.Core` needs no allocator and no OS, like Rust's `core`, so it can run anywhere the compiler targets, including a GPU kernel later on.

Every function in every layer has a contract that is proved when the library builds. Proved means at least the strongest-guarantee defaults (no overflow, in bounds, terminates). Where specification functions allow, it also means functional correctness: `sort` returns a sorted permutation of its input, `binary_search` finds the element if it is there, and `write_all` writes every byte or returns `Err`. The codecs are good stress tests: inflate's back-references need `distance <= bytes written so far`, Huffman decoding needs bounded table indices, LZW needs the code table to stay within 4096 entries, and the decoded image's length is proved against the header's `width * height * channels`, which is why multiplication comes first.

## Suggested order

Each step unlocks a usable slice of the library, and the order follows the roadmap:

1. **Per-goal widths and the multiplication ladder.** No language change, and it unblocks the edge demo's BT.601 grayscale today.
2. **Integer primitives, slicing, constant arrays, `abort`.** Small compiler changes, and enough to write checksums, bit utilities and slice algorithms as a single-file library.
3. **Spec functions and lemmas**, with `Pia.Core.Arith`. So the library can be specified as it is written, and not retrofitted later.
4. **Sum types and `match`.** `option`, `result`, and fallible APIs.
5. **`extern`, `unsafe`, `addr`, `@trusted`, `@linear`, `main`, `--trust-report`, and the runtime error handler.** `Pia.Sys.Posix`, `Pia.Sys.Fs` and `Pia.Rt`. A Pia program can read and write files without C. Until modules land, `piac` takes several source files compiled as one program, so this does not wait for M8.
6. **Modules (M8)**, with the prelude moved into Pia. The library becomes importable, and the trusted-module boundary becomes a module boundary.
7. **`Pia.Mem` and `Image.Bmp`.** The edge demo drops `main.c`.
8. **Generics (M9).** Rewrite `Pia.Core` generically. The metaprogram-instantiated versions show what the generic versions must match.
9. **Floats (M11), `vec` (M10), atomics and `Pia.Par` (M12)**, then the PNG and GIF codecs (M13) for the flagship demo.

Steps 1 to 5 need neither M8 nor M9, so they can start now, alongside M8.

## Prior art

| System | What Pia takes from it |
| --- | --- |
| Rust `core` / `alloc` / `std`, and the `libc` crate | the split between what needs no OS, what needs an allocator, and what needs the OS |
| Zig | explicit allocators; on macOS, linking libSystem rather than raw syscalls (as Go 1.12 also chose) |
| OCaml `external` | a short list of primitives under an ordinary library |
| ATS | POSIX wrapped in linear types and proofs: closest in spirit to `Pia.Sys` |
| Austral | linear types for resources, kept simple |
| SPARK Ada | proved library code over a few bodies whose contracts are trusted; expression functions; formal containers with models |
| Verus (`vstd`, `assume_specification`) | trusted specifications for external functions; nonlinear arithmetic isolated in its own queries; arithmetic lemma libraries |
| Dafny (`{:extern}`, standard libraries) | externs with contracts; nonlinear lemmas; fuel for recursive definitions |
| F* Low* and HACL* | verified code over a small trusted C layer; memory regions |
| Lean 4 (`@[extern]`) | a self-hosted standard library over a few compiler builtins |

The common lesson is that the trusted part should be small, listed, and tested against reality, and that nonlinear arithmetic needs help from the library rather than a bigger solver budget.

## Decided in this proposal

These were open questions in the first draft. ADR 0023 records the answers.

- **Trusted items are listed in certificates.** Each certificate lists its own module's trusted items (foreign contracts, `unsafe` calls, `assume`s, accepted unproved goals), and `piac --trust-report` walks them for the whole program. `addr` and `assume` are only allowed in `@trusted` modules.
- **Allocation failure is a `result`** by default, with a trapping variant clearly named.
- **`extern` is a function body**, `= extern "symbol"`, not a new declaration form, so `let` stays the only binding form.
- **FFI needs explicit contracts.** A foreign function without one can only be called as `unsafe f x`, and each such call is a trusted item.
- **Runtime errors go to one handler**, `Pia.Rt`, which prints the Pia source location, a stack trace, and debug info when it is available.
- **Spec function unfolding**: one level of unfolding by default (Dafny's fuel of 1), with lemmas for anything deeper and a per-function `@fuel(n)` to raise it.
- **`seq<T>` is a library type** whose model is an SMT array plus a length, introduced with ghost values. A core type can come later if the encoding needs it.

## Open questions

- **Operator spellings for bit operations**: OCaml's `land` `lor` `lsl`, or C's `&` `|` `<<`. Pia already uses `||` and `&&` for logic, so `|` and `&` would read as their bitwise forms, but `|` also separates variants.
- **Whether libm is trusted**, or every float function is Pia with an error bound. This proposal writes them in Pia.
