# Codegen v0

Status: implemented in M6 ([#7](https://github.com/deanberris/pia-lang/issues/7)).

`piac --emit=obj -o file.o file.pia` verifies a program ([verifier.md](verifier.md)) and compiles it to an object file for Apple silicon (Mach-O) or Linux x86_64 (ELF) ([ADR 0049](adr/0049-targets-are-theories.md)). The result links with C. The other outputs stop earlier in the pipeline:

| Flag | Output |
| --- | --- |
| `--emit=core` | MLIR in `arith`, `scf`, `memref` and `func`, after contracts are erased |
| `--emit=llvm` | optimised LLVM IR |
| `--emit=asm` | assembly |
| `--emit=obj` | an object file, written to `-o` |

`--target=<triple>` and `--cpu=<name>` choose the machine: `arm64-apple-macosx14.0.0` with `apple-m1`, or `x86_64-unknown-linux-gnu` with `x86-64-v3`. The default is the host `piac` was built for. `x86-64-v3` is also the oldest x86_64 CPU `piac` accepts: a `--cpu` without AVX2, BMI1, BMI2, F16C, FMA, LZCNT and MOVBE is an error ([ADR 0049](adr/0049-targets-are-theories.md)). Bazel always passes both, for the platform it builds for ([tools/piac/targets.bzl](https://github.com/deanberris/pia-lang/blob/main/tools/piac/targets.bzl)). `-O0` to `-O3` set the optimisation level, which defaults to `-O2`.

## Verification comes first

Code is generated only when every obligation is proved. If one fails, piac prints the report from `--verify` and stops. An obligation that is not proved either way, such as the termination of a `while` loop with no `decreases` measure, also stops it: piac lists each unproved obligation with its function and generates nothing.

To compile anyway, accept specific unproved obligations with `--allow-unproved`, which can be repeated:

| Flag | Accepts |
| --- | --- |
| `--allow-unproved=drain` | every unproved obligation in the function `drain` |
| `--allow-unproved=file.pia:30` | the unproved obligations on line 30 |
| `--allow-unproved=file.pia:30:37` | the one at line 30, column 37 |

The location is written the way piac prints it. Accepted obligations are still reported as a warning, and a flag that accepts nothing is reported too, so stale ones show up. A failed obligation cannot be accepted. `piac --verify` takes the same flag, and fails on a skipped goal that it does not accept.

## Stages

1. **Erase contracts.** Every `pia_contract` op is removed: `requires`, `ensures`, `invariant`, `decreases`, `assert`, `assume` and `obligation`. Then everything only they used is removed too, including quantifiers, `old` and the arithmetic inside contracts. An op that writes, or a loop or branch that calls a function which may write (one that takes a buffer, or any call but a spec function's inside it), stays even when only a contract reads its results (tests/codegen/contract_only_loop.pia). That includes calls to ordinary functions and loads: an op whose every use is in a contract, or in another such op, never runs, so it goes even when it is not known to be pure (a call to another module's function is a declaration here). Kept, such code could run a contract's `xs.[result]` when `result = len xs`, since a contract evaluates both sides of `&&`, and LLVM would treat the out-of-bounds load as undefined behaviour (tests/codegen/contract_only.pia). Only ops that write, allocate or free are kept. Spec functions and lemmas (`pia.spec`, `pia.lemma`) are erased with every call to them: they exist only for the verifier. The verifier's `pia.proved` attributes stay.
2. **Lower `pia` to core dialects.** This uses MLIR dialect conversion, with the type mapping below and the ops after it. `scf`, `func.call` and `func.return` are converted structurally. Then each function marked `@lower` gets its MLIR form in place of its body ([below](#lowerings-written-in-pia)).
3. **Lower to the `llvm` dialect.** When a lowering was applied, `convert-linalg-to-loops`, `expand-strided-metadata` and `lower-affine` run first. Then the upstream passes run in this order: `scf` to `cf`, then `cf`, `arith`, `index`, `memref` and `func` to `llvm`, then the reconciliation of casts. Then each public function gets its C entry point.
4. **Translate and optimise.** The module is translated to LLVM IR, given the target's data layout, and run through LLVM's `-O2` pipeline.
5. **Emit.** The LLVM target machine writes the object file or the assembly.

## Types

A range type is stored in the smallest machine integer that holds its range: 8, 16, 32, 64 or 128 bits. It is signed if the range contains a negative value. So `u8` and `int{0..200}` become `i8`, `i8` stays `i8`, and `int{-1..200}` becomes `i16`. `bool` is `i1`, and an index is `index`.

| Pia | Core MLIR |
| --- | --- |
| `!pia.int<lo, hi>` | `iN`, as above |
| `f32`, `f64` | `f32`, `f64` |
| `[T; n]` | `memref<n x T>` |
| `[T]` | `memref<? x T, strided<[1], offset: ?>>` |
| `!pia.atomic<T>` | `memref<1 x T>`, with a `bool` held as `i8` |
| `!pia.rec<"tree">` | `!llvm.struct<"pia.rec.tree", (tag, fields...)>` |
| a mutable function reference, `(u8) -> u8` | `(i8) -> i8`, a pointer to the function |

A mutable function reference ([ADR 0071](adr/0071-function-references.md)) is the address of the wrapper that checked its function against the arrow, `func.constant @"succ@f.pia:5:74"`, and rebinding it replaces the value, so in a loop or a branch it is a `phi` of addresses. A call through it goes to the reference's proxy, `h@f.pia:5:20`, whose body is the `func.call_indirect`; the verifier takes the proxy's contract, the arrow's, as given, and LLVM inlines the proxy, leaving one indirect call.

A slice's offset is dynamic because `xs.[a .. b]` (`pia.slice`) is a view into the same storage: it lowers to `memref.extract_strided_metadata` and `memref.reinterpret_cast`, at the buffer's offset plus `a`, with `b - a` elements. At the C boundary a slice is still a pointer and a length, with offset 0. `abort ()` lowers to `llvm.intr.trap`. A constant array (`pia.const_array`) becomes a private constant `memref.global`, one per constant, which LLVM places in read-only data; each use is a `memref.get_global`. A `with_arena`'s region (`pia.region`) is a `memref.alloca` at the start of the function, zeroed by a loop where the `with_arena` is entered.

An array result is a buffer the caller makes. Arrays are values, and a function's own arrays live in its frame, so `arrayResultsToBuffers` (`src/codegen/ArrayResults.cpp`) runs first: each function whose results include arrays, a record result's array fields among them once records are scalarized, takes one more parameter per array result, each `return` copies the array into it (`pia.copy`, a `memref.copy`), and each call makes the buffer in its caller's frame (`pia.region`, an `alloca` at the function's entry) and reads the result from it. The verifier runs before this, on the value form. A foreign function cannot return an array yet, and an exported function that returns one takes the buffer as a pointer after its other parameters. Records are scalarized before codegen ([irgen.md](irgen.md#records)). A buffer of records arrives as one buffer per field (struct of arrays), so `[pixel; 8]` is four `memref<8 x i8>`, which vectorises like any other buffer. A buffer whose elements are slices, such as a vector's box slots, becomes two buffers before lowering, `splitSliceBuffers` in `src/codegen/SliceBuffers.cpp` ([ADR 0048](adr/0048-buffers-whose-elements-hold-slices.md), step 3): its elements' addresses and their lengths, both `memref<? x index>`, the lengths marked `{pia.length_of}` the addresses. Storing a slice records `pia.address`, its storage's aligned pointer plus its offset in bytes, and its length; loading one rebuilds it from both with `pia.at_address`, a memref descriptor at that address with offset 0. The store that empties an element moved out (`pia.moved_out`) is code like any other, so a moved-out element's length is 0 at run time, as the proof has it. Buffers of buffers of slices and `dyn` are not lowered yet.

A recursive value ([ADR 0047](adr/0047-recursive-sum-types-and-shared-references.md), step 3) is laid out as a variant is: an identified LLVM struct, `pia.rec.tree`, of its tag, then each constructor's payload fields in order, the payload's record leaves as scalarization gives them. A buffer in a payload, such as a box's slot or a vec's items, is its memref descriptor, so a recursive occurrence is a pointer and a length into memory an allocator lent, and the struct is never part of itself. `pia.rec_make` is `llvm.mlir.zero` with the tag and the payload inserted, `pia.rec_tag` and `pia.rec_payload` extract them, and a buffer of recursive values is a memref of the struct, which loads and stores as any element (MLIR is told it may be one). Building a node allocates its boxes explicitly, through its allocator, so every allocation is visible and fallible, and a tree lives in whatever region its allocator draws from: `tests/codegen/rec_run.pia` builds one in cells its C caller lends and sums it (`rec_run_test.c`), and `tests/std/rec_mem.pia` does the same with Pia.Mem's box and bump. A function that takes or returns a recursive value by value has no C entry point, since the struct has no C type yet; C passes a buffer of them. Dropping a recursive value frees nothing: every allocator so far is a region's (bump, arena), whose memory goes when the region does, so no drop runs, and none can use stack. The iterative drop of ADR 0047, section 4, comes with the first allocator that frees one block at a time (ADR 0046, step 2).

A box over a concept, `box c`, is one cache line of the target ([ADR 0046](adr/0046-box-over-a-type-or-a-concept.md#amendment-2026-11-27-a-box-c-is-one-cache-line-with-small-objects-inline), step 1): 8 words on x86_64 Linux and 16 on Apple silicon. Word 0 is the address of the boxed type's descriptor, `pia$t$<type>$<concept>`, a constant holding the type's size and alignment, a drop entry (null for now) and one entry per requirement callable through a box; the words after it hold the object in its C layout, each field at its natural alignment. `widen` is `pia.box_pack`, which stores the descriptor's address and the object's fields into the line, and a call through a box is `pia.box_call`, which loads the entry from the descriptor and calls it with the object's address, one indirection. Each entry is a small function that loads the fields from that address and calls the type's own function. Where LLVM can see which descriptor a box holds, as right after `widen`, the load folds and the call is direct (`tests/codegen/box_direct.pia`). To the verifier both ops are proxies with the requirement's contract, so proofs are unchanged. A type too large for the line is refused for now; boxes across modules, and larger objects through the box's lease, are steps 2 and later. `tests/codegen/box_concept.pia` and `box_error_payload.pia` call boxes from C, which treats the box as an opaque block of words.

## Arithmetic

Each `pia.add`, `sub`, `mul`, `div` and `rem` is computed at one width. That width holds both operands and the result type. Unless the result was proved to fit, it also holds the exact result. The operands are extended by their own signedness, and the operation is signed if anything at that width can be negative. Then the overflow mode brings the exact value into the result type:

| Mode | Lowering |
| --- | --- |
| `proof` | nothing: the verifier proved the value fits, so the result is truncated |
| `saturate` | clamp to `[lo, hi]` with `max` and `min`, then truncate |
| `wrap` | truncate when the type covers a whole machine integer, as `u8` and `i32` do. Otherwise `lo + ((x - lo) mod size)` |
| `trap` | `llvm.intr.trap` if the value is outside `[lo, hi]` |

`pia.convert` is the same with the input as the exact value. `pia.cmp` extends both sides to a width that holds both ranges. `to_index` and `from_index` become `index_cast` (or `index_castui` when the value is non-negative). `len` becomes `memref.dim`, or a constant for a fixed array. `load` and `store` become `memref.load` and `memref.store`, without bounds checks, because the verifier proved them in bounds.

Floats are already core MLIR: IRGen emits `arith.addf`, `subf`, `mulf`, `divf`, `negf`, `cmpf` and float `arith.constant` directly, with no fast-math flags, so each operation is one IEEE 754 operation rounded to nearest (ADR 0004, ADR 0012). Nothing reassociates them, and LLVM contracts `a * b + c` into an FMA only when both operations carry the `contract` flag, which IRGen never sets, and Pia never sets flush-to-zero, so subnormals are kept. `=` is `cmpf oeq` and `<>` is `cmpf une`, so with a NaN every comparison is false but `<>`. Conversions are `pia` ops that lower to LLVM's: `f32 n` of an integer is `sitofp` or `uitofp` by the signedness of its storage, `f64 x` and `f32 x` between the widths are `arith.extf` and `arith.truncf`, `i32 x` of a float is `fptosi` or `fptoui` at the target's storage width, whose result the verifier proved is in range so it is never poison, and `to_bits` and `from_bits` are `arith.bitcast`. `tests/codegen/floats.pia` checks this against C compiled with `-ffp-contract=off`, bit for bit (`floats_test.c`).

LLVM recognises the widen-clamp-truncate pattern, so `add_px` on `u8` with `@overflow(saturate)` compiles to `llvm.uadd.sat.i8`. In a loop over slices, such as `add_rows` in `tests/codegen/saturate.pia`, LLVM's loop vectoriser turns it into NEON `uqadd.16b`.

## Atomics

An atomic cell is a one-element memref ([ADR 0052](adr/0052-atomics.md), section 5). `atomic_new` is a `memref.alloca` at the start of the function and a plain store, since nothing else sees the cell yet. Every other op is an LLVM atomic on the memref's aligned pointer, at the element's alignment: `llvm.load` and `llvm.store` with an ordering, `llvm.atomicrmw`, `llvm.cmpxchg` (whose old value is the result) and `llvm.fence`. `relaxed` is LLVM's `monotonic`, and the other orders keep their names. `atomic_min` and `atomic_max` are `min` and `max` on a signed cell, `umin` and `umax` otherwise. A `bool` is a byte, since LLVM's atomics take whole bytes.

An add or sub lowers by its stated mode. `wrap` and `proof` are one `atomicrmw`. `trap` is one too, after which the exact result is computed from the old value it returns, at twice the cell's width, and checked as trap arithmetic is, so the cell already holds the wrapped value when the program stops. `saturate` is a loop: a relaxed load, then `cmpxchg` of the old value for the clamped result until no other task changed the cell in between, so no wrapped value is ever stored. The loop's failure order is the read half of the op's order.

LLVM's backends choose the instructions, which are those of ADR 0052's table. `tests/codegen/atomics.pia` compiles one function per (operation, order) for both targets and checks the instructions with FileCheck. Both targets detect a `trap` overflow from the old value for now; the target model's `rmw_flags` records that x86_64's `lock xadd` sets the flags, for a lowering that reads them. The x86_64 lowering of `relaxed` inside `@target(x86_64_linux)` items, and its check, are a later step (ADR 0052, section 6).

## C ABI

Each Pia function `f` becomes an internal function. Only the functions a module exports through an interface also get a C entry point ([ADR 0039](adr/0039-module-and-interface-syntax.md)): one in an interface marked `@abi(c)` is named `f`, and one in any other interface is named after its module's path, so `luma` in `module Image.Pixels` is `pia$Image$Pixels$luma`. A file with no `module` header exports nothing but its `main`. Private functions keep internal linkage, so LLVM can inline them and remove the ones nothing calls. An exported function also keeps its Pia calling convention under its module's link symbol, `__pia$Image$Pixels$luma`, which is what another module calls when it imports the function: the importer's object file declares that symbol and has no body for it, so the two object files must be linked together (the `pia_library` rule does this). Calls between Pia functions use the internal one, which takes MLIR memref descriptors. The entry point maps C arguments onto it:

| Pia parameter | C parameters |
| --- | --- |
| an integer | the integer type of its storage width, such as `uint8_t` or `int16_t` |
| `bool` | `bool` |
| `f32`, `f64` | `float`, `double` |
| `[T]` | `const T *data, uint64_t len` (or `T *` when it is written) |
| `[T; n]` | `const T *data` (or `T *`) |

A record parameter is passed as its fields, in declaration order, so `blend (p : pixel) (q : pixel) : pixel` takes eight `uint8_t` arguments. A record result is written through a pointer to a C struct of its fields, which is the last argument; a record that flattens to one scalar, such as a one-field record or a distinct type (ADR 0064), returns that scalar instead. Each field sits at its natural C offset, aligned to its own size:

```c
struct pixel { uint8_t r, g, b, a; };
void blend(uint8_t pr, uint8_t pg, uint8_t pb, uint8_t pa,
           uint8_t qr, uint8_t qg, uint8_t qb, uint8_t qa, struct pixel *out);
```

A buffer of records is passed as one buffer per field, in declaration order. A slice of records has one length, passed after its first field's pointer, which every field buffer shares (`{pia.length_of}` marks the others):

```c
// opaque_all (xs : out mutable [pixel]) (v : u8) : unit
void opaque_all(uint8_t *r, uint64_t n, uint8_t *g, uint8_t *b, uint8_t *a,
                uint8_t v);
```

A buffer of slices is passed the same way, as the buffer of its elements' addresses and the buffer of their lengths, which shares the first's count (tests/codegen/slice_buffers_run.pia, run by slice_buffers_run_test.c):

```c
// first (xs : borrowed [[u16]]) : u16
uint16_t first(uint64_t *addr, int64_t n, uint64_t *len);
```

Integers narrower than 32 bits are marked `zeroext` or `signext`, as the Apple arm64 ABI requires and as clang and GCC do for x86_64 System V. Signedness comes from the range type. Once a range type is lowered to a signless `iN`, its signedness would be lost, so `lowerToCore` records it as a `{pia.signed}` argument or result attribute. Unit results are `void`. A prime cannot appear in a C name, so each `'` in a function's name becomes `_prime` in its entry point: `step'` is called as `step_prime`. Two functions whose C names would be the same are an error. Returning a buffer is not supported yet.

For example, `add_rows (a : [u8]) (b : [u8]) (dst : out mutable [u8]) : unit` is called from C as:

```c
void add_rows(const uint8_t *a, uint64_t na, const uint8_t *b, uint64_t nb,
              uint8_t *dst, uint64_t ndst);
```

## Spec-only state

A parameter, local or record field whose type is spec-only (`int`, `real` or a theory's sort) is state the verifier sees and the program does not have ([ADR 0041](adr/0041-allocator-semantics-as-a-theory.md)). Code can only store spec values in such places, so nothing the program computes reads them. `eraseContracts` replaces every computation of a spec-only value left in code, such as `Alloc.take t.heap b` stored into a field, with `pia.erased`, and marks the spec-only parameters and results `{pia.erased}`. `lowerToCore` lowers each spec-only value to an `i1` that nothing reads, and LLVM removes it. The C entry points leave spec-only parameters and fields out: `skip (n : int) (x : u8) : u8` is `uint8_t skip(uint8_t x)`, and a result `{ v : u8; steps : int }` is returned as its one remaining field, a `uint8_t`. A spec-only field of a buffer's records is a buffer of its own, struct of arrays like every field: `eraseContracts` removes the stores into it, its loads are spec-only values like any other, and it is marked `{pia.erased}`. Its C entry point leaves it out, and when the fields share one length the first field kept takes it, so `[{ steps : int; v : u8 }]` is `uint8_t *v, int64_t n`, and `len xs` reads the length of a field in code. Spec state ([ADR 0058](adr/0058-spec-buffers.md)), a `let spec` local or a spec parameter, is spec-only whatever its type, so it cannot be erased by type: IRGen marks a spec local's `pia.region` and a spec parameter's argument `{pia.spec_state}`. Code only writes spec state, and only contracts read it, so once the contracts are gone `eraseSpecState` erases every op that uses spec state, and every op that uses one of those. A call passes spec state only for a spec parameter, so the pass removes each spec parameter, from definitions and declarations alike, and the argument each call passes for it. A spec field's leaves, once ScalarizeRecords splits a record, are spec parameters and spec results (`{pia.spec_state}`): the pass removes those results from functions, returns and calls, re-points a slice of records' `pia.length_of` when the field it named goes, and follows spec state through `scf.for`, `scf.while` and `scf.if`, where the value a loop or branch still carries becomes `pia.erased` (a one-byte view in place of an erased buffer). tests/codegen/spec_state.pia is run from C by spec_state_test.c.

## Foreign functions

`let f (x : i32) : i32 ensures ... = extern "sym"` declares a C function (#55). IRGen makes `f` a private function whose whole body is `pia.foreign "sym"(...)`, marked `pia.extern`, so callers see its contract like any other function's: preconditions are proved at each call and postconditions are assumed. The verifier never proves the stub itself; the contract is trusted, and `piac --verify --trust-report` lists it.

A foreign function without a `requires` or `ensures` can be called only as `unsafe f x`. The call is marked `pia.unsafe`: the verifier assumes nothing about its result beyond its type, and treats every buffer passed to it as written. `--trust-report` lists each such call site.

Codegen declares `sym` once, as a private function with C types, and calls it. An integer keeps its width, extended to 32 bits as Apple's arm64 ABI and x86_64 System V expect (`llvm.zeroext` or `llvm.signext`), and a bool is a zero-extended `i1`. A buffer is passed as a pointer to its first element, which for a view (`xs.[a .. b]`) is part way into its storage; pass its length as a separate `usize` argument. If the Pia declaration has the same name as the symbol, it is renamed `pia$ffi$sym`. For now a foreign function takes integers, bools and buffers of integers, and returns an integer, a bool or unit. tests/codegen/ffi_run.pia runs against C in ffi_test.c.

A C variadic function, such as `open` or `syscall`, is declared with `@variadic(n)` after the return type, where `n` is the number of its named C parameters ([ADR 0051](adr/0051-variadic-generics-and-foreign-varargs.md)). Codegen declares the symbol as an `llvm.func` with `...` and emits each call as `llvm.call ... vararg(...)`, so LLVM applies the variadic convention: Apple arm64 passes the arguments after the named ones on the stack, and x86_64 System V sets `%al`. Several declarations may call one symbol at different arities, such as `open` and `open_mode`, as long as they agree on `n` and on the named parameters. A variadic argument must be an integer of 32 bits or more, or a buffer, because C promotes anything narrower to an `int`, and IRGen says to widen it rather than doing it silently. tests/codegen/ffi_variadic.pia checks the lowering, and ffi_run.pia runs two arities of one symbol and a buffer passed through `...` against C.

A C function that returns a pointer to an integer, such as glibc's `__errno_location` or Darwin's `__error`, is declared with `@deref` after the return type, which is the integer's type ([ADR 0057](adr/0057-posix-module-per-target-behind-one-interface.md), section 5). Codegen declares the symbol as an `llvm.func` returning `ptr` and follows each call with an `llvm.load` of the result, so the pointer never reaches Pia. `Pia.Sys.Posix.errno` is the one such row. ffi_run.pia reads a counter through one after a call that changes it.

A C function of no arguments, such as `getpid`, is declared like any Pia function of none, `let getpid () : i32 = extern "getpid"`, and called by its name alone, `getpid`.

The POSIX declarations are not written by hand. `tools/bindings/gen.py` reads the names in `tools/bindings/posix.toml` from the target's own headers with clang's JSON AST, and the rows of the `Posix` interface in `lib/Pia/Sys/Posix.pia`, and writes `lib/Pia/Sys/Gen/<target>.pia`, the module `Pia.Sys.Posix` for that target ([ADR 0057](adr/0057-posix-module-per-target-behind-one-interface.md)). It holds every constant's value and C type, every struct's size, alignment and field offsets, each row of the interface as an `extern` with the row's modifiers and contract, and the other functions as `extern`s without one, which stay private to the module. A row that does not fit the header fails the generator: a missing symbol, a type of the wrong width, `mutable` or `out` on a `const` pointer, or a variadic mismatch. A pointer becomes a byte buffer. A function Pia cannot declare yet, such as `mmap`, which returns a pointer, is listed at the end of the file with the reason. The bindings workflow regenerates each file on its own platform and fails on any difference, and the build picks the file by platform (`//lib/Pia/Sys:posix`).

Foreign memory comes back as an address, a `usize`, and `unsafe view addr n` makes it a slice (`pia.view`, marked `pia.unsafe`). Codegen builds the memref descriptor an LLVM lowering of a memref expects, with `addr` as its pointer, offset 0, `n` elements and stride 1, so loads, stores and slices of it lower as usual. tests/codegen/pages.pia fills and sums pages from mmap.

## Lowerings written in Pia

`@lower("mlir")` after a function's return type gives it an MLIR form ([ADR 0065](adr/0065-lowerings-written-in-pia.md)). The Pia body stays: the verifier proves it against the contract as usual, callers prove from the contract, and the body is what the REPL's JIT runs and what `piac --lower=off` compiles everywhere, for differential tests. Codegen puts the MLIR in place of the body:

<!-- untested: needs a @trusted file; tests/codegen/lower_linalg.pia is the tested copy -->
```ocaml
let matmul (a : [i8; 16]) (b : [i8; 16]) (c : out mutable [i32; 16]) : unit
  @lower("%a = memref.expand_shape $a [[0, 1]] output_shape [4, 4] : $a.type into memref<4x4xi8>  %b = memref.expand_shape $b [[0, 1]] output_shape [4, 4] : $b.type into memref<4x4xi8>  %c = memref.expand_shape $c [[0, 1]] output_shape [4, 4] : $c.type into memref<4x4xi32>  %zero = arith.constant 0 : i32  linalg.fill ins(%zero : i32) outs(%c : memref<4x4xi32>)  linalg.matmul ins(%a, %b : memref<4x4xi8>, memref<4x4xi8>) outs(%c : memref<4x4xi32>)")
= for i in 0 .. 4 do
    for j in 0 .. 4 do
      c.[i * 4 + j] <- a.[i * 4] * b.[j] + a.[i * 4 + 1] * b.[4 + j]
        + a.[i * 4 + 2] * b.[8 + j] + a.[i * 4 + 3] * b.[12 + j]
    done
  done
```

- **Splices.** `$name` is the SSA value of the parameter `name`, and `$name.type` its core MLIR type from the table [above](#types), so `$a.type` here is `memref<16xi8>`. A spliced parameter is an integer, a bool, or a buffer of them, which is one value. A record is several values, and is refused unless its type has `@lower`. `$result` is the lowering's value, for a function that returns one: `$result = arith.subi $x, %one : i8` defines it, and codegen adds the `return`. A lowering that defines `$result` gives only that, so it may write no buffer ([ADR 0078](adr/0078-pia-lib-ops-with-proved-substitutions.md)). Escapes in the string are decoded first (`\n`, `\t`, `\"`, `\\`), and MLIR needs no newlines between ops.
- **Types.** `@lower("memref<4x4xi8>", data)` on a record names the MLIR type its values have, as a view of the field that holds its elements ([ADR 0074](adr/0074-library-types-tensors.md), step 3a). In the type, `$n` splices a value parameter, `$s` a shape as `4x4`, and `$t` the elements' type parameter, so `grid i32 [4; 4] r` below has `memref<4x4xi32>`. A lowering that splices a value of the type gets the view, made before the lowering's own ops. An array field is viewed with `memref.expand_shape`, so `$a.type` is `memref<4x4xi8>`. A slice field may start part way into its storage, so it is cast to its length and viewed with a dynamic offset, `memref<4x4xi32, strided<[4, 1], offset: ?>>`. The body proves that length from the type's invariant: a goal at each such parameter says that `'c.data' holds 16 elements`. An `out` or `inout` value of such a type is written through its loan and comes back as it went in, so codegen returns it, and the function returns unit. An `out` or `inout` value of any other type would come back changed, which MLIR text cannot say, so it is refused. Version 1 is a ranked `memref` with static extents and the identity layout. `tensor` comes with step 3b. The views are part of the hashed text in the trust report.

<!-- untested: needs a @trusted file; tests/codegen/lower_type.pia is the tested copy -->
```ocaml
let mat8 = type { data : [i8; 16] } @lower("memref<4x4xi8>", data)

let grid = let (t : type) (s : shape) (r : region) => type {
  data : borrowed(r) mutable [t]
} where len s = 2 && len data = s.[0] * s.[1]
  @lower("memref<$s x $t>", data)

let matmul (r : region) (a : mat8) (b : mat8) (c : inout grid i32 [4; 4] r)
  : unit
  @lower("%zero = arith.constant 0 : i32\nlinalg.fill ins(%zero : i32) outs($c : $c.type)\nlinalg.matmul ins($a, $b : $a.type, $b.type) outs($c : $c.type)")
= ...
```

- **Computed lowerings.** `@lower(gen args)`, where `gen` is a `let meta` that returns a string, runs `gen` during expansion ([meta.md](meta.md)), and the string becomes the attribute's text, as if it were written there; `piac --dump-expanded` shows it. In the arguments, the function's parameters stand for themselves, as names, as a tactic's do, so `name a` is `"a"`. So one metaprogram can write the MLIR for several shapes or element types: tests/codegen/lower_meta.pia computes the matmul above with `@lower(square_matmul 4 a b c "i8" "i32")`. A metaprogram that fails, or returns anything but a string, is an error at the attribute.
- **Parsing.** After `lowerToCore`, `applyLowerings` (`src/codegen/Lowerings.cpp`) splices in the core arguments, wraps the text as the body of `func.func @pia_lowering` with the function's core signature, adds `return` when the function returns nothing (one that returns an integer or a bool ends with its own `return`), and parses and verifies it with MLIR's parser against the dialects piac registers: `linalg`, `tensor`, `bufferization`, `transform`, `affine` and the core ones. A misspelt op or a type that does not match is an error at the attribute, with MLIR's message and its line and column in the spliced text, which a note prints. The parsed body then replaces the function's, with every op located at the attribute, so a later error points there too. `--emit=core` shows the lowered form, `linalg` included.
- **Checked first.** The same splice and parse, and the operand-effect check below, run on a copy of the module as soon as IRGen has made it, before anything is proved, in every mode that makes IR (`--emit=mlir`, `--verify`, codegen) and in the REPL, whose JIT still runs the body (`checkLowerings`). So a mistake in the MLIR costs no proving time. A module that `lowerToCore` cannot compile yet is not checked there; codegen says why if it is compiled.
- **Operand effects.** A lowering may write only the buffers the Pia signature lets it write: those of `out` and `inout` parameters, and the buffers codegen adds, such as an array result's. Every op's memory effects are read through MLIR's `MemoryEffectOpInterface`, following memref's views (`expand_shape`, `subview`, `reinterpret_cast`, `cast`) back to the parameter, so a linalg op whose `outs` view an input, a `memref.store` into one, or a `memref.dealloc` of one is an error that names the op and the parameter. An op with no declared effects that takes an input buffer is refused too, since it could write it. Reading inputs and writing the lowering's own `alloca`s is allowed (tests/irgen/lower_effects.pia).
- **Calls.** A call of a function with `@lower` is `pia_lib.call @f(...)` in core IR ([ADR 0078](adr/0078-pia-lib-ops-with-proved-substitutions.md), step 1), an op that names the Pia function whose body is its meaning, so `--emit=core` shows which calls have a rule. Before LLVM, `pia-lib-lower` substitutes the rule for each one: the function's lowered body, inlined at the call (step 2). With `--lower=off`, or for a lowering that allocates or has more than one block, it is a call of the function instead (tests/codegen/lib_call.pia).
- **Passes.** `linalg` on memrefs goes to `scf` loops with `convert-linalg-to-loops`, then `memref.expand_shape` and the other reshapes to plain descriptors with `expand-strided-metadata`, and `affine` to `arith` with `lower-affine`, before the usual passes. `tensor` ops parse, but nothing bufferises them yet (step 6 of the ADR), so a lowering works on the buffers' memrefs.
- **Trust.** In steps 1 and 2 of ADR 0065 piac does not yet prove that the MLIR does what the body does, so `@lower` is allowed only in a file marked `@trusted`, on a function with a Pia body (not an `extern`, a spec function or a lemma), and every lowering is a trusted item. `piac --verify --trust-report` lists it with the ops it uses and the SHA-256 of its spliced text, and the object's certificate records the same hash ([abi.md](abi.md)). A named `linalg` op's own body is generated from its definition, so the ops in it are not listed; a `linalg.generic`'s are.

`linalg.matmul` adds to its output, so the lowering fills it with zero first, as the body's assignments do; without the fill the differential run below fails, which is the check a trusted lowering has. tests/codegen/lower_linalg.pia is the matmul above, checked at `--emit=core` with and without `--lower=off`, in the trust report and in the certificate, and run from C in lower_linalg_test.c, once from each form. tests/codegen/lower_meta.pia computes the same lowering with a metaprogram and is run from the same harness (`lower_meta_run_test`). tests/codegen/lower_type.pia lowers the matmul over a lowered array type and a lowered slice type. tests/codegen/lower_invalid.pia holds MLIR errors, tests/irgen/lower_effects.pia the operand-effect check, and tests/irgen/lower_errors.pia, lower_meta_errors.pia, lower_untrusted.pia, lower_type_errors.pia and lower_type_inout_errors.pia the rules.

## Tests

- `tests/codegen/*.pia` are lit tests. They check `--emit=core` and `--emit=llvm`, the refusal to compile a program with a failed or unproved obligation, and `--allow-unproved`. They run on any host: the lit runner compiles for `arm64-apple-macosx14.0.0` unless a RUN line passes its own `--target`, so the expected IR is the same everywhere.
- `//tests/codegen:saturate_test` compiles `saturate.pia` to an object file and links it with `saturate_test.c`. The harness compares saturating, wrapping and proof-mode arithmetic, a slice loop and a fixed array against C reference implementations. The 8-bit cases cover every input. The test runs on arm64 macOS and on x86_64 Linux. On other platforms Bazel skips it as incompatible.

## Limits of v0

- There is no vectorisation yet. Loops compile to scalar code, apart from whatever LLVM's own vectoriser does with them.
- `dyn`, buffers nested deeper than a buffer of slices, and buffer results are not lowered.
- A recursive value's layout keeps every constructor's fields side by side, and a box's slot as a whole memref descriptor; the published union layout of ADR 0030, a box as one pointer and `option (box t)` as a nullable one, comes later.
- An atomic cell crosses the C boundary as a pointer to its element, like a one-element array.
- `scf.for` compares its bounds as signed 64-bit integers, so a slice of 2^63 elements or more is not supported.
