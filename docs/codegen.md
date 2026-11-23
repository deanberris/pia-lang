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
2. **Lower `pia` to core dialects.** This uses MLIR dialect conversion, with the type mapping below and the ops after it. `scf`, `func.call` and `func.return` are converted structurally.
3. **Lower to the `llvm` dialect.** The upstream passes run in this order: `scf` to `cf`, then `cf`, `arith`, `index`, `memref` and `func` to `llvm`, then the reconciliation of casts. Then each public function gets its C entry point.
4. **Translate and optimise.** The module is translated to LLVM IR, given the target's data layout, and run through LLVM's `-O2` pipeline.
5. **Emit.** The LLVM target machine writes the object file or the assembly.

## Types

A range type is stored in the smallest machine integer that holds its range: 8, 16, 32, 64 or 128 bits. It is signed if the range contains a negative value. So `u8` and `int{0..200}` become `i8`, `i8` stays `i8`, and `int{-1..200}` becomes `i16`. `bool` is `i1`, and an index is `index`.

| Pia | Core MLIR |
| --- | --- |
| `!pia.int<lo, hi>` | `iN`, as above |
| `[T; n]` | `memref<n x T>` |
| `[T]` | `memref<? x T, strided<[1], offset: ?>>` |
| `!pia.atomic<T>` | `memref<1 x T>`, with a `bool` held as `i8` |

A slice's offset is dynamic because `xs.[a .. b]` (`pia.slice`) is a view into the same storage: it lowers to `memref.extract_strided_metadata` and `memref.reinterpret_cast`, at the buffer's offset plus `a`, with `b - a` elements. At the C boundary a slice is still a pointer and a length, with offset 0. `abort ()` lowers to `llvm.intr.trap`. A constant array (`pia.const_array`) becomes a private constant `memref.global`, one per constant, which LLVM places in read-only data; each use is a `memref.get_global`. A `with_arena`'s region (`pia.region`) is a `memref.alloca` at the start of the function, zeroed by a loop where the `with_arena` is entered.

Records are scalarized before codegen ([irgen.md](irgen.md#records)). A buffer of records arrives as one buffer per field (struct of arrays), so `[pixel; 8]` is four `memref<8 x i8>`, which vectorises like any other buffer. A buffer whose elements are slices, such as a vector's box slots, becomes two buffers before lowering, `splitSliceBuffers` in `src/codegen/SliceBuffers.cpp` ([ADR 0048](adr/0048-buffers-whose-elements-hold-slices.md), step 3): its elements' addresses and their lengths, both `memref<? x index>`, the lengths marked `{pia.length_of}` the addresses. Storing a slice records `pia.address`, its storage's aligned pointer plus its offset in bytes, and its length; loading one rebuilds it from both with `pia.at_address`, a memref descriptor at that address with offset 0. The store that empties an element moved out (`pia.moved_out`) is code like any other, so a moved-out element's length is 0 at run time, as the proof has it. Buffers of buffers of slices and `dyn` are not lowered yet.

## Arithmetic

Each `pia.add`, `sub`, `mul`, `div` and `rem` is computed at one width. That width holds both operands and the result type. Unless the result was proved to fit, it also holds the exact result. The operands are extended by their own signedness, and the operation is signed if anything at that width can be negative. Then the overflow mode brings the exact value into the result type:

| Mode | Lowering |
| --- | --- |
| `proof` | nothing: the verifier proved the value fits, so the result is truncated |
| `saturate` | clamp to `[lo, hi]` with `max` and `min`, then truncate |
| `wrap` | truncate when the type covers a whole machine integer, as `u8` and `i32` do. Otherwise `lo + ((x - lo) mod size)` |
| `trap` | `llvm.intr.trap` if the value is outside `[lo, hi]` |

`pia.convert` is the same with the input as the exact value. `pia.cmp` extends both sides to a width that holds both ranges. `to_index` and `from_index` become `index_cast` (or `index_castui` when the value is non-negative). `len` becomes `memref.dim`, or a constant for a fixed array. `load` and `store` become `memref.load` and `memref.store`, without bounds checks, because the verifier proved them in bounds.

LLVM recognises the widen-clamp-truncate pattern, so `add_px` on `u8` with `@overflow(saturate)` compiles to `llvm.uadd.sat.i8`. In a loop over slices, such as `add_rows` in `tests/codegen/saturate.pia`, LLVM's loop vectoriser turns it into NEON `uqadd.16b`.

## Atomics

An atomic cell is a one-element memref ([ADR 0052](adr/0052-atomics.md), section 5). `atomic_new` is a `memref.alloca` at the start of the function and a plain store, since nothing else sees the cell yet. Every other op is an LLVM atomic on the memref's aligned pointer, at the element's alignment: `llvm.load` and `llvm.store` with an ordering, `llvm.atomicrmw`, `llvm.cmpxchg` (whose old value is the result) and `llvm.fence`. `relaxed` is LLVM's `monotonic`, and the other orders keep their names. `atomic_min` and `atomic_max` are `min` and `max` on a signed cell, `umin` and `umax` otherwise. A `bool` is a byte, since LLVM's atomics take whole bytes.

An add or sub lowers by its stated mode. `wrap` and `proof` are one `atomicrmw`. `trap` is one too, after which the exact result is computed from the old value it returns, at twice the cell's width, and checked as trap arithmetic is, so the cell already holds the wrapped value when the program stops. `saturate` is a loop: a relaxed load, then `cmpxchg` of the old value for the clamped result until no other task changed the cell in between, so no wrapped value is ever stored. The loop's failure order is the read half of the op's order.

LLVM's backends choose the instructions, which are those of ADR 0052's table. `tests/codegen/atomics.pia` compiles one function per (operation, order) for both targets and checks the instructions with FileCheck. Both targets detect a `trap` overflow from the old value for now; the target model's `rmw_flags` records that x86_64's `lock xadd` sets the flags, for a lowering that reads them. **TSO on x86_64** (ADR 0052, section 6). Inside a `@target(x86_64_linux)` item, where the target model says that every atomic store releases and every atomic load acquires (`Target.store_releases`, `Target.load_acquires`), a relaxed load is emitted as LLVM `acquire`, a relaxed store as `release`, and a relaxed read-modify-write or compare-and-swap as `acq_rel` (with an `acquire` failure order). On x86_64 these are the same `mov`, `xchg` and `lock` instructions, so the only cost is that LLVM may no longer reorder them. Each such access gets `!pia.tso` metadata naming its source location. After LLVM's optimisation pipeline, and before instruction selection, `piac` checks two things: every instruction with `!pia.tso` is still `acquire`, `release`, `acq_rel` or `seq_cst`, and every source location tagged before optimisation still has a tagged instruction. A failure is a compile error at that location, saying the optimiser weakened, or removed or merged away, an access the item's proof relies on. Inlining and unrolling copy the metadata, so every copy is checked. The check can be stricter than the proof needs, never weaker: an access the optimiser deletes because it can never run is an error too (`tests/codegen/tso_check.pia`). Outside such items, `relaxed` stays `monotonic` on both targets. `tests/codegen/tso.pia` checks the lowering.

## C ABI

Each Pia function `f` becomes an internal function. Only the functions a module exports through an interface also get a C entry point ([ADR 0039](adr/0039-module-and-interface-syntax.md)): one in an interface marked `@abi(c)` is named `f`, and one in any other interface is named after its module's path, so `luma` in `module Image.Pixels` is `pia$Image$Pixels$luma`. A file with no `module` header exports nothing but its `main`. Private functions keep internal linkage, so LLVM can inline them and remove the ones nothing calls. An exported function also keeps its Pia calling convention under its module's link symbol, `__pia$Image$Pixels$luma`, which is what another module calls when it imports the function: the importer's object file declares that symbol and has no body for it, so the two object files must be linked together (the `pia_library` rule does this). Calls between Pia functions use the internal one, which takes MLIR memref descriptors. The entry point maps C arguments onto it:

| Pia parameter | C parameters |
| --- | --- |
| an integer | the integer type of its storage width, such as `uint8_t` or `int16_t` |
| `bool` | `bool` |
| `[T]` | `const T *data, uint64_t len` (or `T *` when it is written) |
| `[T; n]` | `const T *data` (or `T *`) |

A record parameter is passed as its fields, in declaration order, so `blend (p : pixel) (q : pixel) : pixel` takes eight `uint8_t` arguments. A record result is written through a pointer to a C struct of its fields, which is the last argument. Each field sits at its natural C offset, aligned to its own size:

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

A parameter, local or record field whose type is spec-only (`int`, `real` or a theory's sort) is state the verifier sees and the program does not have ([ADR 0041](adr/0041-allocator-semantics-as-a-theory.md)). Code can only store spec values in such places, so nothing the program computes reads them. `eraseContracts` replaces every computation of a spec-only value left in code, such as `Alloc.take t.heap b` stored into a field, with `pia.erased`, and marks the spec-only parameters and results `{pia.erased}`. `lowerToCore` lowers each spec-only value to an `i1` that nothing reads, and LLVM removes it. The C entry points leave spec-only parameters and fields out: `skip (n : int) (x : u8) : u8` is `uint8_t skip(uint8_t x)`, and a result `{ v : u8; steps : int }` is returned as its one remaining field, a `uint8_t`. A spec-only field of a buffer's records is a buffer of its own, struct of arrays like every field: `eraseContracts` removes the stores into it, its loads are spec-only values like any other, and it is marked `{pia.erased}`. Its C entry point leaves it out, and when the fields share one length the first field kept takes it, so `[{ steps : int; v : u8 }]` is `uint8_t *v, int64_t n`, and `len xs` reads the length of a field in code. tests/codegen/spec_state.pia is run from C by spec_state_test.c.

## Foreign functions

`let f (x : i32) : i32 ensures ... = extern "sym"` declares a C function (#55). IRGen makes `f` a private function whose whole body is `pia.foreign "sym"(...)`, marked `pia.extern`, so callers see its contract like any other function's: preconditions are proved at each call and postconditions are assumed. The verifier never proves the stub itself; the contract is trusted, and `piac --verify --trust-report` lists it.

A foreign function without a `requires` or `ensures` can be called only as `unsafe f x`. The call is marked `pia.unsafe`: the verifier assumes nothing about its result beyond its type, and treats every buffer passed to it as written. `--trust-report` lists each such call site.

Codegen declares `sym` once, as a private function with C types, and calls it. An integer keeps its width, extended to 32 bits as Apple's arm64 ABI and x86_64 System V expect (`llvm.zeroext` or `llvm.signext`), and a bool is a zero-extended `i1`. A buffer is passed as a pointer to its first element, which for a view (`xs.[a .. b]`) is part way into its storage; pass its length as a separate `usize` argument. If the Pia declaration has the same name as the symbol, it is renamed `pia$ffi$sym`. For now a foreign function takes integers, bools and buffers of integers, and returns an integer, a bool or unit. tests/codegen/ffi_run.pia runs against C in ffi_test.c.

A C variadic function, such as `open` or `syscall`, is declared with `@variadic(n)` after the return type, where `n` is the number of its named C parameters ([ADR 0051](adr/0051-variadic-generics-and-foreign-varargs.md)). Codegen declares the symbol as an `llvm.func` with `...` and emits each call as `llvm.call ... vararg(...)`, so LLVM applies the variadic convention: Apple arm64 passes the arguments after the named ones on the stack, and x86_64 System V sets `%al`. Several declarations may call one symbol at different arities, such as `open` and `open_mode`, as long as they agree on `n` and on the named parameters. A variadic argument must be an integer of 32 bits or more, or a buffer, because C promotes anything narrower to an `int`, and IRGen says to widen it rather than doing it silently. tests/codegen/ffi_variadic.pia checks the lowering, and ffi_run.pia runs two arities of one symbol and a buffer passed through `...` against C.

A C function of no arguments, such as `getpid`, is declared like any Pia function of none, `let getpid () : i32 = extern "getpid"`, and called by its name alone, `getpid`.

The POSIX declarations are not written by hand. `tools/bindings/gen.py` reads the names in `tools/bindings/posix.toml` from the target's own headers with clang's JSON AST and writes `lib/Pia/Sys/Gen/<target>.pia`: every constant's value and C type, every struct's size, alignment and field offsets, and every function's C signature as an `extern` without a contract, which only `unsafe` can call until the contract overlay gives it one ([ADR 0051](adr/0051-variadic-generics-and-foreign-varargs.md), section 6). A pointer becomes a byte buffer. A function Pia cannot declare yet, such as `mmap`, which returns a pointer, is listed at the end of the file with the reason. The bindings workflow regenerates each file on its own platform and fails on any difference.

Foreign memory comes back as an address, a `usize`, and `unsafe view addr n` makes it a slice (`pia.view`, marked `pia.unsafe`). Codegen builds the memref descriptor an LLVM lowering of a memref expects, with `addr` as its pointer, offset 0, `n` elements and stride 1, so loads, stores and slices of it lower as usual. tests/codegen/pages.pia fills and sums pages from mmap.

## Tests

- `tests/codegen/*.pia` are lit tests. They check `--emit=core` and `--emit=llvm`, the refusal to compile a program with a failed or unproved obligation, and `--allow-unproved`. They run on any host: the lit runner compiles for `arm64-apple-macosx14.0.0` unless a RUN line passes its own `--target`, so the expected IR is the same everywhere.
- `//tests/codegen:saturate_test` compiles `saturate.pia` to an object file and links it with `saturate_test.c`. The harness compares saturating, wrapping and proof-mode arithmetic, a slice loop and a fixed array against C reference implementations. The 8-bit cases cover every input. The test runs on arm64 macOS and on x86_64 Linux. On other platforms Bazel skips it as incompatible.

## Limits of v0

- There is no vectorisation yet. Loops compile to scalar code, apart from whatever LLVM's own vectoriser does with them.
- `dyn`, buffers nested deeper than a buffer of slices, and buffer results are not lowered.
- An atomic cell crosses the C boundary as a pointer to its element, like a one-element array.
- `scf.for` compares its bounds as signed 64-bit integers, so a slice of 2^63 elements or more is not supported.
