# Codegen v0

Status: implemented in M6 ([#7](https://github.com/deanberris/pia-lang/issues/7)).

`piac --emit=obj -o file.o file.pia` verifies a program ([verifier.md](verifier.md)) and compiles it to an object file for Apple Silicon. The result links with C. The other outputs stop earlier in the pipeline:

| Flag | Output |
| --- | --- |
| `--emit=core` | MLIR in `arith`, `scf`, `memref` and `func`, after contracts are erased |
| `--emit=llvm` | optimised LLVM IR |
| `--emit=asm` | assembly |
| `--emit=obj` | an object file, written to `-o` |

`--target=<triple>` and `--cpu=<name>` choose the machine. The defaults are `arm64-apple-macosx14.0.0` and `apple-m1`. `-O0` to `-O3` set the optimisation level, which defaults to `-O2`.

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

1. **Erase contracts.** Every `pia_contract` op is removed: `requires`, `ensures`, `invariant`, `decreases`, `assert`, `assume` and `obligation`. Then everything only they used is removed too, including quantifiers, `old` and the arithmetic inside contracts. That includes calls to ordinary functions and loads: an op whose every use is in a contract, or in another such op, never runs, so it goes even when it is not known to be pure (a call to another module's function is a declaration here). Kept, such code could run a contract's `xs.[result]` when `result = len xs`, since a contract evaluates both sides of `&&`, and LLVM would treat the out-of-bounds load as undefined behaviour (tests/codegen/contract_only.pia). Only ops that write, allocate or free are kept. Spec functions and lemmas (`pia.spec`, `pia.lemma`) are erased with every call to them: they exist only for the verifier. The verifier's `pia.proved` attributes stay.
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

A slice's offset is dynamic because `xs.[a .. b]` (`pia.slice`) is a view into the same storage: it lowers to `memref.extract_strided_metadata` and `memref.reinterpret_cast`, at the buffer's offset plus `a`, with `b - a` elements. At the C boundary a slice is still a pointer and a length, with offset 0. `abort ()` lowers to `llvm.intr.trap`. A constant array (`pia.const_array`) becomes a private constant `memref.global`, one per constant, which LLVM places in read-only data; each use is a `memref.get_global`. A `with_arena`'s region (`pia.region`) is a `memref.alloca` at the start of the function, zeroed by a loop where the `with_arena` is entered.

Records are scalarized before codegen ([irgen.md](irgen.md#records)). A buffer of records arrives as one buffer per field (struct of arrays), so `[pixel; 8]` is four `memref<8 x i8>`, which vectorises like any other buffer. Buffers of buffers and `dyn` are not lowered yet.

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

Integers narrower than 32 bits are marked `zeroext` or `signext`, as the Apple arm64 ABI requires. Signedness comes from the range type. Once a range type is lowered to a signless `iN`, its signedness would be lost, so `lowerToCore` records it as a `{pia.signed}` argument or result attribute. Unit results are `void`. A prime cannot appear in a C name, so each `'` in a function's name becomes `_prime` in its entry point: `step'` is called as `step_prime`. Two functions whose C names would be the same are an error. Returning a buffer is not supported yet.

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

Codegen declares `sym` once, as a private function with C types, and calls it. An integer keeps its width, extended to 32 bits as Apple's arm64 ABI expects (`llvm.zeroext` or `llvm.signext`), and a bool is a zero-extended `i1`. A buffer is passed as a pointer to its first element, which for a view (`xs.[a .. b]`) is part way into its storage; pass its length as a separate `usize` argument. If the Pia declaration has the same name as the symbol, it is renamed `pia$ffi$sym`. For now a foreign function takes integers, bools and buffers of integers, and returns an integer, a bool or unit. tests/codegen/ffi_run.pia runs against C in ffi_test.c.

Foreign memory comes back as an address, a `usize`, and `unsafe view addr n` makes it a slice (`pia.view`, marked `pia.unsafe`). Codegen builds the memref descriptor an LLVM lowering of a memref expects, with `addr` as its pointer, offset 0, `n` elements and stride 1, so loads, stores and slices of it lower as usual. tests/codegen/pages.pia fills and sums pages from mmap.

## Tests

- `tests/codegen/*.pia` are lit tests. They check `--emit=core` and `--emit=llvm`, the refusal to compile a program with a failed or unproved obligation, and `--allow-unproved`. They run on any host whose LLVM includes the AArch64 target, which the Bazel build always does.
- `//tests/codegen:saturate_test` compiles `saturate.pia` to an object file and links it with `saturate_test.c`. The harness compares saturating, wrapping and proof-mode arithmetic, a slice loop and a fixed array against C reference implementations. The 8-bit cases cover every input. The test runs on arm64 macOS only. On other hosts Bazel skips it as incompatible.

## Limits of v0

- There is no vectorisation yet. Loops compile to scalar code, apart from whatever LLVM's own vectoriser does with them.
- `dyn`, nested buffers and buffer results are not lowered.
- `scf.for` compares its bounds as signed 64-bit integers, so a slice of 2^63 elements or more is not supported.
