# 49. Linux x86_64 is a second target, tested in Linux CI, and each target is a model of a built-in `Pia.Target` theory

Date: 2026-11-22

Status: Accepted (2026-11-23, with Dean's answers to its three questions, recorded under "Answers" below and folded into the decision).

## Context

Every Pia build target is restricted to Apple silicon. Codegen defaults to `arm64-apple-macosx14.0.0` with `-mcpu=apple-m1` ([src/codegen/Codegen.h](../../src/codegen/Codegen.h)), and nine BUILD files mark everything that runs `piac` as `target_compatible_with = [macos, arm64]`. So every proof, build and test runs on Dean's iMac or on the macOS CI runner, which is slow when cold (about 2.5 hours) and is the only place proof work happens.

Dean asked for three things: run the proof work in the cloud, add Linux x86_64 as a real target, and encode the differences between platforms, such as the arm64 and x86_64 memory models, as theories the solver knows about.

Most of the compiler is target-independent already. The parser, sema, IRGen and the verifier never look at the target, and LLVM is configured with both the AArch64 and X86 back ends ([MODULE.bazel](../../MODULE.bazel)). What depends on the target today:

- **Codegen.** The triple, the CPU, the data layout, and the C calling convention. Pia's C ABI ([docs/codegen.md](../codegen.md#c-abi)) passes records through an out-pointer and extends integers narrower than 32 bits at the call, which both Apple arm64 and the x86_64 System V ABI expect.
- **Facts the proofs assume but never state.** Pointers are 64 bits, so `usize` is `u64`. Bytes are little-endian. `Pia.Mem.alloc` returns 16-byte-aligned blocks. A page is 16 KiB. A cache line is 128 bytes, which is what false-sharing padding is sized by. None of these hold on every target, and two of them (pages and cache lines) differ between the two targets here.
- **The hardware memory model.** arm64 is weakly ordered: loads and stores may be reordered with each other unless a barrier or an acquire/release instruction orders them. x86_64 is TSO: the only reordering is a later load passing an earlier store to a different address. [ADR 0027](0027-coroutines-and-race-freedom.md) defines Pia's memory orders at the language level (sequentially consistent, release/acquire, and `relaxed` where its value orders nothing), and [docs/theories.md](../theories.md#happens-before-and-memory-orders) gives them as a theory.
- **The operating system.** System calls, `errno` values, `open` flags and `mmap` constants differ between Darwin and Linux. `Pia.Sys` goes through libc on both, because Darwin's system-call numbers are not a stable ABI.
- **Layouts.** [ADR 0030](0030-published-object-layouts.md) publishes the optimised layout of each type in the ABI. Layouts depend on pointer width, alignment and endianness.

Several hardware differences matter less to Pia than to C, because the proofs already exclude the behaviour that differs. Integer division by zero and `INT_MIN / -1` trap on x86_64 and do not on arm64, shifts by the width or more are masked differently, and signed overflow wraps on both. Pia proves every division nonzero, every shift in range and every overflow handled, so a proved program never reaches any of them.

## Decision

### 1. Proofs and the compiler run on Linux, and CI runs there too

The constraint applies only to what runs compiled Pia code: a `cc_test`, `sh_test` or `cc_binary` that links a Pia object. Proving a file, compiling it to an object, IRGen and the lit tests run on any host, so their `target_compatible_with` is removed, and each Pia object is compiled for the platform Bazel is building for (section 2).

CI gets a second job, `bazel test (Linux x86_64)`, on `ubuntu-24.04`, which builds and tests `//...` with the same disk-cache scheme as the macOS job. It also runs the proof benchmark ([ADR 0032](0032-parallel-sliced-cached-proving.md)). A separate Linux baseline was planned, in case Z3 built on Linux spent a different rlimit on the same query, but the first Linux run matched the iMac's baseline on several files exactly and cost no more than 1.5% above it on any, so both jobs gate on `tools/bench/baseline.json`. The macOS job stays, because arm64 macOS is still the product target and the only place Apple-specific code runs.

For day-to-day work, slow proofs move to Linux: a cloud session can prove, compile and test the x86_64 build on its own, and the iMac is needed only for what must run on arm64 macOS.

### 2. `x86_64-unknown-linux-gnu` is a codegen target

`piac` has two targets, named by their LLVM triples:

| Target | Triple | Default CPU | Object |
|---|---|---|---|
| Apple silicon (product) | `arm64-apple-macosx14.0.0` | `apple-m1` | Mach-O |
| Linux x86_64 | `x86_64-unknown-linux-gnu` | `x86-64-v3` | ELF |

`x86-64-v3` is AVX2, FMA and BMI2, which every x86_64 server sold since about 2015 has, and which gives the vectoriser 256-bit vectors. It is the minimum, not just the default: `piac` refuses an x86_64 `--cpu` that lacks any v3 feature, so older machines are not supported.

`piac`'s default target is the host it runs on, chosen when `piac` is built, and `--target` overrides it. Bazel never relies on the default: `pia_object` and `pia_library` pass `--target` and `--cpu` from the platform being built for, through a `select`, so cross-compiling is a platform flag, and the object always matches the code it is linked with.

The C ABI is unchanged. Both targets extend integers narrower than 32 bits at the call and return records through an out-pointer, so the same lowering serves both. The code that adds those attributes says so for both ABIs, and the C harness tests in `//tests/codegen` and `//examples` run on both.

`Pia.Sys` and `Pia.Mem` get a Linux side wherever they name an OS constant: `MAP_ANON` is `0x1000` on Darwin and `0x20` on Linux, and the `errno` values in each error set are mapped per OS. These constants come from the target's model (section 3), never from literals in the library.

### 3. Each target is a model of a built-in theory, `Pia.Target`

`Pia.Target` is a theory in the sense of [ADR 0036](0036-library-theories.md), built into the compiler rather than written in a library. Its signature names every fact about the machine a proof may use:

```ocaml
let theory Target = sig
  let spec ptr_bits : usize
  let spec little_endian : bool
  let spec max_align : usize          \ alignment Pia.Mem.alloc guarantees
  let spec page_size : usize
  let spec cache_line : usize         \ destructive interference size
  let spec vector_bits : usize        \ widest vector the CPU executes natively

  let axiom ptr_pow2 ensures is_pow2 ptr_bits && ptr_bits >= 32
  let axiom little ensures little_endian
  let axiom align_16 ensures max_align = 16
  let axiom page_pow2 ensures is_pow2 page_size && page_size >= 4096
  let axiom line_pow2 ensures is_pow2 cache_line && cache_line >= 64
  let axiom vector_min ensures vector_bits >= 128
end
```

The axioms are what both targets have in common, and they are all a target-generic program may assume. A program proved against them holds on both targets, and on any later target whose model meets them. Each axiom must be true of every build of the architectures Pia targets, not just of the two triples it has today, so a later triple on the same architecture can never break a target-generic proof:

- **Little-endian is an axiom.** x86_64 is little-endian in every mode, on Intel and AMD alike: AMD64 and Intel 64 are one architecture, and nothing in it is byte-order configurable. arm64 *can* run big-endian (the `aarch64_be` triples), but Apple's platforms never do, and a big-endian arm64 target would be a new architecture variant for Pia, with this axiom reconsidered then.
- **64-bit pointers are not an axiom.** Pointer width is a property of the ABI, not of x86_64. The same 64-bit CPU runs 32-bit code with 32-bit pointers in compatibility mode (the i386 ABI under a 64-bit OS), and Linux's x32 ABI (`x86_64-unknown-linux-gnux32`) runs in 64-bit mode with 32-bit pointers. So `ptr_bits` is a value of each model, 64 for both of Pia's triples, and the theory only says it is a power of two of at least 32. `usize` is then as wide as the model says, and target-generic code that needs 64-bit pointers marks itself `@target(m)` for the models with 64-bit pointers, or branches on `if Target.is m`, which folds to one branch per target. Even on 64-bit ABIs, only 48 bits of a virtual address are in use with 4-level paging and 57 with 5-level paging (LA57), which is one more reason [ADR 0030](0030-published-object-layouts.md) never tags a pointer's high bits.

Every axiom a module's proof used is listed in its certificate ([ADR 0024](0024-published-proof-certificates.md)).

Each target is a model of the theory, with each spec given its value:

| Spec | `arm64-apple-macosx` | `x86_64-unknown-linux-gnu` |
|---|---|---|
| `ptr_bits` | 64 | 64 |
| `little_endian` | true | true |
| `max_align` | 16 | 16 |
| `page_size` | 16384 | 4096 |
| `cache_line` | 128 | 64 |
| `vector_bits` | 128 (NEON) | 256 (AVX2 at `x86-64-v3`) |

`piac` proves that each model meets the axioms, as for any model ([ADR 0036](0036-library-theories.md)), so the theory is consistent by construction.

Code that needs a target's own value says so with `@target`:

```ocaml
let huge_page_count (bytes : usize) : usize @target(x86_64_linux)
  requires bytes <= 1000000
  ensures result * Target.page_size >= bytes
= (bytes + 4095) / 4096
```

Like `@overflow`, the attribute follows the return type. Inside `@target(m)`, the solver sees model `m`'s definitions as well as the axioms, and the item is compiled only for that target. An exported `@target` item appears only in that target's interface, and its importers must be `@target` of the same model, or reach it from the `then` of an `if Target.is m`, which `piac` folds at compile time, so the other target's branch is never compiled. This is an ordinary `if`, not a new keyword. The certificate lists each module's `@target` items.

Constants such as `cache_line` are values, not just facts: `Pia.Sync` pads a contended atomic to `Target.cache_line`, so it is 128 bytes on Apple silicon and 64 on x86_64, and the layout ([ADR 0030](0030-published-object-layouts.md)) published for each target says which.

### 4. The hardware memory model is part of the target, and the language model stays the same on both

Pia programs are proved against the language memory model of [ADR 0027](0027-coroutines-and-race-freedom.md), on every target. That is what makes a target-generic proof about atomics hold on both machines.

Each target's model also includes its hardware memory model, as a theory of the same shape as `Order` in [docs/theories.md](../theories.md#happens-before-and-memory-orders): `po`, `rf` and the hardware's preserved program order, `ppo`. On x86_64 (TSO), `ppo` relates every pair of accesses except an earlier store and a later load. On arm64, `ppo` relates an access to a later one only through an address, data or control dependency, a barrier, or an acquire or release instruction.

The hardware models are used in two ways:

1. **The lowering is proved.** For each memory order and each target, codegen picks instructions: on arm64, `ldar`/`stlr` for acquire and release, and `dmb ish` where a fence is needed; on x86_64, plain `mov` for acquire loads and release stores, and `xchg` (or `mov` and `mfence`) for sequentially consistent stores. A lemma per target proves that the hardware order of the chosen instructions gives every happens-before edge the language model promises. These are compiler lemmas, proved when the compiler is built, and a mistake in the instruction table is a failed lemma rather than a miscompiled program.
2. **Code may rely on TSO, but only inside `@target(x86_64_linux)`, only for atomics, and only as far as it is proved at compile time.** Under TSO every atomic store is a release and every atomic load an acquire at no cost, but only if the compiler does not reorder them either: LLVM may move a `monotonic` access past another. So on x86_64 Pia lowers `relaxed` atomics to LLVM `release` stores and `acquire` loads. They compile to the same `mov` instructions, and they forbid only the compiler's own reorderings. The target model then adds two axioms, `every atomic store releases` and `every atomic load acquires`, which are true of the code Pia emits. They are not trusted: after LLVM's optimisation, `piac` checks every atomic access in each `@target(x86_64_linux)` item that relied on them, and each must still be an acquire or release (or stronger) access in the final IR, with no fence or ordering removed. A check that fails is a compile error, like a failed goal, so the axioms are proved of each program rather than assumed. With them, the message-passing idiom with a `relaxed` flag (`publish_relaxed` in [docs/theories.md](../theories.md#happens-before-and-memory-orders)) proves on x86_64 and fails everywhere else, which is exactly the hardware's behaviour.

Plain, non-atomic accesses are never ordered by either model. A data race on them is a race on both targets, and stays a compile error ([ADR 0027](0027-coroutines-and-race-freedom.md)).

### 5. Build order

1. Linux builds and proves (section 1): constraints relaxed, Linux CI job, Linux proof baseline. No language change.
2. The x86_64 target (section 2): `piac` default target from the host, `--target` from the Bazel platform, C harness tests on Linux.
3. `Pia.Target` and the hardware memory models (sections 3 and 4), after Dean has reviewed this ADR.

## Answers (Dean, 2026-11-23)

1. **TSO-reliant code:** yes, and it must be proved at compile time. Section 4.2 now checks, for each program, that the emitted atomics really are acquire and release after optimisation, on top of the per-target lowering lemmas.
2. **The x86_64 CPU:** `x86-64-v3`, and no older. It is the minimum, and `piac` refuses a CPU without its features (section 2).
3. **Axioms for pointer width and byte order:** only if true of every x86_64 build. Little-endian is, on Intel and AMD alike, since they implement one architecture. 64-bit pointers are not: compatibility mode and the x32 ABI both run 32-bit pointers on a 64-bit CPU, so the width is per ABI, not per vendor or architecture. Section 3 keeps `little` as an axiom and makes `ptr_bits` a model value.

The questions, as they were asked:

1. **TSO-reliant code (section 4.2).** Allowing `@target(x86_64_linux)` code to rely on TSO for `relaxed` atomics costs nothing at run time, but it makes such code non-portable by design. The alternative is to prove every program only against the language model and use the hardware models only for the lowering lemmas. The recommendation is to allow it: it is opt-in, it is visible in the certificate, and a port to arm64 then fails to prove rather than failing at run time.
2. **The default x86_64 CPU.** `x86-64-v3` (AVX2) or `x86-64-v2` (SSE4.2 only)? The recommendation is v3, since Pia is aimed at SIMD pipelines and every current cloud and desktop x86_64 machine has it.
3. **Should `ptr_64` and `little` be axioms?** They make target-generic code simpler today. Leaving them out would make code that depends on them say `@target`, or prove a `when Target.ptr_bits = 64` branch, so a 32-bit or big-endian port would be free of hidden assumptions from the start. The recommendation is to keep them as axioms, listed in the certificate, until a target without them is planned.

## Consequences

- Proof work, the whole x86_64 build and its tests run in a cloud session and in Linux CI. The iMac is needed only for arm64 runs.
- `usize` is as wide as the target model says. Today it is 64 bits on both targets, and `piac` refuses a model whose pointers are another width until `usize` can follow it.
- Every proof that used a machine fact now names it, through the `Pia.Target` axioms or a model under `@target`, and the certificate lists it.
- Two targets means two published layouts per type and two interfaces where `@target` items differ.
- On x86_64, `relaxed` atomics lose some compiler reorderings, which costs nothing in the instructions emitted.
- The lowering lemmas need the hardware memory models written as theories, which is new work, and the model checker's RC11 mode ([ADR 0027](0027-coroutines-and-race-freedom.md)) is still needed for `relaxed` on arm64.
- CI cost doubles: a second cold build of LLVM, MLIR and Z3, cached as on macOS.
