# 68. GPU compute: a proved `spread` placed on the GPU, lowered through SPIR-V and SPIRV-Cross to Metal, launched by a small trusted shim

Date: 2026-11-25

Status: Accepted (2026-11-25, with Dean's answers below). Section 9 and step 4b, a placed sequence, are an amendment Proposed on 2026-11-27.

## Context

[ADR 0015](0015-device-placement.md) lets code be placed on the GPU with `@place(gpu)` and requires that placement never change the proved result. Nothing implements it yet: the compiler has no GPU code, and `pia_par` has no lowering to a device. Three things now need it:

- **The flagship demo** ([ADR 0016](0016-stream-delineation-flagship-demo.md), [ADR 0055](0055-sediment-transport-in-fixed-point.md) section 6). D8 directions, rendering and the pull form of the sediment step all write one cell per iteration. On a real SRTM tile (13.0M cells, PR #422) the CPU pipeline takes 3.7 s.
- **Lowerings written in Pia** ([ADR 0065](0065-lowerings-written-in-pia.md) section 6). That ADR takes a `linalg` kernel down to a `spirv.module` and defers the host side, the Metal shim and `@place(gpu)` to "the GPU ADR". This is that ADR.
- **Release 0.1.0** ([ADR 0067](https://github.com/deanberris/pia-lang/pull/424), Proposed). Its milestone is a proved small Llama model on the M3, which needs f32 matrix-vector products on the GPU, with weights kept on the GPU across tokens.

Dean decided on 2026-11-23 (on the [survey](https://claude.ai/artifact/GNhoJ74ocgLnBPzE5kUcFA)) that the GPU path is **SPIR-V**, so that AMD, Intel and NVIDIA can come later through Vulkan, with **SPIRV-Cross translating it to MSL** for Metal now.

What is already in place:

- **`spread` v0** ([ADR 0060](0060-spread-v0-ownership-and-runtime.md)) proves that each iteration writes only the cells it owns, one iteration at a time. This is exactly the fact a GPU kernel needs: each thread is an iteration, and no two threads write the same cell.
- **ADR 0038** defines tolerance contracts over a rounding theory. Each device has a float model that states its `eps`, its `tiny` (the absolute error term) and the operations it does not round correctly. A kernel may be placed only on a device whose model proves its contract.
- **Apple Silicon has unified memory.** A `MTLBuffer` in shared storage mode is the same physical memory to the CPU and the GPU, so placing work on the GPU copies nothing.

## Decision

### 1. A kernel is a `spread` placed on the GPU

`@place(gpu)` on a `spread` makes each iteration a GPU thread. The loop is proved exactly as on the CPU: by the body, the ownership goals of ADR 0060 and the loop's `ensures`. Nothing about the proof depends on the placement. The rules of `spread` v0 carry over unchanged: no assignment to outer variables, writes only through owned cells, and calls only with footprints.

A GPU body has extra rules, checked by the type checker:

- **No calls that cannot run on the device.** Allowed are other functions the compiler can inline, or that are themselves GPU-placeable: no allocation, no foreign calls, no I/O, no recursion.
- **Element types the device supports.** These are integers of 8 to 64 bits and, after M11, `f32`. Storage of 8- and 16-bit elements uses SPIR-V's `StorageBuffer8BitAccess` and `16BitAccess`.
- **Every buffer the body touches is a device buffer** (section 4), or a slice the shim can wrap without a copy.

A function marked `@place(gpu)` is a function whose body is one such `spread` plus scalar set-up, so `let directions (dem) (out) @place(gpu) = spread i in 0 .. len out do ... done` reads as one kernel.

**Placement does not change an integer result.** The body that runs on the GPU is the body that was proved. Integer operations have one meaning in Pia: wrap, saturate and checked are explicit, and division by zero and shifts out of range are already proved absent. Codegen lowers each operation to the same SPIR-V arithmetic on every device. So for integer kernels, ADR 0015's rule holds by construction, and the differential tests (section 6) check the toolchain rather than the proof.

### 2. The lowering: `scf.parallel` to `gpu` to SPIR-V to MSL

IRGen already lowers `spread` to `scf.parallel` (ADR 0060). For a GPU-placed loop, codegen then runs upstream MLIR passes only:

1. `gpu-map-parallel-loops` and `convert-parallel-loops-to-gpu` make a `gpu.launch` with one thread per iteration, in blocks of a fixed size (256 by default; a `@schedule` from ADR 0065 can choose it).
2. `gpu-kernel-outlining` moves the body into a `gpu.module`, and `gpu.launch_func` stays on the host.
3. The storage-class mapping and `convert-gpu-to-spirv` (with `arith`, `memref` and `scf` to SPIR-V) produce a `spirv.module`. It is serialised to a SPIR-V binary with the target environment `Vulkan 1.1` plus the capabilities above.
4. **SPIRV-Cross** translates the binary to MSL, with the Metal version and argument-buffer options fixed by the target model.
5. The Metal compiler (`xcrun metal`, then `metallib`) builds a `.metallib`, which is embedded in the object file as a section. At load, the shim finds kernels by name.

The host side of `gpu.launch_func` lowers to calls into the shim (section 3), not to MLIR's GPU runtime wrappers. Those wrappers exist for CUDA, ROCm and Vulkan, but not for Metal.

ADR 0065's `linalg` kernels join the same pipeline at step 1. Their `@schedule` maps `scf.forall` to blocks and threads, and steps 2 to 5 are shared.

### 3. The host shim is small, written in Objective-C, and trusted

`src/runtime/metal/` is one Objective-C file over Metal, compiled with ARC, plus a C header. It exposes about eight functions, each declared in Pia as an `extern` with a contract:

- `device_open` returns a device or `Gpu_unavailable`.
- `buffer_new` makes a shared-storage buffer of `n` bytes, or returns `Gpu_out_of_memory`. `buffer_view` gives the CPU a slice over it, with no copy. `buffer_free` releases it.
- `kernel_get` looks a kernel up in the embedded library by name, with a pipeline cache.
- `dispatch` takes a kernel, its buffers, scalar arguments and a grid size. It encodes one compute pass, commits it, and **waits for completion**. It returns `Ok`, `Gpu_fault` (a command buffer error) or `Gpu_timeout`.

v0 is synchronous, so when `dispatch` returns, the GPU's writes are visible to the CPU and no buffer is in use by the device. That keeps ownership trivial: the host cannot touch a buffer while a kernel writes it, because the host is blocked. Asynchronous launches come with `Pia.Exec.Metal` ([ADR 0050](0050-senders-and-receivers.md) step 9), where a buffer is `moved` into the GPU stage and returned in its value. That is the same rule, expressed as a sender.

The shim, SPIRV-Cross, the Metal compiler and the upstream MLIR GPU and SPIR-V conversions are **trusted items**, listed in the trust report and the certificate ([ADR 0024](0024-published-proof-certificates.md)). They are trusted the way the MLIR async runtime is in ADR 0060, and for the same reason: they are external toolchain pieces with wide use. Section 6 says how they are tested.

### 4. Device buffers are linear resources that stay on the GPU

`Pia.Gpu.buffer t` is a `@linear` resource ([ADR 0026](0026-memory-manager.md)) that holds `len` elements of `t` in a shared-storage `MTLBuffer`. Making one is fallible, like every allocation. `drop` frees it. It lives as long as its owner, so weights loaded once stay resident across many launches. This is the LLM's requirement: load once, then one matrix-vector product per token.

On the CPU, `view b` is a slice of `t` over the same memory. It is borrowed, so it cannot outlive the buffer, and the type checker forbids holding it across a `dispatch` that writes `b`. A kernel takes buffers, not slices. Slices of a buffer (`b.[lo .. hi]`) are passed as a buffer and an offset.

On a device with its own memory (later, Vulkan), the same type holds device memory, and `view` becomes an explicit, fallible transfer. The Pia code does not change.

### 5. Errors: placement may fail, and the caller decides

A `@place(gpu)` function's error set gains `Gpu.error` (`Gpu_unavailable | Gpu_out_of_memory | Gpu_fault | Gpu_timeout`), handled with `?` as any other error ([ADR 0028](0028-error-propagation-and-cleanup.md)). An explicit placement never silently runs on the CPU. `@place(auto, prefer = gpu)` may fall back to the CPU, because both run the same proved body. For integers the result is the same. For floats the fallback is allowed only when the CPU's float model also proves the contract, which the strict IEEE CPU model always does when the GPU's does.

### 6. Testing what is trusted

- **Differential tests.** Every `@place(gpu)` test runs the kernel on the CPU too. Integers must match bit for bit. Floats must lie within the proved tolerance of each other and of a `f64` reference.
- **A litmus battery for the float model** (section 7), run on each Apple GPU we support. It checks the rounding of `+`, `-`, `*` and `fma` against a correctly rounded reference, subnormal inputs and outputs, and whether `a * b + c` was contracted, for every rounding-sensitive pattern. It runs as for atomics ([ADR 0052](0052-atomics.md)).
- **GPU tests run on the iMac only**, tagged `requires-gpu`. Linux CI has no Metal, so it builds the SPIR-V and the MSL (SPIRV-Cross runs anywhere) and checks them with `spirv-val`, but does not run them. A Vulkan runner can come with a Linux GPU.

### 7. The Apple GPU float model

Each placement target has a float model under ADR 0038. `Pia.Device.Apple_gpu` is a theory with one model per GPU family (M1 to M4 first). For `f32` it states:

- **Rounding.** `+`, `-`, `*` and `fma` round to nearest even when fast math is off, so `eps f32 = 2⁻²⁴`. Pia compiles MSL with fast math off (`-fno-fast-math`), and the MSL specification's accuracy table lists these operations as correctly rounded. The litmus battery confirms it for each family. Division and `sqrt` are not correctly rounded on all families, so the model gives their error in ulps from the battery, or leaves them out, which makes a kernel that uses them unplaceable until it is measured.
- **Subnormals may be flushed.** The model takes `tiny = 2⁻¹²⁶` (the smallest normal) as the absolute error term of every operation, instead of the CPU's half-subnormal. That is sound whether or not a family flushes. If the battery shows that a family keeps subnormals, its model can use the CPU's value.
- **Contraction is stated, not assumed away.** SPIR-V marks an operation that must not be contracted with `NoContraction`. Pia marks every float operation `NoContraction` unless ADR 0012 licenses contraction for that expression, so the GPU computes what was proved. Whether SPIRV-Cross carries the decoration into MSL is checked in step 6. If it does not, contraction is turned off for the whole kernel with the Metal compiler's options. If the battery finds a family that contracts anyway, its model says "may contract", which is still sound for ADR 0038's bounds because a contraction only removes a rounding.
- **Reduction order is free.** Threadgroup reductions reorder sums, so a GPU reduction is proved with ADR 0038's order-free bound, `γₙ` for a sum of length `n`. That bound does not depend on the tree, so the proof holds for any schedule.

`f16` and `bf16` are later. The model is a trusted theory, since Apple documents correct rounding only in prose, and it is listed in the trust report.

### 8. Threadgroup memory, barriers and SIMD-group matrices

A `spread` v0 iteration shares nothing with other iterations, so it cannot use threadgroup memory. A tiled reduction or matmul needs a tile in threadgroup memory, a barrier, and threads that read each other's writes after it. These come through ADR 0065's `@schedule` (`tile_using_forall` with promotion to workgroup memory, upstream `gpu.barrier`), trusted at first and translation-validated later (ADR 0065 step 8), not through new `spread` syntax. A language-level form, a `group` of iterations with a scratch buffer they share between barriers, is left for a later ADR, once a kernel needs it that a schedule cannot express.

Apple's SIMD-group matrix operations (`simdgroup_matrix`) are vendor ops with no SPIR-V equivalent that SPIRV-Cross maps. If used, they are a trusted `@lower` to MSL (ADR 0065, state 3) behind a Pia contract. They are optional.

### 9. A sequence of placed spreads is one command buffer (amendment, Proposed 2026-11-27)

Step 4 put each wave of the sediment pull step on the GPU, one wave per placed `spread`, with the commit pass on the CPU between waves. It is correct, but slow. On the tile N46E008, 3,924 waves a step take 33 to 57 s, against 0.5 s on the CPU. Each wave is one `pia_gpu_run`: it wraps about nine tile-sized buffers, which maps their pages into the GPU's address space, then commits one command buffer and waits. That costs 8 to 15 ms a wave, while the kernel takes only microseconds. A step that waits for the GPU between waves cannot beat the CPU, whatever the shim caches. Dean chose (2026-11-27) to remove the waits: a whole step becomes one command buffer.

**`@place(gpu)` on a sequential `for` makes a placed sequence.** Its body may hold spreads, ghost code (lemma calls and assertions), and scalar `let`s. The spreads need no `@place` of their own: each becomes a kernel, and each iteration of the `for` encodes their dispatches, in order, into one command buffer. The host wraps every buffer once, commits once and waits once. For the pull step:

```text
let ok = for k in 0 .. waves @place(gpu)
  invariant ...
do
  let lo = starts.[k] in
  let hi = starts.[k + 1] in
  spread q in lo .. hi do ... done;                  (* the wave *)
  spread q in lo .. hi @owns(bed, pos) @owns(flux, pos) @owns(seen, pos)
  do ... done                                       (* its commit *)
done
```

The rules, each checked by piac:

- **The host runs the scalar code while it encodes.** A scalar `let` in the body may read only buffers that no kernel of the sequence writes, such as `starts` above. So each dispatch's bounds are known when it is encoded, and no value has to come back from the GPU. Reading back a value the GPU computes, such as indirect dispatch, is left for later.
- **Dispatches run in order, each after the one before has finished.** Metal's default serial compute encoder gives this, so the sequence means what the `for` means on the CPU: every spread sees all writes of the spreads before it. A sequence that needs no ordering between two dispatches can say so later, with a concurrent encoder.
- **The proof does not change.** The `for` is proved as written, with its invariants, and its spreads are proved as in section 1. Placement adds no goal.
- **Errors are as in section 5.** The sequence evaluates to `result unit gpu_error`. On `Ok`, the `for`'s postcondition holds. On `Err`, every buffer the sequence writes may be partly written, and nothing about it is promised.
- **A spread in a sequence may own cells through an owner array** (`@owns(buf, owner)`, ADR 0060), not only by identity. On the device an owner is only a proof fact: the kernel writes where the body says. This lifts step 3's rule against `@owns` on the GPU, for spreads in a sequence and on their own. The pull step needs it: the commit writes cell `order.[q]` from slot `q`, and `pos` is its owner array, since `pos.[order.[q]] = q`.

The shim gets one new entry, `pia_gpu_run_sequence`. It takes the kernels, the buffers once, and a table of dispatches, each a kernel, its bounds and its scalars. It wraps each page-aligned buffer once, sets each dispatch's scalars with `setBytes`, and encodes every dispatch into one command buffer. Codegen builds the table on the host stack as the `for` runs, then makes the one call.

**The pull step's other work moves out of the loop.** The wave boundaries, which `wave_end` finds one at a time, are found before the step by a proved scan into `starts`. The mass sent off the map, which `copy_back` added up wave by wave, is `osum order down flux n` of the final loads, summed on the CPU after the step. Both are linear and cheap next to the step. The commit of a wave, a spread with owner array `pos`, needs a lemma that commits a whole wave at once, `commit_wave`. It is proved from the same facts `copy_cell` uses: the cells of a wave have the same height, so none drains into another, and committing one cell leaves the others' inflows as they were.

The expected cost of a step is the kernels plus the encoding, about 8,000 dispatches. At a few microseconds each that is tens of milliseconds, against 0.5 s on the CPU. The measurement on the tile decides it.

## Implementation order

Each step is one PR and useful on its own. Steps 1 to 4 are integer-only.

1. **Toolchain.** Link the `gpu` and `spirv` dialects and conversions into piac. Add SPIRV-Cross and SPIRV-Tools as Bazel modules (from the Bazel Central Registry where they are, otherwise pinned like Z3). Add a macOS-only rule that runs `xcrun metal` and `metallib` and embeds the library. Test: a hand-written `gpu.module` that adds two buffers goes all the way to a `.metallib`, and `spirv-val` passes.
2. **The shim and `Pia.Gpu.buffer`.** `src/runtime/metal/`, the `extern` contracts, the trust items, and `buffer` with `view` and `drop`. Test: a C harness dispatches step 1's kernel on the iMac.
3. **`@place(gpu)` on a `spread` with identity ownership**, with the device rules of section 1 and the error set of section 5. First kernels: D8 directions and render from the streams demo, with differential tests against the CPU on the SRTM fixture and the full tile.
   *Done (2026-11-27).* `src/gpu/Place.cpp` outlines, lowers and embeds each placed spread at compile time (taking in issue #435), and the shim's `pia_gpu_run` runs it. [placed.pia.md](../placed.pia.md) has both kernels. On the 3601 × 3601 tile N46E008, both match the CPU on every cell. With a warm device on the iMac, directions take 35 to 52 ms on the GPU against 41 ms on the CPU, and render 66 to 83 ms against 37 to 50 ms. The first run adds about 70 ms to open the device and load the library. Each run copies every buffer into a new `MTLBuffer` and back, and the copies dominate, so the next step is to wrap page-aligned host memory without a copy (`newBufferWithBytesNoCopy`) or to keep `Pia.Gpu.buffer`s resident.
4. **The sediment pull step on the GPU**, once its equality proof against the sequential step is merged ([ADR 0055](0055-sediment-transport-in-fixed-point.md) section 6). The demo page then shows CPU and GPU timings on real tiles.
   *Built (#463, 2026-11-27).* [pull_gpu.pia.md](../pull_gpu.pia.md) places each wave and imports the commit pass and its proof through pull.pia.md's `PullWaves` interface. It matches the CPU on every cell of the tile, at 33 to 57 s a step against 0.5 s on the CPU, one GPU run per wave (section 9).
4b. **A placed sequence** (section 9): `@place(gpu)` on a `for`, `@owns` on the device, `pia_gpu_run_sequence`, and the pull step as one command buffer a step, with its CPU and GPU timings on the tile.
5. **ADR 0065 schedules on the GPU**: `tile_using_forall` mapped to blocks and threads, workgroup promotion, an integer matmul.
6. **Floats**, after M11: the Apple GPU float model and its litmus battery, `NoContraction`, and an `f32` matrix-vector product with a tolerance contract (`γₙ`, `n` up to 768) for the 0.1.0 LLM.
7. **`Pia.Exec.Metal`**: asynchronous launches as senders (ADR 0050 step 9), and placement of `@place(auto)` stages by the cost model.

## Consequences

- The flagship demo and the 0.1.0 LLM get the GPU through one path, and that path is SPIR-V, so Vulkan devices need only a second shim.
- Integer kernels are proved once, and placing them on the GPU adds no proof obligation. The new trust is the toolchain (MLIR GPU and SPIR-V conversions, SPIRV-Cross, the Metal compiler) and a small shim. All of it is listed, and all of it is checked by differential tests.
- Float kernels on the GPU are proved against a stated device model, with subnormal flushing and contraction accounted for, so no kernel relies on Metal behaviour that wasn't written down.
- Building GPU code needs Xcode's Metal toolchain on macOS. Linux builds the SPIR-V and MSL but cannot run them.
- `Pia.Gpu.buffer` is a new resource type, and the type checker gains device rules for GPU-placed bodies.

## Answers to the review questions

Dean answered on 2026-11-25. Each answer is the proposed option:

1. ~~Explicit placement and failure?~~ **`@place(gpu)` adds `Gpu.error` to the function's error set.** An explicit placement never runs silently on the CPU. Only `@place(auto, prefer = gpu)` may fall back.
2. ~~Where is MSL compiled?~~ **At build time**, by `xcrun metal` and `metallib`, into a `.metallib` embedded in the object file. No compiler runs or is trusted at run time, and GPU builds need Xcode's Metal toolchain.
3. ~~The shim's language?~~ **Objective-C with ARC.** It is one small file compiled by clang, with no extra dependency.

## Review question for section 9

1. **How is a placed sequence written?** The proposal is `@place(gpu)` on a sequential `for`, so its spreads need no `@place` of their own. The alternative is to keep `@place(gpu)` on each spread and add a new block form, such as `gpu do ... done`, that groups them into one command buffer. That would be a new keyword.
