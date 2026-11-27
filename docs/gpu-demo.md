# CPU and GPU, side by side

The terrain demo runs on the CPU and on an Apple GPU, from the same proved
Pia. This page puts the two side by side on one real tile, stage by stage.
It also says how to run the comparison yourself, and what is proved, what
is tested and what is trusted on each side.

The stages are those of the [stream delineation](streams.pia.md) and
[sediment in pull form](pull.pia.md) pages:

- **D8 directions.** Each cell points at its lowest neighbour.
- **The picture.** Each cell's height and flow become a pixel.
- **The sediment pull step.** Each cell takes in what flows into it,
  then erodes or deposits, one wave of equal-height cells at a time.

On the GPU, the first two stages are each one placed `spread`
([D8 directions and the picture on the GPU](placed.pia.md)). The pull step
is a placed `for` over the waves, which runs a whole step as one Metal
command buffer ([the sediment pull step on the GPU](pull_gpu.pia.md)).

## The numbers

These are from tile N46E008 in the Swiss Alps: 3601 × 3601 cells, and
3,924 waves in each pull step. They were taken on an Apple M3 iMac on
2026-11-28, over three runs, with the GPU kernels pre-warmed at load
([ADR 0068](adr/0068-gpu-compute-through-spirv-and-metal.md), step 4b).
"Warm" is a later run, after the first.

| Stage | CPU | GPU, warm | GPU, first run | GPU speed-up, warm |
| --- | --- | --- | --- | --- |
| D8 directions | 42 to 43 ms | 6 to 7 ms | 13 to 19 ms | about 6× |
| The picture | 30 to 38 ms | 8 to 9 ms | 24 to 40 ms | about 4× |
| Sediment pull, per step | 509 to 524 ms | 235 to 253 ms | 246 to 274 ms | about 2.1× |

The GPU's results match the CPU's on every cell, in every run. That holds
for the directions, the picture's pixels, and each cell's bed and load
after four pull steps, and both send 2,861,964 units of sediment off the
map.

A whole run of the comparison takes about 53 s.

How the GPU got here:

- **Copies.** At first, each run copied every buffer into Metal and back,
  and the GPU was slower than the CPU. On Apple silicon the CPU and GPU
  share memory, so the shim now wraps each page-aligned buffer where it
  is.
- **One command buffer per step.** With a command buffer per wave, a pull
  step took 33 to 57 s, because each of its 3,924 waves waited for the
  GPU. As one command buffer, the step waits once.
- **Pre-warming.** A stage's first run used to open the device and build
  its pipeline, which put the first run of directions at 42 to 57 ms.
  Every placed kernel is now built in the background while the program
  starts.

## Running it

You need a Mac with Apple silicon and Xcode's Metal toolchain. Fetch a
tile, then build and run the comparison:

```text
examples/streams/fetch_srtm.sh /tmp/srtm
bazel run //examples/streams:srtm_gpu -- /tmp/srtm/N46E008.hgt
```

It prints one line for each stage, with the CPU time, the GPU's warm and
first-run times, and how many cells differ. Then it prints how the
buffers were bound, how many dispatches the sequences made, and how many
kernels were pre-warmed. It exits non-zero if any cell differs.
`PIA_GPU_WARM=0` turns pre-warming off, so you can time a cold first run.
`bazel test //examples/streams:srtm_gpu_run_test` runs the same comparison
on a 256 × 256 fixture.

## What is proved, tested and trusted

| | CPU | GPU |
| --- | --- | --- |
| The algorithm | proved: each stage meets its specification, and the pull step conserves mass | the same proof, since placement adds no goal |
| Each thread writes only its own cells | not needed: the loops are sequential | proved, by the ownership check of ADR 0060 |
| The waves of a step | proved equal to the sequential step (`same_step`) | proved, when the sequence returns `Ok` |
| Errors | none | each GPU stage returns `result unit gpu_error`, and the caller decides |
| The compiler below Pia's IR | LLVM, trusted | SPIR-V, SPIRV-Cross, Metal's compiler and the shim, trusted and tested by this comparison (ADR 0068, section 6) |

The GPU is trusted no more than the CPU's compiler, and it is tested more:
every cell of every stage is compared with the CPU on a real tile.
