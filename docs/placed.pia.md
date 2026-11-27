# Demo: D8 directions and the picture on the GPU

Two stages of [stream delineation](streams.pia.md) do the same work on
every cell and read only their inputs: the D8 direction of a cell, and its
colour in the picture. Each is a `spread` ([ADR
0060](adr/0060-spread-v0-ownership-and-runtime.md)) in which iteration `i`
writes only cell `i`, so here each is placed on the GPU with `@place(gpu)`
([ADR 0068](adr/0068-gpu-compute-through-spirv-and-metal.md), step 3).

The proof does not change with the placement. Each spread is proved as on
the CPU: its body, the ownership of its writes, and its `ensures`. piac
then outlines the body as a kernel, one thread per cell, lowers it to
SPIR-V, translates it to the Metal Shading Language with SPIRV-Cross,
compiles it with fast math off, and embeds the `.metallib` in the object.
At run time the Metal shim copies the buffers in, runs the kernel, waits,
and copies back what it wrote.

A placed spread is fallible: it evaluates to `result unit gpu_error`, with
`gpu_error = Gpu_unavailable | Gpu_out_of_memory | Gpu_fault | Gpu_timeout`
in that order. Its `ensures` holds only when it returns `Ok`, since a
failed run may leave a buffer part written, and an explicit placement
never falls back to the CPU on its own (ADR 0068, section 5).

`examples/streams/srtm_gpu.c` runs both stages on the GPU and checks them
against the CPU stages of [streams.pia.md](streams.pia.md), cell for cell,
on the SRTM fixture and on a whole tile:

```console
$ bazel run //examples/streams:srtm_gpu -- /tmp/srtm/N46E008.hgt
```

On the iMac the CPU and GPU share memory, so the shim binds each buffer
where it is, without a copy, when it starts on a page boundary
(`newBufferWithBytesNoCopy`); only the few scalars, and any buffer that
does not start on a page, are copied. On the whole tile, 3601 × 3601
cells, both stages match the CPU on every cell, and over three runs:

| Stage | CPU | GPU, warm | GPU, first run |
|---|---|---|---|
| D8 directions | 41 ms | 6 to 16 ms | 50 to 60 ms |
| The picture | 25 to 30 ms | 9 to 12 ms | 26 to 29 ms |

The first run of directions also opened the device and loaded the kernel.
The shim now pre-warms them instead: when the program loads, a background
queue opens the device and builds every placed kernel's pipeline, so a first
run finds them ready (ADR 0068, step 4b). `PIA_GPU_WARM=0` turns this off.
Before the buffers were wrapped, the copies in and back made both stages
slower on the GPU than on the CPU (ADR 0068, step 3).

The device rules of ADR 0068, section 1 decide what a body may do. Its
calls are inlined, since the GPU has no call stack, and after that it may
use only integer arithmetic of 8 to 64 bits, loads and stores of integer
buffers, and `if`, `for` and `while`. A record is not one of those yet, so
the bodies below work in scalars: the best route as a target and a drop,
and a colour as one packed `u32`.

The file is one module, `Placed`. Its interface is what the C program
calls. Each function returns 0 when the stage ran, or 1 plus the
`gpu_error`, in its order.

```pia
module Placed : PlacedStages

interface PlacedStages @abi(c) = sig
  let directions_gpu : (fill : [u16]) -> (w : usize)
      -> (down : out mutable [usize]) -> i32
    requires len down = len fill && w >= 3 && w + w + w <= len fill
  let render_gpu : (dem : [u16]) -> (fill : [u16]) -> (acc : [u32])
      -> (basin : [usize]) -> (threshold : u32)
      -> (rgba : out mutable [u32]) -> i32
    requires len fill = len dem && len acc = len dem && len basin = len dem
    requires len rgba = len dem
end
```

## D8 directions

As on the CPU, a drop to one of the four near neighbours is weighted by 10
and a drop to a diagonal by 7.

```pia
let tenfold (d : u16) : u32 =
  let d2 : u32 = d + d in
  let d4 : u32 = d2 + d2 in
  d4 + d4 + d2
```

Seven times a drop.

```pia
let sevenfold (d : u16) : u32 =
  let d2 : u32 = d + d in
  let d4 : u32 = d2 + d2 in
  d4 + d2 + d
```

The weighted drop from cell `m` to neighbour `n`, or 0 if `n` is not
lower. A lower neighbour's drop is at least 7, so a gain above 0 means
downhill.

```pia
let gain (fill : [u16]) (m : usize) (n : usize) (diagonal : bool) : u32
  requires m < len fill && n < len fill
  ensures result > 0 ==> fill.[n] < fill.[m]
=
  if fill.[n] < fill.[m] then
    (let d : u16 = fill.[m] - fill.[n] in
     if diagonal then sevenfold d else tenfold d)
  else 0
```

The target after considering a neighbour with gain `g` against the best
drop so far: the neighbour wins only if it beats the best, so ties go to
the first considered.

```pia
let better (g : u32) (best : u32) (n : usize) (t : usize) : usize =
  if g > best then n else t
```

The best drop after considering it.

```pia
let most (g : u32) (best : u32) : u32 = if g > best then g else best
```

The direction of a cell with all eight neighbours on the map, in the same
order as `steepest` in streams.pia.md: row above, own row, row below. The
CPU's `consider` takes a neighbour when it is lower and its weighted drop
beats the best; here that is `g > best`, since `g` is 0 for one that is
not lower. So both pick the same neighbour.

```pia
let steepest_at (fill : [u16]) (w : usize) (m : usize) : usize
  requires w >= 1 && w < m && m + w + 1 < len fill
  ensures result = m || (result < len fill && fill.[result] < fill.[m])
=
  let a = m - w in
  let b = m + w in
  let g1 = gain fill m (a - 1) true in
  let t1 = better g1 0 (a - 1) m in
  let d1 = most g1 0 in
  let g2 = gain fill m a false in
  let t2 = better g2 d1 a t1 in
  let d2 = most g2 d1 in
  let g3 = gain fill m (a + 1) true in
  let t3 = better g3 d2 (a + 1) t2 in
  let d3 = most g3 d2 in
  let g4 = gain fill m (m - 1) false in
  let t4 = better g4 d3 (m - 1) t3 in
  let d4 = most g4 d3 in
  let g5 = gain fill m (m + 1) false in
  let t5 = better g5 d4 (m + 1) t4 in
  let d5 = most g5 d4 in
  let g6 = gain fill m (b - 1) true in
  let t6 = better g6 d5 (b - 1) t5 in
  let d6 = most g6 d5 in
  let g7 = gain fill m b false in
  let t7 = better g7 d6 b t6 in
  let d7 = most g7 d6 in
  let g8 = gain fill m (b + 1) true in
  better g8 d7 (b + 1) t7
```

The direction of cell `m`, given the start `last` of the last interior
row. The CPU visits the interior a row at a time; a thread instead finds
its own row and column. A cell is interior when its row starts at `w` to
`last` and its column is 1 to `w - 2`; every other cell points at itself.

The first test, that all eight neighbours are on the map, holds for every
interior cell, so it changes no direction. It keeps the `mod` away from the
call's precondition, which the solver then proves quickly.

```pia
let direction_of (fill : [u16]) (w : usize) (last : usize) (m : usize) : usize
  requires w >= 3 && w <= last && last + w + w <= len fill && m < len fill
  ensures result = m || (result < len fill && fill.[result] < fill.[m])
=
  if w < m && m < len fill - w - 1 then
    (let s = steepest_at fill w m in
     let col = m mod w in
     let row = m - col in
     if row >= w && row <= last && col >= 1 && col + 1 < w then s else m)
  else m
```

The start of the last interior row, as in streams.pia.md.

```pia
let last_row (n : usize) (w : usize) : usize
  requires w >= 3 && w + w + w <= n
  ensures w <= result && result + w + w <= n
=
  let r : mutable usize = w in
  while w <= n - (r + w + w)
    invariant w <= r && r + w + w <= n
    decreases n - r
  do
    r <- r + w
  done;
  r
```

The stage: one thread per cell. When it returns `Ok`, every direction
points strictly downhill or at the cell itself, the property flow
accumulation needs.

```pia
let directions_on_gpu (fill : [u16]) (w : usize) (down : out mutable [usize])
    : result unit gpu_error
  requires len down = len fill && w >= 3 && w + w + w <= len fill
=
  let last = last_row (len fill) w in
  spread m in 0 .. len down @place(gpu)
    ensures down.[m] = m || (down.[m] < len fill && fill.[down.[m]] < fill.[m])
  do
    down.[m] <- direction_of fill w last m
  done
```

Its C entry point.

```pia
let directions_gpu (fill : [u16]) (w : usize) (down : out mutable [usize]) : i32
  requires len down = len fill && w >= 3 && w + w + w <= len fill
=
  match directions_on_gpu fill w down with
  | Ok -> 0
  | Err e ->
    (match e with
     | Gpu_unavailable -> 1
     | Gpu_out_of_memory -> 2
     | Gpu_fault -> 3
     | Gpu_timeout -> 4)
```

## The picture

The colours of streams.pia.md, section 4, each cell's packed as
`red + 256 green + 65536 blue`. Whether flow `a` is at least sixteen times
`threshold`:

```pia
let major (a : u32) (threshold : u32) : bool =
  let t2 : u64 = threshold + threshold in
  let t4 : u64 = t2 + t2 in
  let t8 : u64 = t4 + t4 in
  a >= t8 + t8
```

A colour as one `u32`.

```pia
let pack (r : u32) (g : u32) (b : u32) : u32
  requires r < 256 && g < 256 && b < 256
= r + g * 256 + b * 65536
```

The red of watershed colour `k`, one of six.

```pia
let tint_red (k : usize) : u16 =
  if k = 0 then 214 else if k = 1 then 150 else if k = 2 then 200
  else if k = 3 then 120 else if k = 4 then 210 else 170
```

Its green.

```pia
let tint_green (k : usize) : u16 =
  if k = 0 then 168 else if k = 1 then 190 else if k = 2 then 140
  else if k = 3 then 170 else if k = 4 then 200 else 150
```

Its blue.

```pia
let tint_blue (k : usize) : u16 =
  if k = 0 then 110 else if k = 1 then 110 else if k = 2 then 160
  else if k = 3 then 160 else if k = 4 then 120 else 200
```

The colour of one cell, as `paint` gives it: streams in blue, lakes in pale
blue, and the rest in its watershed's colour, darker where it is lower.

```pia
let paint_packed (h : u16) (f : u16) (a : u32) (outlet : usize) (threshold : u32) : u32 =
  if a >= threshold then
    (if major a threshold then pack 20 70 190 else pack 70 140 240)
  else if f > h then pack 150 205 235
  else
    (let k = outlet mod 6 in
     let shade : u16 = h / 256 in
     let r : u16 = tint_red k + shade in
     let g : u16 = tint_green k + shade in
     let b : u16 = tint_blue k + shade in
     pack (r / 2) (g / 2) (b / 2))
```

The stage: one thread per cell.

```pia
let render_on_gpu (dem : [u16]) (fill : [u16]) (acc : [u32]) (basin : [usize])
    (threshold : u32) (rgba : out mutable [u32]) : result unit gpu_error
  requires len fill = len dem && len acc = len dem && len basin = len dem
  requires len rgba = len dem
=
  spread i in 0 .. len rgba @place(gpu) do
    rgba.[i] <- paint_packed (dem.[i]) (fill.[i]) (acc.[i]) (basin.[i]) threshold
  done
```

Its C entry point.

```pia
let render_gpu (dem : [u16]) (fill : [u16]) (acc : [u32]) (basin : [usize])
    (threshold : u32) (rgba : out mutable [u32]) : i32
  requires len fill = len dem && len acc = len dem && len basin = len dem
  requires len rgba = len dem
=
  match render_on_gpu dem fill acc basin threshold rgba with
  | Ok -> 0
  | Err e ->
    (match e with
     | Gpu_unavailable -> 1
     | Gpu_out_of_memory -> 2
     | Gpu_fault -> 3
     | Gpu_timeout -> 4)
```

## Many spreads, one command buffer

Each placed spread on this page is a single GPU run: the shim wraps the
buffers, commits one command buffer and waits for it. That is fine for a
stage that runs once. A step made of thousands of small spreads in a row,
such as the waves of the sediment pull step, would spend all its time
waiting. For that, put `@place(gpu)` on the `for` that runs them instead
([ADR 0068, section 9](adr/0068-gpu-compute-through-spirv-and-metal.md)):

```text
let run = for k in 0 .. waves @place(gpu)
    invariant ...
  do
    let lo = starts.[k] in
    let hi = starts.[k + 1] in
    wave ... lo hi;        (* a spread, through a call *)
    commit ... lo hi       (* another *)
  done
in
match run with
| Ok -> ...
| Err e -> ...
```

Every spread the body reaches, through calls too, becomes one dispatch of
a single command buffer, in order, and the host commits and waits once.
The loop is proved as an ordinary `for`, and evaluates to
`result unit gpu_error`: its invariants hold after it only on `Ok`. Its
spreads need no `@place` of their own, and may own cells through an owner
array (`@owns`). The rest of the body runs on the host while the dispatches
are encoded, before any of them runs, so piac checks that it only computes
scalars, such as the bounds above, from buffers no spread in the loop
writes, and that it assigns no variable from outside. The
[pull step on the GPU](pull_gpu.pia.md) is built this way.

## What is proved, and what is checked

| Claim | Where |
|---|---|
| A GPU direction points strictly downhill, or at the cell itself | `directions_on_gpu`'s spread, when it returns `Ok` |
| Each thread writes only its own cell | the ownership check of ADR 0060 |
| Every index is in bounds and nothing overflows | every function |
| The GPU gives the CPU's directions and colours, cell for cell | `srtm_gpu`, a differential test (ADR 0068, section 6) |

The last line is a test, not a theorem. The bodies here are not proved
equal to `steepest` and `paint` of streams.pia.md, which are written with
records. The differential test checks that, and the toolchain from SPIR-V
to Metal, on real terrain.
