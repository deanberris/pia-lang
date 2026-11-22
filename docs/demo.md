# Demo: edge detection

This demo is a real program built with Pia: an image pipeline that finds the edges in a picture. It turns a colour image into brightness, blurs it to remove noise, and runs the Sobel operator to measure how sharply the brightness changes at each pixel. `piac` proves every array index, every sum and every narrowing in the pipeline before it generates any code, and the compiled loops have no bounds checks.

## Run it

On an Apple Silicon Mac, from a checkout of the repository:

```sh
bazel run //examples/edges
```

With no arguments the demo draws a test scene (a sky, a sun and a house, with some noise), runs the Pia pipeline over it, and writes two files in the directory you ran it from: `edges-input.bmp` and `edges-output.bmp`. It also prints both images as text, so you can see the result in the terminal: the outlines of the sun, the roof, the walls and the window, with the noise gone.

```sh
open edges-input.bmp edges-output.bmp
```

To run it on your own picture, convert it to BMP first. On macOS, `sips` does that:

```sh
sips -s format bmp photo.jpg --out "$PWD/photo.bmp"
bazel run //examples/edges -- photo.bmp photo-edges.bmp
open photo-edges.bmp
```

The image processing is all Pia, in [`examples/edges/edges.pia`](../examples/edges/edges.pia). Pia has no I/O yet, so a small C program, [`main.c`](../examples/edges/main.c), reads and writes the BMP files and calls the compiled Pia function `edges` through the [C ABI](codegen.md#c-abi). The tests compare each pass with a C reference over images of several sizes:

```sh
bazel test //examples/edges/...
```

## The program

<!-- example: edges.pia -->
<!-- source: examples/edges/edges.pia -->
```ocaml
(* Edge detection: the Pia demo (docs/demo.md).

   `edges` takes an image as packed RGB bytes, `w` pixels wide, and writes
   an edge map that is bright where the brightness changes sharply. It runs
   three passes, and the verifier proves every index, every sum and every
   narrowing in them before any code is generated:

   1. `gray`, from RGB to brightness,
   2. `blur`, a 3x3 box blur that smooths out noise,
   3. `sobel`, the Sobel operator, which measures how fast the brightness
      changes at each pixel.

   An image is stored row by row, so the pixel above `m` is `m - w` and the
   pixel below is `m + w`. The row loops keep a row on each side of the one
   they are working on, and the column loops keep a column on each side, so
   every neighbour is in bounds. Pia does not allocate memory yet, so the
   caller passes the buffers.

   The file is written to keep the solver's work small. It adds where it
   could multiply (`len dst + len dst + len dst`, `mr + mr`), because a
   module that multiplies is encoded with wider bit-vectors
   (docs/verifier.md). Each pixel is read by a function of its own, whose
   precondition says the whole 3x3 window is in bounds, and the column
   loops `assert` the step from the loop bounds to that precondition.
*)
module Edges : Pipeline
(* Brightness, as (r + 2g + b) / 4, a cheap stand-in for BT.601's
   0.299r + 0.587g + 0.114b. The weights add up to 4, so the result fits in
   a byte. *)
let luma (r : u8) (g : u8) (b : u8) : u8 =
  let y : u16 = r + g + g + b in
  y / 4

let gray (rgb : [u8]) (dst : out mutable [u8]) : unit
  requires len rgb = len dst + len dst + len dst
=
  for i in 0..len dst do
    let j = i + i + i in
    dst.[i] <- luma (rgb.[j]) (rgb.[j + 1]) (rgb.[j + 2])
  done

(* The mean of pixel `m` and its eight neighbours. *)
let mean_at (src : [u8]) (w : usize) (m : usize) : u8
  requires w < m && m + w + 1 < len src
=
  let a = m - w in
  let b = m + w in
  let s : u16 =
    src.[a - 1] + src.[a] + src.[a + 1]
    + src.[m - 1] + src.[m] + src.[m + 1]
    + src.[b - 1] + src.[b] + src.[b + 1]
  in
  s / 9

(* Blurs the row that starts at `r`, apart from its first and last
   pixels. *)
let blur_row (src : [u8]) (w : usize) (r : usize) (dst : inout mutable [u8])
  : unit
  requires len dst = len src && w >= 3 && w <= r && r + w + w <= len src
=
  for x in 1..w - 1 do
    assert x + 1 < w;
    assert r + x + 1 < r + w;
    dst.[r + x] <- mean_at src w (r + x)
  done

(* A 3x3 box blur, which smooths out noise. Border pixels are copied
   unchanged. *)
let blur (src : [u8]) (w : usize) (dst : out mutable [u8]) : unit
  requires len dst = len src && w >= 3 && w + w + w <= len src
=
  for i in 0..len src do dst.[i] <- src.[i] done;
  let r : mutable usize = w in
  while w <= len src - (r + w)
    invariant w <= r && r + w <= len src
    decreases len src - r
  do
    blur_row src w r dst;
    r <- r + w
  done

(* The Sobel gradient at a pixel, from its eight neighbours: how much
   brighter its right side is than its left side (gx), and its bottom than
   its top (gy). The edge strength |gx| + |gy| is clamped to 255. *)
let strength (tl : u8) (tc : u8) (tr : u8) (ml : u8) (mr : u8) (bl : u8)
    (bc : u8) (br : u8) : u8 =
  let right : u16 = tr + mr + mr + br in
  let left : u16 = tl + ml + ml + bl in
  let bottom : u16 = bl + bc + bc + br in
  let top : u16 = tl + tc + tc + tr in
  let gx : u16 = if right > left then right - left else left - right in
  let gy : u16 = if bottom > top then bottom - top else top - bottom in
  let g : u32 = gx + gy in
  if g > 255 then 255 else g

(* The edge strength of pixel `m`. *)
let strength_at (src : [u8]) (w : usize) (m : usize) : u8
  requires w < m && m + w + 1 < len src
=
  let a = m - w in
  let b = m + w in
  strength (src.[a - 1]) (src.[a]) (src.[a + 1])
    (src.[m - 1]) (src.[m + 1])
    (src.[b - 1]) (src.[b]) (src.[b + 1])

(* The edge strength of the row that starts at `r`, apart from its first
   and last pixels. *)
let sobel_row (src : [u8]) (w : usize) (r : usize) (dst : inout mutable [u8])
  : unit
  requires len dst = len src && w >= 3 && w <= r && r + w + w <= len src
=
  for x in 1..w - 1 do
    assert x + 1 < w;
    assert r + x + 1 < r + w;
    dst.[r + x] <- strength_at src w (r + x)
  done

(* The edge strength of every pixel. Border pixels are 0. *)
let sobel (src : [u8]) (w : usize) (dst : out mutable [u8]) : unit
  requires len dst = len src && w >= 3 && w + w + w <= len src
=
  for i in 0..len src do dst.[i] <- 0 done;
  let r : mutable usize = w in
  while w <= len src - (r + w)
    invariant w <= r && r + w <= len src
    decreases len src - r
  do
    sobel_row src w r dst;
    r <- r + w
  done

(* The whole pipeline. `luma_buf` and `smooth` hold the intermediate
   images. *)
let edges (rgb : [u8]) (w : usize) (luma_buf : out mutable [u8])
    (smooth : out mutable [u8]) (dst : out mutable [u8]) : unit
  requires len rgb = len dst + len dst + len dst && len luma_buf = len dst
  requires len smooth = len dst && w >= 3 && w + w + w <= len dst
=
  gray rgb luma_buf;
  blur luma_buf w smooth;
  sobel smooth w dst

(* What main.c calls, by its C names (ADR 0039). The helpers above are
   private to the module. *)
interface Pipeline @abi(c) = sig
  let gray : (rgb : [u8]) -> (dst : out mutable [u8]) -> unit
    requires len rgb = len dst + len dst + len dst
  let blur : (src : [u8]) -> (w : usize) -> (dst : out mutable [u8]) -> unit
    requires len dst = len src && w >= 3 && w + w + w <= len src
  let sobel : (src : [u8]) -> (w : usize) -> (dst : out mutable [u8]) -> unit
    requires len dst = len src && w >= 3 && w + w + w <= len src
  let edges : (rgb : [u8]) -> (w : usize) -> (luma_buf : out mutable [u8])
      -> (smooth : out mutable [u8]) -> (dst : out mutable [u8]) -> unit
    requires len rgb = len dst + len dst + len dst && len luma_buf = len dst
    requires len smooth = len dst && w >= 3 && w + w + w <= len dst
end
```

Every goal in it is proved:

```console
$ piac --verify edges.pia
...
115 proved, 0 failed, 0 skipped
```

The row loops are where the proofs matter. An image is stored row by row, so the pixel below `m` is `m + w`. In `blur` and `sobel`, the loop condition `w <= len src - (r + w)` says there is a whole row after row `r`, and the invariant `r + w <= len src` keeps that subtraction from going below zero. Together they prove the precondition of `blur_row` and `sobel_row`, `r + w + w <= len src`, and nothing in the loop can overflow: there is no `r + 2 * w` that could wrap around for a huge image. In the row functions, the column loop asserts `x + 1 < w` and then `r + x + 1 < r + w`. With `r + w + w <= len src`, that gives the precondition of `mean_at` and `strength_at` for pixel `m = r + x`: `w < m && m + w + 1 < len src`. That says the whole 3x3 window around `m` is in the image, from `m - w - 1` up to `b + 1 = m + w + 1`, so each of the nine reads is proved from it directly.

Splitting the work up this way is for the solver's sake. Each query holds one function and the goals before it, so small functions with precise preconditions keep the queries small, and the two assertions give the solver the steps it would otherwise have to find itself. Written as one loop nest, the same program had goals that Z3 could not settle within its 10-second timeout.

The `edges` precondition is the contract the C caller has to keep: three bytes per pixel, buffers of the same size, and at least three rows of at least three pixels. Inside Pia, the calls to `gray`, `blur` and `sobel` are checked against their preconditions.

## A bug the compiler catches

Here is `mean_at` with a classic off-by-one. Its precondition leaves room for the pixel below `m`, but not for the one below and to the right:

<!-- example: edges_buggy.pia -->
<!-- source: examples/edges/edges_buggy.pia -->
<!-- expect: fail -->
```ocaml
(* A buggy `mean_at` for the demo (docs/demo.md): its precondition leaves
   room for the pixel below `m`, but not for the one below and to the
   right, so `b + 1` can be past the end of the image. `piac --verify`
   finds the input that breaks it, and `piac --emit=obj` refuses to
   compile it.
*)
let mean_at (src : [u8]) (w : usize) (m : usize) : u8
  requires w < m && m + w < len src
=
  let a = m - w in
  let b = m + w in
  let s : u16 =
    src.[a - 1] + src.[a] + src.[a + 1]
    + src.[m - 1] + src.[m] + src.[m + 1]
    + src.[b - 1] + src.[b] + src.[b + 1]
  in
  s / 9
```

`piac` finds an image where it reads past the end:

```console
$ piac --verify edges_buggy.pia
edges_buggy.pia:10:13: proved: '-' does not overflow usize [smt]
edges_buggy.pia:11:13: proved: '+' does not overflow usize [smt]
edges_buggy.pia:13:12: proved: '-' does not overflow usize [smt]
edges_buggy.pia:13:5: proved: the index is within bounds [smt]
edges_buggy.pia:13:19: proved: the index is within bounds [smt]
edges_buggy.pia:13:17: proved: '+' does not overflow u16 [intervals]
edges_buggy.pia:13:36: proved: '+' does not overflow usize [smt]
edges_buggy.pia:13:29: failed: the index is within bounds
  counterexample: len src = 2311472508747907072, w = 0, m = 2311472508747907071, index = 2311472508747907072, length = 2311472508747907072
edges_buggy.pia:13:27: proved: '+' does not overflow u16 [intervals]
edges_buggy.pia:14:14: proved: '-' does not overflow usize [smt]
edges_buggy.pia:14:7: proved: the index is within bounds [smt]
edges_buggy.pia:14:5: proved: '+' does not overflow u16 [intervals]
edges_buggy.pia:14:21: proved: the index is within bounds [smt]
edges_buggy.pia:14:19: proved: '+' does not overflow u16 [intervals]
edges_buggy.pia:14:38: proved: '+' does not overflow usize [smt]
edges_buggy.pia:14:31: proved: the index is within bounds [smt]
edges_buggy.pia:14:29: proved: '+' does not overflow u16 [intervals]
edges_buggy.pia:15:14: proved: '-' does not overflow usize [smt]
edges_buggy.pia:15:7: proved: the index is within bounds [smt]
edges_buggy.pia:15:5: proved: '+' does not overflow u16 [intervals]
edges_buggy.pia:15:21: proved: the index is within bounds [smt]
edges_buggy.pia:15:19: proved: '+' does not overflow u16 [intervals]
edges_buggy.pia:15:38: proved: '+' does not overflow usize [smt]
edges_buggy.pia:15:31: failed: the index is within bounds
  counterexample: len src = 17329207052307791873, w = 8255452159714263041, m = 9073754892593528831, index = 17329207052307791873, length = 17329207052307791873
edges_buggy.pia:15:29: proved: '+' does not overflow u16 [intervals]
edges_buggy.pia:17:5: proved: the divisor is not zero [intervals]
edges_buggy.pia:17:5: proved: '/' does not overflow u16 [intervals]
edges_buggy.pia:10:3: proved: the value fits in u8 [smt]
26 proved, 2 failed, 0 skipped
```

Each counterexample is a call that satisfies the precondition and reads past the end; the solver is free to pick enormous sizes, since nothing in the precondition bounds them. In the first, `w` is 0, so the precondition allows `m` to be the last pixel (`m = len src - 1`), and its right neighbour `m + 1` is `len src`, one past the end. In the second, `m + w` is 17329207052307791872, the last pixel again, so `b` is in bounds but `b + 1` is not. In C this compiles and reads whatever is in memory after the buffer. In Pia it does not compile at all:

```console
$ piac --emit=obj -o edges_buggy.o edges_buggy.pia
edges_buggy.pia:10:13: proved: '-' does not overflow usize [smt]
edges_buggy.pia:11:13: proved: '+' does not overflow usize [smt]
edges_buggy.pia:13:12: proved: '-' does not overflow usize [smt]
edges_buggy.pia:13:5: proved: the index is within bounds [smt]
edges_buggy.pia:13:19: proved: the index is within bounds [smt]
edges_buggy.pia:13:17: proved: '+' does not overflow u16 [intervals]
edges_buggy.pia:13:36: proved: '+' does not overflow usize [smt]
edges_buggy.pia:13:29: failed: the index is within bounds
  counterexample: len src = 2311472508747907072, w = 0, m = 2311472508747907071, index = 2311472508747907072, length = 2311472508747907072
edges_buggy.pia:13:27: proved: '+' does not overflow u16 [intervals]
edges_buggy.pia:14:14: proved: '-' does not overflow usize [smt]
edges_buggy.pia:14:7: proved: the index is within bounds [smt]
edges_buggy.pia:14:5: proved: '+' does not overflow u16 [intervals]
edges_buggy.pia:14:21: proved: the index is within bounds [smt]
edges_buggy.pia:14:19: proved: '+' does not overflow u16 [intervals]
edges_buggy.pia:14:38: proved: '+' does not overflow usize [smt]
edges_buggy.pia:14:31: proved: the index is within bounds [smt]
edges_buggy.pia:14:29: proved: '+' does not overflow u16 [intervals]
edges_buggy.pia:15:14: proved: '-' does not overflow usize [smt]
edges_buggy.pia:15:7: proved: the index is within bounds [smt]
edges_buggy.pia:15:5: proved: '+' does not overflow u16 [intervals]
edges_buggy.pia:15:21: proved: the index is within bounds [smt]
edges_buggy.pia:15:19: proved: '+' does not overflow u16 [intervals]
edges_buggy.pia:15:38: proved: '+' does not overflow usize [smt]
edges_buggy.pia:15:31: failed: the index is within bounds
  counterexample: len src = 17329207052307791873, w = 8255452159714263041, m = 9073754892593528831, index = 17329207052307791873, length = 17329207052307791873
edges_buggy.pia:15:29: proved: '+' does not overflow u16 [intervals]
edges_buggy.pia:17:5: proved: the divisor is not zero [intervals]
edges_buggy.pia:17:5: proved: '/' does not overflow u16 [intervals]
edges_buggy.pia:10:3: proved: the value fits in u8 [smt]
26 proved, 2 failed, 0 skipped
```

The fix is the precondition of the real `mean_at` above, `m + w + 1 < len src`, which leaves room for `b + 1`. Callers then have to prove it, as `blur_row` does.
