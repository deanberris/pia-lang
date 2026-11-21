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
*)

(* BT.601 brightness in 8.8 fixed point. The weights add up to 256, so the
   result fits in a byte. *)
let luma (r : u8) (g : u8) (b : u8) : u8 =
  let y : u32 = 77 * r + 150 * g + 29 * b in
  y / 256

let gray (rgb : [u8]) (dst : out mutable [u8]) : unit
  requires len rgb = 3 * len dst
=
  for i in 0..len dst do
    dst.[i] <- luma (rgb.[3 * i]) (rgb.[3 * i + 1]) (rgb.[3 * i + 2])
  done

(* The mean of each pixel and its eight neighbours. Border pixels are
   copied unchanged. *)
let blur (src : [u8]) (w : usize) (dst : out mutable [u8]) : unit
  requires len dst = len src && w >= 3 && 3 * w <= len src
=
  for i in 0..len src do dst.[i] <- src.[i] done;
  let r : mutable usize = w in
  while w <= len src - (r + w)
    invariant w <= r && r + w <= len src
    decreases len src - r
  do
    for x in 1..w - 1 do
      let a = r - w + x in
      let m = r + x in
      let b = r + w + x in
      let s : u16 =
        src.[a - 1] + src.[a] + src.[a + 1]
        + src.[m - 1] + src.[m] + src.[m + 1]
        + src.[b - 1] + src.[b] + src.[b + 1]
      in
      dst.[m] <- s / 9
    done;
    r <- r + w
  done

(* The Sobel gradient: how much brighter the right side of each pixel is
   than its left side (gx), and its bottom than its top (gy). The edge
   strength |gx| + |gy| is clamped to 255. Border pixels are 0. *)
let sobel (src : [u8]) (w : usize) (dst : out mutable [u8]) : unit
  requires len dst = len src && w >= 3 && 3 * w <= len src
=
  for i in 0..len dst do dst.[i] <- 0 done;
  let r : mutable usize = w in
  while w <= len src - (r + w)
    invariant w <= r && r + w <= len src
    decreases len src - r
  do
    for x in 1..w - 1 do
      let a = r - w + x in
      let m = r + x in
      let b = r + w + x in
      let gx : i32 =
        (src.[a + 1] + 2 * src.[m + 1] + src.[b + 1])
        - (src.[a - 1] + 2 * src.[m - 1] + src.[b - 1])
      in
      let gy : i32 =
        (src.[b - 1] + 2 * src.[b] + src.[b + 1])
        - (src.[a - 1] + 2 * src.[a] + src.[a + 1])
      in
      let ax : i32 = if gx < 0 then 0 - gx else gx in
      let ay : i32 = if gy < 0 then 0 - gy else gy in
      let g : i32 = ax + ay in
      dst.[m] <- if g > 255 then 255 else g
    done;
    r <- r + w
  done

(* The whole pipeline. `luma_buf` and `smooth` hold the intermediate
   images. *)
let edges (rgb : [u8]) (w : usize) (luma_buf : out mutable [u8])
    (smooth : out mutable [u8]) (dst : out mutable [u8]) : unit
  requires len rgb = 3 * len dst && len luma_buf = len dst
  requires len smooth = len dst && w >= 3 && 3 * w <= len dst
=
  gray rgb luma_buf;
  blur luma_buf w smooth;
  sobel smooth w dst
```

Every goal in it is proved:

```console
$ piac --verify edges.pia
...
FILL_IN proved, 0 failed, 0 skipped
```

The row loops are where the proofs matter. An image is stored row by row, so the pixel below `m` is `m + w`. The loop condition `w <= len src - (r + w)` says there is a whole row after row `r`, and the invariant `r + w <= len src` keeps that subtraction from going below zero. Together they prove that `b + 1`, the last neighbour read, is inside the image. Written that way, nothing in the loop can overflow either: there is no `r + 2 * w` that could wrap around for a huge image.

The `edges` precondition is the contract the C caller has to keep: three bytes per pixel, buffers of the same size, and at least three rows of at least three pixels. Inside Pia, the calls to `gray`, `blur` and `sobel` are checked against their preconditions.

## A bug the compiler catches

Here is `blur` with a classic off-by-one. The loop checks that there is room for row `r`, but forgets that it also reads the row below:

<!-- example: edges_buggy.pia -->
<!-- source: examples/edges/edges_buggy.pia -->
<!-- expect: fail -->
```ocaml
(* A buggy blur for the demo (docs/demo.md): the row loop forgets that it
   reads the row below the one it writes, so on the last row `b + 1` is
   past the end of the image. `piac --verify` finds the input that breaks
   it, and `piac --emit=obj` refuses to compile it.
*)
let blur (src : [u8]) (w : usize) (dst : out mutable [u8]) : unit
  requires len dst = len src && w >= 3 && 3 * w <= len src
=
  for i in 0..len src do dst.[i] <- src.[i] done;
  let r : mutable usize = w in
  while w <= len src - r
    invariant w <= r && r <= len src
    decreases len src - r
  do
    for x in 1..w - 1 do
      let a = r - w + x in
      let m = r + x in
      let b = r + w + x in
      let s : u16 =
        src.[a - 1] + src.[a] + src.[a + 1]
        + src.[m - 1] + src.[m] + src.[m + 1]
        + src.[b - 1] + src.[b] + src.[b + 1]
      in
      dst.[m] <- s / 9
    done;
    r <- r + w
  done
```

`piac` finds an image where it reads past the end:

```console
$ piac --verify edges_buggy.pia
FILL_IN
```

The counterexample is an image size that breaks the program: on its last row, the neighbours below are outside the image. In C this compiles and reads whatever is in memory after the buffer. In Pia it does not compile at all:

```console
$ piac --emit=obj -o edges_buggy.o edges_buggy.pia
FILL_IN
```

The fix is the loop condition and invariant of the real `blur` above, which leave room for the row below.
