#!/usr/bin/env python3
"""Writes tests/std/Inputs/gif_encode_run.pia: two animations, the GIF
Pia.Image.Gif.Encode writes for each, checked here with giflib, for the
encoder's run test.

The encoder runs through a C entry point (gif_encode_c.pia) linked into a
small C program, and giflib's decoder (through gif_frames.c) composites
every frame of what it wrote, which must be exactly the frame given. The
run test then checks that the encoder still writes those bytes, and that
Pia.Image.Gif.Decode composites them back to the frames.

    bazel build //lib/Pia/Image/Gif:encode
    piac --emit=interface -o /tmp/if lib/Pia/Image/... (each module)
    piac --emit=obj --iface-path=/tmp/if -o /tmp/w.o tests/std/Inputs/gif_encode_c.pia
    cc -o /tmp/gen gen_main.c /tmp/w.o bazel-bin/lib/Pia/Image/*.o bazel-bin/lib/Pia/Image/Gif/*.o
    python3 tests/std/Inputs/gif_encode_gen.py tests/std/Inputs/gif_encode_run.pia \\
        /tmp/gen /tmp/gif_frames /tmp/gifenc

where gen_main.c is tests/std/Inputs/gif_encode_main.c and gif_frames is
tests/std/Inputs/gif_frames.c built with giflib.
"""
import os, subprocess, sys

out_path, gen, frames_tool, tmp = sys.argv[1:5]
os.makedirs(tmp, exist_ok=True)

def lcg(n, mod, seed):
    x = seed; r = []
    for _ in range(n):
        x = (x * 1103515245 + 12345) & 0x7fffffff; r.append((x >> 16) % mod)
    return r

# A moving square over a gradient, 8 colours, 5 frames: frame 3 repeats
# frame 2, so it is written as one unchanged pixel.
W1, H1 = 32, 24
pal1 = []
for i in range(8): pal1 += [i * 32, 255 - i * 30, (i * 70) % 256]
def sq(t):
    px = [((x + y) // 7) % 6 for y in range(H1) for x in range(W1)]
    for y in range(4 + 3 * t, 10 + 3 * t):
        for x in range(2 + 5 * t, 9 + 5 * t):
            if x < W1 and y < H1: px[y * W1 + x] = 7
    return px
frames1 = sq(0) + sq(1) + sq(2) + sq(2) + sq(4)
# Noise with 256 colours, 2 frames, so the dictionary fills and clears.
W2, H2 = 96, 64
pal2 = []
for i in range(256): pal2 += [i, (i * 7) % 256, 255 - i]
frames2 = lcg(W2 * H2, 256, 3) + lcg(W2 * H2, 256, 4)
anims = [('square', W1, H1, 5, 10, 0, pal1, frames1), ('noise', W2, H2, 2, 50, 3, pal2, frames2)]

def arr(name, xs):
    return 'let %s : [u8; %d] = [%s]\n' % (name, len(xs), '; '.join(map(str, xs)))

HEAD = r'''(* Runs Pia.Image.Gif.Encode's compiled code, linked by pia_binary: 0 when
   encode_animation writes, for each of two animations, exactly the GIF
   that giflib composited back to the frames given (checked when
   tests/std/Inputs/gif_encode_gen.py generated this file), and when
   Pia.Image.Gif.Decode reads that GIF's screen, frame count and loop count
   and composites every frame back to the frames given; otherwise the
   number of the first wrong check. square is 32 by 24 with 8 colours and
   5 frames, a square moving over a gradient, whose frame 3 repeats frame
   2; noise is 96 by 64 with 256 colours and 2 frames of noise, so the
   LZW dictionary fills and is cleared. *)
import Pia.Image.Bits.Bits as B
import Pia.Image.Raster.Raster as R
import Pia.Image.Gif.Spec.Lzw as S
import Pia.Image.Gif.Spec.Blocks as G
import Pia.Image.Gif.Lzw.Lzw as L
import Pia.Image.Gif.Decode.Decode as D
import Pia.Image.Gif.LzwEncode.LzwEncode as E
import Pia.Image.Gif.Encode.Encode as X

'''
TAIL = r'''
(* a and b hold the same bytes. *)
let same (a : [u8]) (b : [u8]) : bool
= if len a <> len b then false
  else (
    let bad : mutable bool = false in
    for j in 0 .. len a do
      if a.[j] <> b.[j] then bad <- true else ()
    done;
    bad = false)

(* encode_animation writes exactly expect, in buffers carved from m. *)
let encodes_to (w : u16) (h : u16) (pal : [u8]) (frames : [u8]) (nf : u16) (delay : u16) (loops : u16) (expect : [u8]) (m : borrowed inout mutable [u8]) : bool
  requires len m = 262144
= if w = 0 || h = 0 then false
  else (
    let w' : int{1..65535} = w in
    let h' : int{1..65535} = h in
    let fs : usize = w' * h' * 1 in
    if fs > 8192 then false
    else (
      let bound = X.size_bound w' h' nf in
      if bound > 65536 then false
      else (
        let rect = m.[0 .. fs] in
        let lz = m.[8192 .. 8192 + 3 * fs + 5] in
        let hash = m.[40960 .. 81920] in
        let dst = m.[81920 .. 81920 + bound] in
        match X.encode_animation w' h' pal frames nf delay loops dst rect lz hash with
        | Ok n -> n <= bound && same (m.[81920 .. 81920 + n]) expect
        | Err _ -> false)))

(* Frame k of s, decoded into buffers carved from m, is the frame at
   frames.[base ..] through pal, opaque. *)
let frame_ok (s : [u8]) (i : D.gif_info) (k : usize) (frames : [u8]) (base : usize) (pal : [u8]) (m : borrowed inout mutable [u8]) : bool
  requires len m = 262144
= let sz : usize = i.w * i.h * 1 in
  let c4 : usize = i.w * i.h * 4 in
  if sz > 8192 || c4 > 32768 || len s > 65536 || base > len frames || len frames - base < sz then false
  else (
    let canvas = m.[0 .. c4] in
    let save = m.[32768 .. 32768 + c4] in
    let idx = m.[65536 .. 65536 + sz] in
    let data = m.[73728 .. 73728 + len s] in
    let t = m.[139264 .. 151552] in
    let cmap = m.[151552 .. 152320] in
    match D.decode_frame s i k canvas save idx data t cmap with
    | Ok f -> (
        let bad : mutable bool = false in
        for p in 0 .. sz do
          let v : usize = frames.[base + p] in
          if 3 * v + 2 >= len pal || 4 * p + 3 >= c4 then bad <- true
          else if m.[4 * p] <> pal.[3 * v] || m.[4 * p + 1] <> pal.[3 * v + 1]
                  || m.[4 * p + 2] <> pal.[3 * v + 2] || m.[4 * p + 3] <> 255 then bad <- true
          else ()
        done;
        bad = false)
    | Err _ -> false)

(* info reads w, h, nf and loops from s, and every frame decodes to the
   frames given. *)
let decodes_to (s : [u8]) (w : u16) (h : u16) (pal : [u8]) (frames : [u8]) (nf : u16) (loops : u16) (m : borrowed inout mutable [u8]) : bool
  requires len m = 262144
= match D.info s with
  | Ok i -> (
      if i.w <> w || i.h <> h || i.frames <> nf || i.loops <> loops then false
      else (
        let sz : usize = i.w * i.h * 1 in
        let bad : mutable bool = false in
        let base : mutable usize = 0 in
        for k in 0 .. nf do
          (if frame_ok s i k frames base pal m = false then bad <- true else ());
          (if base <= 1000000000 && sz <= 1000000000 then base <- base + sz else bad <- true)
        done;
        bad = false))
  | Err _ -> false

let run (m : borrowed inout mutable [u8]) : i32
  requires len m = 262144
= if encodes_to 32 24 square_pal square_frames 5 10 0 square_gif m = false then 1
  else if decodes_to square_gif 32 24 square_pal square_frames 5 0 m = false then 2
  else if encodes_to 96 64 noise_pal noise_frames 2 50 3 noise_gif m = false then 3
  else if decodes_to noise_gif 96 64 noise_pal noise_frames 2 3 m = false then 4
  else 0

let main () : i32 = with_arena 262144 (let (a) => run a.mem)
'''

o = open(out_path, 'w')
o.write(HEAD)
for name, w, h, nf, delay, loops, pal, frames in anims:
    pp = os.path.join(tmp, name + '.pal'); open(pp, 'wb').write(bytes(pal))
    fp = os.path.join(tmp, name + '.idx'); open(fp, 'wb').write(bytes(frames))
    gp = os.path.join(tmp, name + '.gif')
    subprocess.check_call([gen, str(w), str(h), str(nf), str(delay), str(loops), pp, fp, gp])
    for k in range(nf):
        got = list(map(int, subprocess.check_output([frames_tool, 'comp', gp, str(k)]).split()))
        want = []
        for v in frames[k * w * h:(k + 1) * w * h]: want += pal[3 * v:3 * v + 3] + [255]
        assert got == want, (name, k)
    data = open(gp, 'rb').read()
    o.write(arr(name + '_pal', pal)); o.write(arr(name + '_frames', frames)); o.write(arr(name + '_gif', list(data)))
    print(name, 'frames', nf, 'gif bytes', len(data), 'raw', len(frames))
o.write(TAIL)
