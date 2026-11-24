#!/usr/bin/env python3
"""Writes tests/std/Inputs/gif_quantise_run.pia: two RGB animations, the
GIF Pia.Image.Gif.Quantise's encode_rgb_animation writes for each, and
giflib's composite of every frame of it, for the quantiser's run test.

    bazel build //lib/Pia/Image/Gif:quantise
    piac --emit=interface -o /tmp/if lib/Pia/Image/... (each module)
    piac --emit=obj --iface-path=/tmp/if -o /tmp/w.o tests/std/Inputs/gif_quantise_c.pia
    cc -o /tmp/gen tests/std/Inputs/gif_quantise_main.c /tmp/w.o \\
        bazel-bin/lib/Pia/Image/*.o bazel-bin/lib/Pia/Image/Gif/*.o
    python3 tests/std/Inputs/gif_quantise_gen.py tests/std/Inputs/gif_quantise_run.pia \\
        /tmp/gen /tmp/gif_frames /tmp/gifq

few has six colours, so its palette is exact and giflib must composite each
frame back to the RGB given; gradient has 3072 colours, so it is median
cut, and the run test checks that Pia.Image.Gif.Decode composites it as
giflib does.
"""
import os, subprocess, sys

out_path, gen, frames_tool, tmp = sys.argv[1:5]
os.makedirs(tmp, exist_ok=True)
cols = [(250, 10, 10), (10, 200, 30), (20, 20, 220), (240, 240, 0), (0, 0, 0), (255, 255, 255)]
def few(t):
    px = []
    for y in range(30):
        for x in range(40):
            c = cols[(x // 8 + y // 10) % 4]
            if 5 + 6 * t <= x < 15 + 6 * t and 8 <= y < 18: c = cols[4 + t % 2]
            px += list(c)
    return px
grad = []
for y in range(48):
    for x in range(64): grad += [x * 4, y * 5, (x + y) * 2]
anims = [('few', 40, 30, 2, 20, 0, few(0) + few(1)), ('gradient', 64, 48, 1, 0, 0, grad)]

def arr(name, xs):
    return 'let %s : [u8; %d] = [%s]\n' % (name, len(xs), '; '.join(map(str, xs)))

HEAD = r'''(* Runs Pia.Image.Gif.Quantise's compiled code, linked by pia_binary: 0
   when, for two RGB animations, quantise reports what it should (few's six
   colours exactly, gradient's 3072 by median cut), encode_rgb_animation
   writes exactly the GIF whose frames giflib composited when
   tests/std/Inputs/gif_quantise_gen.py generated this file (for few, back
   to the RGB given), and Pia.Image.Gif.Decode composites every frame as
   giflib did; otherwise the number of the first wrong check. *)
import Pia.Image.Bits.Bits as B
import Pia.Image.Raster.Raster as R
import Pia.Image.Gif.Spec.Lzw as S
import Pia.Image.Gif.Spec.Blocks as G
import Pia.Image.Gif.Lzw.Lzw as L
import Pia.Image.Gif.Decode.Decode as D
import Pia.Image.Gif.LzwEncode.LzwEncode as E
import Pia.Image.Gif.Encode.Encode as X
import Pia.Image.Gif.Quantise.Quantise as Q

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

(* quantise rgb says exact = ex, and k colours when k is not 0. *)
let quantises (rgb : [u8]) (ex : bool) (k : u16) (m : borrowed inout mutable [u8]) : bool
  requires len m = 196608
= let npx : usize = len rgb / 3 in
  if npx > 4096 || len rgb <> 3 * npx then false
  else (
    let q = Q.quantise rgb 256 (m.[4096 .. 4864]) (m.[0 .. npx]) (m.[4864 .. 6400]) (m.[6400 .. 7424]) in
    q.exact = ex && (k = 0 || q.k = k))

(* encode_rgb_animation writes exactly expect. *)
let encodes (w : u16) (h : u16) (rgb : [u8]) (nf : u16) (delay : u16) (loops : u16) (expect : [u8]) (m : borrowed inout mutable [u8]) : bool
  requires len m = 196608
= if w = 0 || h = 0 then false
  else (
    let w' : int{1..65535} = w in
    let h' : int{1..65535} = h in
    let fs : usize = w' * h' * 1 in
    let npx : usize = len rgb / 3 in
    if fs > 4096 || npx > 4096 || len rgb <> 3 * npx then false
    else (
      let bound = X.size_bound w' h' nf in
      if bound > 32768 then false
      else (
        let idx = m.[0 .. npx] in
        let pal = m.[4096 .. 4864] in
        let bx = m.[4864 .. 6400] in
        let hist = m.[6400 .. 7424] in
        let rect = m.[8192 .. 8192 + fs] in
        let lz = m.[12288 .. 12288 + 3 * fs + 5] in
        let hash = m.[28672 .. 69632] in
        let dst = m.[69632 .. 69632 + bound] in
        match Q.encode_rgb_animation w' h' rgb nf delay loops dst idx pal bx hist rect lz hash with
        | Ok n -> n <= bound && same (m.[69632 .. 69632 + n]) expect
        | Err _ -> false)))

(* Frame k of s composites to exactly e. *)
let decodes (s : [u8]) (k : usize) (e : [u8]) (m : borrowed inout mutable [u8]) : bool
  requires len m = 196608
= match D.info s with
  | Ok i -> (
      let sz : usize = i.w * i.h * 1 in
      let c4 : usize = i.w * i.h * 4 in
      if sz > 4096 || c4 > 16384 || len s > 32768 then false
      else (
        let canvas = m.[102400 .. 102400 + c4] in
        let save = m.[118784 .. 118784 + c4] in
        let idx = m.[135168 .. 135168 + sz] in
        let data = m.[139264 .. 139264 + len s] in
        let t = m.[172032 .. 184320] in
        let cmap = m.[184320 .. 185088] in
        match D.decode_frame s i k canvas save idx data t cmap with
        | Ok f -> same (m.[102400 .. 102400 + c4]) e
        | Err _ -> false))
  | Err _ -> false

let run (m : borrowed inout mutable [u8]) : i32
  requires len m = 196608
= if quantises few_rgb true 6 m = false then 1
  else if quantises gradient_rgb false 0 m = false then 2
  else if encodes 40 30 few_rgb 2 20 0 few_gif m = false then 3
  else if decodes few_gif 0 few_giflib_0 m = false then 4
  else if decodes few_gif 1 few_giflib_1 m = false then 5
  else if encodes 64 48 gradient_rgb 1 0 0 gradient_gif m = false then 6
  else if decodes gradient_gif 0 gradient_giflib_0 m = false then 7
  else 0

let main () : i32 = with_arena 196608 (let (a) => run a.mem)
'''

o = open(out_path, 'w')
o.write(HEAD)
for name, w, h, nf, delay, loops, rgb in anims:
    rp = os.path.join(tmp, name + '.rgb'); open(rp, 'wb').write(bytes(rgb))
    gp = os.path.join(tmp, name + '.gif')
    subprocess.check_call([gen, str(w), str(h), str(nf), str(delay), str(loops), rp, gp])
    o.write(arr(name + '_rgb', rgb)); o.write(arr(name + '_gif', list(open(gp, 'rb').read())))
    for k in range(nf):
        got = list(map(int, subprocess.check_output([frames_tool, 'comp', gp, str(k)]).split()))
        if name == 'few':
            want = []
            fr = rgb[k * w * h * 3:(k + 1) * w * h * 3]
            for i in range(w * h): want += fr[3 * i:3 * i + 3] + [255]
            assert got == want, (name, k)
        o.write(arr('%s_giflib_%d' % (name, k), got))
    print(name, 'gif bytes', len(open(gp, 'rb').read()))
o.write(TAIL)
