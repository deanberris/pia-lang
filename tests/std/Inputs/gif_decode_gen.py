#!/usr/bin/env python3
"""Writes tests/std/Inputs/gif_decode_run.pia: three GIFs made with giflib
and every frame of each composited by giflib, for Pia.Image.Gif.Decode's
differential run test.

    cc -I/opt/homebrew/include -L/opt/homebrew/lib -o /tmp/gif_frames \\
        tests/std/Inputs/gif_frames.c -lgif
    python3 tests/std/Inputs/gif_decode_gen.py \\
        tests/std/Inputs/gif_decode_run.pia /tmp/gif_frames /tmp/gifs
"""
import os, subprocess, sys

out_path, tool, tmp = sys.argv[1:4]
os.makedirs(tmp, exist_ok=True)
subprocess.check_call([tool, 'make', tmp])
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

(* Decodes frame k of s, with info i, in buffers carved from m: the
   canvas is m.[0 .. 4wh]. None when the screen is over 1024 pixels or s
   over 1024 bytes, the budget of this test. *)
let decode_in (s : [u8]) (i : D.gif_info) (k : usize) (m : borrowed inout mutable [u8]) : result D.frame D.gif_error
  requires len m = 24576
= let sz : usize = i.w * i.h * 1 in
  let c4 : usize = i.w * i.h * 4 in
  if sz > 1024 || c4 > 4096 || len s > 1024 then Err (D.TooLarge 0)
  else (
    let canvas = m.[0 .. c4] in
    let save = m.[4096 .. 4096 + c4] in
    let idx = m.[8192 .. 8192 + sz] in
    let data = m.[9216 .. 9216 + len s] in
    let t = m.[10240 .. 22528] in
    let pal = m.[22528 .. 23296] in
    D.decode_frame s i k canvas save idx data t pal)

(* Frame k of s composites to exactly e, and info agrees with w, h, the
   frame count n and the loop count lp. *)
let frame_is (s : [u8]) (k : usize) (e : [u8]) (w : u16) (h : u16) (n : usize) (lp : int{0..65536}) (m : borrowed inout mutable [u8]) : bool
  requires len m = 24576
= match D.info s with
  | Ok i -> (
      if i.w <> w || i.h <> h || i.frames <> n || i.loops <> lp then false
      else (
        match decode_in s i k m with
        | Ok f -> len e <= 4096 && same (m.[0 .. len e]) e
        | Err _ -> false))
  | Err _ -> false

(* The frame record of frame k of s. *)
let record (s : [u8]) (k : usize) (m : borrowed inout mutable [u8]) : result D.frame D.gif_error
  requires len m = 24576
= match D.info s with
  | Ok i -> decode_in s i k m
  | Err e -> Err e

(* Every prefix of s shorter than s is an error. *)
let truncations (s : [u8]) : bool
= let bad : mutable bool = false in
  for n in 0 .. len s do
    match D.info (s.[0 .. n]) with
    | Ok _ -> bad <- true
    | Err _ -> ()
  done;
  bad = false

(* s with byte p flipped decodes, or fails, without crashing: c is the
   copy to flip. Returns how many frames decoded. *)
let flips (s : [u8]) (c : borrowed inout mutable [u8]) (m : borrowed inout mutable [u8]) : usize
  requires len m = 24576 && len c = len s && len s <= 1024
= let ok : mutable usize = 0 in
  for p in 0 .. len s
    invariant ok <= 8 * p
  do
    for j in 0 .. len s do c.[j] <- s.[j] done;
    c.[p] <- c.[p] ^ 0xFF;
    match D.info c with
    | Ok i -> (
        for k in 0 .. 8
          invariant ok <= 8 * p + k
        do
          if k < i.frames then (
            match decode_in c i k m with
            | Ok _ -> ok <- ok + 1
            | Err _ -> ())
          else ()
        done)
    | Err _ -> ()
  done;
  ok

let run (m : borrowed inout mutable [u8]) (c : borrowed inout mutable [u8]) : i32
  requires len m = 24576 && len c = 1024
= if frame_is still 0 still_0 20 12 1 65536 m = false then 1
  else if frame_is interlaced 0 interlaced_0 16 19 1 65536 m = false then 2
  else if frame_is anim 0 anim_0 24 16 4 3 m = false then 3
  else if frame_is anim 1 anim_1 24 16 4 3 m = false then 4
  else if frame_is anim 2 anim_2 24 16 4 3 m = false then 5
  else if frame_is anim 3 anim_3 24 16 4 3 m = false then 6
  else (
    match record anim 2 m with
    | Ok f -> (
        if f.disposal <> 3 || f.delay <> 30 || f.transparent <> 3 || f.x0 <> 10 || f.fw <> 14 then 7
        else (
          match record anim 3 m with
          | Ok g -> (
              if g.x0 <> 18 || g.y0 <> 12 || g.fw <> 10 || g.fh <> 6 || g.transparent <> 256 then 8
              else if truncations still = false || truncations interlaced = false || truncations anim = false then 9
              else (
                let a = flips still (c.[0 .. len still]) m in
                let b = flips interlaced (c.[0 .. len interlaced]) m in
                let d = flips anim (c.[0 .. len anim]) m in
                if a = 0 || d = 0 then 10 else 0))
          | Err _ -> 11))
    | Err _ -> 12)

let main () : i32 = with_arena 25600 (let (a) => run (a.mem.[0 .. 24576]) (a.mem.[24576 .. 25600]))
'''

gifs = [('still', 1), ('interlaced', 1), ('anim', 4)]

def arr(name, xs):
    return 'let %s : [u8; %d] = [%s]\n' % (name, len(xs), '; '.join(map(str, xs)))

o = open(out_path, 'w')
o.write('''(* Runs Pia.Image.Gif.Decode's compiled code, linked by pia_binary: 0 when
   every frame of three GIFs made by giflib composites to what giflib's
   decoder and tests/std/Inputs/gif_frames.c composite, when info and the
   frame records say what the files hold, and when every truncation of
   each file is an error and no corrupted copy (each byte flipped in turn)
   crashes; otherwise the number of the first wrong check. Generated by
   tests/std/Inputs/gif_decode_gen.py. still is one frame with a global
   table; interlaced is one interlaced frame with a local table; anim is
   four frames with disposals 1, 2, 3 and 0, transparency, a NETSCAPE2.0
   loop count of 3, and a last frame that runs off the screen. *)
import Pia.Image.Bits.Bits as B
import Pia.Image.Raster.Raster as R
import Pia.Image.Gif.Spec.Lzw as S
import Pia.Image.Gif.Spec.Blocks as G
import Pia.Image.Gif.Lzw.Lzw as L
import Pia.Image.Gif.Decode.Decode as D

''')
biggest = 0
for name, n in gifs:
    data = open(os.path.join(tmp, name + '.gif'), 'rb').read()
    o.write(arr(name, list(data)))
    for k in range(n):
        px = list(map(int, subprocess.check_output([tool, 'comp', os.path.join(tmp, name + '.gif'), str(k)]).split()))
        o.write(arr('%s_%d' % (name, k), px))
        biggest = max(biggest, len(px))
    biggest = max(biggest, len(data))
o.write(TAIL)
o.close()
print('biggest', biggest)
