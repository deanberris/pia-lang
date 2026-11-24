# giflib's background colour

In April 2016, giflib fixed CVE-2016-3977, a heap buffer overflow in
`gif2rgb`, the utility that converts GIF images to RGB. The CVE record
says a crafted GIF crashes it "via the background color index". Henri Salo
found it with the afl fuzzer and reported it as giflib [bug #87][bug].

A GIF names its background colour by an index into its colour table, and
nothing makes the index fit the table.

This page is a literate Pia file,
[`docs/cases/giflib-background.pia.md`](https://github.com/deanberris/pia-lang/blob/main/docs/cases/giflib-background.pia.md).
The `pia` blocks are the fixed program, which the test suite proves, and
the other code blocks are the broken versions, each checked to fail
exactly as shown.

## The bug

The logical screen descriptor at the start of every GIF holds the
background colour's index in one byte, so it can be 0 to 255. The global
colour table holds 2 to 256 colours, as the same descriptor says. As
Red Hat's analysis of the report ([bug 1325771][rh]) describes, `gif2rgb`
fills the first row of its screen buffer with `SBackGroundColor`, and
`DumpScreen2RGB` later looks every pixel up as `ColorMap->Colors[GifRow[j]]`
with no check against the table's `ColorCount`. The reproducer's table has
two colours and a background index of 255, so the lookup reads far past
the end of the table. The [fix][fix] checks the index before the dump:
if `SBackGroundColor` is negative or at least `ColorMap->ColorCount`, it
prints "Background color out of range for colormap" and exits.

## The same shape in Pia

This is not giflib's code; it is the shape of the bug: an RGB colour
table and an index read from the file.

<!-- example: colours.pia -->
<!-- expect: fail -->
```ocaml
let background_red (colors : [u8]) (bg : u8) : u8 =
  let i : usize = bg in
  colors.[3 * i]
```

`piac` will not compile it:

```console
$ piac --verify colours.pia
colours.pia:3:13: proved: '*' does not overflow usize [intervals]
colours.pia:3:3: failed: the index is within bounds
  counterexample: len colors = 1, bg = 239, index = 717, length = 1
1 proved, 1 failed, 0 skipped
```

The counterexample is the bug: a table shorter than the colour the file
names.

## The fix, proved, two ways

giflib's fix rejects a file whose index does not fit its table. In Pia
the check is what lets the index through:

```pia
let background_red (colors : [u8]) (bg : u8) : result u8 usize
= let i : usize = bg in
  if 3 * i + 2 < len colors then Ok colors.[3 * i] else Err i
```

Pia's own GIF decoder, [`Pia.Image.Gif.Decode`][decode] (ADR 0054, step
2), takes the other way: it copies every colour table into a 256-entry map
padded with black, so every index a byte can hold has a colour, and states
that in the type of what it indexes. Then there is nothing left to check:

```pia
let padded_red (colors : [u8]) (bg : u8) : u8
  requires len colors = 768
= let i : usize = bg in
  colors.[3 * i]
```

Every goal on this page is proved:

```console
$ piac --verify giflib-background.pia.md
...
giflib-background.pia.md:77:3: proved: the index is within bounds [smt]
6 proved, 0 failed, 0 skipped
```

The decoder proves the same of every pixel: each index its LZW decoder
writes is below 2^8, and the map it looks them up in is 768 bytes, so no
frame of any input can read past its colour table. Its run test decodes
every one-byte corruption of three GIFs without a crash.

## Sources

- The CVE record, [CVE-2016-3977][cve], published 21 April 2016: giflib
  5.1.2's `util/gif2rgb.c`.
- giflib [bug #87][bug], "Heap buffer overflow in 5.1.2 gif2rgb.c:531",
  by Henri Salo, March 2016.
- giflib commit [ea8dbc5786862a3e16a5acfa3d24e2c2f608cd88][fix], "Fix SF
  bug #87 Heap buffer overflow in 5.1.2 (gif2rgb)", by Eric S. Raymond, 2
  April 2016: the range check on the background colour.
- Red Hat [bug 1325771][rh]: the analysis of the out-of-bounds read
  through `ColorMap->Colors`.

[cve]: https://www.cve.org/CVERecord?id=CVE-2016-3977
[bug]: https://sourceforge.net/p/giflib/bugs/87/
[fix]: https://sourceforge.net/p/giflib/code/ci/ea8dbc5786862a3e16a5acfa3d24e2c2f608cd88/
[rh]: https://bugzilla.redhat.com/show_bug.cgi?id=1325771
[decode]: https://github.com/deanberris/pia-lang/blob/main/lib/Pia/Image/Gif/Decode.pia
