# 54. GIF and JPEG codecs are proved total on every input, decode to a written specification, and round-trip wherever the format is lossless

Date: 2026-11-23

Status: Proposed

## Context

Dean asked (2026-11-23) for GIF and JPEG encode and decode, implemented in Pia and proved correct, "so we don't have the rendering related bugs that other shaders and renderers have encountered". [ADR 0016](0016-stream-delineation-flagship-demo.md) already puts image I/O on the path of the flagship demo, M13 ([#14](https://github.com/deanberris/pia-lang/issues/14)) is the image I/O milestone, and [stdlib.md](../stdlib.md) lists `Image.Gif` with "GIF LZW" as one of the library's stress tests. JPEG is new.

Image decoders are among the most attacked code there is, because an image arrives from anywhere and is decoded before anyone looks at it. The bugs fall into a few classes, and each one is a goal the verifier already knows how to state:

| Bug class | Example | What rules it out here |
| --- | --- | --- |
| A length field trusted before it is checked | GDI+ JPEG, MS04-028 (CVE-2004-0200): a comment segment of length 0 or 1 underflowed `length - 2` and overwrote the heap | every segment length is a range type, `- 2` is proved not to underflow, and a segment is proved to lie inside the input |
| A table built from a code the image describes | libwebp CVE-2023-4863: Huffman tables written past their allocation before the code was validated ([case study](../cases/libwebp.pia.md)) | a Huffman code is proved complete or rejected before any table is written, and each table index is proved in bounds |
| An index used before the table holds it | LZW decoders that accept a code above the next free entry, or let the dictionary grow past 4096 | the code is proved `<= next` before it is looked up, and `next <= 4096` is an invariant |
| A palette index outside the palette | giflib's `gif2rgb` (CVE-2016-3977, background colour index) | every index written is proved `< palette size`, or the colour map is padded to 256 by the decoder |
| Pixels never written | libjpeg CVE-2013-6629: a scan that names a component twice left output uninitialised, which leaked heap memory into the picture | the decoder proves that every pixel of the output is written, and rejects duplicate or missing components |
| Out-of-range samples and edge reads | IDCT overflow, colour conversion wrapping past 255, chroma upsampling reading the row after the last one when the height is not a multiple of the MCU | the IDCT's intermediates are proved in range, outputs are clamped by type (`u8`, not wrap), and every upsampling read is proved in bounds |
| Frames outside the canvas | a GIF frame rectangle larger than the logical screen | a frame is proved inside the screen or clipped, by the type of its rectangle |
| Decompression bombs | a 65535 x 65535 header with a few bytes of data | the decoder takes a pixel budget, and `width * height * channels <= budget` is checked before any output is touched |

The renderer bugs Dean mentions sit one step further on, in code that consumes the pixels: a shader that samples past an edge, or assumes values in `0..255` that a decoder did not deliver. The codecs cannot fix that code, but they can hand it facts. A decoded image carries its dimensions and sample ranges in its type, so a kernel in the dataflow graph of [ADR 0050](0050-senders-and-receivers.md) that reads it starts from those facts instead of hoping for them.

What the compiler can do today shapes the plan:

- **Integers only.** Floats (M11) are not compiled yet ([status.md](../status.md)), and [ADR 0038](0038-float-kernels-against-real-theories.md) proves float kernels against reals by error bounds, which is heavy for an 8x8 transform run millions of times. Every widely deployed JPEG decoder has an integer IDCT for this reason.
- **Products of small values stay cheap.** A product keeps a function at 68-bit bit-vectors when its operands' types bound it ([verifier.md](../verifier.md)), and IDCT constants times 16-bit coefficients do. `width * height` goes through the `index_2d_lt` style lemmas of [stdlib.md](../stdlib.md).
- **No `Pia.Mem` module yet.** Allocators, `box` and `vec` are prototyped as tests ([CODEMAP.md](../../CODEMAP.md), section 3), so the codecs should not need to allocate.
- **The pattern exists.** `Pia.Core.Utf8` proves both round trips of a codec, and `Pia.Text.Json` proves a tokenizer against a grammar written as spec functions ([ADR 0045](0045-json-derived-codecs-and-conforming-dom.md)). The codecs follow the same shape: a `Spec` module that says what the bytes mean, and code proved equal to it function by function.

## Decision

### 1. What "proved correct" means

Every codec function has four levels of guarantee. The first two hold for every function, the other two where the format allows them.

1. **Total and safe on every input.** For any byte slice, decoding returns `Ok` or an `Err` from a closed set, with no out-of-bounds access, no overflow, no uninitialised read, and a termination measure (bytes left to read). This is the strongest-guarantee default of [ADR 0004](0004-strongest-guarantee-by-default.md); nothing is `@trusted`.
2. **Bounded.** Output size is checked against a caller's pixel budget before decoding, and the decoder needs no memory beyond the output and fixed-size tables (the LZW dictionary is 4096 entries, a JPEG Huffman lookup table is bounded by the code lengths).
3. **Conforming decode.** `Ok` happens exactly when the input is in the format's grammar, written as spec functions, and the pixels are the ones the specification defines. For GIF that is the GIF89a block grammar and the LZW semantics. For JPEG it is the baseline grammar of ITU-T T.81 and its decoding process up to the IDCT, with the IDCT fixed by section 4.
4. **Round trips.** Where a format is lossless, decode after encode is the identity, proved: GIF images, and JPEG's entropy coding. JPEG's lossy steps are named in the theorem instead of hidden: the encoder's output decodes to exactly `idct (dequantise (quantise (fdct x)))`, so the only loss is quantisation and the two transforms.

### 2. Scope

| Codec | In | Out (rejected with `Unsupported`, never misread) |
| --- | --- | --- |
| GIF decode | GIF87a and GIF89a; global and local colour tables; LZW code sizes 2 to 12; interlacing; transparency and disposal from the Graphic Control Extension; every frame of an animation; other extensions skipped by their length | nothing: every valid GIF decodes |
| GIF encode | indexed images with a palette of up to 256 colours, one frame or an animation, interlaced or not, with a dictionary reset when it fills | colour quantisation from RGB, which is a separate function (section 6) |
| JPEG decode | baseline sequential DCT (SOF0) and extended sequential with Huffman coding at 8 bits (SOF1); 1 or 3 components; sampling factors 1 to 4 (4:4:4, 4:2:2, 4:2:0, 4:4:0 and the rest); restart intervals; JFIF and Adobe colour transforms; progressive (SOF2) as the second step | arithmetic coding, 12-bit and lossless JPEG, hierarchical mode, CMYK (a later ADR if needed) |
| JPEG encode | baseline, 1 or 3 components, 4:4:4 or 4:2:0, quality scaled from the Annex K tables, optional optimised Huffman tables | progressive encode |

### 3. Modules

The codecs live under `Pia.Image`, one module per file ([ADR 0039](0039-module-and-interface-syntax.md)). Each format has a `Spec` that the rest is proved against, as `Json.Spec` is for JSON.

| Module | Provides |
| --- | --- |
| `Image.Raster` | `raster c`: width, height and `c` channels of `u8` over a borrowed slice, with `len = width * height * c` in its type; `rect` inside a raster |
| `Image.Bits` | bit readers and writers over a byte slice: LSB-first for GIF, MSB-first with `0xFF 0x00` stuffing and marker detection for JPEG, each proved against a spec function of "the bit at position k" |
| `Image.Gif.Spec` | the block grammar and the meaning of a code stream: `lzw_decode` as a spec function over a dictionary of strings |
| `Image.Gif.Lzw` | the decoder over prefix/suffix tables, and the encoder over a hash of (prefix, byte), each proved equal to the spec |
| `Image.Gif.Decode`, `Image.Gif.Encode` | the container: screen descriptor, colour tables, image descriptors, extensions, interlace order, frames |
| `Image.Jpeg.Spec` | markers and segments, the canonical Huffman code of Annex C, the entropy decoding of F.2, zigzag order, dequantisation and the reference IDCT of section 4 |
| `Image.Jpeg.Huffman` | table building with the completeness check, fast lookup, decode and encode |
| `Image.Jpeg.Idct`, `Image.Jpeg.Fdct` | the integer transforms |
| `Image.Jpeg.Color` | upsampling and YCbCr to RGB in fixed point, and the reverse |
| `Image.Jpeg.Decode`, `Image.Jpeg.Encode` | the container and the scan loop |

`Image.Bits` and the LZW and Huffman modules need neither an allocator nor the OS, so they belong with `Pia.Core` in what [stdlib.md](../stdlib.md) says can later run in a GPU kernel.

### 4. JPEG's IDCT is an integer transform proved bit-exact against a reference, with its accuracy tested

The real-valued IDCT of T.81 is not computable exactly, so "conforming" needs a definite target. The decision is:

- `Jpeg.Spec` defines one integer IDCT as a spec function: the "islow" algorithm of the IJG library (Loeffler, Ligtenberg and Moschytz, 13-bit fixed-point constants), which libjpeg-turbo and most decoders use as their accurate default. `Jpeg.Idct` is proved equal to it for every input block, and every intermediate is proved in range for coefficients in `-2048 .. 2047` after dequantisation, so the transform cannot overflow on any input.
- Its accuracy against the real IDCT is tested, not proved: the IEEE 1180 procedure (10,000 random blocks per range, peak error at most 1, mean square error bounds) runs as a test, and the decoder's output is compared with libjpeg-turbo's at the same settings across a corpus. Proving the error bound against reals with [ADR 0038](0038-float-kernels-against-real-theories.md) is possible later and is question 2.
- Being bit-exact against a named algorithm means the decoder's pixels are a function the reader can check, and the encoder's round-trip theorem in section 1 has a concrete `idct` in it.

The forward DCT is the matching integer transform, proved in range; its accuracy is tested the same way.

### 5. Decoding is in two steps and does not allocate

```ocaml
let info : (s : [u8]) -> result gif_info GifError
let decode_frame : (s : [u8]) -> (i : gif_info) -> (k : usize)
                 -> (out : borrowed inout mutable [u8]) -> result frame GifError
  requires k < frames i && len out = width i * height i * 4
```

`info` reads the headers and returns the dimensions, frame count and component layout, proved to agree with `Spec`. The caller checks them against its own budget, allocates the output with whatever allocator it holds, and calls `decode` into it. JPEG has the same shape, with a scratch buffer whose size `info` also returns (one MCU row of coefficients for baseline, the whole coefficient image for progressive). Wrappers that take an allocator and a budget, and return an owned image, come when `Pia.Mem` is a module.

Errors are a closed set per format ([ADR 0028](0028-error-propagation-and-cleanup.md)): `Truncated`, `BadSignature`, `BadSegment of usize` (the offset), `BadHuffmanTable`, `BadCode`, `Unsupported`, `TooLarge`, and the like. An error carries the byte offset where the spec stops accepting the input, proved to be that offset, as `Json.Lex` does.

### 6. Encoders take indexed or planar input; quantisation is separate

The GIF encoder takes an index raster and a palette, so its round trip is exact. A separate `Image.Gif.Quantise` maps RGB to a palette (median cut first) and is proved to produce indices below the palette size; it makes no claim about visual quality. The JPEG encoder takes RGB or gray, and its colour conversion and subsampling are in the round-trip theorem as named steps.

### 7. Tests beside the proofs

Proofs cover the Pia code. Three test kinds cover the claims the proofs do not reach, and catch a wrong spec:

- **Differential:** every image of a corpus (the libjpeg-turbo and giflib test images, the JPEG conformance streams of ITU-T T.83 where they can be had, and images from the streams demo) decodes to the same pixels as libjpeg-turbo (islow) and giflib. Run on the iMac and in Linux CI.
- **Fuzzing:** libFuzzer through `--sanitize=fuzzer` when it exists ([ADR 0025](0025-sanitizers.md)), which checks that the compiled code matches the proved code, not the proofs themselves.
- **Case studies:** GDI+ JPEG and CVE-2013-6629 join `docs/cases`, written against primary sources, each showing the unsound decoder failing `piac --verify` and the library's version proving.

### 8. Build order

One issue and one pull request at a time, each prototyped in the REPL first:

1. `Image.Bits` and `Image.Raster`.
2. GIF LZW decode against `Gif.Spec`, then the container decode: every GIF decodes.
3. GIF LZW encode and the round-trip theorem, then the container encode.
4. JPEG Huffman: table building with the completeness check, decode against Annex C.
5. JPEG baseline decode: markers, entropy decoding, dequantisation, `Idct` bit-exact against the spec, upsampling, colour conversion, every pixel written.
6. JPEG baseline encode and its round-trip theorem.
7. JPEG progressive decode.
8. The case studies, and the streams demo writing its output as an animated GIF (flow accumulation over time) and reading imagery as JPEG.

## Questions for Dean

1. **Is progressive JPEG decode in scope?** The recommendation is yes, as step 7 after baseline, because most photographs on the web are progressive and a decoder that rejects them is not usable as a general reader. The alternative is baseline only, which covers cameras and the encoder's own output.
2. **Is a bit-exact integer IDCT with tested accuracy enough, or should its error bound against the real IDCT be proved?** The recommendation is bit-exact plus the IEEE 1180 test now (section 4), with the proved bound as later work once floats and reals proofs are cheaper. The alternative proves the bound now through the reals theory of ADR 0038, which would likely be the slowest proof in the library.
3. **Should decoders allocate?** The recommendation is two-step decoding into a caller's buffer (section 5), so the codecs work before `Pia.Mem` exists and run anywhere `Pia.Core` runs. The alternative takes an allocator now and waits on `Pia.Mem`.
4. **Is colour quantisation (RGB to a 256-colour palette) part of this work?** The recommendation is yes, but only proved safe, not proved good. The alternative leaves GIF encoding to callers that already have indexed images.

## Consequences

- Two more formats join `Json` and `Utf8` as codecs proved against a written spec, and the pattern (spec module, code proved equal to it, round trip where lossless) becomes the house style for formats, ahead of PNG and zlib.
- The image path of the flagship demo no longer needs a C harness for GIF and JPEG.
- Pixels from these decoders carry proved dimensions and ranges into the code that renders them.
- The proofs add to build time ([ADR 0032](0032-parallel-sliced-cached-proving.md)). The IDCT and the Huffman decoder are the likely hot spots and go into the proof benchmark corpus when they land.
- Bit-exactness pins the IDCT. A faster transform (AAN, or SIMD) has to be proved equal to the same spec, or come with its own spec and say so.

## Prior art

| Source | What Pia takes |
| --- | --- |
| ITU-T T.81 (JPEG), Annexes B, C, F, G and K | the grammar, canonical Huffman codes, the decoding process, progressive mode and the example tables |
| ITU-T T.83 and IEEE 1180-1990 | the conformance streams and the IDCT accuracy test |
| CompuServe GIF89a specification | the block grammar, LZW variant, interlace order and extensions |
| IJG libjpeg and libjpeg-turbo (`jidctint.c`, `jfdctint.c`) | the islow integer transforms that `Jpeg.Spec` fixes as the reference |
| giflib | the reference GIF decoder for differential tests |
| Wuffs (Google) | a memory-safe, bounds-checked GIF and JPEG decoder language with no allocation in the codec, which shows the two-step, caller-buffer design works at production speed; Pia adds functional specs and round trips |
| EverParse (Project Everest) | parsers proved against a format grammar, with the grammar as the specification |
