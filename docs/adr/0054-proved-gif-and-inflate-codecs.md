# 54. GIF and inflate are proved total on every input, decode to a written specification, and GIF round-trips exactly

Date: 2026-11-23

Status: Proposed

## Context

Dean asked (2026-11-23) for proved image codecs, "so we don't have the rendering related bugs that other shaders and renderers have encountered". [ADR 0016](0016-stream-delineation-flagship-demo.md) already puts image I/O on the path of the flagship demo. M13 ([#14](https://github.com/deanberris/pia-lang/issues/14)) is the image I/O milestone, and [stdlib.md](../stdlib.md) lists `Image.Gif`, with "GIF LZW", as one of the library's stress tests.

Dean also decided three things on 2026-11-23:

- **The codecs run in parallel with the GPU work.** They are pure Pia over byte buffers. This was decided in the survey of the path to the GPU demo.
- **GIF comes first, then inflate.** Inflate (RFC 1951) is here because PNG and the Copernicus GeoTIFF elevation tiles both need it later.
- **JPEG is deferred entirely.** It is complicated, and it may be patent encumbered. Issue [#313](https://github.com/deanberris/pia-lang/issues/313) holds it, with the design that the first draft of this ADR worked out.

Image and compression decoders are among the most attacked code there is, because their input arrives from anywhere and is decoded before anyone looks at it. The bugs fall into a few classes, and the verifier can already state a goal that rules out each one:

| Bug class | Example | What rules it out here |
| --- | --- | --- |
| A length field trusted before it is checked | zlib CVE-2022-37434: a large gzip header extra field overflowed `inflateGetHeader`'s buffer | every length is a range type, and every copy is proved to lie inside both its source and its destination |
| A table built from a code the input describes | libwebp CVE-2023-4863: Huffman tables were written past their allocation before the code was validated ([case study](../cases/libwebp.pia.md)) | a Huffman code is proved complete, or rejected, before any table is written, and each table index is proved in bounds |
| A back-reference before the start of the output | inflate's "distance too far back", which reads memory before the output buffer | every distance is proved `<= bytes written so far` before the copy |
| An index used before the table holds it | LZW decoders that accept a code above the next free entry, or let the dictionary grow past 4096 | each code is proved `<= next` before it is looked up, and `next <= 4096` is an invariant |
| A palette index outside the palette | giflib's `gif2rgb` (CVE-2016-3977, through the background colour index) | every index written is proved `< palette size`, or the decoder pads the colour map to 256 entries |
| Pixels never written | a frame or a truncated code stream that leaves part of the canvas as old heap contents | the decoder proves that every pixel of the output is written: from the frame, from disposal, or from the background |
| Frames outside the canvas | a GIF frame rectangle that does not fit inside the logical screen | a frame is proved to lie inside the screen, or is clipped to it, by the type of its rectangle |
| Decompression bombs | a 65535 x 65535 header with a few bytes of data, or a deflate stream that expands a thousandfold | the caller gives a budget, and `width * height * channels <= budget` is checked, and the output length bounded, before any output is written |

The renderer bugs Dean mentions are one step further on, in code that consumes the pixels: a shader that samples past an edge, or one that assumes values a decoder did not deliver. The codecs cannot fix that code, but they can hand it facts. A decoded image carries its dimensions and sample ranges in its type. A kernel in the dataflow graph of [ADR 0050](0050-senders-and-receivers.md) that reads it starts from those facts instead of hoping for them.

What the compiler can do today shapes the plan:

- **Integers only.** Neither codec needs floats, which are not compiled yet (M11).
- **Products of header values.** `width * height * channels` meets verifier issue [#45](https://github.com/deanberris/pia-lang/issues/45) (multiplication). It goes through lemmas in the style of `index_2d_lt` from [stdlib.md](../stdlib.md), with each dimension capped at 65535 as GIF's 16-bit fields already cap it.
- **No `Pia.Mem` module yet.** Allocators, `box` and `vec` are prototyped as tests ([CODEMAP.md](../../CODEMAP.md), section 3), so the codecs should not need to allocate.
- **The pattern exists.** `Pia.Core.Utf8` proves both round trips of a codec, and `Pia.Text.Json` proves a tokenizer against a grammar written as spec functions ([ADR 0045](0045-json-derived-codecs-and-conforming-dom.md)). The codecs take the same shape: a `Spec` module that says what the bytes mean, and code proved equal to it, function by function.

## Decision

### 1. What "proved correct" means

Each codec function has up to four levels of guarantee. The first two hold for every function, and the last two hold where the format allows them.

1. **Total and safe on every input.** For any byte slice, decoding returns `Ok`, or an `Err` from a closed set. There is no out-of-bounds access, no overflow and no uninitialised read, and a termination measure (the input bits left to read) proves that decoding ends. This is the strongest-guarantee default of [ADR 0004](0004-strongest-guarantee-by-default.md). Nothing is `@trusted`.
2. **Bounded.** The output's size is checked against the caller's budget before decoding. The decoder needs no memory beyond the output and fixed-size tables: 4096 entries for the LZW dictionary, and a few hundred for inflate's Huffman tables plus its 32 KiB window, which is the output itself.
3. **Conforming decode.** Decoding returns `Ok` exactly when the input is in the format's grammar, which is written as spec functions, and the output is the one the specification defines. For GIF that means the GIF89a block grammar and the LZW semantics. For inflate it means RFC 1951's blocks, codes and back-references, and RFC 1950's framing with Adler-32.
4. **An exact round trip.** For GIF, decoding what was encoded gives back the frames, palettes and timing exactly, and this is proved. Inflate is decode only in this ADR, so its round trip comes with deflate (section 2).

### 2. Scope

| Codec | In scope | Out of scope |
| --- | --- | --- |
| GIF decode | GIF87a and GIF89a; global and local colour tables; LZW code sizes 2 to 12; interlacing; transparency and disposal from the Graphic Control Extension; every frame of an animation, with its delay; the NETSCAPE2.0 application extension's loop count; other extensions, skipped by their length | nothing: every valid GIF decodes |
| GIF encode | indexed images with a palette of up to 256 colours, interlaced or not, with a dictionary reset when it fills; animations with one global palette shared by every frame (a local palette only where a frame asks for one), a delay, disposal method and transparent index per frame, a loop count (the NETSCAPE2.0 extension), and frames that cover only the changed rectangle of the screen | colour quantisation from RGB, which is a separate function (section 5) |
| Inflate | every RFC 1951 stream (stored, fixed Huffman and dynamic Huffman blocks) into a caller's buffer whose length bounds the output; zlib (RFC 1950) framing, checked with its Adler-32 | deflate (compression), which comes with PNG encode in a later ADR; gzip framing until something needs it |
| JPEG | none | all of it, deferred to [#313](https://github.com/deanberris/pia-lang/issues/313) |

### 3. Modules

The codecs live under `Pia.Image` and `Pia.Compress`, one module per file ([ADR 0039](0039-module-and-interface-syntax.md)). Each format has a `Spec` that the rest is proved against, as `Json.Spec` is for JSON.

| Module | Provides |
| --- | --- |
| `Image.Raster` | `raster c`: width, height and `c` channels of `u8` over a borrowed slice, with `len = width * height * c` in its type; and `rect`, a rectangle inside a raster |
| `Image.Bits` | bit readers and writers over a byte slice, LSB first (GIF and deflate), each proved against a spec function of "the bit at position k" |
| `Image.Gif.Spec` | the block grammar, and the meaning of a code stream: `lzw_decode` as a spec function over a dictionary of strings |
| `Image.Gif.Lzw` | the decoder over prefix and suffix tables, and the encoder over a hash of (prefix, byte), each proved equal to the spec |
| `Image.Gif.Decode`, `Image.Gif.Encode` | the container: the screen descriptor, colour tables, image descriptors, extensions, interlace order and frames |
| `Image.Gif.Quantise` | RGB to a palette of at most 256 colours (section 5) |
| `Compress.Huffman` | canonical Huffman codes built from code lengths, with the completeness check, and fast lookup. Later formats reuse it. |
| `Compress.Inflate.Spec`, `Compress.Inflate` | RFC 1951 as spec functions (block types, the length and distance codes, the code-length code), and a decoder proved equal to it |
| `Compress.Zlib` | RFC 1950 framing, with Adler-32 from `Pia.Core` |

None of these needs an allocator or the OS, so they belong with `Pia.Core` in what [stdlib.md](../stdlib.md) says can later run in a GPU kernel.

### 4. Decoding is in two steps and does not allocate

```ocaml
let info : (s : [u8]) -> result gif_info GifError
let decode_frame : (s : [u8]) -> (i : gif_info) -> (k : usize)
                 -> (out : borrowed inout mutable [u8]) -> result frame GifError
  requires k < frames i && len out = width i * height i * 4
```

`info` reads the headers and returns the dimensions and the frame count, proved to agree with `Spec`. The caller checks them against its own budget, allocates the output with whatever allocator it holds, and calls `decode_frame` to fill it. Inflate takes an output slice, and returns the number of bytes written or `OutputFull` with the input offset, so a caller can grow its buffer and resume. Wrappers that take an allocator and a budget, and return an owned image or byte vector, come once `Pia.Mem` is a module.

Errors are a closed set per format ([ADR 0028](0028-error-propagation-and-cleanup.md)), such as `Truncated`, `BadSignature`, `BadBlock`, `BadHuffmanCode`, `BadCode`, `DistanceTooFar`, `BadChecksum` and `TooLarge`. Each error carries the byte offset at which the spec stops accepting the input, and that offset is proved, as `Json.Lex` proves its own.

### 5. The GIF encoder takes indexed input, and quantisation is separate

The GIF encoder takes an index raster and a palette, so its round trip is exact. `Image.Gif.Quantise` maps RGB to a palette, median cut first. It is proved to produce indices below the palette size, and it makes no claim about visual quality.

### 6. Tests beside the proofs

Proofs cover the Pia code. Three kinds of test cover the claims the proofs do not reach, and would catch a wrong spec:

- **Differential tests.** Every file in a corpus decodes to the same output as giflib for GIF, and as zlib for inflate. The corpus holds giflib's test images, zlib's test streams and the streams demo's own output. The tests run on the iMac and in Linux CI.
- **Fuzzing.** libFuzzer, through `--sanitize=fuzzer` once that exists ([ADR 0025](0025-sanitizers.md)), checks that the compiled code matches the proved code. It does not check the proofs themselves.
- **Case studies.** zlib CVE-2022-37434 and giflib CVE-2016-3977 join `docs/cases`, written from primary sources. Each shows the unsound decoder failing `piac --verify`, and the library's version proving.

### 7. Build order

Each step is one issue and one pull request, prototyped in the REPL first:

1. `Image.Bits` and `Image.Raster`. Any verifier fix that #45 needs is a pull request of its own.
2. GIF LZW decode against `Gif.Spec`, then the container decode. After this step, every GIF decodes.
3. GIF LZW encode and the round-trip theorem, then the container encode, animations included. After this step, the streams demo can write its output as a GIF. Dean's next demo renders terrain evolving under rainfall models as an animated GIF (2026-11-23, ADR 0055), so the encoder writes each frame as the rectangle that changed since the last one, and the round trip is proved over the composited frames that a viewer shows.
4. `Image.Gif.Quantise`.
5. `Compress.Huffman`, then inflate against `Inflate.Spec`, then zlib framing.
6. The case studies.

## Questions for Dean

1. **Should decoders allocate?** I recommend two-step decoding into a caller's buffer (section 4). That way the codecs work before `Pia.Mem` exists, and they run anywhere `Pia.Core` runs. The alternative is to take an allocator now, which means waiting for `Pia.Mem`.
2. **Is colour quantisation (RGB to a 256-colour palette) part of this work?** I recommend yes, proved safe but not proved good, because the streams demo renders in RGB. The alternative leaves GIF encoding to callers that already have indexed images.

## Consequences

- GIF and inflate join `Json` and `Utf8` as codecs proved against a written spec. The pattern (a spec module, code proved equal to it, and a round trip where the format is lossless) becomes the house style for formats.
- PNG and GeoTIFF need only their own containers on top of `Compress.Inflate`.
- The streams demo's GIF output no longer needs a C harness.
- Pixels from these decoders carry proved dimensions and ranges into the code that renders them.
- The proofs add to build time ([ADR 0032](0032-parallel-sliced-cached-proving.md)). The LZW and inflate decoders go into the proof benchmark corpus when they land.

## Prior art

| Source | What Pia takes |
| --- | --- |
| CompuServe GIF89a specification | the block grammar, the LZW variant, the interlace order and the extensions |
| RFC 1950 and RFC 1951 | the zlib and deflate formats, written as `Inflate.Spec` |
| giflib and zlib | the reference decoders for the differential tests |
| Wuffs (Google) | memory-safe, bounds-checked GIF and deflate decoders that do not allocate. They show that two-step decoding into a caller's buffer works at production speed. Pia adds functional specs and round trips. |
| EverParse (Project Everest) | parsers proved against a format grammar, with the grammar as the specification |
