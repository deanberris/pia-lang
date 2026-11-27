# The standard library today

This page lists every module of Pia's standard library as it is built, in [`lib/Pia`](../lib/Pia/). Each module is written in Pia and proved: what its contracts promise holds for every input, so a caller proves its own code from those contracts alone. [The standard library and its core](stdlib.md) is the design the library follows, and [The C++23 standard library in Pia](cpp-std.md) maps each C++ header to the module that covers it.

A program uses a module through an interface it names, `import Pia.Core.Order.Compare` ([getting started](getting-started.md), [ADR 0039](adr/0039-module-and-interface-syntax.md)). In Bazel, each module is a `pia_library` target in [`lib/Pia/BUILD.bazel`](../lib/Pia/BUILD.bazel).

`tools/docs/check.py` fails a pull request that adds a module without a line here.

## Core

The vocabulary types, concepts and algorithms that everything else is built from ([ADR 0040](adr/0040-cpp23-standard-library-in-pia.md)).

| Module | What it gives |
| --- | --- |
| [`Pia.Core.Order`](../lib/Pia/Core/Order.pia) | The concepts `Eq` and `Ord` with their laws, and `min`, `max`, `clamp`, `swap`, `exchange` and `lexicographical_compare` over them: C++'s `<compare>` and `<concepts>` |
| [`Pia.Core.Option`](../lib/Pia/Core/Option.pia) | `option t`, `None` or `Some` of a `t`, and the functions over it: C++'s `<optional>` |
| [`Pia.Core.Result`](../lib/Pia/Core/Result.pia) | What C++23's `std::expected` has on top of the language's own `result t e` |
| [`Pia.Core.Int`](../lib/Pia/Core/Int.pia) | `gcd`, `midpoint`, `abs`, `div` and saturating arithmetic for `u8` to `i64`, with C++'s undefined cases ruled out by preconditions |
| [`Pia.Core.Bit`](../lib/Pia/Core/Bit.pia) | The rest of C++23's `<bit>`, beside the builtins `clz`, `ctz`, `popcount`, `bswap`, `rotl` and `rotr` |
| [`Pia.Core.Hash`](../lib/Pia/Core/Hash.pia) | The concept `Hash`, an `Eq` whose `hash` agrees with it, its instances, and `@derive(hash)` |
| [`Pia.Core.Ratio`](../lib/Pia/Core/Ratio.pia) | C++'s `<ratio>`, as metaprograms over exact integers |
| [`Pia.Core.Ascii`](../lib/Pia/Core/Ascii.pia) | C++'s `<cctype>` for ASCII bytes, each classifier exact |
| [`Pia.Core.Utf8`](../lib/Pia/Core/Utf8.pia) | UTF-8 decoding, encoding and validity, with both round trips proved |
| [`Pia.Core.Charconv`](../lib/Pia/Core/Charconv.pia) | `from_chars` and `to_chars` for integers in bases 2 to 36, with the round trip proved |
| [`Pia.Core.Digits`](../lib/Pia/Core/Digits.pia) | The facts about digit strings that formatting and parsing proofs need, as lemmas |
| [`Pia.Fn`](../lib/Pia/Fn.pia) | Laws of function arguments, such as `strict_weak_order` and `sorted`, that a higher-order function states as preconditions ([ADR 0044](adr/0044-function-values-and-lambdas.md)) |
| [`Pia.Time`](../lib/Pia/Time.pia) | C++'s `<chrono>` durations, as types a metaprogram makes over a ratio |

### Algorithms

C++'s `<algorithm>` and `<numeric>` on slices. Each takes its comparison or operation as a function value and is proved once, for every element type and every such function ([ADR 0043](adr/0043-generic-definitions-proved-once.md)).

| Module | What it gives |
| --- | --- |
| [`Pia.Core.Algo.Search`](../lib/Pia/Core/Algo/Search.pia) | `find`, `count`, `contains`, `equal`, `mismatch`, `search`, `min_element`, `is_sorted` and the rest of the non-modifying algorithms |
| [`Pia.Core.Algo.BinarySearch`](../lib/Pia/Core/Algo/BinarySearch.pia) | `lower_bound`, `upper_bound`, `equal_range` and `binary_search` |
| [`Pia.Core.Algo.Modify`](../lib/Pia/Core/Algo/Modify.pia) | `fill`, `copy`, `copy_backward`, `swap_ranges`, `reverse`, `replace`, `shift_left` and `shift_right` |
| [`Pia.Core.Algo.Remove`](../lib/Pia/Core/Algo/Remove.pia) | `remove`, whose contract says where each kept element goes |
| [`Pia.Core.Algo.Numeric`](../lib/Pia/Core/Algo/Numeric.pia) | `iota`, `accumulate`, `reduce`, `inner_product`, the scans and `adjacent_difference` |
| [`Pia.Core.Algo.Permutation`](../lib/Pia/Core/Algo/Permutation.pia) | The multiset spec functions that sorting states its results with |
| [`Pia.Core.Algo.Sort`](../lib/Pia/Core/Algo/Sort.pia) | `insertion_sort`: sorted, and a permutation of its input |
| [`Pia.Core.Algo.Heap`](../lib/Pia/Core/Algo/Heap.pia) | The heap operations, and `sort` as a heap sort |
| [`Pia.Core.Algo.PartialSort`](../lib/Pia/Core/Algo/PartialSort.pia) | `partial_sort` and `nth_element` |
| [`Pia.Core.Algo.Partition`](../lib/Pia/Core/Algo/Partition.pia) | `is_partitioned`, `partition_point` and `partition` |
| [`Pia.Core.Algo.Merge`](../lib/Pia/Core/Algo/Merge.pia) | `merge` of two sorted ranges |
| [`Pia.Core.Algo.Set`](../lib/Pia/Core/Algo/Set.pia) | `includes`, `set_intersection` and `set_difference` on sorted ranges |
| [`Pia.Core.Algo.SetUnion`](../lib/Pia/Core/Algo/SetUnion.pia) | `set_union` |
| [`Pia.Core.Algo.SetSymmetric`](../lib/Pia/Core/Algo/SetSymmetric.pia) | `set_symmetric_difference` |

## Memory

Allocators, boxes and vectors, with no garbage collector and every allocation fallible ([ADR 0026](adr/0026-memory-manager.md), [ADR 0041](adr/0041-allocator-semantics-as-a-theory.md), [ADR 0042](adr/0042-lifetimes-liveness-and-escape-analysis.md)).

| Module | What it gives |
| --- | --- |
| [`Pia.Mem.Alloc`](../lib/Pia/Mem/Alloc.pia) | `oom`, the one way an allocation fails; the concept `Allocator a t r`, an allocator of `t`s lent from the region `r`; and the bump allocator `bump t r` |
| [`Pia.Mem.Box`](../lib/Pia/Mem/Box.pia) | `box t r`, an owning box of one `t`, whose fullness is spec-only state, so a use after `release` is a failed goal; its type parameter is `@unsized`, so it may be a concept, and `box Shape` holds any type that meets `Shape` ([ADR 0046](adr/0046-box-over-a-type-or-a-concept.md)) |
| [`Pia.Mem.Vec`](../lib/Pia/Mem/Vec.pia) | `vec t a r`, a growable vector that holds its allocator, C++'s `std::vector` with every growth fallible |

## Text and data formats

| Module | What it gives |
| --- | --- |
| [`Pia.Text.Json.Spec`](../lib/Pia/Text/Json/Spec.pia) | RFC 8259's token grammar, as spec functions over bytes, which the rest of the JSON modules are proved against ([ADR 0045](adr/0045-json-derived-codecs-and-conforming-dom.md)) |
| [`Pia.Text.Json.Lex`](../lib/Pia/Text/Json/Lex.pia) | A JSON tokenizer over a byte slice that never reads outside its input and always ends |
| [`Pia.Text.Json.Write`](../lib/Pia/Text/Json/Write.pia) | A JSON writer into a caller's buffer, whose room is its precondition, so nothing fails at run time |
| [`Pia.Text.Json.Read`](../lib/Pia/Text/Json/Read.pia) | The token readers that derived decoders are built from |
| [`Pia.Text.Json.Derive`](../lib/Pia/Text/Json/Derive.pia) | `@derive(json)`: the metaprograms that write a JSON codec for a type |
| [`Pia.Text.Json.Dom`](../lib/Pia/Text/Json/Dom.pia) | A JSON document as a recursive sum type over spans of its input, copying no text ([ADR 0047](adr/0047-recursive-sum-types-and-shared-references.md)) |
| [`Pia.Format.Safetensors`](../lib/Pia/Format/Safetensors.pia) | The safetensors container that model weights come in, read from a file's bytes and proved total and safe on every input ([ADR 0067](adr/0067-release-0-1-0-a-proved-small-llm.md)) |
| [`Pia.Llm.Tokenizer`](../lib/Pia/Llm/Tokenizer.pia) | llama2.c's byte-pair tokenizer, read from its `tokenizer.bin` and proved ([ADR 0067](adr/0067-release-0-1-0-a-proved-small-llm.md)) |

## Compression and images

The codecs are proved total and safe on every input, and allocate nothing: the caller lends every buffer ([ADR 0054](adr/0054-proved-gif-and-inflate-codecs.md)).

| Module | What it gives |
| --- | --- |
| [`Pia.Image.Bits`](../lib/Pia/Image/Bits.pia) | LSB-first bit readers and writers over a byte slice, as GIF and deflate read them |
| [`Pia.Image.Raster`](../lib/Pia/Image/Raster.pia) | An image's dimensions and the indices of its samples |
| [`Pia.Image.Gif.Spec`](../lib/Pia/Image/Gif/Spec.pia) | What a GIF means, as spec functions: the LZW dictionary of GIF89a |
| [`Pia.Image.Gif.Lzw`](../lib/Pia/Image/Gif/Lzw.pia) | GIF's LZW decoder, proved against the spec's dictionary |
| [`Pia.Image.Gif.Ref`](../lib/Pia/Image/Gif/Ref.pia) | GIF89a's LZW reading of a whole code stream, as a trace spec (`lzw_ok`), which `Lzw`'s decoder is proved against |
| [`Pia.Image.Gif.LzwEncode`](../lib/Pia/Image/Gif/LzwEncode.pia) | GIF's LZW encoder |
| [`Pia.Image.Gif.Decode`](../lib/Pia/Image/Gif/Decode.pia) | The GIF container, proved to accept exactly what the spec's block grammar accepts |
| [`Pia.Image.Gif.Encode`](../lib/Pia/Image/Gif/Encode.pia) | Animated GIF encoding |
| [`Pia.Image.Gif.Quantise`](../lib/Pia/Image/Gif/Quantise.pia) | An RGB raster to a palette of at most 256 colours and an index raster |
| [`Pia.Compress.Huffman`](../lib/Pia/Compress/Huffman.pia) | Canonical Huffman codes as deflate defines them, with the completeness check and decoding |
| [`Pia.Compress.Inflate.Spec`](../lib/Pia/Compress/Inflate/Spec.pia) | The parts of a deflate block, as spec functions |
| [`Pia.Compress.Inflate`](../lib/Pia/Compress/Inflate.pia) | Deflate decoding into a caller's buffer, after zlib's `puff.c` |
| [`Pia.Compress.Zlib`](../lib/Pia/Compress/Zlib.pia) | The zlib format, with `adler32` proved equal to RFC 1950's definition |

## The system and the GPU

| Module | What it gives |
| --- | --- |
| [`Pia.Sys.Posix`](../lib/Pia/Sys/Posix.pia) | The contracts of the POSIX functions Pia calls, as one interface that every target meets ([ADR 0057](adr/0057-posix-module-per-target-behind-one-interface.md)) |
| [`Pia.Sys.Fs`](../lib/Pia/Sys/Fs.pia) | Files over `Pia.Sys.Posix`, written once for both targets: a `@linear` `file` that must be closed exactly once, `open_read`, `create`, `read_some`, `write_all` and `close`, each failing with a decoded `errno` |
| [`Pia.Sys.Gen.arm64_macos`](../lib/Pia/Sys/Gen/arm64_macos.pia) | The bindings for arm64 macOS, generated from the system headers by `tools/bindings/gen.py`, which CI checks are current |
| [`Pia.Sys.Gen.x86_64_linux`](../lib/Pia/Sys/Gen/x86_64_linux.pia) | The same for x86_64 Linux |
| [`Pia.Gpu`](../lib/Pia/Gpu.pia) | Devices, buffers and kernels on the GPU through a Metal host shim, which `--trust-report` lists as trusted ([ADR 0068](adr/0068-gpu-compute-through-spirv-and-metal.md)) |

A spread marked `@place(gpu)` runs on the GPU without calling `Pia.Gpu` itself: [the GPU demo](placed.pia.md) shows one.
