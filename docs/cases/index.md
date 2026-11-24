# Famous bugs, proved away

Some of the most expensive bugs in software history were not subtle. A
length was trusted, an index ran one past the end, a sum overflowed, a
conversion lost its top bits. Code review, testing and fuzzing missed each
of them for months or years, because they only show up on inputs nobody
tried.

Each page in this section takes one such bug, recreates its essence in Pia,
and shows `piac --verify` refusing to compile it, with the counterexample
the solver found: an input that triggers the bug. Then it shows the fix,
proved. Every example on these pages is run by the test suite, so the
failures and proofs you read are the compiler's real output.

The point is not that these programs were written carelessly. It is that a
compiler which proves bounds, overflow and contracts before it generates
code turns each of these from a production incident into a compile error.

## The cases

| Bug | Year | What went wrong | Pia catches it with | |
| --- | --- | --- | --- | --- |
| [Heartbleed](heartbleed.pia.md) (OpenSSL, CVE-2014-0160) | 2014 | a length field from the network was trusted, and `memcpy` read past the record | slice bounds | done |
| [Binary search midpoint](binary-search.pia.md) (Java, C) | 2006 | `(low + high) / 2` overflows on large arrays | overflow goals | done |
| [Cloudbleed](cloudbleed.pia.md) (Cloudflare) | 2017 | an HTML parser's end-of-buffer test used `==`, and a pointer stepped past the end | bounds and loop invariants | done |
| [CrowdStrike Channel File 291](crowdstrike.pia.md) | 2024 | a template defined 21 input fields, the sensor supplied 20, and the 21st was read out of bounds | bounds and preconditions | done |
| [Rust `str::repeat`](rust-str-repeat.pia.md) (CVE-2018-1000810) | 2018 | a wrapping multiplication sized a buffer that `unsafe` code then overran | overflow goals and postconditions | done |
| [Rust `VecDeque`](rust-vecdeque.pia.md) (CVE-2018-1000657) | 2017 | `reserve` compared against the wrong "capacity", and `unsafe` code moved elements past the end | preconditions | done |
| [libwebp Huffman tables](libwebp.pia.md) (CVE-2023-4863) | 2023 | tables sized for valid codes were filled before the code was checked | bounds and loop invariants | done |
| [Bun `readFile` on Windows](bun-readfile.pia.md) (Zig) | 2026 | a byte count past 2 GB was truncated to a C `int`, and the negative result was cast to `usize` | narrowing goals and postconditions | done |
| [zlib gzip extra field](zlib-gzip-extra.pia.md) (CVE-2022-37434) | 2022 | a copy into the caller's buffer was clamped by `extra_max - len`, which wrapped once the buffer was full | overflow goals and postconditions | done |
| [giflib background colour](giflib-background.pia.md) (CVE-2016-3977) | 2016 | the background colour's index from the file was looked up in a colour table it did not fit | bounds and preconditions | done |
| Ariane 5 flight 501 | 1996 | a 64-bit float converted to a 16-bit integer overflowed | narrowing goals | needs floats ([M11](https://github.com/deanberris/pia-lang/issues/12)) |
| Therac-25 | 1985 to 1987 | a race between operator input and the treatment setup | race proofs | needs concurrency ([M12](https://github.com/deanberris/pia-lang/issues/13)) |

The Rust and Zig cases matter because those languages are memory-safe by
default. Their bugs live where the guarantees stop: in `unsafe` blocks, and
in checks that release builds turn off. Pia has no unchecked mode for
arithmetic or indexing; every goal is proved or the program does not
compile ([ADR 0004](../adr/0004-strongest-guarantee-by-default.md)).

Each page cites its primary sources: the advisory, the fix and the code
before it.
