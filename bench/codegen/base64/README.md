# base64

kostya's base64 ([third_party/benchmarks/kostya](../../../third_party/benchmarks/kostya), MIT), its C `test-nolib.c`: check two fixtures, then encode 131,072 `a`s and decode the result, `tries` times each, and print the total sizes. The benchmark input is 8192 tries, the instruction count runs 64, and the test runs 2.

| Program | Source |
| --- | --- |
| `base64_pia` | [base64.pia](base64.pia), called from [main.c](main.c) |
| `base64_control` | [control.c](control.c): main.c's driver with test-nolib.c's `encode` and `decode` |
| `base64_c` | kostya's `test-nolib.c`, patched to drop its harness socket and timings and to read the number of tries |

kostya's Rust and Zig programs call library codecs (the `base64` crate and `std.base64`), not test-nolib.c's algorithm, so they belong in the best-known lane rather than here.

## Why there is a control

The algorithm is test-nolib.c's, but its `main` and its codec are in one file. clang sees that nothing reads the encoded output, drops the stores and most of the encode loop, and counts 1.2 million instructions for 20 rounds of encoding where a codec it cannot see into takes 24 million. The Pia functions are in their own object, so the fair comparison is with the same C codec behind the same entry points, marked `noinline`: `control.c`.

## What the proof changed

- **Indices instead of pointers.** `decode`'s `ends = str + size - 4` points before the input when it is shorter than 4 bytes. The port keeps `p + 4 <= size` instead.
- **The output size, stated.** `b64_encode` requires `3 * len dst >= 4 * len src + 15` and `b64_decode` requires `4 * len dst >= 3 * len src + 16`, which `encode_size` and `decode_size` meet. Loop invariants (`3 * o = 4 * p`, `4 * o <= 3 * p`) prove every write in bounds.
- **An early exit as a flag.** C returns `false` from inside the loop on a bad byte; the port sets `bad`, moves `p` to the end so the loop stops, and returns -1.
- **Shifts in `u32`.** `a << 2` on a byte can overflow, so the decoded values are widened to `u32` and masked back to a byte.

207 of 207 goals prove with the prebuilt `piac`, in about 52 s with `--jobs=4`. The slowest goals (up to 7 s) are index bounds in the decode loop.

## First numbers

The prebuilt `piac` (`latest`, 2026-11-27) in a cloud container (Intel Xeon at 2.1 GHz), all at `-O3` for x86-64-v3 with clang 18.1.3. 20 tries:

| Program | Encode | Decode |
| --- | ---: | ---: |
| pia | 25,690,765 | 42,206,428 |
| control | 23,914,554 | 38,536,184 |

Pia's codec takes 7% more instructions than the same C to encode and 10% more to decode. Issue to follow.
