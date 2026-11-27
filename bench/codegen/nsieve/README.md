# nsieve

hanabi1224's nsieve ([third_party/benchmarks/hanabi1224](../../../third_party/benchmarks/hanabi1224), MIT), from the old shootout's C entry: three sieves of Eratosthenes over 10000 << (n - i) one-byte flags, i = 0, 1, 2, each printing the number of primes below its size. The benchmark input is n = 12 (40,960,000 flags in the largest sieve), the instruction count runs n = 8, and the test runs n = 2.

| Program | Source |
| --- | --- |
| `nsieve_pia` | [nsieve.pia](nsieve.pia), called from [main.c](main.c) |
| `nsieve_c`, `nsieve_cpp`, `nsieve_rust`, `nsieve_zig` | hanabi1224's `1.c`, `1.cpp`, `1.rs` and `1.zig` (patched for Zig 0.15) |

The port runs 1.c's algorithm, so there is no control: Pia is compared with 1.c directly. The C++ reference keeps one bit per flag (`std::vector<bool>`), the others one byte.

## What the proof changed

- **C owns the buffer.** 1.c `malloc`s the flags and `free`s them. The driver does the same and lends the buffer to `ns_count`, which sets and sieves it. Allocation in Pia goes through an explicit allocator (ADR 0026), which is outside what this benchmark measures.
- **A bound on the size.** `j <- j + i` must not overflow, so `ns_count` requires at most 10⁹ flags; the measure `m + i - j` proves the inner loop ends.
- **A saturating count.** The count adds with `+|`, since the verifier has no bound on the number of primes found.

9 of 9 goals prove with the prebuilt `piac`.

## First numbers

The prebuilt `piac` (`latest`, 2026-11-27) in a cloud container (Intel Xeon at 2.1 GHz), all at `-O3` for x86-64-v3, with clang 18.1.3, rustc 1.97.0 and Zig 0.15.2. Instructions at n = 8, wall time at n = 12 (median of 2 runs).

| Program | Instructions | vs C | Wall time (s) |
| --- | ---: | ---: | ---: |
| pia | 75,546,841 | 0.879 | 0.560 |
| c | 85,929,341 | 1.000 | 0.564 |
| cpp | 270,206,005 | 3.145 | 0.515 |
| rust | 134,534,996 | 1.566 | 0.600 |
| zig | 73,315,478 | 0.853 | 0.602 |

The sieve is bound by memory, so the wall times are close even where the instruction counts are not.
