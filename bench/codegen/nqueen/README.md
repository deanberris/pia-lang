# nqueen

plb2's nqueen ([third_party/benchmarks/plb2](../../../third_party/benchmarks/plb2), CC0): count the solutions of the n-queens problem with bit masks. The benchmark input is n = 15 (2,279,184 solutions), the instruction count runs n = 12 (14,200), and the test runs n = 10 (724).

| Program | Source |
| --- | --- |
| `nqueen_pia` | [nqueen.pia](nqueen.pia), called from [main.c](main.c) |
| `nqueen_control` | [control.c](control.c): the Pia program's recursion in C |
| `nqueen_c`, `nqueen_rust`, `nqueen_zig` | plb2's `nqueen.c`, `nqueen.rs` and `nqueen.zig` (patched to read n) |

## What the proof changed

- **Recursion instead of an explicit stack.** plb2 backtracks in a `for (k = 0; k >= 0;)` loop over arrays of masks. That loop ends because the stack's contents, read as a number in base n, grow at every step, and one `decreases` cannot say so. The port recurses over the row with `decreases n - k`, and `control.c` is the same recursion in C, so the gap splits into codegen (Pia against the control) and algorithm (the control against plb2's C).
- **A mask before the shift.** C lets bits fall off the top of `l << 1`. Pia proves that `<<` does not overflow, so the port clears bit 31 first.
- **A saturating count.** The verifier has no bound on the number of solutions, so the count adds with `+|`.

## First numbers

The prebuilt `piac` (`latest`, 2026-11-27) in a cloud container (Intel Xeon at 2.1 GHz), all at `-O3` for x86-64-v3, with clang 18.1.3, rustc 1.97.0 and Zig 0.14.1 (ADR 0075's prototype). 19 of 19 goals proved in 0.12 s.

| Program | Instructions, n = 12 | Wall time, n = 15 (s) |
| --- | ---: | ---: |
| plb2 C | 62.07 M | 3.35 – 3.57 |
| control (C) | 93.72 M | 3.76 – 3.91 |
| Pia | 93.80 M | 3.90 – 4.05 |

CI's numbers are in the `bazel test (Linux x86_64)` job's summary, from `tools/bench/codegen_bench.py`.
