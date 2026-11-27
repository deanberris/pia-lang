# matmul

plb2's matmul ([third_party/benchmarks/plb2](../../../third_party/benchmarks/plb2), CC0): the product of two n × n `f64` matrices, `a[i][j] = (i - j)(i + j) / n²`, in the i, k, j loop order, printing the middle element of the result with six decimals. The benchmark input is n = 1500, the instruction count runs n = 300 (-28.500833), and the test runs n = 7 (-0.501458).

| Program | Source |
| --- | --- |
| `matmul_pia` | [matmul.pia](matmul.pia), called from [main.c](main.c) |
| `matmul_c`, `matmul_rust`, `matmul_zig` | plb2's `matmul.c`, `matmul.rs` and `matmul.zig` (Rust and Zig patched to read n and print as C does) |

The port runs the same algorithm, so there is no control. Every program is built without floating-point contraction or reassociation, so no FMA or reordering changes a result, and all of them print the same digits.

## What the proof changed

- **Flat matrices.** plb2's C keeps an array of row pointers into one `calloc`. The port takes three flat row-major slices, and `c.[i * n + j]` is the same element. Each index is proved in bounds from `len a = n * n` and `n <= 46'340` (so `n * n` fits); Z3's int-blasting proves the nonlinear goals.
- **The driver generates the input.** `main.c` runs `mat_gen` as plb2's C does and lends the three buffers to `mm_mul`, so only the multiply is Pia.
- **`aik` named once.** The port reads `a.[i * n + k]` once per k, as plb2's Rust and Zig do (`aik`).

14 of 14 goals prove with the prebuilt `piac`, with `@allow(range_requires)` on `mm_mul` so that n stays a `size_t` in C.

## First numbers

The prebuilt `piac` (`latest`, 2026-11-27) in a cloud container (Intel Xeon at 2.1 GHz), all at `-O3` for x86-64-v3, with clang 18.1.3, rustc 1.97.0 and Zig 0.15.2. Instructions at n = 300.

| Program | Instructions | vs C |
| --- | ---: | ---: |
| pia | 29,192,701 | 0.888 |
| c | 32,883,639 | 1.000 |
| rust | 33,299,340 | 1.013 |
| zig | 30,524,525 | 0.928 |

The best-known lane (ADR 0075) will run the same product through `@lower` to `linalg.matmul` with a `@schedule`.
