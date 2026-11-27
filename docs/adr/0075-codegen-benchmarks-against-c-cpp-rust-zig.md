# 75. Codegen is benchmarked against C, C++, Rust and Zig on public problems, same algorithm first, counted in instructions on Linux and timed on Apple Silicon

Date: 2026-11-27

Status: Accepted (2026-11-27, with Dean's answers below)

## Context

Dean asked for public benchmarks of C, C++, Rust and Zig on common problems, so that Pia's generated code can be replicated against, or measured against, their best implementations: "a good representation of how well the code gen competes".

Pia already tracks two costs as benchmarks: proof cost (ADR 0032, `tools/bench/proof_bench.py`, three Linux shards that gate every PR) and build time. Nothing measures the code `piac` emits. The codegen tests (`tests/codegen`) check that compiled Pia gives the same answers as C, not how fast it is.

### The public suites, and what their licences allow

| Suite | Problems | Languages | Licence | What we may do |
| --- | --- | --- | --- | --- |
| [plb2](https://github.com/attractivechaos/plb2) (attractivechaos, 2024) | nqueen, matmul, sudoku, bedcov | 25, including C, Rust, Zig (nqueen, matmul only), Swift, Nim, D | CC0 1.0 | vendor freely |
| [Computer Language Benchmarks Game](https://benchmarksgame-team.pages.debian.net/benchmarksgame/) (CLBG) | n-body, spectral-norm, mandelbrot, fannkuch-redux, fasta, k-nucleotide, reverse-complement, binary-trees, pidigits, regex-redux | C, C++, Rust and about 25 others; no Zig | Revised BSD (3-clause); the names "The Computer Language Benchmarks Game" and "The Benchmarks Game" may not endorse a derived product | vendor with the notice kept; never say "Benchmarks Game" in a claim about Pia |
| [Programming Language Benchmarks](https://github.com/hanabi1224/Programming-Language-Benchmarks) (hanabi1224) | the CLBG problems plus nsieve, edigits, merkletrees, lru, json-serde, coro-prime-sieve | adds Zig, Odin, V, Nim and others to CLBG's set; runs in GitHub Actions | MIT | vendor with the notice; the source of most Zig versions |
| [kostya/benchmarks](https://github.com/kostya/benchmarks) | Brainfuck (bench.b, mandel.b), base64, JSON, matmul, primes, havlak | C, C++, Rust, Zig, D, Go and more | MIT | vendor with the notice |
| [niklas-heer/speed-comparison](https://github.com/niklas-heer/speed-comparison) | one problem (Leibniz π) | many | MIT | too small to be worth it |

None of the suites is GPL, so the licence rule (never use, bundle or depend on GPL code) is met by every reference program as written. Two programs need care anyway: CLBG's fastest **pidigits** programs link GMP, which is LGPL/GPL, and **regex-redux** links PCRE2 or a language's regex library, which measures the library, not the compiler. Neither is in the shortlist.

The suites answer different questions. plb2 is the closest to Dean's: every language runs **the same algorithm**, written by one author, with no library calls in the hot loop, so the difference is the compiler. CLBG is the opposite: each language's **fastest known program**, often hand-vectorised with intrinsics and multithreaded, so it measures how far an expert can push a language. hanabi1224 sits between them and is the only suite with Zig for most CLBG problems.

### What Pia can express today

Checked against `docs/status.md` on main (2026-11-27) and the `latest` prerelease of `piac`:

- **Built:** bounded integers with proved overflow, bit operators, fixed arrays and slices, records, variants, loops with invariants, recursion with `decreases`, saturating and wrapping arithmetic, `f32`/`f64` with `+ - * /` and strict IEEE codegen (no FMA contraction), C calls both ways, `spread` on the CPU (ADR 0060), `@lower` to `linalg` (ADR 0065).
- **Not built yet:** conversions between floats and integers (PR #452, open), a square root (there is no `sqrt` intrinsic, and libm is never trusted without a contract), `vec<T, k>` (M10), recursive types in codegen, a hash map, `Pia.Sys.Fs` (PR #444, open).

`piac` compiles at `CodeGenOptLevel::Default` and runs MLIR's optimising transformer at `-O<n>`; for x86_64 it requires x86-64-v3 (ADR 0049), so references must be built for the same CPU to be comparable.

### Prototype: plb2 nqueen

nqueen ported to Pia with the prebuilt `piac` (`latest`, 2026-11-27) and run in a cloud container (Intel Xeon at 2.1 GHz, 4 cores, clang 18.1.3, rustc 1.97.0, Zig 0.14.1), `n = 15`, all built for x86-64-v3 at `-O3` / `opt-level=3` / `ReleaseFast`:

```ocaml
let rec place (n : int{1..31}) (k : u32) (l : u32) (c : u32) (r : u32) : u64
  requires k < n
  decreases n - k
= let m : mutable u64 = 0 in
  let used : u32 = (l | c | r) in
  let nn : u32 = n in
  for i in 0 .. nn do
    let z : u32 = 1u32 << i in
    if used & z = 0 then
      (if k + 1 = n then m <- m +| 1
       else m <- m +| place n (k + 1) (((l | z) & 0x7FFF'FFFF) << 1) (c | z) ((r | z) >> 1))
    else ()
  done;
  m
```

All 19 goals proved in 0.12 s (14 by intervals, 5 by Z3).

| Program | Wall time, 5 runs (s) | Instructions at `n = 12` (cachegrind) |
| --- | --- | --- |
| plb2 C (explicit stack) | 3.35 – 3.57 | 62.07 M |
| plb2 Rust (explicit stack) | 3.58 – 3.68 | |
| plb2 Zig (explicit stack, `n` a constant) | 3.76 – 3.98 | |
| C, the Pia program's recursion transcribed | 3.76 – 3.91 | 93.72 M |
| **Pia** | 3.90 – 4.05 | **93.80 M** |

Three findings:

1. **Against the same algorithm in C, Pia's code is within 0.1% in instructions** (93.80 M against 93.72 M) and about 3% in wall time, which is inside this container's noise. The assembly of `place` is the loop clang emits, with `bt` for the test and `shlx` for the shift.
2. **Against plb2's C, Pia is about 14% slower, and the cause is the algorithm, not codegen.** plb2 backtracks with an explicit stack in a `for (k = 0; k >= 0;)` loop. That loop's termination needs a lexicographic measure over the stack, which Pia cannot state as one `decreases` today, so the port recurses instead. This is the most useful kind of result the benchmark can give: it names a language gap (a lexicographic or well-founded `decreases`), not a codegen one.
3. **Proof shapes the code, a little.** C lets bits fall off the top of `l << 1`; Pia proves `<<` does not overflow, so the port masks first (one `and` a call), and the count uses `+|` because the number of solutions has no bound the verifier can see. Neither shows up in the instruction count. Each such change is recorded with the port.

Wall times in the cloud vary by 5% between runs; instruction counts do not vary at all. That decides the metric (section 4).

## Decision

### 1. Two lanes: same algorithm (the headline) and best known (the stretch)

- **Same algorithm.** The Pia port and every reference run one algorithm, as plb2 requires. This is the codegen comparison Dean asked for, and the number we publish first. When a proof forces the Pia port away from the reference's shape (as nqueen's recursion did), the benchmark also carries a C **control**: the Pia program transcribed back into C, so that "codegen" and "algorithm" separate.
- **Best known.** The fastest single-threaded and multithreaded C, C++, Rust and Zig programs from CLBG and hanabi1224, against the best Pia program we can write, with `spread` for parallelism. It is reported, never headlined, because it measures intrinsics and experts as much as compilers.

### 2. The shortlist, by what Pia needs

**Wave 1: buildable now** (integers, buffers, recursion, floats without conversions):

| Problem | Source | References (same algorithm) | Best known | Exercises |
| --- | --- | --- | --- | --- |
| nqueen | plb2 | C, Rust, Zig (plb2) | same | bit operators, recursion |
| sudoku (kudoku) | plb2 | C, Rust (plb2); C++ port of the C | same | small fixed arrays, branches |
| fannkuch-redux | CLBG, hanabi1224 | single-threaded C and Rust (CLBG); C++ `1-im.cpp`, Rust `1.rs`, Zig `1.zig` (hanabi1224) | the fastest multithreaded C, C++ and Rust (CLBG), Rust `1-m.rs`, Zig `2-m.zig` (hanabi1224) | permutations in fixed arrays, `spread` |
| matmul, 1500 × 1500 `f64` | plb2 | C, Rust, Zig (plb2) | the same through `@lower` to `linalg` | float loops, vectorisation, `@lower` |
| nsieve | hanabi1224 | C `1.c`, C++ `1.cpp`, Rust `1.rs`, Zig `1.zig` (hanabi1224) | same | a byte buffer, strided loops |
| Brainfuck (bench.b, mandel.b) | kostya | C, C++, Rust, Zig (kostya) | same | an interpreter loop, variants, a jump table |
| base64 encode and decode | kostya | C, Rust, Zig (kostya) | C with aklomp's SIMD codec (BSD 2-clause), reported only | byte tables, slices |

matmul's input is filled by the C driver until float conversions land, so the kernel needs none.

**Wave 2: after a feature lands:**

| Problem | Waits on |
| --- | --- |
| mandelbrot, spectral-norm | float to integer conversions (PR #452) |
| n-body | a proved `sqrt` (an intrinsic with ADR 0038's rounding contract) |
| bedcov | allocation and sort from the standard library on a 1 M-element array (`Pia.Mem`, `sort`) |
| fasta, reverse-complement | `Pia.Sys.Fs` (PR #444) for output, or a C driver that writes the buffer |
| mandelbrot, spectral-norm, fannkuch-redux with `spread` | wave 1, then the best-known lane |

**Out of scope:** binary-trees and merkletrees (recursive types are not compiled, and they measure allocators), pidigits (GMP), regex-redux (a regex library), k-nucleotide and lru (a hash map, the standard library's not the compiler's), JSON (a library comparison; `Pia.Text.Json` can join later as a library benchmark).

C++ has its own entry only where CLBG's best C++ differs from its C (fannkuch-redux, Brainfuck); elsewhere a C++ build of the C program measures the same compiler and says nothing new.

### 3. Layout and Bazel targets

- `bench/codegen/<problem>/` holds the Pia port (`<problem>.pia`), its C driver (`main.c`, which parses arguments and prints the result, so every program has the same `argv` and output), the C control when there is one, and a `README.md` with the source, the input size, and every change the proof forced.
- `third_party/benchmarks/{plb2,clbg,hanabi1224,kostya}/` holds the reference programs, unmodified except for a header that names the origin, each directory with the suite's `LICENSE` (the BSD and MIT notices must be kept). A reference that must change (Zig 0.11 syntax, a constant `n` turned into an argument so the compiler cannot specialise on it) gets a patch file beside it, not an edit.
- Bazel builds everything with one CPU target: C and C++ with the repository's clang toolchain; Rust with `rules_rust`; Zig with `rules_zig`. Both are Apache 2.0 or MIT and come from the Bazel Central Registry. Flags are fixed per lane and listed in one file, `bench/codegen/flags.bzl`: `-O3 -march=x86-64-v3` or `-mcpu=apple-m1`, `-ffp-contract=off` for C and C++ (Pia does not contract FMAs unless licensed, and clang does by default), Rust `opt-level=3 -C target-cpu=…`, Zig `ReleaseFast -mcpu=…`; no LTO and no PGO, since `piac` has neither.
- `//bench/codegen:<problem>_test` runs every build of a problem on a small input and checks that they print the same answer. These run in `bazel test //...`, so a wrong Pia program fails CI like any other test.
- `tools/bench/codegen_bench.py --bazel-bin=…` runs every program on its benchmark input and writes one JSON file: per program, the instruction count, the wall times, and the ratios to C.

### 4. What is measured, where, and what gates

- **Instructions on Linux CI** (cachegrind, `--cache-sim=no`): deterministic, so they can be compared across commits like Z3's rlimit in the proof benchmark. Inputs are scaled down so that each program runs in under a second under cachegrind. They are reported against a baseline, `bench/codegen/baseline.json`.
- **Wall time on Apple Silicon**: the median of 10 runs after one warm-up, in the nightly macOS job, with the machine's chip in the report. This is the number to publish for the 0.1.0 target (Dean's M3).
- **Wall time on Linux**: reported, never compared across runs, because shared runners vary.
- **No gate** (CLAUDE.md: only the proof shards gate besides build and tests). The report lands in the job summary and as an artifact. Gating on a Pia/C instruction ratio is an open question below.

### 5. Reports

Each run's report follows the project's report format: per problem, the input, Pia's instructions and wall time, each reference's, the ratio to the same-algorithm C, the proof cost and goal count of the Pia port, and for each port the list of changes the proof forced. The summary line is the geometric mean of Pia/C over wave 1. Any claim made from it names the suite (plb2, CLBG, hanabi1224, kostya) as the source of the problems and reference programs, and never uses CLBG's names to endorse Pia.

### 6. Steps

1. This ADR.
2. `bench/codegen/nqueen` and the harness: Bazel targets for C, Rust and Zig through `rules_rust` and `rules_zig`, the output test, `codegen_bench.py`, and a `codegen benchmark (Linux)` report job in CI.
3. The rest of wave 1, one problem a PR, each with its proof stats and first numbers.
4. The nightly macOS wall-time run, and the Linux instruction gate once wave 1 is complete.
5. Wave 2 as its features land, and the multithreaded best-known programs against `spread`; the hand-vectorised ones after M10.

## Consequences

- Each port is also a test of the language on code it did not grow up with. Gaps found this way (nqueen's lexicographic `decreases`) become issues, and the README of each port lists what the proof cost in code shape.
- CI gains a toolchain for Rust and one for Zig, both from the registry; the first cold build downloads them once. Neither enters `piac` or its release.
- Vendored programs carry BSD and MIT notices, which `third_party/benchmarks` keeps beside them. Nothing in it is linked into Pia.
- A Pia/C ratio becomes a number Pia is judged by. The same-algorithm lane keeps that number about codegen; the best-known lane keeps us honest about what experts get from intrinsics, until `vec<T, k>` (M10) gives Pia its own.

## Open questions

1. Should a codegen regression gate PRs, on the instruction count against the baseline, as the proof benchmark does? Proposed: report only until wave 1 is complete, then gate at +5% instructions on Linux.
2. Where should Apple Silicon wall times come from: the nightly macOS CI job (an M1 VM, shared), or occasional runs on the iMac (Dean's M3, the 0.1.0 target)? Proposed: CI nightly for tracking, the iMac only for a published comparison, by hand and with Dean's say-so.
3. Should the best-known lane be built at all before `vec<T, k>`? Proposed: yes for the multithreaded programs with `spread`, no for the hand-vectorised ones until M10.

## Answers to the open questions

Accepted by Dean on 2026-11-27 ("0075 LGTM").

Dean, 2026-11-27:

1. **Gating:** report only until wave 1 is complete, then gate PRs at +5% instructions on Linux against `bench/codegen/baseline.json`.
2. **Apple Silicon timings:** the nightly macOS CI job tracks them. The iMac (Dean's M3) runs only a published comparison, by hand and with Dean's say-so.
3. **Best-known lane before `vec<T, k>`:** build the multithreaded programs now, against `spread`. Leave the hand-vectorised references out until M10.
