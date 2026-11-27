---
name: piac-verify
description: Prove Pia files with `piac --verify`, read its goal report and counterexamples, accept unproved goals narrowly, and compile only proved code. Use when checking or building a .pia or .pia.md file from the command line or in CI.
---

# Proving files with `piac`

`piac` is the Pia compiler. It proves every *goal* (proof obligation) in a file before it generates code, and generates nothing if a goal fails. `--verify` stops after the proof and prints a report.

```sh
bazel build //tools/piac
piac=bazel-bin/tools/piac/piac
```

## The report

<!-- example: limits.pia -->
<!-- expect: fail -->
```ocaml
let inc (x : u8) : u8
  requires x < 255
  ensures result = x + 1
= x + 1

let twice (x : u8) : u8 = inc (inc x)
```

```console
$ piac --verify limits.pia
limits.pia:4:5: proved: '+' does not overflow u8 [smt]
limits.pia:3:3: proved: the postcondition holds [smt]
limits.pia:6:32: failed: the precondition of 'inc' holds
  counterexample: x = 255
limits.pia:6:27: failed: the precondition of 'inc' holds
  counterexample: x = 254
2 proved, 2 failed, 0 skipped
limits.pia:2:3: warning: this precondition only bounds 'x' by constants; say it in the type instead, (x : int{0..254}), so the fact travels with the value and intervals can use it [range_requires]
    requires x < 255
    ^
  fix: Move the bound into the type: (x : int{0..254})
```

- One line per goal: `file:line:col: status: claim [method]`. The method is `intervals` (range analysis, cheap) or `smt` (Z3).
- **proved** holds for every input. **failed** has an input that breaks it, the counterexample, when Z3 found one. **skipped** means this verifier cannot decide it yet, for example a `while` loop or recursion with no `decreases`.
- `warning: ... [name]` lines on stderr are lints (docs/idioms.md, ADR 0037): opinions about a better way to say the same thing, never errors. `@allow(name)` on a function's return annotation, or `--no-lint=name`, turns one off.
- The last line counts them. The exit status is 0 if nothing failed and nothing was skipped without being accepted, 1 otherwise, and 2 for a usage error.

## Reading a counterexample

A counterexample is one assignment to the function's inputs that makes the claim false:

- parameters by name, `len xs` for a slice's length, `p.r` for a record field;
- `result` for the exact value an overflowing operation would have produced;
- `index` and `length` for an out-of-bounds index;
- `amount` for a shift.

Z3 returns whichever model it finds first, so the values often look arbitrary or huge. Do not read meaning into the particular numbers. Ask instead what *class* of input they belong to: here `x = 254` passes the inner call, which returns 255, which breaks the outer call. The values can also differ between Z3 versions, so never assert on them in your own tests unless the docs tests pin the same Z3.

Each goal is proved from the function's own contracts and the callee's *contracts*, never the callee's body. A failure at a call (`the precondition of 'inc' holds`) is fixed either at the caller (a `requires` on `twice`, or a guard) or by weakening the callee's `requires`.

## Accepting what cannot be proved yet

A failed goal can never be accepted. A skipped one can, narrowly:

| Flag | Accepts |
| --- | --- |
| `--allow-unproved=drain` | every unproved goal in function `drain` |
| `--allow-unproved=f.pia:30` | the unproved goals on line 30 |
| `--allow-unproved=f.pia:30:37` | the one at line 30, column 37 |

The flag repeats. Accepted goals still print as warnings, and a flag that accepts nothing is reported, so stale ones show up. Prefer adding a `decreases` measure to accepting a termination goal.

## Other modes

| Command | What it does |
| --- | --- |
| `piac --verify f.pia` | prove and report |
| `piac --emit=obj -o f.o f.pia` | prove, then compile to an arm64 object file |
| `piac --emit=asm f.pia` | prove, then print assembly (also `--emit=llvm`, `--emit=core`) |
| `piac --emit=mlir f.pia` | print the Pia dialects; with `--verify`, proved ops are marked `pia.proved` |
| `piac --dump-smt f.pia` | prove, printing each SMT query sent to Z3 |
| `piac --dump-ast f.pia`, `--dump-expanded` | the syntax tree, before or after metaprograms run |
| `piac --check f.pia` | parse only |
| `piac --emit=lean f.pia -o Statements.lean` | the statements of the lemmas proved in Lean (`= by lean T`), as Lean 4; `--verify --lean-receipt=<file>` reads the receipts that prove them (the `pia-lean` skill) |

A `.pia.md` file is literate: only its ` ```pia ` blocks are code, and the file name alone switches that on.

Codegen options: `--target=<triple>`, `--cpu=<name>` (default arm64 macOS, `apple-m1`) and `-O0` to `-O3`. Each Pia function becomes a C function of the same name.

## Solver limits

Whether a goal is proved must not depend on how busy the machine is, so the deterministic resource limit decides: `--solver-rlimit=N` (default 1200000000). `--solver-timeout=ms` (default 600000) is only a safety net. Raise the rlimit for a goal that runs out; never lower the timeout to make a run faster, since that turns proofs into failures that depend on load. Bazel's `pia_object` rule uses the same defaults.

For large files, see the `pia-fast-proofs` skill: `--jobs`, `--verify-only`, `--proof-cache`, `--verify-stats` and slicing.

## When a proved object is refused later

A proof is only as sound as the piac and Z3 that found it. When one of them turns out to have a soundness bug, an advisory (`security/advisories/`, [docs/advisories.md](../../docs/advisories.md)) names the affected versions, and `pia-cert check` refuses every object they proved, even though `piac --verify` passed at the time. The fix is to prove and compile the module again with the fixed piac: the refusal names the version. `piac --version` says which piac and Z3 you have, and ends with a `revoked by <id>` line for each advisory against them (`--advisories=<dir>` adds a newer set); a revoked toolchain also warns on every run. Do not reach for `--accept-advisory` to get a build through; it is for a module whose proofs someone has checked another way, and it shows up as a trusted item.
