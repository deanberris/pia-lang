---
name: pia-language
description: Write idiomatic Pia that proves first time - syntax at a glance, where each fact belongs (types before contracts), the usual shapes for loops, errors, generics, lambdas and modules, and the pitfalls that cost the most time. Use when writing, porting or reviewing .pia or .pia.md code, or adding a standard library module.
---

# Writing Pia

Pia looks like OCaml, and every program is proved before it compiles. Most of the work is deciding *where a fact lives*, because that decides who has to prove it again. This skill is the compact version of [docs/tour.md](../../docs/tour.md) and [docs/idioms.md](../../docs/idioms.md). When a goal fails, switch to `pia-contracts`. To run the prover, see `piac-verify`, or `pia-mcp` and `pia-repl` for cell by cell work.

## Before writing anything

1. **Copy from a proved example.** `tests/verify/<feature>.pia` has a proved file for nearly every feature, such as `handlers.pia`, `defer.pia`, `concepts.pia`, `lambda_captures.pia`, `models.pia`, `vec_generic.pia` and `ffi.pia`. The `lib/Pia` modules show what a finished library module looks like. `CODEMAP.md` lists them all.
2. **Check that the feature exists.** [docs/status.md](../../docs/status.md) lists what compiles. `dyn`, floats, `vec<T, k>`, refinement types, recursive types and `spread` are designed but not built yet, and piac says "not supported yet".
3. **Prove one function at a time.** Write it without contracts, run `piac --verify`, and let the failed goals tell you what is missing.

## Syntax at a glance

<!-- example: glance.pia -->
```ocaml
(** A level, as a variant rather than an integer tag. *)
let level = type | Dark | Mid | Bright

let classify (y : u16) : level =
  if y < 256 then Dark else if y < 512 then Mid else Bright

let is_bright (y : u16) : bool =
  match classify y with
  | Bright -> true
  | _ -> false

(** A record type is a value, bound with `let`. *)
let pixel = type { r : u8; g : u8; b : u8 }

let luma (p : pixel) : u16 = p.r + p.g + p.b

\ A bound on one value goes in its type: callers keep the fact.
let scale (p : int{0..100}) : u16 = p * 3

let count_bright (ys : [u16]) : usize
  ensures result <= len ys
= let n : mutable usize = 0 in
  for i in 0 .. len ys
    invariant n <= i
  do
    if is_bright ys.[i] then n <- n + 1 else ()
  done;
  n
```

| Form | Meaning |
| --- | --- |
| `let x : t = e`, `let f (a : t) : r = e`, `let rec` | the only binding form. Types are values too: `let byte = type u8` |
| `let ... in e`, `e1; e2`, `x <- e` | local binding, sequencing, assignment to a `mutable` |
| `u8`…`u64`, `i8`…`i64`, `usize`, `isize`, `bool`, `int{lo..hi}` | integers are bounded. Widening is implicit and narrowing is a goal. Comparing two different integer types is exact |
| `100'000`, `0xFFFF'FFFF`, `1_000_000`, `42u8` | digits group with `'` (between two digits) or `_`; `,` never groups. A suffix gives a literal its type |
| `[t; n]`, `[t]`, `xs.[i]`, `xs.[a .. b]`, `len xs` | arrays, slices, indexing (a goal) and sub-slices, which are views, not copies |
| `type { a : t }`, `type \| A \| B of t` | records, and variants with at most one payload each |
| `match e with \| C x -> … \| _ -> …` | must be exhaustive. An unreachable arm is an error |
| `(x : borrowed inout mutable [u8])` | ownership (`borrowed`/`moved`), access (`in`/`out`/`inout`), modifiability (`fixed`/`mutable`). The default is a read-only borrow |
| `@overflow(proof\|wrap\|saturate\|trap)`, `+\|`, `-\|` | after the return type. `proof` is the default. The `+\|` operators always saturate |
| `(* *)` (nests), `\` to the end of the line, `(** *)` doc | comments are syntax. `//` is **not** a comment |
| `abort ()` | proved unreachable |

## Where each fact goes

Prefer the earliest rung that can say it. The order is also the order of proof cost (ADR 0037).

1. **In a type.** Use range types (`int{0..99}`), ranged elements (`[int{0..15}]`), a variant instead of a tag, a slice instead of a pointer and length, and a slice of records instead of parallel arrays. Intervals decide these without the solver, and the fact travels with the value.
2. **In a contract**, for relations between values: `requires i < len xs`, `requires lo <= hi`, `ensures result >= a`. A contract stops at the function, and every caller proves it again.
3. **In a spec function or a lemma**, to name an idea once (`let spec`) or prove a hard step once (`let lemma`, by induction with `decreases`).
4. **In a generic or a metaprogram**, for families: one generic function with a concept (`(t : type where Ord t)`), or `@derive(eq)` and other metaprograms when the bodies differ by constants or structure.
5. **In an `assert`**, as a stepping stone that splits one hard goal.
6. **Escape hatches**, last: `assume` (only in a file marked `@trusted`), `@overflow(wrap)` for arithmetic that is not really modular, `--allow-unproved`, and `unsafe`.

The lints say when code skips a rung: `range_requires`, `range_ensures`, `redundant_bound`, `generic_candidate`, `nonlinear_contract`, `deep_fuel` and `costly_goal` ([docs/idioms.md](../../docs/idioms.md#the-lints)). Take their fixes unless the bound mirrors a C API. In that case write `@allow(name)` on the return annotation.

## The usual shapes

**Loops.** After a loop the verifier knows only its invariant and, for a `for`, that the loop variable reached its bound. Bound accumulators by the loop variable (`s <= 255 * i`). A `while` loop needs `decreases`. The details are in `pia-contracts`.

**Errors.** Errors are closed variants carried in `result t e`. `e?` returns the error to the caller, or to a `handle` block after the body. `a | b` is the union of two error sets. `defer cleanup` runs at every exit, in reverse order, before a `?`'s error leaves:

<!-- example: errors.pia -->
```ocaml
let parse_error = type | NotDigit of u8

let digit (c : u8) : result u8 parse_error
  ensures (match result with | Ok d -> d < 10 | Err _ -> true)
= if c >= 48 && c < 58 then Ok (c - 48) else Err (NotDigit c)

let two_digits (a : u8) (b : u8) : result u8 parse_error
  ensures (match result with | Ok v -> v < 100 | Err _ -> true)
= let x = digit a? in
  let y = digit b? in
  Ok (x * 10 + y)

let or_zero (a : u8) (b : u8) : int{0..99}
=
  let v = two_digits a b? in v
handle
| NotDigit _ -> 0
```

Each value bound by a `?` keeps its callee's postcondition (`x < 10` above), which is what proves `x * 10 + y`. To see `defer` and error sets in use, read `tests/verify/defer.pia` and `tests/verify/error_sets.pia`.

**Generics, concepts and lambdas.** A type parameter comes first, `(t : type where C t)`, and the type arguments are deduced from the arguments. A generic function must write its return type. A concept is a `let meta C (t : type) : concept = sig ... end` with requirements and laws. A lambda is a nameless `let`, and it lists its captures in brackets:

<!-- example: lambda.pia -->
```ocaml
let find (xs : [u8]) (p : u8 -> bool) : usize
  ensures result <= len xs
  ensures result < len xs ==> p xs.[result]
= let i : mutable usize = 0 in
  while i < len xs && p xs.[i] = false
    invariant i <= len xs
    decreases len xs - i
  do i <- i + 1 done;
  i

let first_between (xs : [u8]) (lo : u8) (hi : u8) : usize
  ensures result < len xs ==> lo <= xs.[result] && xs.[result] <= hi
= find xs (let [lo, hi] (x : u8) => lo <= x && x <= hi)
```

The verifier knows a lambda's body where the lambda is passed, so it needs no contract of its own. Captures are copied (`[x]`), borrowed (`[borrowed x]`) or written (`[inout x]`).

**Modules.** One file is one module. Everything in it is private unless an interface the module claims lists it, and an import names an interface, never a wildcard:

<!-- untested: needs the interfaces of the imported modules built with --emit=interface -->
```ocaml
module Pia.Core.Clamp : Clamp

import Pia.Core.Order.Ops

interface Clamp = sig
  (** C++: std::clamp. *)
  let clamp : (v : u8) -> (lo : u8) -> (hi : u8) -> u8
    requires lo <= hi
    ensures lo <= result && result <= hi
end
```

`import M.I as X { a, b }` renames the module and brings `a` and `b` in unqualified. Build an importer with `piac --emit=interface -o DIR dep.pia`, then `piac --verify --iface-path=DIR f.pia`. In Bazel, use `pia_library` from `tools/piac/pia.bzl`. A standard library module also gets a row in `docs/cpp-std.md` and three tests in `tests/std`.

**C functions.** `let f (x : i32) : i32 ensures ... = extern "sym"` has its contract trusted and listed by `--trust-report`. An extern without a contract can only be called as `unsafe f x`.

## Pitfalls

| Symptom | Cause | Fix |
| --- | --- | --- |
| `'x' shadows a local of the same name` (or a function, type, constructor or core builtin) | no shadowing at all, of locals, parameters, functions or builtins (`add`, `sub`, `mul`, `div`, `rem`, `eq`, `lt`, `len`, `old`, `and`, `or`, `shl`, `clz`, `popcount`, `abort` and more) | the new name the error suggests: primes are identifier characters, as in `x'` |
| `let d = x - 1` fails for `x : int{1..64}` | arithmetic with nothing wider expected happens at the operand's range | give the `let` a type: `let d : u8 = x - 1 in` |
| a literal does not fit | a literal takes its context's type | add a suffix, `42u8`, or annotate |
| `buf.[i] << 8` fails "the shift amount is less than 8" | Pia shifts at the operand's width. It does not promote like C | bind the value to a wider `let` first |
| `x & m = 0` surprises a C reader | the bit operators bind tighter than comparisons | nothing to do, it means `(x & m) = 0` |
| `a \| b` parses as match arms | `\|` is bitwise or only inside brackets | `x <- (a \| b)` |
| a parse error after `then`, or after the last `ensures` | `if c then let ...` and a body starting `=` right after `ensures` can misparse | wrap the inner `let`, or the body, in parentheses |
| a contract mentions `limit` or `f x` and the solver knows nothing about it | calls to ordinary functions, and `let` constants, are unknown values inside contracts | a literal, or a `let spec` function |
| a fact is lost after a call | callers see only the callee's `ensures` | state it in the callee's `ensures`, or better, in its return type |
| slow or nonlinear goals | `w * h` or `/ n` in a `requires`, a `forall` in a `requires`, or `@fuel` above 4 | range-typed factors, ranged element types, a lemma, or a helper with its own contract |
| `requires x < 100` still costs a solver query at each call | a precondition is always sent to Z3 | `int{0..99}` instead |
| `=` on two records is rejected | records have no built-in equality | `@derive(eq)` on the type |
| an intended failure hangs the test | a failing goal over arrays of arrays with quantifiers can run Z3 for a long time | keep intended failures free of quantifiers |
| a `// CHECK:` line is ignored, or breaks the parse | `//` is not a Pia comment | put the RUN and CHECK lines inside `(* *)` |
| a docs `console` block does not match the output | lints print to stderr, so their output is part of it | include the warnings, or pass `--no-lint` |
