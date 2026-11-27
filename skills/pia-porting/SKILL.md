---
name: pia-porting
description: Port code from C, C++, Rust, OCaml, Zig or Go to Pia with a feature map - what each construct becomes, what has no equivalent, and the traps each source language sets. Use when translating code or an idiom into Pia, or explaining Pia to someone who knows another language.
---

# Porting to Pia

Three things are different from every language you are porting from, and they decide most of the port:

1. **Everything that can go wrong is a goal.** Overflow, an index out of bounds, a division by zero, a narrowing conversion and a precondition at a call are proved before the program compiles, instead of being undefined, wrapping, panicking or raising at run time. A port that compiles cannot do any of them.
2. **Facts live in types.** Where the original checks or comments a bound, Pia states it once, in a range type (`int{0..99}`) or a contract, and callers prove it.
3. **Less is allowed.** There is no shadowing, no null, no exceptions, no garbage collector and no implicit truncation. Each has a Pia form below.

Port one function at a time, callee first, and read each failed goal as a question about the original: `pia-proof-debugging` shows how to tell a porting artifact from a real bug. `pia-language` has the syntax, and [docs/comparison.md](../../docs/comparison.md) compares Pia with other verified languages.

## The feature map

| Concept | Pia | C / C++ | Rust | OCaml | Zig |
| --- | --- | --- | --- | --- | --- |
| binding | `let x = e in`, `let x : mutable t = e`, `x <- e` | `const auto x`, `T x; x = e` | `let`, `let mut` | `let ... in`, `ref` | `const`, `var` |
| function | `let f (a : t) : r = e` | `r f(t a)` | `fn f(a: T) -> R` | `let f a = e` | `fn f(a: T) R` |
| shadowing | **none**, of locals, parameters, functions or builtins: `x'` | inner scopes | `let x = x + 1` | everywhere | none |
| integers | `u8`…`u64`, `i8`…`i64`, `usize`, `isize`, all bounded | UB on signed overflow, unsigned wraps | panics in debug, wraps in release | 63-bit, wraps | illegal behaviour |
| a bounded value | `int{0..99}`, `[int{0..15}]` | a comment | a newtype with a check | a private type | `u7`, a check |
| type alias | `let byte = u8` | `using byte = uint8_t` | `type Byte = u8` | `type byte = int` | `const Byte = u8` |
| distinct type (newtype) | `let length = type u32`; `length 5` wraps, `u32 l` unwraps, no implicit conversion; operators from `@derive(ord, add, scale)`, `@derive(hash)` and `@derive(json)` from their modules | `enum class`, a one-field struct | `struct Length(u32)` | a private type | `enum(u32)` |
| wraparound | `@overflow(wrap)` after the result type | unsigned arithmetic | `wrapping_add`, `Wrapping<T>` | the default | `+%` |
| saturation | `+\|`, `-\|`, or `@overflow(saturate)` | by hand | `saturating_add` | by hand | `+\|` |
| checked arithmetic | a `requires`, a guard, or a `result` | `__builtin_add_overflow` | `checked_add` | by hand | `@addWithOverflow` |
| type bounds | `max u32`, `min i64` | `UINT32_MAX`, `numeric_limits` | `u32::MAX` | `max_int` | `maxInt(u32)` |
| digit groups | `100'000`, `0xFFFF_FFFF` | `100'000` (C++14) | `100_000` | `100_000` | `100_000` |
| conversions | widening is implicit; narrowing (`let y : u8 = x`) is a goal | implicit truncation | `as` truncates, `try_into` | `Int32.of_int` | `@intCast` |
| arrays, slices | `[t; n]`, `[t]`, `xs.[i]` (a goal), `xs.[a .. b]` (a view) | `T a[n]`, `T* p, size_t n`, `std::span` | `[T; N]`, `&[T]` (panics) | `array`, `.(i)` (raises) | `[N]T`, `[]T` |
| records | `type { a : t; b : u }` | `struct` | `struct` | record | `struct` |
| variants | `type \| A \| B of t` (one payload; a record for more) | tagged `union`, `std::variant` | `enum` | variant | `union(enum)` |
| match | `match e with \| A -> ...`, exhaustive, no unreachable arms | `switch` | `match` | `match` | `switch` |
| no value | a variant: `type \| Missing \| At of usize`; `Pia.Core.Option` | `nullptr`, `std::optional` | `Option<T>` | `option` | `?T` |
| errors | closed variants in `result t e`, `e?`, `handle`, `a \| b` sets | `errno`, exceptions, `std::expected` | `Result`, `?` | `result`, exceptions | `!T`, `try`, `catch` |
| cleanup | `defer e`, at every exit, before an error leaves | destructors, `goto out` | `Drop` | `Fun.protect` | `defer`, `errdefer` |
| ownership | `borrowed` / `moved`, `in` / `out` / `inout`, `fixed` / `mutable` | `const T&`, `T&`, `T&&` | `&T`, `&mut T`, moves | none | pointers |
| generics | `(t : type where Ord t)`, deduced at calls | templates | generics | polymorphism, functors | `comptime T: type` |
| value parameters | `let block = let (t : type) (n : usize) => type ...`, `block u8 4` (types only for now) | `template <size_t N>` | const generics `<const N: usize>` | none | `comptime n: usize` |
| interfaces | concepts with laws, proved per type | C++20 concepts (no laws) | traits | module signatures | duck-typed `comptime` |
| metaprograms | `let meta`, quotes and splices, `@derive(eq)` | macros, templates, `constexpr` | `macro_rules!`, proc macros | ppx | `comptime` |
| closures | `let [x] (a : t) => e`, captures listed | `[x](T a) { }` | `move \|a\| e` | `fun a -> e` | none |
| function pointers | `let h : u8 -> u8 = succ`, a reference with the arrow's contract (no `&`); `let h : mutable (u8 -> u8) = succ` and `h <- twice` to rebind | `T (*h)(U) = succ` | `let h: fn(u8) -> u8 = succ` | `let h = succ` | `const h: *const fn (u8) u8 = succ` |
| modules | one per file; `interface I = sig ... end`; `import M.I` | headers, C++20 modules | `mod`, `pub`, `use` | `.mli` | `@import`, `pub` |
| memory | explicit allocators, every allocation fallible, `box t` | `malloc`, `new` | `Box`, infallible by default | GC | explicit allocators |
| floats | `f32`, `f64`, strict IEEE 754; `0.5f32`, or `0.5` where a float is expected; `f32 n`, `i32 x` (a goal: not NaN, in range), `to_bits x`, `from_bits u` | `float`, `double`, with `-ffp-contract=off` | `f32`, `f64` | `float` (64-bit) | `f32`, `f64` |
| C calls | `let f (x : i32) : i32 ensures ... = extern "f"`; `unsafe f x` if uncontracted | native | `extern "C"`, `unsafe` | `external` | `extern` |
| assertions | `assert p`, proved, never run | `assert` at run time | `assert!` | `assert` | `std.debug.assert` |
| loops | `for i in 0 .. n` (half open) with `invariant`; `while` with `decreases` | `for` | `for i in 0..n` | `for i = 0 to n - 1` (inclusive) | `for (0..n) \|i\|` |
| complexity | `costs iterations <= len xs`, proved (ADR 0062) | a comment | a comment | a comment | a comment |
| theorems Z3 cannot prove | `let lemma l ... = by lean T`, proved in Lean 4 (ADR 0061, `pia-lean`) | none | none (Verus, Kani outside the language) | none (Coq outside the language) | none |
| parallel loops | `spread i in 0 .. n do ... done`, proved race-free; `@place(gpu)` on a Mac's GPU | OpenMP | rayon | domains | threads |
| a sequence of GPU kernels | `for k in 0 .. n @place(gpu) do ... done`, its spreads one command buffer | CUDA streams, Metal command buffers | wgpu command encoders | — | — |
| recursive data | `let rec tree = type \| Leaf \| Node of { l : box tree; ... }` | pointers | `Box<Tree>` | `type tree = ...` | pointers |
| comments | `(* *)` nests, `\` to end of line, `(** *)` doc; `//` is **not** a comment | `//`, `/* */` | `//` | `(* *)` | `//` |

**Designed, not built yet** (piac says "not supported yet"; check [docs/status.md](../../docs/status.md) before relying on one): the real-valued proofs of float kernels (ADR 0038), `dyn`, `vec<T, k>`, refinement types, cost bounds that count calls to a function such as `less` (ADR 0062 step 2), functions stored in data and generic lambdas that capture, collectives, and `@place(auto)`. Recursive types now compile, and a `spread` runs on the GPU under `@place(gpu)`; [docs/features.md](../../docs/features.md) lists everything built.

## From C and C++

- **Integer promotion is gone.** C widens `uint8_t` to `int` before `<<`, `+` and `*`. Pia computes at the operand's type, so `p.[0] << 24` on a `u8` fails `the shift amount is less than 8`. Bind to a wider `let` first.
- **`size_t` subtraction** (`n - k`) is a goal: it is the most common real bug a port finds. Compare against what is left (`k <= n`) before subtracting.
- **Pointer and length become a slice**, and a write-only buffer an `out mutable` slice. `len` replaces the length parameter, so the port cannot pass the wrong one.
- **Exceptions and `errno` become `result`** with a closed error variant. RAII and `goto cleanup` become `defer`.
- **A float cast is a goal.** C's `(int)x` is undefined for a NaN or an out-of-range `x`; Pia's `i32 x` is the same truncation with a goal that neither happens, so state the range (`requires -1.0 < x && x < 256.0` before `u8 x`). `(float)n` is `f32 n`, and type punning through a union or `memcpy` is `to_bits`/`from_bits`.
- **Templates become generics with concepts.** A concept's laws are proved for each type that meets it, so a `std::sort` comparator that is not a strict weak order is a compile error, not undefined behaviour.

<!-- example: be32.pia -->
```ocaml
(** C: p[0] << 24 | p[1] << 16 | p[2] << 8 | p[3] *)
let be32 (p : [u8]) : u32
  requires len p >= 4
= let b0 : u32 = p.[0] in
  let b1 : u32 = p.[1] in
  let b2 : u32 = p.[2] in
  let b3 : u32 = p.[3] in
  ((b0 << 24) | (b1 << 16) | (b2 << 8) | b3)
```

## From Rust

- **`?` works the same way**, but error sets are closed variants and `a | b` is their union, so a caller's `handle` must cover exactly the errors that can reach it. There is no `From` conversion.
- **A panic path is a goal.** Indexing, `unwrap`, overflow in debug builds and `unreachable!()` become proof obligations; `abort ()` is Pia's `unreachable!()`, proved unreachable.
- **`as` casts truncate silently; Pia's narrowing is a goal.** Port `x as u8` as a `let y : u8 = x` and see whether it proves; if the truncation is meant, mask first (`x & 255`).
- **Borrows look familiar.** `&T` is the default parameter, `&mut T` is `borrowed inout mutable`, and a move is `moved`. Loans end at their last use, as with non-lexical lifetimes, and there are no lifetime annotations.
- **`unsafe` blocks have no counterpart in Pia code**; `unsafe` is only for calling a C function without a contract. A `// SAFETY:` comment in Rust becomes the `requires` that proves it.
- **Iterator chains become loops with invariants**, or calls taking lambdas; the verifier knows a lambda's body where it is passed.

<!-- example: rust_find.pia -->
```ocaml
(** Rust: xs.iter().position(|&x| x == key) *)
let found = type | Missing | At of usize

let position (xs : [u16]) (key : u16) : found
  ensures (match result with | At i -> i < len xs && xs.[i] = key | Missing -> true)
= let i : mutable usize = 0 in
  while i < len xs && xs.[i] <> key
    invariant i <= len xs
    decreases len xs - i
  do i <- i + 1 done;
  if i < len xs then At i else Missing
```

## From OCaml

Pia's syntax is OCaml's, so the differences are easy to miss:

- **No shadowing.** `let x = x + 1 in` is an error; write `let x' = x + 1 in`. This includes builtins: a function cannot be called `add`, `len` or `old`.
- **Types are values**: `let t = type { ... }`, not `type t = { ... }`, and a generic type is a function, `let box = let (t : type) => type { slot : [t] }`.
- **Integers are bounded.** `int` exists only in specifications; code uses `u32`, `i64` or a range type.
- **No lists, no GC.** Use slices and arrays, or a `vec` from an allocator. Recursion over a `let rec` type is proved but not compiled yet.
- **`for i = 0 to n - 1` is `for i in 0 .. n`**, half open. Indexing is `xs.[i]`, not `xs.(i)`.
- **No exceptions.** `raise` and `try ... with` become `result`, `?` and `handle`.
- **Functors become generics constrained by concepts**; a concept is a `let meta C (t : type) : concept = sig ... end` with laws.
- **A constructor has at most one payload.** `Node of tree * int * tree` becomes `Node of { left : box tree; key : u32; right : box tree }`.

## From Zig

Zig is the nearest in spirit: explicit allocators, `defer`, error sets, no shadowing and types as values.

- `comptime` code becomes `let meta` metaprograms; `comptime T: type` becomes `(t : type)`, deduced at calls.
- Error unions (`!T`) become `result t e`, `try` becomes `?`, and `catch` becomes a `handle` block. `errdefer` has no separate form: a `defer` already runs before an error leaves.
- `+%` becomes `@overflow(wrap)` on the function, `+|` is the same operator, and safety-checked illegal behaviour becomes a compile-time goal, so `ReleaseFast` loses nothing.
- Allocators are passed explicitly in both, and every Pia allocation returns a `result`.

## From Go and others

- **Go:** multiple returns with `err` become `result t e`; `defer` is the same word but runs at every exit of its sequence, not only the function's; goroutines over disjoint data become `spread`; slices are views as in Go, but cannot grow (a `vec` does).
- **Python, JavaScript:** dynamic values become variants; port the type each value really has, and the bounds the code assumes become range types.
- **Ada/SPARK, Dafny, F\*:** contracts carry over almost directly (`requires`, `ensures`, `invariant`, `decreases`, ghost state as `spec`, and Dafny's `opaque` and `reveal` as `@opaque` on a spec function and `with f`); see [docs/comparison.md](../../docs/comparison.md).

## After the port

Run `piac --verify` (`piac-verify`) or send the functions to a REPL (`pia-mcp`, `pia-repl`). Each failed goal is one of: a porting artifact, defined behaviour that is meant (`@overflow(wrap)`), an assumption the original made silently (a `requires`), or a bug. Then take the lints' advice (`pia-idioms`) and move constant bounds into types.
