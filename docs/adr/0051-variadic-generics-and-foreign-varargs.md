# 51. Variadic generics are tuple types walked by type `match`, proved once by structural induction, and foreign varargs are typed per declaration

Date: 2026-11-23

Status: Proposed

## Context

Dean (2026-11-23): "we need the equivalent of variadic functions that are provably safe. We should have language features for generic variadic functions and types, like C++ gives us, but with more straightforward syntax through metaprograms."

Three things need variadics now:

- **C functions.** `open`, `fcntl`, `ioctl` and `syscall` are C variadic functions. [ADR 0050](0050-senders-and-receivers.md) needs `syscall` for io_uring, and `Pia.Sys.Fs` needs `open` with a mode. Apple arm64 passes variadic arguments on the stack, while named arguments go in registers, so declaring `open` with a fixed third parameter gives the wrong ABI. x86_64 System V also needs `%al` set to the number of vector registers a variadic call uses. Pia's FFI today takes only fixed integer, bool and buffer parameters (`genForeign`).
- **Generic code over any number of types.** `when_all (a, b, c)` in ADR 0050 completes with the values of all its senders and the union of their error sets. `format` takes any number of arguments of types that meet `Format`. `apply`, `tuple_cat`, `std::get` by type and argument forwarding for constructors are the same shape.
- **Types over any number of types.** An operation state for `when_all` holds one child per sender, and `std::variant<Ts...>` is a sum over a list of types.

C++ answers with parameter packs: `typename... Ts`, pack expansions `f(xs)...` in a dozen syntactic positions, fold expressions `(... + xs)`, `sizeof...`, and recursion through partial specialisation or `if constexpr`. They are powerful, but the syntax is irregular. Pack indexing only arrived in C++26, and an error inside an expansion surfaces at instantiation. C varargs (`va_list`) are unchecked: the callee trusts the caller's count and types, which is the root of format-string bugs.

[ADR 0040](0040-cpp23-standard-library-in-pia.md), section 9, already decided that tuples are a core type and that tuple types are the type lists for variadic code, "without a separate pack feature", and said core tuples need their own ADR. This is that ADR. It also covers the parts section 9 left open: how generic code walks a tuple and is proved, variadic types, and foreign varargs.

## Decision

### 1. Core tuples

This section builds what ADR 0040 section 9 specifies, unchanged:

- `(a, b, c)` is a tuple value, and `(u8, str, bool)` is its type, since types are values. `()` is `unit`. There is no one-element tuple.
- `t.0`, `t.1`: positional access, checked at compile time.
- A tuple is an anonymous record with fields `0`, `1`, ... It has the same layout, ownership, `moved`, `@linear`, borrow and contract rules as a record, and struct-of-arrays buffers. Two tuple types with the same element types are the same type.
- `Eq`, `Ord` and `Hash` are structural, proved once (ADR 0043).

### 2. A pack is a tuple: variadic functions take one tuple parameter

A variadic function takes a tuple whose type is a deduced type parameter:

```ocaml
(* Designed syntax. *)
let print (ts : type where All Format ts) (w : borrowed inout writer) (xs : ts) : unit = ...

print w (x, name, 42u8)          (* ts = (u32, str, u8), deduced *)
```

There is no new call syntax. `f (a, b, c)` reads as C++'s `f(a, b, c)`, and it fits curried application: since a call always takes exactly one tuple, `print w` is still a partial application with nothing ambiguous about where the arguments stop. `All c ts` is a prelude concept over tuple types: every element type meets `c`, and `ts` is a tuple. Concepts are already values that type-level metaprograms take ([ADR 0046](0046-box-over-a-type-or-a-concept.md)). `Tuple ts` alone says only that `ts` is a tuple type.

### 3. Walking a pack: tuple patterns in type and value `match`

[ADR 0035](0035-substitution-failure-and-total-constraints.md)'s type `match` gains two tuple patterns: `()` and `(h, ..rest)`, which binds the first element type and the tuple of the rest. Type-level metaprograms over packs are then ordinary structural recursion, total without a `decreases`:

```ocaml
let meta size (ts : type where Tuple ts) : usize =
  match ts with
  | () -> 0
  | (h, ..rest) -> 1 + size rest

let meta map_types (f : type -> type) (ts : type where Tuple ts) : type =
  match ts with
  | () -> ()
  | (h, ..rest) -> (f h, ..map_types f rest)

let meta union_all (es : type where Tuple es) : type =   (* error sets: e1 | e2 | ... *)
  match es with
  | () -> never
  | (e, ..rest) -> e | union_all rest
```

The same patterns work on values. A `match` on a value whose type is a generic tuple is **type-directed**: which arm applies is decided by the tuple's type at each instance, not at run time. Such a `match` is exhaustive with `()` and `(x, ..rest)`, and an arm that cannot apply to some instance is not an "unreachable arm" error:

```ocaml
let rec print (ts : type where All Format ts) (w : borrowed inout writer) (xs : ts) : unit
  ensures written_count w = old (written_count w) + size ts
= match xs with
  | () -> ()
  | (x, ..rest) -> format w x; print w rest
```

`(x, ..rest)` in an expression builds a tuple, which is `tuple_cat`'s base case. `..` before a name inside tuple parentheses is the rest of a tuple. A range always has a left operand (`a..b`) inside a tuple, so the two cannot be confused (question 2).

The library's `Pia.Core.Tuple` gives the usual operations as generic functions over this one mechanism: `map` and `fold` with a generic lambda ([ADR 0044](0044-function-values-and-lambdas.md), step 4), `apply f xs`, `cat`, `get` by index or by type, and `zip`. C++'s fold expressions become `fold`. `sizeof...` becomes `size`, and pack indexing becomes `xs.i` with a constant `i`, or `element i ts`.

### 4. Proved once, by structural induction on the tuple

A recursive function over a generic tuple is proved once, for every tuple type, not once per instance. Pia already proves a `let rec` by assuming its own contract at each recursive call and proving that a measure decreases. Here the recursive call is at the tail's type, and the measure is `size ts`, which the `(x, ..rest)` arm decreases by construction, so termination needs no `decreases`. The `()` arm is the base case, and the `(x, ..rest)` arm is the step, with the contract for `rest` as the induction hypothesis. Inside the step, `x` has the head type `h`, constrained by `Format h` because `All Format ts` unfolds to `Format h && All Format rest`. This is ADR 0043's generic proof, with induction supplied by the shape of the type.

Codegen still specialises each instance, as for every generic. The recursion unrolls at compile time, so `print w (a, b, c)` compiles to three calls with no loop and no run-time dispatch.

Errors are reported once, at the definition, for every tuple type, because the body is checked against `All Format ts` and not against each instance (ADR 0034's definition check). That closes C++'s gap, where a pack expansion fails at instantiation.

### 5. Variadic types

A generic type may take a tuple type parameter, and its fields may use type-level metaprograms over it:

```ocaml
(* when_all's operation state: one child operation per sender (ADR 0050). *)
let when_all_op (ss : type where All Sender ss) (r : type) = type {
  children : map_types (let (s) => op_of s (child_receiver r)) ss;
  results  : map_types (let (s) => option (value_of s)) ss;
  rcv      : r;
}

let when_all (ss : type where All Sender ss) (xs : moved ss) : when_all_sender ss = ...
(* value_of (when_all_sender ss) = map_types value_of ss
   error_of (when_all_sender ss) = union_all (map_types error_of ss) *)
```

A sum over a type list, C++'s `std::variant<Ts...>`, is `one_of ts`. This is a type-level metaprogram that builds a variant with one constructor per position, `At0 of t0 | At1 of t1 | ...`. It comes with `index`, `get` and a type-directed `visit`, and with exhaustive `match` on its constructors. A core anonymous sum type with nicer constructor names stays a separate decision, as ADR 0040 left it (question 3).

### 6. Foreign varargs are typed per declaration

A C variadic function is declared once for each way Pia calls it, with `@variadic(n)`, where `n` is the number of named C parameters. The parameters after the first `n` are the variadic ones, each with a fixed Pia type:

```ocaml
(* Pia.Sys.Posix, @trusted. open(2): the mode is read only when O_CREAT is set. *)
let open (path : cstr) (flags : i32) : i32 @variadic(2)
  requires flags & o_creat = 0
  ensures result >= -1
= extern "open"

let open_create (path : cstr) (flags : i32) (mode : u32) : i32 @variadic(2)
  requires flags & o_creat <> 0
  ensures result >= -1
= extern "open"

(* syscall(2), one declaration per system call the library makes. *)
let io_uring_enter (fd : i64) (to_submit : u32) (min_complete : u32) (flags : u32) : i64
  @variadic(1) @syscall(426)
  ensures result >= -1
= extern "syscall"
```

- **Calls use the variadic ABI.** Codegen emits the call as a variadic LLVM call, so Apple arm64 puts the variadic arguments on the stack and x86_64 sets `%al`. A declaration that names a variadic C function without `@variadic` is wrong on Apple arm64, and the trust report lists every foreign symbol with the arity it was called at.
- **`cstr`** above is a `[u8]` refined to end in a NUL byte, which `Pia.Sys` builds and proves. It is not a new core type.
- **Variadic parameters are C-promoted types only:** `i32`, `u32`, `i64`, `u64`, `isize`, `usize`, buffers (passed as pointers) and, once floats land, `f64`. A narrower integer or a `bool` is a compile error that says to widen it, because C would promote it and the callee would read an `int`. A record is an error, because C cannot pass a struct through `...` portably.
- **The count and the types are fixed by the declaration,** so a call can never pass the wrong number or the wrong types. What the C function reads depends on its other arguments, as `open` reads a mode only with `O_CREAT`, and that becomes a `requires` that ties the two together, proved at every call. This is the "provably safe" part: the `va_arg` reads that C trusts become goals.
- **`@syscall(n)`** is sugar for a first fixed argument that is the system-call number, taken from the target model (`Target` on Linux, [ADR 0049](0049-targets-are-theories.md)), so a wrong number cannot be written by hand. It is `@target(x86_64_linux)`: macOS has no stable system-call numbers, and the library goes through libSystem there.
- **Pia functions are never C-variadic.** Pia code takes tuples instead. Exporting a variadic function to C, or taking a `va_list`, is not supported. C callbacks that need one are wrapped in C, outside Pia.
- **Format strings stay in Pia.** `printf` and its family are not declared. `Pia.Text.Format` uses section 2, with `requires placeholders fmt = size ts`, which the verifier folds when `fmt` is a literal. So a format string with the wrong number of arguments is a failed goal, not a crash.

## Implementation steps

1. **Foreign varargs** (section 6): `@variadic(n)` and the promoted-type check, emitted as variadic calls. This needs no tuples, so it comes first, because ADR 0050's I/O stack and `Pia.Sys` (#55, #57) need it. `@syscall` waits for `@target` (ADR 0049, step 3c).
2. **Core tuples** (section 1): syntax, sema as anonymous records, IRGen, codegen and the verifier through the record paths, patterns, `t.0`, and the structural instances.
3. **Tuple type patterns** (section 3): `()` and `(h, ..rest)` in type `match`, then `size`, `map_types`, `union_all`, `All` and `Tuple` in the prelude.
4. **Generic functions over tuples** (sections 3 and 4): type-directed value `match`, structural termination, the induction proof, and unrolled specialisation.
5. **`Pia.Core.Tuple`**: `map`, `fold`, `apply`, `cat`, `get` and `zip`, and `Pia.Text.Format` on top.
6. **Variadic types** (section 5): fields typed by metaprograms over a tuple parameter, then `one_of`.

## Consequences

- One feature serves three purposes, with no separate pack syntax: tuples are the values, tuple types are the type lists, and type `match` is the recursion.
- Generic variadic code is proved and checked once, at its definition. Each instance still compiles to straight-line code.
- Calls to C varargs carry their count and types in the declaration and their dependencies in contracts. The ABI is right on both targets, and C's promotion rules are enforced rather than assumed.
- Pia cannot call a C variadic function with an arity it did not declare, and cannot be called as one. Both restrictions are deliberate.
- The `..rest` form is new syntax in tuple patterns and tuple expressions, and the grammar must keep it apart from ranges.

## Questions for Dean

1. **Should a variadic call take one explicit tuple, `f (a, b, c)`?** The recommendation is yes. Curried application cannot tell where a bare `f a b c` ends, and the tuple form is what C++ readers expect. The alternative is a trailing-arguments marker on the declaration, which would end partial application for those functions.
2. **Spelling of the rest pattern.** The recommendation is `(h, ..rest)`, which reuses `..` from ranges, unambiguous inside tuple parentheses because a range there always has a left operand. The alternative is `(h, ...rest)`, which is closer to C++ and JavaScript and costs a new token.
3. **Sums over type lists.** Should `one_of ts` with positional constructors (`At0`, `At1`) be enough for now, or should core anonymous sum types come with this ADR? The recommendation is `one_of` now, and anonymous sums in their own ADR when `<variant>` needs them.
4. **One declaration per C arity.** The recommendation is to keep `@variadic(n)` declarations fixed. The alternative is a single declaration whose variadic part is a tuple constrained by a metaprogram, which would allow arbitrary calls but would make the ABI and the contracts harder to audit in a `@trusted` module.

## Prior art

| Source | What Pia takes |
| --- | --- |
| C++11 parameter packs, C++17 fold expressions, C++26 pack indexing | the capabilities: variadic functions and types, folds, size and indexing |
| C++ `std::tuple`, `std::apply`, `std::variant` | tuples as the pack value, `apply`, sums over a type list |
| Rust's tuples and its macro-generated tuple trait impls | tuples as anonymous records, with traits implemented for each arity |
| Haskell's and Idris's heterogeneous lists (`HList`), and induction over their type index | recursion over a type-level list, proved by induction |
| Zig's `anytype` tuples and `inline for` | a variadic call as one tuple argument, and the loop unrolled per instance |
| GCC's `format` attribute | argument checking for format strings, here as a proved `requires` |
