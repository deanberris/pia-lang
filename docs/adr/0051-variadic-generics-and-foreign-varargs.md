# 51. Variadic functions and types take a pack that is called like any argument list, walked by metaprograms and proved once; foreign bindings are generated from tables

Date: 2026-11-23

Status: Proposed (revised 2026-11-23 after Dean's first review: plain call syntax, metaprograms instead of recursive `match`, and foreign bindings from tables)

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


### 2. A variadic function is called like any other function

The last parameter of a function may be a **pack**, written `..`, with its type a deduced type parameter:

```ocaml
(* Designed syntax. *)
let print (ts : type where All Format ts) (w : borrowed inout writer) (xs : ..ts) : unit = ...

print w x name 42u8              (* ts = (u32, str, u8), deduced *)
print w                          (* ts = (), an empty pack *)
```

- **The call site is ordinary application.** A pack takes every argument that follows the fixed ones in that application. An application ends where it always ends: at a closing parenthesis, an operator, `;`, `then`, `in` and so on. So `print w x name 42u8` is one call with three pack arguments, and `print w (f x) y` is one call with two. Nothing about the call says the function is variadic.
- **Inside the body, the pack is a tuple.** `xs` has the tuple type `ts`. Its elements are `xs.0`, `xs.1` and so on, and it can be passed on whole, so ADR 0040's tuple decision still holds: a pack is a tuple, and only the parameter is marked.
- **Passing a tuple as a pack** is `..t` at the call: `print w ..pair`. This is how one variadic function forwards its pack to another, as C++'s `f(xs...)` does.
- **No partial application of a pack.** A call of a variadic function always supplies its whole pack, which is what lets the arguments end where the application ends. `print w` is a call with an empty pack, not a function waiting for more. To pass a variadic function as a value, wrap it in a lambda with the arity you want, `let (x) => print w x` (question 1).
- **`All c ts`** is a prelude concept over pack types: every element type meets `c`. Concepts are already values that type-level metaprograms take ([ADR 0046](0046-box-over-a-type-or-a-concept.md)).

### 3. Packs are walked by metaprograms, not by recursion

Code never recurses over a pack. Two kinds of metaprogram do the walking instead.

**Type-level metaprograms over a list of types.** The builtin `elements ts` gives a pack type's element types as a metaprogram list, and `tuple_of xs` builds a pack type from a list. Everything else is the list functions metaprograms already have, `map`, `fold` and `length` ([docs/meta.md](../meta.md#the-interpreter)):

```ocaml
let meta size (ts : type) : usize = length (elements ts)

(* when_all's value and error types (ADR 0050). *)
let meta values_of (ss : type) : type = tuple_of (map value_of (elements ss))
let meta errors_of (ss : type) : type = fold (let (a) (e) => a | e) never (map error_of (elements ss))
```

These are total by the rule tactics already follow ([docs/meta.md](../meta.md#tactics)): the only recursion is `map` and `fold` over the components of a parameter.

**A loop over a pack, unrolled by expansion.** In code, a `for` over a pack runs its body once for each element, and the expansion stamps out one copy of the body per element, as Zig's `inline for` does. `x` has each element's own type in its copy:

```ocaml
let print (ts : type where All Format ts) (w : borrowed inout writer) (xs : ..ts) : unit
  ensures written_count w = old (written_count w) + size ts
= for i, x in xs
    invariant written_count w = old (written_count w) + i
  do format w x done
```

The library's `Pia.Core.Pack` is written the same way: `map`, `fold`, `apply`, `cat`, `get` by type and `zip`. C++'s fold expressions become `fold`, `sizeof...` becomes `size`, and pack indexing becomes `xs.i` with a constant `i`.

### 4. Proved once, though compiled per element

The loop above is proved once, as an ordinary loop. Its body is proved for an abstract position `i` and an abstract element type `element i ts`, which is an abstract sort constrained only by `Format`, because `All Format ts` says that much of every element ([ADR 0043](0043-generic-definitions-proved-once.md)). The invariant is the induction over positions, exactly as for `for i in 0 .. n`. Each unrolled copy is then discharged by that one proof, as an instance of a generic is.

So a variadic function is proved and checked once, at its definition, for every pack, and errors are reported there rather than at an instantiation (ADR 0034's definition check). That closes C++'s gap, where a pack expansion fails only when instantiated. Codegen still compiles straight-line code: `print w a b c` becomes three calls of `format`, with no loop and no run-time dispatch.

### 5. Variadic types

A generic type's last type parameter may be a pack too, and an instance is written like any other generic application, `when_all_sender a b c`. Its fields use type-level metaprograms over the pack:

```ocaml
(* when_all's operation state: one child operation per sender (ADR 0050). *)
let when_all_op (r : type) (ss : ..type where All Sender ss) = type {
  children : tuple_of (map (let (s) => op_of s (child_receiver r)) (elements ss));
  results  : tuple_of (map (let (s) => option (value_of s)) (elements ss));
  rcv      : r;
}
```

A sum over a pack, C++'s `std::variant<Ts...>`, is `one_of ts`, a type-level metaprogram that builds a variant with one constructor per position, `At0 of t0 | At1 of t1 | ...`. It comes with `index`, `get`, a `visit` that is a `for` over the alternatives, and exhaustive `match` on its constructors. A core anonymous sum type stays a separate decision, as ADR 0040 left it (question 3).

### 6. Foreign bindings: variadic C calls, and declarations generated from tables

**A C variadic function is declared once, with a pack.** A pack in a foreign declaration is restricted to C-promoted types, and each call passes whatever its arguments are, with the ABI emitted for that call:

```ocaml
(* open(2): the mode is read only when O_CREAT or O_TMPFILE is set. *)
let open (ts : type where All CPromoted ts) (path : cstr) (flags : i32) (mode : ..ts) : i32
  requires (flags & o_creat <> 0) = (size ts = 1)
  requires size ts = 1 ==> element 0 ts = u32
  ensures result >= -1
= extern "open"

open path o_rdonly                         (* 2 arguments *)
open path (o_creat | o_wronly) 420u32      (* 3 arguments; 420 is 0644 *)
```

- **Calls use the variadic ABI.** Codegen emits each call as a variadic LLVM call with the argument types of that call, so Apple arm64 puts the pack on the stack and x86_64 sets `%al`.
- **`CPromoted`** holds for `i32`, `u32`, `i64`, `u64`, `isize`, `usize`, buffers (passed as pointers) and, once floats land, `f64`. A narrower integer or a `bool` fails the constraint with a message that says to widen it, because C would promote it and the callee would read an `int`. A record fails it, because C cannot pass a struct through `...` portably.
- **The contract decides what a call may pass.** What the C function reads depends on its other arguments, as `open` reads a mode only with `O_CREAT`. So the declaration's `requires` relates the pack's size and element types (`size ts`, `element i ts`) and values (`mode.0`) to the other arguments, and every call proves it. This is the "provably safe" part: the `va_arg` reads that C trusts become goals.
- **`cstr`** is a `[u8]` refined to end in a NUL byte, which `Pia.Sys` builds and proves. It is not a new core type.
- **Pia functions are never C-variadic.** Pia's own variadic functions take packs, which are tuples, and nothing in Pia makes or reads a `va_list`. Exporting a variadic function to C is not supported.
- **Format strings stay in Pia.** `printf` and its family are not declared. `Pia.Text.Format` uses section 2, with `requires placeholders fmt = size ts`, which the verifier folds when `fmt` is a literal. So a format string with the wrong number of arguments is a failed goal, not a crash.

**Declarations come from tables, not from hand-written items.** POSIX alone needs a few hundred declarations, most of them per target, so `Pia.Sys.Posix` writes none by hand. Each area (files, memory, processes, time, threads, sockets, io_uring's system calls) is a table, a list literal of rows passed to a binding metaprogram. The metaprogram stamps out the declarations, as `bit_family` already stamps out `Pia.Core.Bit` ([lib/Pia/Core/Bit.pia](../../lib/Pia/Core/Bit.pia)):

```ocaml
posix [
  call "read"  "read(2)"  [fd "fd"; out_buf "buf" "n"; size "n"] (ret isize)
       [ensures "result <= n"; ensures "result >= 0 ==> written buf 0 result"] [blocking];
  call "open"  "open(2)"  [cstr "path"; flag "flags"] (ret i32)
       [pack_if "flags & o_creat <> 0" [mode "mode"]] [];
  ...
]

constants x86_64_linux [ "o_creat" 0o100; "eagain" 11; "sys_io_uring_enter" 426; ... ]
constants arm64_macos  [ "o_creat" 0x200; "eagain" 35; ... ]
```

- **A row says what C says.** Its columns are the symbol, the manual page it cites, the parameters with their modifiers, the result, the contract clauses, any pack and the condition that decides it, and the attributes (`@blocking`, `@threadsafe`). The metaprogram turns the column kinds into Pia types and contracts: `fd` becomes an `i32` with `requires fd >= 0`, and `out_buf "buf" "n"` becomes an `out mutable [u8]` with `requires n <= len buf`.
- **What differs per target is data.** Constants, `errno` values, system-call numbers, and struct sizes and offsets live in one table per target, which `@target` selects ([ADR 0049](0049-targets-are-theories.md)). The binding table is shared. A system call is a row whose symbol is `syscall` and whose number comes from the Linux constants table, so no number is written by hand. On macOS there are no system-call rows, because the library goes through libSystem there.
- **The tables are checked against the real headers.** For each target, the metaprogram also writes a C file that `static_assert`s every constant, `sizeof` and `offsetof` in the tables against the platform's own headers, and CI compiles it on both jobs. A wrong constant is then a build failure on that platform, not a trusted lie.
- **The trust report lists rows, not items.** Every generated declaration is a trusted foreign contract. The report names the table and row each came from, with the manual page, so an audit reads the tables.
- **Headers are not parsed.** Generating the tables from C headers would get the types but not the contracts, which say what the manual page promises. The tables are written by hand, and only their constants and layouts are checked against the headers.

## Implementation steps

1. **Foreign bindings first** (section 6), since ADR 0050's I/O stack and `Pia.Sys` (#55, #57) need them: the `posix` and `constants` binding metaprograms, variadic calls, and the generated header check. Until packs exist (step 3), a pack row is stamped out as one fixed declaration per arity (`open` and `open_mode`), with the variadic ABI. That restriction is internal to the tables and goes away in step 4.
2. **Core tuples** (section 1): syntax, sema as anonymous records, IRGen, codegen and the verifier through the record paths, patterns, `t.0`, and the structural instances.
3. **Pack parameters and calls** (section 2): `..ts` parameters, deduction, the argument-collection rule, `..t` spreading, and `All` and `CPromoted`.
4. **Walking packs** (sections 3 and 4): `elements` and `tuple_of`, `for` over a pack with its expansion, the proof against an abstract element, and unrolled codegen. Foreign packs replace the per-arity declarations.
5. **`Pia.Core.Pack`**: `map`, `fold`, `apply`, `cat`, `get` and `zip`, and `Pia.Text.Format` on top.
6. **Variadic types** (section 5): pack type parameters, then `one_of`.

## Consequences

- A variadic call looks like any other call, and a variadic definition looks like an ordinary loop. The only new syntax is `..` on the pack parameter and on a spread argument.
- There is no recursion over packs, in types or in code. Type-level work is list metaprogramming, and code-level work is a loop that expansion unrolls.
- Variadic code is proved and checked once, at its definition. Each call still compiles to straight-line code.
- Calls to C varargs are typed by their arguments, checked against C's promotion rules, and constrained by contracts, with the ABI right on both targets.
- Foreign bindings grow by adding table rows. The constants and layouts in the tables are checked against each platform's headers in CI, and the trust report audits the rows.
- A variadic function cannot be partially applied, and it is named as a value only through a lambda.

## Questions for Dean

1. **Is no partial application for variadic functions acceptable?** It is what lets `f a b c` collect the pack without any marker at the call. The alternative is to allow partial application of the fixed parameters only, so that `print w` would be a function waiting for its pack, at the cost of an empty pack needing `print w ..()`. The recommendation is no partial application.
2. **Is the pack spelled `..ts`, in the parameter and in a spread argument?** It reuses `..` from ranges, and it cannot be confused with one, because a range always has a left operand. The alternative is `...`, which is closer to C++ and JavaScript and costs a new token.
3. **Is `one_of ts` with positional constructors (`At0`, `At1`) enough for sums over a pack for now?** The recommendation is yes, with core anonymous sums in their own ADR when `<variant>` needs them.
4. **Should binding tables be written by hand and checked against headers?** The recommendation is yes, because the tables carry contracts and headers do not. The alternative is generating them from headers with a tool, and adding contracts as a separate overlay.

## Prior art

| Source | What Pia takes |
| --- | --- |
| C++11 parameter packs, C++17 fold expressions, C++26 pack indexing | the capabilities: variadic functions and types, folds, size and indexing |
| C++ `std::tuple`, `std::apply`, `std::variant` | tuples as the pack value, `apply`, sums over a type list |
| Zig's `inline for` over tuples and `comptime` type lists | a loop over a pack unrolled per element, and types computed by ordinary compile-time code |
| Rust's `libc` crate and `bindgen` | per-target binding tables, and why types from headers are not contracts |
| Go's `zerrors_*` and `zsysnum_*` tables, generated per platform | constants and system-call numbers as per-target data, checked against the platform |
| GCC's `format` attribute | argument checking for format strings, here as a proved `requires` |
