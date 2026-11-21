# IRGen: the scalar subset

Status: implemented in M4 ([#5](https://github.com/deanberris/pia-lang/issues/5)).

`piac --emit=mlir file.pia` lowers a program to the `pia` and `pia_contract` dialects ([ADR 0018](adr/0018-dialect-layering.md)), with control flow in upstream `scf` and functions in `func`. This page describes the subset it accepts and how each construct lowers. Anything outside the subset is reported as "not supported yet" at its source location.

## The pipeline

1. **Parse** (`src/syntax`) to the uniform syntax tree.
1. **Expand metaprograms** (`src/meta`, [meta.md](meta.md)). Binary operators become calls of core builtins, `@derive` runs, and the `let meta` items are removed.
2. **Sema** (`src/sema`) resolves written types and collects the signature of every top-level `let`, so a function can be called before its definition. It reports items outside the subset (types, modules, metaprograms) before any code is generated.
3. **IRGen** (`src/irgen`) type checks expressions as it lowers them. A separate typed AST comes when the language outgrows the scalar subset.
4. The module is run through the MLIR verifier.

## Types

| Pia | IR |
| --- | --- |
| `u8` `u16` `u32` `u64`, `i8` ... `i64` | `!pia.int<lo, hi>` with the machine range |
| `usize`, `isize` | the 64-bit ranges, printed as the aliases `!usize` and `!isize` |
| `int{lo..hi}` | `!pia.int<lo, hi>` (bounds are integer literals for now) |
| `bool` | `i1` |
| `[T; n]` | `!pia.array<n x T>` (n is a literal for now) |
| `[T]` | `!pia.slice<T>` |
| `unit` | no value; a function returning unit has no results |
| `let pixel = type { r : u8; ... }` | `!pia.record<"pixel", r : !pia.int<0, 255>, ...>`, printed as `!pixel` |

Types are structural: `u64` and `usize` are the same type. `int{0..255}` is `u8`. Records are the exception: they are named, so two record types with the same fields are different types. `let byte = type u8` is another name for `u8`.

## Integers

- **Literals** take the type the context expects. With no context they are `i32`, or `i64` or `u64` if the value does not fit. A suffix (`42u8`) fixes the type. A literal that does not fit its type is an error.
- **Binary operators** arrive from expansion as calls of core builtins (`a + b` is `add a b`, [meta.md](meta.md#operators)). IRGen lowers a builtin call as the operator it stands for. They compute at the join of the operand types, the smallest range holding both. When the context expects a wider integer, they compute at that type, so `dst.[i] <- src.[i] * 3` with `u8` source and `u16` destination multiplies at `u16`. The other operand is widened with `pia.convert`. A literal takes the other operand's type, whichever side it is on.
- **Conversions**: wherever a value meets a declared type (a parameter, a return type, an annotated `let`, an assignment, an element store), IRGen inserts `pia.convert`. Widening always holds. Narrowing is a proof obligation for the verifier (M5).
- **Overflow**: `+ - * / %` lower to `pia.add`, `sub`, `mul`, `div`, `rem` with the function's overflow mode. The default is `proof`. `@overflow(wrap | saturate | trap)` on the return annotation sets another mode, and `+|` `-|` always saturate. `mod` is `%`.
- **Negation** `-x` is `0 - x` at x's type, so it is an obligation for unsigned and minimum values. `-5` is a literal.
- **Comparisons** lower to `pia.cmp` at the joined type. `=` and `<>` on bools lower to `arith.cmpi`.

## Bindings and mutation

- `let x = e in body` binds an SSA value. An annotation converts `e` to the declared type.
- There is no shadowing ([ADR 0022](adr/0022-metaprogram-hygiene.md)). A `let`, parameter, loop variable or quantifier binder may not reuse the name of a local in scope, a function, a type or a core builtin. Assigning to a mutable local is not shadowing.
- `let x : mutable T = e in ...` makes `x` assignable. There is no memory: each `x <- v` rebinds the SSA value, and structured control flow threads it through. A mutable local assigned inside `if` becomes an extra `scf.if` result, and one assigned inside a loop becomes a loop-carried value (`iter_args` for `for`, `scf.while` operands).
- Parameters are mutable only with `mutable`. Their modifiers are kept as the `pia.modifiers` argument attribute.
- `xs.[i]` lowers to `pia.load` and `xs.[i] <- v` to `pia.store`. Writing requires the parameter to be `out` or `inout`. Indices go through `pia.to_index`. `len xs` is `pia.len` followed by `pia.from_index` to `usize`.

## Control flow

- `if c then a else b` lowers to `scf.if` with the joined result type. An `if` without `else` must have type unit.
- `&&`, `||` and `==>` in code short-circuit, so they lower to `scf.if`. This keeps `i < len xs && xs.[i] <> x` from loading out of bounds.
- `for i in lo..hi step s do ... done` lowers to `scf.for` over `index`. The bounds are joined to one type, and `i` is bound with `pia.from_index` at that type. The range is half-open. Two literal bounds are `usize`.
- `while c do ... done` lowers to `scf.while`. The condition is computed in the `before` region.
- `a; b` evaluates `a` for its effects.

## Contracts

| Pia | IR |
| --- | --- |
| `requires p` | `pia_contract.requires` at function entry |
| `ensures p` | `pia_contract.ensures` before the return, with `result` bound to the return value |
| `decreases m` on a function | `pia_contract.decreases` at entry |
| `invariant p`, `decreases m` on a loop | at the head of each iteration: the start of the `for` body, or the `before` region of `scf.while` |
| `assert p`, `assume p` | `pia_contract.assert`, `pia_contract.assume` |
| `old e` | `pia_contract.old` |
| `forall (i in lo..hi). p` | `pia_contract.forall` whose block argument is `i`, yielding `(lo <= i && i < hi) ==> p` |
| `exists (i in lo..hi). p` | `pia_contract.exists`, yielding `lo <= i && i < hi && p` |
| `forall (k : u8). p` | quantifies over the whole type, with no guard |

Several binders nest one quantifier op per name, so a later range can mention an earlier name. Inside contracts, which have no effects, `&&`, `||` and `==>` are plain `arith` logic, and `==>` is `(a xor true) or b`. Whether arithmetic in contracts is exact or follows the overflow mode is settled with the verifier in M5. Quantifiers are rejected outside contracts and assertions.

## Records

A `let name = type { field : T; ... }` item defines a record type. Records are values, like integers.

- **Literals.** `{ r = v; g = 0; b = 0; a = 255 }` lowers to `pia.record`, with the fields in declaration order, whatever order they are written in. Its type comes from the context. Failing that, it is the one record type whose fields are exactly these. Every field must be given, once.
- **Field reads.** `p.r` lowers to `pia.field %p, "r"`.
- **Field assignment.** `q.r <- v` on a mutable local record rebuilds `q` with one field replaced. So, like any mutable local, `q` is an SSA value threaded through `scf.if` and loops.
- **Equality.** `p = q` on records calls `eq_<name>`, which `@derive(eq)` makes ([meta.md](meta.md#derives)). `<>` negates it.
- **Not yet supported:** arrays and slices of records, buffers inside records, and attributes on type items other than `@derive`.

The verifier and code generation do not see records. `transforms::scalarizeRecords` replaces each record value with its fields first, using MLIR's 1:N dialect conversion. A `pixel` parameter becomes four parameters named `p.r`, `p.g`, `p.b` and `p.a`, a `pixel` result becomes four results, and `pia.record` and `pia.field` disappear. `old p` becomes `old` of each field.

## Functions

Each top-level `let f (x : T) ... : R = body` becomes `func.func @f`. Parameters need annotations. A `let` with no parameters becomes a function with no arguments, and its uses call it. The return type may be left out, and then it comes from the body. Such a function cannot be called before its definition, or recursively. Calls must pass every argument, since partial application and functions as values come later.

## Not yet

Local functions and lambdas, `match`, variants, `dyn`, floats, `spread` and tiles (M8), slicing `xs.[a .. b]`, type-level lengths (`[T; n]`), refinements (`where`), modules, and concepts and generic types.
