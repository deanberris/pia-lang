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

## Buffers

- **Indexing** `xs.[i]` is `pia.load`, and `xs.[i] <- v` on an `out` or `inout` parameter is `pia.store`.
- **Slicing** `xs.[a .. b]` is `pia.slice`, a view of the same storage. An array passed where a slice is expected becomes a `pia.slice` of all of it.
- **Array literals** `[1; 2; 3]` where an array type is expected, and top-level `let t : [T; n] = [...]`, are `pia.const_array`. A top-level constant is not a function: each use is a `pia.const_array` with the constant's name as its `label`. The elements must be integer literals for now. Passing constant data, or a slice of it, to an `out` or `inout` parameter is an error.
- **`abort ()`** is `pia.abort`, with a result of the type the context expects.

## Variants

A variant `let shape = type | Circle of u16 | Empty` is a record named `shape` with a field `tag`, `int{0..n-1}`, and one field per constructor that has a payload, named after the constructor. A constructor's tag is its position. `Circle r` is a `pia.record` with tag 0, `r` in `Circle`, and a fixed value in every other payload field. Only constructors and `match` see these fields: `.tag` and record literals are errors on a variant. Records then scalarize as usual, so the verifier and codegen need nothing new, and a variant crosses the C boundary as its fields.

`match` checks its arms first: they must cover every constructor or end with a catch-all, and an arm after a catch-all, a constructor matched twice, or a catch-all after every constructor is an error. It then becomes a chain of `if`s on the tag, the last arm untested, with each arm's payload bound by a `let`. So arms carry mutable locals and join their result types exactly as `if` does.

## Bindings and mutation

- `let x = e in body` binds an SSA value. An annotation converts `e` to the declared type.
- There is no shadowing ([ADR 0022](adr/0022-metaprogram-hygiene.md)). A `let`, parameter, loop variable or quantifier binder may not reuse the name of a local in scope, a function, a type or a core builtin. Assigning to a mutable local is not shadowing. The error suggests a primed name instead: `x'`, or `x''` if that is taken. A prime is an ordinary identifier character, so `let x' = x + 1 in ...` names a value related to `x`.
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
- **Buffers of records.** `[pixel; 8]` and `[pixel]` hold records. `xs.[i]` reads one, `xs.[i] <- p` writes one, and `xs.[i].a <- v` reads element `i`, replaces its field and writes it back. Writing needs an `out` or `inout` parameter, as for any buffer.
- **Not yet supported:** buffers inside records, and attributes on type items other than `@derive`.

The verifier and code generation do not see records. `transforms::scalarizeRecords` replaces each record value with its fields first, using MLIR's 1:N dialect conversion. A `pixel` parameter becomes four parameters named `p.r`, `p.g`, `p.b` and `p.a`, a `pixel` result becomes four results, and `pia.record` and `pia.field` disappear. `old p` becomes `old` of each field. A buffer of records becomes one buffer per field, struct of arrays: an `xs : [pixel]` parameter becomes `xs.r`, `xs.g`, `xs.b` and `xs.a`, and loads, stores, views and `len` apply to each. The field buffers of a slice share one length, so every one after the first carries `{pia.length_of = k}`, naming the argument whose length it has; the verifier gives them that length, and the C entry point takes it once. A store of a field read back from the same element is dropped, so `xs.[i].a <- v` writes only `xs.a`. The field copies of one load, store or view share its index and length, so every copy after the first carries the unit attribute `pia.bounds_shared`: the first carries the bounds goal, and the verifier only assumes it for the others, so each index is reported once. Copies of a load or view that nothing uses are erased, and the first copy still in use carries the goal, so a record read only by a contract raises no goal, as a scalar one would not.

## Functions

Each top-level `let f (x : T) ... : R = body` becomes `func.func @f`. Parameters need annotations. A `let` with no parameters becomes a function with no arguments, and its uses call it. The return type may be left out, and then it comes from the body. Such a function cannot be called before its definition, or recursively. Calls must pass every argument, since partial application and functions as values come later.

A generic function, one with `(t : type)` parameters, is never generated itself. Each call works out the type arguments: first from `f<u8>` or `f<t = u8>`, then by matching the written types of the parameters that mention an unknown type parameter against the types of their arguments, which are generated first for this, then from the type the call is expected to have. The call goes to the instance, a private `func.func @"f<u8>"`, which is made on first use and generated after the function that used it, with each type parameter naming its argument. Generic types work the same way: `option u8` is a record type named `option<u8>`, made the first time it is used, and a generic constructor such as `Some` builds the instance it is expected to build, or else the one its payload's type gives.

A constraint on a type parameter, `(t : type where Ord t)`, names a concept: a `let meta C (t : type) : concept = sig ... end` that the metaprogram pass keeps in the program. Each call checks that the deduced type arguments meet it (the use check of ADR 0034). A requirement `let f : (a : t) -> bool` is met by a function in scope with that name, those parameter types and modifiers, and that result, and `include` requires another concept. Whether a concept is met is decided once per concept and type arguments. Each law, `let lemma name params ensures p`, becomes a lemma for those type arguments, `@"Ord<u8>.irreflexive"`, generated and proved like any other function. A requirement's contract becomes one too, `@"Ord<u8>.less.contract"`: under the requirement's `requires` it asserts the function's own `requires`, and it ensures the requirement's `ensures` of a call of the function. In an overload set, a generic whose type arguments do not meet its constraints is removed from the call, and the error for a call with no candidate left gives that reason.

A generic body is checked once, at its definition (the definition check). It is generated with each type parameter standing for an unknown type, a record named after the parameter with no fields, and then thrown away with every instance it made. A call with an argument of such a type resolves against the requirements of the concepts its constraints promise, including the ones they include, and a generic it calls must have constraints those concepts promise. Anything else, such as `<` on a `t` or a function the constraints do not require, is an error there, with a hint naming a concept that requires the function. A contract may still compare such values with `=`. Each instance then resolves its calls by its concrete types, which picks the function that met the concept at the use check, since two functions cannot share a name and parameter types.

An adapter, `let adapter by_red : Same pixel = struct ... end`, holds functions named after it, `@"by_red.same"`, which no call reaches by name. The use check meets a concept directly when it can. Otherwise it uses the adapter the call names (`alike<Same = by_red>`), the one the function being generated already chose, or the only adapter in scope for that concept and those types. Two such adapters, with neither named, are an error. An instance made through adapters is named after them, `@"alike<pixel, Same = by_red>"`, and while it is generated a call by a requirement's name goes to the adapter's function in place of any with the same parameter types. The concept's laws and requirement contracts are proved the same way, about the adapter's functions.

A type-level metaprogram, a `let meta` whose parameters are all types and that returns a `type` or a `bool`, also stays in the program (ADR 0035). A type such as `widen u8` or `widen t` runs it on the types it is applied to, and gives the type it returns. A `where` may state a predicate over types beside its concepts: a comparison, `||`, `==>`, `<==>`, or a call of such a metaprogram that returns a bool, as in `where Ord t && size_of t <= 8`, or `where t = u8 || t = i8`. Each call evaluates it for the deduced type arguments; when it is false, the candidate is removed with the reason "the constraint 'small t' is false for t = u32". A concept can only be joined to the rest by `&&`. Types are the metaprogram's values: a type's name denotes it, `=` compares types, `name t` spells one, and `size_of t` gives the bytes it takes (an integer the smallest of 1, 2, 4 or 8 that holds its range, a bool 1, an array its elements', and a record the sum of its fields'; a slice has no fixed size). Such a metaprogram must terminate: recursion only on components of a type parameter, no mutual recursion, and nothing that reads or changes the program ([meta.md](meta.md#type-level-metaprograms)); a use of one that may not is an error at the use. For now, a metaprogram's failure in a type, or in a predicate, is an error; it removes the candidate in ADR 0035's step 3. In the definition check, a type-level metaprogram applied to a type parameter stands for an unknown type too, and a signature with one has its body checked in each instance instead, since its types are only known there. A generic body may call a generic with a predicate only if its own constraints state the same predicate, and a generic whose constraints state every predicate of another's, and more, is the more specific. A type-level metaprogram applied in a parameter's type does not deduce its type arguments.

A name may have several generic overloads. The first keeps the name and the others are numbered, `rank#2`, and so are their instances, `@"rank#2<u8>"`. When two generics both fit a call equally well by their arguments, the more specific one wins. A is more specific than B when A's parameter types, with stand-in types for its type parameters, are an instance of B's but not the reverse. When each is an instance of the other, A is more specific when its constraints entail B's and not the reverse. A concept is entailed when A's constraints promise it through `include`, or when the requirements they promise include every one of its requirements and it states no law or requirement contract. Laws and contracts would need a proof, which is not done yet. Two generics with the same patterns whose constraints entail each other are an error at the second definition. A call with no single most specific candidate is an ambiguity error that lists them. Overloads with the same parameter types are told apart by their preconditions. They must be ordered: each one's `requires` clauses, compared with the parameters renamed by position, include every clause of the next, which proves that each precondition implies the next. They must also return the same type. They are named `copy(out [u8], [u8])#2` and on. A call that only they fit goes to the least specific, with all of them, most specific first, in `pia.overload_candidates`, and the verifier picks the most specific one whose precondition it proves at the call ([the verifier](verifier.md#choosing-overloads-by-precondition)). A call inside a contract uses the least specific, so a contract means the same in every build.

## Not yet

Local functions and lambdas, recursive types, `dyn`, floats, `spread` and tiles (M8), type-level lengths (`[T; n]`), refinements (`where` on values), modules, `decreases` for metaprograms, soft failure of a type-level metaprogram, generic adapters, entailment proved from laws and contracts, and precondition orders that need a proof rather than included clauses.
