# Metaprograms

Status: implemented in M7 ([#8](https://github.com/deanberris/pia-lang/issues/8)). Decisions: [ADR 0007](adr/0007-metaprogramming-fixed-point-expansion.md) and [ADR 0008](adr/0008-operators-via-metaprograms.md).

A metaprogram is a `let meta` function that runs at compile time. It takes and returns values, and syntax is one kind of value. `src/meta` holds the engine: a tree-walking interpreter (`Interpreter.cpp`) and the expansion loop (`Expand.cpp`). Expansion runs after parsing and before Sema, so everything a metaprogram produces is type checked and proved like hand-written code.

`piac --dump-expanded file.pia` prints the syntax tree after expansion. `--dump-ast` still prints it as parsed.

## Operators

Pia has no built-in infix operators. Each one is a `let meta operator` declaration that gives a symbol its fixity and expands it to a call of a core builtin:

```ocaml
let meta operator ( + ) : prec 6 left = let (a) (b) => `( add $a $b )
```

The standard operators live in the prelude ([`src/syntax/Prelude.cpp`](../src/syntax/Prelude.cpp)), which every program imports:

| Level | Operators | Associativity | Builtins |
| --- | --- | --- | --- |
| 1 | `==>` `<==>` | right | `implies` `iff` |
| 2 | `\|\|` | right | `or` |
| 3 | `&&` | right | `and` |
| 4 | `=` `<>` `<` `>` `<=` `>=` | none | `eq` `ne` `lt` `gt` `le` `ge` |
| 5.5 | `<<` `>>` | left | `shl` `shr` |
| 6 | `+` `-` `+\|` `-\|` | left | `add` `sub` `add_sat` `sub_sat` |
| 6.3 | `\|` | left | `bor` |
| 6.4 | `^` | left | `bxor` |
| 6.5 | `&` | left | `band` |
| 7 | `*` `/` `%` `mod` | left | `mul` `div` `rem` `rem` |

Prefix `~x` is built into the parser, like `-x`, and stands for `bnot x`. `|` is bitwise or only inside brackets ([grammar.md](grammar.md#operators)).

The parser reads the fixities from these declarations. A program can declare its own operators, or redeclare a prelude one. When it does, `parseProgram` parses the program again with the new table. An operator nobody declares still parses, with a level from its first character ([grammar.md](grammar.md#operators)), and expansion then reports it as undeclared.

```ocaml
let meta operator ( ** ) : prec 8 right = let (a) (b) => `( pow $a $b )
let pow (a : u8) (b : u8) : u8 = ...
let times : u16 = 2 * 3 ** 1        (* 2 * (3 ** 1) *)
```

Expansion replaces each binary node with the operator's result, innermost first. The new call takes the location of the operator token, so diagnostics and proof reports point where they did before. The builtins can also be called by name, as in `add_sat x y`. IRGen lowers a builtin call exactly like the operator it stands for ([irgen.md](irgen.md#integers)).

`-x` is still built in. Operators declared for a type (`let meta operator ( + ) for vec<T, k>`) are not supported yet.

## The interpreter

Values are integers (64-bit), bools, strings, syntax, lists, functions and unit. A metaprogram can use literals, names, application (curried, with partial application), `let ... in` (a local function may recurse), lambdas, `if`, `;`, list literals, quotes, and `+ - * / % mod < > <= >= = <> && ||` on its own values. Inside a metaprogram these operators act on its values directly. They are not expanded.

| Builtin | Meaning |
| --- | --- |
| `map f xs` | apply `f` to each element |
| `fold f init xs` | `f (... (f init x0) ...) xn` |
| `length xs` | the number of elements |
| `fields t` | the field names of the record type item `t`, as strings |
| `name t` | the name of an item or a name, as a string |
| `concat a b` | two strings joined (an integer counts as its digits), or two lists |

Each expansion has a fuel budget of a million steps. Running out is an error.

## Type-level metaprograms

A `let meta` whose parameters are all types and that returns a `type` or a `bool` is type-level ([ADR 0035](adr/0035-substitution-failure-and-total-constraints.md)). It stays in the program after expansion, because types and `where` predicates call it while the compiler checks types ([irgen.md](irgen.md#functions)):

```ocaml
let meta widen (t : type) : type =
  if t = u8 then u16 else if t = u16 then u32 else if t = u32 then u64
  else fail (concat "no integer type is wider than " (name t))

let meta small (t : type) : bool = size_of t <= 2

let add_wide (t : type where small t) (a : t) (b : t) : widen t = a + b
```

There, types are values. A type's name, such as `u8` or `pixel`, denotes the type, `=` and `<>` compare types, and `name t` spells one as Pia does (`u8`, `option<u8>`, `[u8]`).

| Builtin | Meaning |
| --- | --- |
| `size_of t` | the bytes a value of `t` takes: an integer the smallest of 1, 2, 4 or 8 that holds its range, a bool 1, an array its elements', a record the sum of its fields'; a slice has no fixed size, which is an error |
| `type_kind t` | `"int"`, `"bool"`, `"unit"`, `"array"`, `"slice"`, `"record"` or `"variant"` |
| `element t` | an array's or a slice's element type |
| `field_types t` | a record's field types, or a variant's payload types, as a list |
| `type_args t` | a generic instance's type arguments, as a list (empty for any other type) |
| `eq ne lt gt le ge add sub mul div rem and or implies iff` | the core builtins that a `where` predicate's operators expand to |

`match` takes a type too, which reads better than a cascade of `if`s:

```ocaml
let meta widen (t : type) : type =
  match t with
  | u8 ensures size_of result = 2 -> u16
  | u16 -> u32
  | u32 -> u64
  | _ -> fail (concat "no integer type is wider than " (name t))

let meta small (t : type) : bool =
  match t with
  | int -> size_of t <= 2
  | [e; n] requires n > 0 -> n <= 16 && small e
  | option e -> small e
  | _ -> false
```

- A type's name matches that type, and `int` every integer type. `[e]` matches a slice and `[e; n]` an array, binding the element type and the length. A generic's name applied to patterns, as in `option e`, matches its instances, binding their type arguments. `record fs` and `variant cs` bind the list of field or payload types. Any other name binds the whole type, and `p as x` binds it as well as matching `p`.
- Types are an open set, so a match on a type must end with a catch-all.
- An arm's `requires` is not a guard: if a type reaches the arm and it does not hold, that is an error (or, during overload resolution, the candidate's reason). An arm's `ensures` is checked of the arm's value, `result`, when the arm is taken.
- The same arm contracts work on a value `match` in ordinary code, where they are proof goals ([irgen.md](irgen.md#variants)).

A metaprogram that runs during expansion has no type values: a type's name there is an unknown name, as before.

A type-level metaprogram that a type or a constraint uses must terminate, so that which overloads a call can choose never depends on the step budget. The compiler checks this where it is defined, and an error is reported only where one that may not terminate is used:

- it may call the builtins, except `listing` and `redefine`, and other type-level metaprograms that terminate;
- a recursive call must be on a component of a type parameter, in one parameter position that all its recursive calls share: `element t`, an element of `field_types t` or `type_args t` that `map` or `fold` hands to a lambda, a name that a `match` on `t` binds below its top (`e` in `[e]` or `option e`), or a component of one of those. Types are finite trees, so this always ends;
- local functions may not recurse, it may refer to itself only by calling itself, and a cycle of metaprograms calling each other is rejected (it would need a measure they all decrease, which is not supported yet).

```ocaml
let meta plain (t : type) : bool =
  if type_kind t = "int" || type_kind t = "bool" then true
  else if type_kind t = "array" then plain (element t)
  else if type_kind t = "record" then
    fold (let (ok) (f) => ok && plain f) true (field_types t)
  else false
```

Running out of steps in such a metaprogram is an internal compiler error.

## Quotes and splices

`` `( ... ) `` builds syntax: an expression, one item, or several items. Inside a quote:

- `$x` splices the value of `x`. Syntax is copied in. A string becomes a name, or a type name in a type position such as `(a : $t)`. A type item in a type position becomes its name. An integer becomes a literal, and a bool becomes `true` or `false`.
- `$(e)` splices the value of the expression `e`.
- `$x` in a binder or field position (`let $n`, `a.$f`) splices a string, or the name of an item, as that name.

The code a quote builds takes the location of the expansion site: the operator, the `@derive` attribute, or the top-level call. Spliced code keeps its own locations.

## Hygiene

The rules are [ADR 0022](adr/0022-metaprogram-hygiene.md). Pia has no shadowing: a binding written in the source may not reuse the name of a local in scope, a function, a type or a core builtin. So an unqualified name always means its one visible binding. On top of that, hygiene keeps a quote from capturing, or being captured by, names at the expansion site:

- **Names a quote binds are renamed.** A `let ... in`, a parameter, a lambda or loop variable, or a quantifier binder inside a quote gets a fresh name such as `t#1`, so code spliced into its scope still sees the caller's `t`. The names of quoted top-level items are not renamed, since they are meant to be used.
- **Free names refer to the definition site.** A free name in a quote is marked `[prelude]` when it is a core builtin, and `[toplevel]` otherwise. IRGen resolves a `[prelude]` name to the builtin and a `[toplevel]` name to a top-level function, never to a local. With modules (M8), these become module-qualified paths such as `prelude.add`.
- **Operators and derives for a type will use argument-dependent lookup.** They are found in the module that defines the type and in adapter modules the program imports. Two candidates are an ambiguity error. This arrives with modules.
- **`$!name` opts out.** It stands for the plain name `name`, bound or resolved where the code lands. `derive_eq` uses it for the parameters `a` and `b`, which two separate quotes share:

```ocaml
let meta derive_eq (t : type_decl) : item =
  let n = concat "eq_" (name t) in
  let c = fold_and (map (let (f) => `( $!a.$f = $!b.$f )) (fields t)) in
  `( let $n ($!a : $t) ($!b : $t) : bool ensures $!result <==> $c = $c )
```

## Theory-building metaprograms

`let theory T = gen args` runs the metaprogram `gen` ([ADR 0036](adr/0036-library-theories.md), step 5). It returns a list of items: exactly one `let theory ... = sig ... end`, under any name, and any number of models of it (`let model m : ... = struct ... end`) and other items. The theory is named `T`, and the models are models of `T`.

```ocaml
let conn_state = type | Closed | Open | Draining

let theory Conn = machine "conn" conn_state Closed
  [ edge Closed "connect" Open
  ; edge Open "send" Open
  ; edge Open "shutdown" Draining
  ; edge Draining "close" Closed ]
```

- **Total and pure.** What the metaprogram returns becomes hypotheses of proofs, so it must terminate and read nothing of the program, by the rules for type-level metaprograms ([ADR 0035](adr/0035-substitution-failure-and-total-constraints.md), `src/meta/Totality.cpp`). It may not recurse except on a component of a parameter, may not call `listing` or `redefine`, and the same holds for the metaprograms it calls. A violation is an error at the `let theory` that says why.
- **Arguments.** In a top-level call, the name of one of the program's items stands for that item, and a variant's constructor stands for its name. So `conn_state` above is the type item and `Closed` is the name `Closed`.
- **Quotes of theories.** A quote can hold `let theory`, `let model` and theory members (`let sort`, an abstract `let spec f : ...`, `let axiom`). In a theory's or a model's body, `$xs` splices a list of members. `let sort $s`, `let spec $f` and `let axiom $n` splice names.
- **Hygiene.** The members' names are kept, since they are meant to be used. Their parameters and binders are renamed as in any quote ([Hygiene](#hygiene)).
- **One theory per argument tuple.** A second `let theory U = gen args` with the same call, written the same way, does not build again: `U` is another name for the first theory, so `U.x` is `T.x`.

The prelude's `machine` builds a state machine's theory and its model from a table of `edge`s ([theories.md](theories.md#state-machines)). It is written in Pia with `map` and `fold`, so it is total.

## Comments and literate programs

Comments are syntax ([ADR 0029](adr/0029-comments-as-syntax-and-literate-pia.md), [grammar.md](grammar.md#comments-in-the-syntax-tree)), and metaprograms can read them:

| Builtin | Meaning |
| --- | --- |
| `listing ()` | the program's items in source order, as the current pass found them, then the comments at the end of the file |
| `comments x` | the comments attached to the syntax `x`, in source order |
| `doc x` | the text of the `doc` and `prose` comments leading `x`, joined by blank lines; `""` when there are none |
| `text c` | a comment's text (also a string literal's value) |
| `style c` | `"line"`, `"block"`, `"doc"` or `"prose"` |
| `place c` | `"leading"`, `"trailing"` or `"detached"` |
| `kind x` | the kind of a syntax value, such as `"LetItem"`, `"Apply"` or `"Comment"` |
| `with_doc s x` | a copy of the syntax `x` (or the first of a list of items) with a leading doc comment `s` |
| `fail s` | stop with the error `s`, reported at the expansion site |

In the REPL, metaprograms can also change definitions that already exist, through `Pia.Live` ([ADR 0031](adr/0031-verified-repl-and-live-environment.md)). `listing ()` there lists the whole environment.

| Builtin | Meaning |
| --- | --- |
| `redefine x` | the definitions in the syntax `x`, marked to replace the environment's definitions of the same names; the REPL proves the change like a `:redef` cell before it commits it ([repl.md](repl.md#live-redefinition)) |

`piac` has no `Pia.Live`: a compiled program cannot redefine anything, so `redefine` fails there.

Comments survive everything expansion does:

- **Quotes** keep the comments written inside them, at the expansion site like the rest of the quote.
- **Splices** keep the comments on the spliced code. A comment on the splice itself, as in `` `( (** the sum *) $e ) ``, moves to the code that replaces it.
- **Expansion** moves the comments on a replaced node to its replacement: an operator's comments to the builtin call, and a top-level call's comments to the first item it makes.
- **Hygiene** never looks inside a comment. Comments bind no names and refer to none.

A comment can be read but not spliced into code. To document generated code, use `with_doc`, as the prelude's `derive_eq` does, so `eq_pixel` reads "Field-by-field equality for pixel, made by @derive(eq)." on hover.

`tests/meta/doc_lint.pia` walks `listing ()` and fails on an undocumented function, and `tests/meta/literate.pia.md` is a literate program that `piac --verify` proves. Rendering listings to LaTeX, HTML, SVG and DOT ([#63](https://github.com/deanberris/pia-lang/issues/63)) and a Jupyter kernel ([#64](https://github.com/deanberris/pia-lang/issues/64)) build on these.

## Derives

`@derive(x)` on a type item calls the metaprogram `derive_x` with the item and adds the items it returns after the type. The prelude defines `derive_eq`. For `let pixel = type { r : u8; g : u8 } @derive(eq)` it makes:

```ocaml
let eq_pixel (a : pixel) (b : pixel) : bool
  ensures result <==> (true && a.r = b.r) && a.g = b.g
  = (true && a.r = b.r) && a.g = b.g
```

`=` on two values of a record type calls `eq_<name>`, and `<>` is its negation. Without the derive, comparing records in code is an error that suggests `@derive(eq)`; in a contract they compare as values ([irgen.md](irgen.md#records)). Because `eq_pixel` has a postcondition, callers can prove facts about `p = q`, such as `ensures result ==> p.r = q.r`.

Other derives (`ord`, `hash`, `serialise`, `deserialise`) come later. A user can write their own `derive_x`.

## Top-level calls

An item that is a call of a metaprogram, such as `make_byte ()` in column 1, runs it. The items it returns replace the call. A metaprogram may also return a call of another metaprogram, which runs in the next pass.

## The expansion loop

Expansion runs in passes, to a fixed point (design.md, "Stages"). Each pass looks only at the items that existed when it started:

1. Each `@derive` runs.
2. Each top-level metaprogram call runs.
3. Each binary operator expands.

Code produced in one pass expands in the next. So `@derive(eq)` takes two passes: one makes `eq_pixel`, and the next expands the operators inside it.

A metaprogram sees a type only once it is defined. `fields t` on a record whose field types are not all defined yet defers the derive to the next pass. In this program the derive waits one pass for `make_byte` to define `byte`:

```ocaml
let wide = type { v : byte; w : u8 } @derive(eq)
let meta make_byte () : item = `( let byte = type u8 )
make_byte ()
```

The loop stops when a pass changes nothing. A metaprogram still waiting then is an error that names the type it needed. `--meta-cycles=N` (default 32) caps the passes that may produce code. Reaching the cap is an error that names the metaprograms still producing code. Once expansion stops, the `let meta` items and operator declarations are removed, and Sema sees ordinary code. Sema defines types in dependency order, so a generated type may come after its uses.

## Tests

`tests/meta/*.pia` are lit tests:

| Test | Covers |
| --- | --- |
| `derive.pia` | `@derive(eq)` and record `=`/`<>`, proved; deferral until a later pass defines a type |
| `operators.pia` | a user operator's precedence, renaming and `[toplevel]` resolution |
| `errors.pia` | undeclared operators, unknown derives, failing metaprograms, operators for a type |
| `waiting.pia` | a derive waiting for a type that is never defined |
| `cycles.pia` | `--meta-cycles` and its default |
| `shadowing.pia`, `builtin_name.pia` | the no-shadowing rule, and that quote binders never trip it |
| `comments.pia` | where comments attach, and that quotes, splices, derives and operators keep them |
| `doc_lint.pia` | a metaprogram that walks `listing ()` and insists on doc comments |
| `literate.pia.md`, `literate_errors.pia.md`, `literate_unclosed.pia.md` | a literate program, proved, and its errors |

## Not yet

- operators for a type, and overloading
- nested quotes
- a metaprogram's errors are reported at the expansion site, not inside the metaprogram
- concepts (`let meta Numeric (t : type) : concept`) and generic types
- module-level prelude import control
