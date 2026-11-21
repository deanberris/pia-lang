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
| 6 | `+` `-` `+\|` `-\|` | left | `add` `sub` `add_sat` `sub_sat` |
| 7 | `*` `/` `%` `mod` | left | `mul` `div` `rem` `rem` |

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

## Quotes and splices

`` `( ... ) `` builds syntax: an expression, one item, or several items. Inside a quote:

- `$x` splices the value of `x`. Syntax is copied in. A string becomes a name, or a type name in a type position such as `(a : $t)`. A type item in a type position becomes its name. An integer becomes a literal, and a bool becomes `true` or `false`.
- `$(e)` splices the value of the expression `e`.
- `$x` in a binder or field position (`let $n`, `a.$f`) splices a string, or the name of an item, as that name.

The code a quote builds takes the location of the expansion site: the operator, the `@derive` attribute, or the top-level call. Spliced code keeps its own locations.

## Hygiene

The rules are [ADR 0022](adr/0022-metaprogram-hygiene.md).

Hygiene is on by default, so a quote cannot capture or be captured by names at the expansion site:

- **Names a quote binds are renamed.** A `let ... in`, a parameter, a lambda or loop variable, or a quantifier binder inside a quote gets a fresh name such as `t#1`, so code spliced into its scope still sees the caller's `t`. The names of quoted top-level items are not renamed, since they are meant to be used.
- **Free names refer to the definition site.** A free name in a quote is marked `[prelude]` when it is a core builtin, and `[toplevel]` otherwise. IRGen resolves a `[prelude]` name to the builtin and a `[toplevel]` name to a top-level function, never to a local.
- **`$!name` opts out.** It stands for the plain name `name`, bound or resolved where the code lands. `derive_eq` uses it for the parameters `a` and `b`, which two separate quotes share:

```ocaml
let meta derive_eq (t : type_decl) : item =
  let n = concat "eq_" (name t) in
  let c = fold_and (map (let (f) => `( $!a.$f = $!b.$f )) (fields t)) in
  `( let $n ($!a : $t) ($!b : $t) : bool ensures $!result <==> $c = $c )
```

## Derives

`@derive(x)` on a type item calls the metaprogram `derive_x` with the item and adds the items it returns after the type. The prelude defines `derive_eq`. For `let pixel = type { r : u8; g : u8 } @derive(eq)` it makes:

```ocaml
let eq_pixel (a : pixel) (b : pixel) : bool
  ensures result <==> (true && a.r = b.r) && a.g = b.g
  = (true && a.r = b.r) && a.g = b.g
```

`=` on two values of a record type calls `eq_<name>`, and `<>` is its negation. Without the derive, comparing records is an error that suggests `@derive(eq)`. Because `eq_pixel` has a postcondition, callers can prove facts about `p = q`, such as `ensures result ==> p.r = q.r`.

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

## Not yet

- operators for a type, and overloading
- nested quotes
- a metaprogram's errors are reported at the expansion site, not inside the metaprogram
- concepts (`let meta Numeric (t : type) : concept`) and generic types
- module-level prelude import control
