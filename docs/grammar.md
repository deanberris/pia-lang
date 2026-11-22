# Pia grammar

Status: accepted for milestone M1 ([#2](https://github.com/deanberris/pia-lang/issues/2)), 2026-11-20. The disambiguation rules are recorded in [ADR 0019](adr/0019-grammar-disambiguation.md).

This document is the specification. Two files make it executable:

- [`grammar/pia_lexer.py`](../grammar/pia_lexer.py) is the reference lexer, including the layout rule.
- [`grammar/pia.lark`](../grammar/pia.lark) is the reference phrase grammar, run by Lark's Earley parser.

[`tests/grammar/test_grammar.py`](../tests/grammar/test_grammar.py) parses every `ocaml` code block in [`design.md`](design.md), the cases in `tests/grammar/valid/`, and checks that every case in `tests/grammar/invalid/` is rejected. The C++ front end (M2) must accept and reject the same corpus.

Run the tests with `pip install -r tests/grammar/requirements.txt` and then `python3 tests/grammar/test_grammar.py`. Bazel will wrap this as a `py_test` in M0.

## Notation

The phrase grammar uses EBNF. `x?` is optional, `x*` is zero or more, `x+` is one or more, `( ... )` groups, `|` separates alternatives, and quoted text is a literal token. Names in `UPPER_CASE` are tokens from the lexical grammar.

## Lexical grammar

### Whitespace and comments

Spaces, tabs and newlines separate tokens. There are three kinds of comment ([ADR 0029](adr/0029-comments-as-syntax-and-literate-pia.md)):

| Comment | Spelling | Notes |
| --- | --- | --- |
| Block | `(* ... *)` | Nests, as in OCaml. Because `(*` always opens a comment, the multiplication operator value is written `( * )` with spaces |
| Doc | `(** ... *)` | A block comment that documents the code after it. `(**)` and `(***` are ordinary comments |
| Line | `\` to the end of the line | Backslash is used nowhere else outside strings. `//` and `--` stay free for operators, and `#` for directives |

Comments never change how a program parses, and they do not count for the layout rule. They are not thrown away either.

### Comments in the syntax tree

The parser keeps every comment as a `Comment` node attached to the node it describes, beside that node's children. Each has a style (`line`, `block`, `doc` or `prose`), a place and its text, which is the content without delimiters, trimmed, and with the indentation its later lines share removed. Line comments alone on consecutive lines are one comment.

- A **trailing** comment has code before it on its line and none after it. It goes to the outermost node that ends at the token before it and starts on that line; if none starts on that line, as after `done`, to the innermost node that ends there. A `;`, `,` or `in` before the comment is skipped, so `let m = n + 1 in  \ one more` documents `n + 1`. After a token that leads into what follows (`=`, `->`, `=>`, `<-`, `then`, `else`, `with`, `|` or an opening bracket), a comment leads instead.
- Any other comment is **leading** on the outermost node that starts at the next token, looking past opening brackets. A blank line in between makes it **detached**, like a section heading. Sequences, parameter lists, contract lists and other groups never take a comment; their first member does.
- A comment with no code after it is detached on the program.

`piac --dump-ast --comments` shows where each comment went.

### Literate files

A file whose name ends in `.pia.md`, or any file with `piac --literate`, is Markdown. Only fenced blocks whose info string is `pia` are code; other fences are prose. A code block must close every bracket it opens, and the last one needs its closing fence. Lines and columns are those of the Markdown file.

The prose between two code blocks is one `prose` comment, leading on the first item of the block after it. Prose after the last block is detached on the program.

### Identifiers and keywords

```ebnf
IDENT = ( letter | "_" ) { letter | digit | "_" | "'" } ;
```

A prime (`'`) may follow the first character, as in `x'` and `x''`. Pia has no shadowing ([ADR 0022](adr/0022-metaprogram-hygiene.md)), so primes are the usual way to name a value related to `x`. Nothing else in the language uses `'`: there are no character literals, and type variables are written `<T>`.

Reserved words:

```
let rec meta in type of where if then else match with for spread while do done
requires ensures invariant decreases assert assume forall exists
interface sig module struct end import operator true false
borrowed moved out inout fixed mutable mod handle defer as
```

`step` is a keyword only inside a `for` or `spread` header, between the keyword and `do`. Everywhere else it is an ordinary identifier, so a function can still be called `step`.

`spec` and `lemma` are keywords only right after `let` or `let rec`, when a name follows: `let spec sorted ...` defines a spec function and `let lemma split ...` a lemma ([verifier.md](verifier.md#spec-functions-and-lemmas)). `let spec = 3` binds a value called `spec`.

Names such as `result`, `old`, `dyn`, `concept`, `adapter`, `item`, `ident`, `prec`, `left` and `right` are ordinary identifiers that the prelude or the contract checker gives meaning to.

### Literals

```ebnf
INT    = digits [ suffix ] | "0x" hexdigits [ suffix ] | "0b" bindigits [ suffix ] | "0o" octdigits [ suffix ] ;
FLOAT  = digits "." digits [ exponent ] [ suffix ] | digits exponent [ suffix ] ;
suffix = ( "u" | "i" | "f" ) digits | "usize" | "isize" ;     (* 42u8, 1i64, 0.5f32, 3usize *)
STRING = '"' { char | escape } '"' ;
```

Digits may contain `_` separators (`1_000_000`). A float needs a digit after the point, so `0..n` lexes as `0`, `..`, `n`.

### Operators

An operator is a maximal run of `+ - * / < > = | & ^ ~ ! % ?`. A few spellings are reserved by the grammar:

| Token | Meaning |
| --- | --- |
| `=` | Binding, and the equality operator |
| `->` | Function type, match arm |
| `=>` | Function literal |
| `<-` | Assignment |
| `\|` | Variant, match arm, union type, refinement |
| `?` | Passes an error on: `e?` ([ADR 0028](adr/0028-error-propagation-and-cleanup.md)) |

Every other operator gets its precedence from the operator table. The table comes from the `let meta operator` declarations in the prelude ([meta.md](meta.md#operators)) and in the program. Operators not in the table get a level from their first character, as in OCaml.

| Level | Operators | Associativity |
| --- | --- | --- |
| 1 | `==>` `<==>` | right |
| 2 | `\|\|` | right |
| 3 | `&&` | right |
| 4 | `=` `<>` `<` `>` `<=` `>=` | none |
| 5 | `..` (range) | none |
| 5.5 | `<<` `>>` | left |
| 6 | `+` `-` `+\|` `-\|` | left |
| 6.3 | `\|` (bitwise or, inside brackets) | left |
| 6.4 | `^` | left |
| 6.5 | `&` | left |
| 7 | `*` `/` `%` `mod` | left |
| prefix | `-` `~` | |
| | application | left |
| | `.f` `.[i]` `name<...>` | postfix |

The levels match the design's `let meta operator ( + ) : prec 6 left`. A level may have one decimal place, as in `prec 6.5`. A user operator declared at a level above 7 binds tighter than `*` and looser than application.

Unlike C, the bit operators bind tighter than comparisons, so `x & mask = 0` is `(x & mask) = 0`. Because `|` also separates variants and match arms, it is bitwise or only inside parentheses, brackets or braces, and not directly in a match arm's body there: `| A -> (x | y)` needs its parentheses. `~x` is the builtin `bnot x`. The lexer reads a run of operator characters as one token, so `a&~b` is the operator `&~`; write `a & ~b`.

### Other punctuation

| Token | Spelling | Notes |
| --- | --- | --- |
| `QUOTE_OPEN` | `` `( `` | Quoted syntax, closed by `)` |
| `QIDENT` | `` `name `` | A quoted identifier, e.g. `` `sgemm_4x16 `` |
| `SPLICE_IDENT` | `$name`, `$!name` | Splice a metaprogram value. `$!name` escapes hygiene ([meta.md](meta.md#hygiene)) |
| `SPLICE_OPEN` | `$(` | Splice an expression, closed by `)` |
| `ATTR`, `ATTR_OPEN` | `@name`, `@name(` | Attributes; arguments follow `(` with no space |
| `TARGS_OPEN` | `<` straight after an identifier | Explicit type arguments, see below |
| `LBRACE_ADJ` | `{` straight after an identifier | Range types such as `int{0..255}` |
| `DOT_LBRACKET` | `.[` | Indexing and slicing |
| `QDOT` | `.` followed by whitespace | Ends quantifier binders |
| `DOT` | `.` followed by anything else | Field access and paths |
| `DOTDOT` | `..` | Ranges |
| `HOLE` | `...` | A hole, see below |
| `SEMI`, `SEP` | `;`, `;;` | Sequencing; explicit item separator |

### Adjacency rules

Spacing decides three things.

1. **`name<` opens type arguments.** `sum<i64> xs` and `vec<u8, 16>` instantiate. Less-than must be written with a space: `a < b`. Writing `x<y` is an error that names the rule. Inside the list, `>` closes it, and `>>` closes two lists.
2. **`name{` opens a range type.** `int{0..255}` is a range-refined integer. Bare `int`, with no brace straight after it, is the spec-only unbounded integer ([verifier.md](verifier.md#spec-only-int-and-real)). A record literal passed to a function is written with a space, `f { x = 1 }`.
3. **A dot followed by whitespace ends quantifier binders.** In `forall i in 0..n. p i` the dot is `QDOT`. Field access never has a space after the dot.

### Layout rule

Pia is not indentation-sensitive, except in one place. Top-level items start in column 1, and the lexer inserts an item separator (`SEP`) before a token in column 1 when three things hold:

- it is outside every bracket, `sig`/`struct ... end` and `do ... done`
- it can start an item: an identifier, literal, `let`, `interface`, `module`, `import`, `(`, `[`, a quote or a splice
- it is not the first token in the file

So a continuation line is either indented or starts with a token that cannot start an item, such as `=`, `|`, `&&` or `end`. This matches every example in the design: `= for i in 0..n do ... done` in column 1 continues the definition above it, and `tiled_matmul ...` in column 1 starts a new item. `;;` is an explicit separator for anyone who wants to put two items on one line.

Without this rule, a bare top-level metaprogram call would be read as further arguments to the expression that ends the previous item.

## Phrase grammar

### Programs and items

```ebnf
program   = [ ( module_header | item ) { SEP item } ] ;  (* ADR 0039 *)
item      = let_item | meta_operator | interface | module | import | expr_item ;
expr_item = application ;                         (* a compile-time call that yields items *)
import    = "import" path ;
path      = IDENT { "." IDENT } ;
```

### Bindings

```ebnf
let_item  = "let" [ "rec" ] [ "meta" ] binder { param } [ ret_annot ] { contract } "=" handled ;
let_in    = "let" [ "rec" ] binder { param } [ ret_annot ] { contract } "=" handled "in" seq ;
handled   = seq [ "handle" [ "|" ] arm { "|" arm } ] ;
binder    = IDENT | SPLICE_IDENT ;
param     = IDENT | SPLICE_IDENT
          | "(" ( IDENT | SPLICE_IDENT ) ":" annot ")"
          | "(" ")" | "(" "..." ")" ;
ret_annot = ":" annot { attribute } | attribute { attribute } ;
contract  = "requires" stmt | "ensures" stmt | "decreases" stmt ;

lambda    = "let" lparam { lparam } "=>" seq ;
lparam    = "(" pattern [ ":" annot ] ")" | "(" ")" ;

meta_operator = "let" "meta" "operator" "(" operator ")"
                [ ":" "prec" ( INT | FLOAT ) ( "left" | "right" | "none" ) ]
                [ "for" type ] "=" seq ;
```

`let` followed by `(` is a function literal. `let` followed by a name is a binding. Pia has no tuple destructuring in `let` today; if it is added, the `=>` still tells the two apart.

### Annotations and types

```ebnf
annot      = modifiers union_type [ "where" stmt ]
           | arrow_type [ "where" stmt ] ;
modifiers  = [ "borrowed" | "moved" ] [ "in" | "out" | "inout" ] [ "fixed" | "mutable" ] ;

type       = arrow_type | union_type ;
arrow_type = arrow_dom "->" type ;
arrow_dom  = modifiers union_type | "(" IDENT ":" annot ")" ;
union_type = app_type { "|" app_type } ;
app_type   = type_atom { type_arg } ;             (* pair u8 f32, adapter Eq f32 *)
type_arg   = type_atom | INT | "(" expr ")" ;

type_atom  = IDENT
           | "type"                               (* the type of types *)
           | IDENT "<" targ { "," targ } ">"      (* vec<u8, 16>, tiled<cell, 256, 256, halo = 1> *)
           | IDENT "{" expr ".." expr "}"         (* int{0..255} *)
           | "[" type "]"                         (* slice, length carried at run time *)
           | "[" type ";" expr "]"                (* array, length known to the prover *)
           | "{" field_decl { ";" field_decl } [ ";" ] "}"
           | "{" IDENT ":" type "|" stmt "}"      (* refinement *)
           | "(" type ")" | "(" ")"
           | SPLICE_IDENT | "$(" expr ")" ;
targ       = type | elem | IDENT "=" elem ;
field_decl = IDENT ":" annot ;
```

Modifiers come in a fixed order: ownership, then access, then mutability. Each one is optional. Before a function type they belong to its first parameter: `borrowed in [pixel] -> [u8]` takes a borrowed input slice.

A type value is an expression:

```ebnf
type_value = "type" ( variants | type ) { attribute } [ "where" stmt ] { attribute } ;
variants   = "|" ctor { "|" ctor } ;
ctor       = IDENT [ "of" app_type ] ;
attribute  = "@" IDENT [ "(" attr_arg { "," attr_arg } ")" ] ;
attr_arg   = stmt | IDENT "=" stmt ;
```

A constructor's payload is one type application. A union or function payload needs parentheses, since `| A of t | B` already means two constructors.

### Expressions

Constructs that extend as far right as possible sit at the sequence level. The rest are ordered by the operator table.

```ebnf
expr   = seq ;
seq    = stmt [ ";" [ seq ] ] | let_in | match | lambda ;
elem   = stmt | "let" lparam { lparam } "=>" elem ;     (* list, record and argument elements *)

stmt   = postfix "<-" stmt
       | "if" seq "then" stmt [ "else" stmt ]
       | "for" pattern "in" or_e [ "step" add_e ] { loop_annot } "do" handled "done"
       | "spread" pattern "in" or_e { attribute } { loop_annot } "do" handled "done"
       | "while" seq { loop_annot } "do" handled "done"
       | quantifier
       | "assert" imp_e | "assume" imp_e
       | type_value
       | sig_value
       | imp_e ;
loop_annot = "invariant" stmt | "decreases" stmt ;

quantifier = ( "forall" | "exists" ) qbinder { qbinder } QDOT stmt ;
qbinder    = IDENT [ ":" type ] | IDENT "in" range_e
           | "(" IDENT ":" type ")" | "(" IDENT "in" range_e ")" ;

imp_e   = or_e [ "==>" ( imp_e | quantifier ) ] ;
or_e    = and_e [ "||" ( or_e | quantifier ) ] ;
and_e   = cmp_e [ "&&" ( and_e | quantifier ) ] ;
cmp_e   = range_e [ cmp_op ( range_e | quantifier ) ] ;
range_e = add_e [ ".." add_e ] ;
add_e   = mul_e { add_op mul_e } ;
mul_e   = unary { mul_op unary } ;
unary   = "-" unary | application ;
application = postfix { postfix } { "?" } ;   (* f x? is (f x)? *)

postfix = atom
        | postfix "." ( IDENT | SPLICE_IDENT )
        | postfix ".[" seq "]"                    (* xs.[i], frame.[0 .. w] *)
        | postfix "<" targ { "," targ } ">" ;     (* sum<i64> *)

atom = IDENT | INT | FLOAT | STRING | "true" | "false"
     | QIDENT | "..."
     | "(" handled ")" | "(" ")" | "(" operator ")"
     | "[" [ elem { ";" elem } [ ";" ] ] "]"
     | "{" field_init { ";" field_init } [ ";" ] "}"
     | "{" postfix "with" field_init { ";" field_init } [ ";" ] "}"
     | "`(" quoted ")"
     | SPLICE_IDENT | "$(" seq ")" ;
field_init = IDENT "=" elem ;

quoted = let_item { [ SEP ] let_item }            (* items *)
       | IDENT ":" type                            (* a declaration: `( add : $t -> $t -> $t ) *)
       | seq ;                                     (* an expression *)

match = "match" seq "with" [ "|" ] arm { "|" arm } ;
arm   = pattern { ( "requires" | "ensures" ) stmt } "->" seq ;
```

`e?` passes an error on ([ADR 0028](adr/0028-error-propagation-and-cleanup.md)): it applies to the whole application before it, so `read_all m f?` is `(read_all m f)?`, and it binds tighter than every binary operator. `handle` ends the expression before it and attaches to what encloses it: a function body, a `let` value, a parenthesised expression (which is how a `let ... in` scope gets one) or a loop body. Its arms are parsed like a `match`'s. `defer` is reserved for scope cleanup and is not accepted yet.

### Patterns

```ebnf
pattern      = pattern_core [ "as" IDENT ] ;                          (* NoEntry as e *)
pattern_core = IDENT pattern_atom { pattern_atom } | pattern_atom ;   (* Num n *)
pattern_atom = IDENT | INT | STRING | "true" | "false" | SPLICE_IDENT
             | "(" pattern ":" type ")" | "(" pattern ")"
             | "{" pfield { ";" pfield } [ ";" ] "}"
             | "[" pattern "]" | "[" pattern ";" pattern "]" ;       (* types *)
pfield       = IDENT [ "=" pattern ] ;
```

`_` is an ordinary identifier pattern that binds nothing. `p as x` matches `p` and also binds `x` to the whole value, as in a handler arm `| NoEntry as e -> Err (Wrapped e)`.

### Modules and interfaces

```ebnf
interface = "interface" IDENT { attribute } "=" "sig" { sig_item } "end" ;   (* @abi(c), @within(...) *)
sig_item  = "let" binder ":" annot { attribute } { contract }    (* exported symbol *)
          | "let" binder "=" type_value                           (* exported type *)
          | "..." ;
sig_value = "sig" { sig_item | concept_item } "end" ;          (* a concept's body *)
concept_item = "include" type                                  (* "include" is contextual *)
             | "let" "lemma" IDENT { param } { contract } ;   (* a law *)
adapter   = "let" "adapter" IDENT ":" type "=" "struct" { item } "end" ;  (* "adapter" is contextual *)
module    = "module" IDENT [ ":" path { "," path } ] "=" "struct" { item } "end" ;
module_header = "module" path { attribute } [ ":" path { "," path } ] ;  (* a file's first item only *)
```

A file is one module. Its first item may be a module header, `module Pixels : PixelOps, PixelCodec`, which names the module and the interfaces it claims; the rest of the file is the module's body. A `let` is private unless one of those interfaces lists it, and each item an interface lists is checked against the module, with contracts proved ([ADR 0039](adr/0039-module-and-interface-syntax.md)). A header anywhere but first is an error. `module M : I = struct ... end` is a module nested in a file.

## Disambiguation

The grammar is ambiguous in a few places. Each one is settled by a rule, and each rule has a test in `Disambiguation` in the test file.

1. **Contract predicate before the body.** A definition with contracts reads `let f ... ensures p = body`, and `p` may itself contain `=`. The predicate takes the longest reading: if it can end after a top-level comparison, it does, and the next `=` starts the body. `ensures total g = old (total g) - drained g = step g` therefore ensures `total g = old (total g) - drained g`. If the last predicate has no comparison (`requires sorted xs = body`), there is only one reading. A body that is itself a comparison, after a predicate that is not, needs parentheses. A hand-written parser does this by parsing the predicate greedily and, if no body `=` follows, splitting the last top-level `=` of the final clause.
2. **Comparisons do not associate.** `a = b = c` is an error. This is what makes rule 1 work.
3. **Layout.** A column-1 token that can start an item starts one. See [Layout rule](#layout-rule).
4. **`name<` is instantiation.** See [Adjacency rules](#adjacency-rules).
5. **Named type arguments.** In `tiled<cell, 256, halo = 1>`, `halo = 1` is a named argument, not a comparison.
6. **Type or value.** Since types are values, `sum<f32, eq_f32>`, `pair u8 f32` and `adapter Numeric (fast f32)` have arguments that could be types or expressions. The parser accepts both readings and Sema decides.
7. **Right-extending constructs.** `let ... in`, `match`, function literals, `if` and quantifiers extend as far right as they can, as in OCaml. Inside a list, record or argument list, a function literal stops at the next `;` or `,`. A nested `match` needs parentheses.
8. **Modifiers before a function type** belong to its first parameter.

## Holes

`...` is a hole. The parser accepts it as an expression, a parameter list, a contract predicate, an interface item or a module body, so sketches like the ones in the design parse. Sema reports every hole as an unfinished definition, so a program with holes never compiles.

## Not yet in the grammar

These are in the design's direction but have no syntax yet. Each will get an ADR when it is needed.

- Tuple types and tuple patterns
- Guards on match arms (`when`)
- Placement and task-graph syntax beyond `spread` and `@place` (M12)
- Doc comments
