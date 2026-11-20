# 19. Grammar disambiguation rules

Date: 2026-11-20

Status: Proposed

## Context

The design's syntax is OCaml-like: application by juxtaposition, `=` for both binding and equality, items without terminators, and types that are values. Writing the grammar down ([`grammar.md`](../grammar.md)) and parsing every design example with a reference parser exposed these ambiguities:

- A contract predicate and the body share `=`: `ensures total g = old (total g) - drained g` followed by `= step g` has two readings.
- A bare top-level metaprogram call (`tiled_matmul `sgemm_4x16 f32 4 16 64 4`) after a definition reads as more arguments to that definition's last expression.
- `sum<i64> xs` and `a < b` both use `<`.
- `forall i in 0..n. p` uses `.`, which is also field access.
- `borrowed in [u8] -> [pixel]` could put the modifiers on the whole function or on its parameter.

## Decision

1. Comparisons do not associate, and a contract predicate takes the longest reading that still leaves a body. Then the `=` after a complete comparison starts the body.
2. Top-level items start in column 1. The lexer inserts an item separator before a column-1 token that can start an item, outside brackets, `sig`/`struct ... end` and `do ... done`. `;;` is an explicit separator.
3. `<` straight after an identifier opens explicit type arguments. Less-than needs a space before it.
4. `{` straight after an identifier opens a range type (`int{0..255}`).
5. A dot followed by whitespace ends quantifier binders.
6. Modifiers before a function type belong to its first parameter. They come in a fixed order: ownership, then access, then mutability.
7. `==>` (implication) is added to the bootstrap operator table at level 1, below `||`, because contracts need it.
8. `step` is a keyword only inside a `for` header. The parameter modifiers, `par_for` and `mod` are reserved words.
9. `...` is a hole token. It parses wherever the design's sketches use it, and Sema rejects it.

## Consequences

- Every example in `design.md` parses unchanged, and the tests pin each rule.
- Spacing is significant in three places (`name<`, `name{`, `. `). A formatter that always spaces binary operators makes these rules invisible in practice.
- The layout rule is the only indentation sensitivity. A top-level body written flush left in column 1 starting with an identifier would split, so bodies are indented, as in all the examples.
- The C++ parser (M2) can implement rule 1 deterministically. It parses the predicate greedily, and if no body `=` follows, it splits at the last top-level `=` of the final clause.
- Reserving `in`, `out` and `fixed` takes them away as names.
