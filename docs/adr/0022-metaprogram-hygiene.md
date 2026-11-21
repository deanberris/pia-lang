# 22. Hygiene and name lookup: no shadowing, renamed quote binders, qualified names, ADL

Date: 2026-11-21

Status: Accepted

## Context

[ADR 0007](0007-metaprogramming-fixed-point-expansion.md) makes metaprograms hygienic by default, with `$!name` breaking hygiene on purpose. It does not say what hygiene means for Pia, or how names are found once modules arrive. When a quote is spliced into user code, two kinds of capture can happen.

**A name the quote binds captures a name in spliced code.**

```ocaml
let meta operator ( +^ ) : prec 6 left = let (a) (b) => `( let t = $a in t + $b )
let f (t : u8) (x : u8) : u16 = x +^ t
```

Spliced naively, this is `let t = x in t + t`: it type checks and silently computes `2x`. Lexical scoping cannot catch this, because after splicing the wrong `t` really is the closest binding.

**A free name in the quote is captured at the expansion site.** The prelude's `+` expands to the builtin `add`. In `let scale (add : u8) (x : u8) : u8 = x + add`, resolving `add` at the expansion site finds the parameter.

Shadowing in user code causes the same confusion without any metaprogram. Once there are modules, a helper that a quote in module `M` calls would also resolve against the program that uses the quote, not against `M`.

Full syntax-object hygiene, as in Racket, tracks scope sets on every identifier. That is more machinery than v0 needs, and it would also reject the design's own `derive_eq`: its `a` and `b` are bound in one quote and used in another.

## Decision

1. **No shadowing.** A binding written in the source may not reuse a name that is visible where it is written. That covers a local in scope, a top-level function, a type, and a core builtin (`add`, `eq`, `and`, ..., `len`, `old`). Parameters, `let ... in`, loop variables and quantifier binders are all checked. Breaking the rule is an error. Assigning to a `mutable` local is not shadowing.
2. **Names a quote binds are renamed.** A `let ... in`, parameter, lambda or loop variable, or quantifier binder inside a quote gets a fresh name (`t#1`), so it can never capture or shadow a name in spliced code. The names of quoted top-level items are kept, since they are the metaprogram's output. A name that the generated code clashes with, such as a hand-written `eq_pixel`, is reported as already defined.
3. **Free names in a quote are qualified.** A free name refers to its definition at the metaprogram's site. Before modules exist, a core builtin is marked `[prelude]` and anything else `[toplevel]`. IRGen resolves `[prelude]` to the builtin and `[toplevel]` among top-level functions, never among locals. With modules, quotes produce module-qualified paths instead (`prelude.add`, `M.pow`), and the marks go away.
4. **`$!name` opts out.** It stands for the plain name, bound or resolved where the code lands. Quotes that work together, like the two in `derive_eq`, share names this way. Rule 1 still applies to the code it produces.
5. **Argument-dependent lookup for operators and derives on types.** An operator declared for a type (`let meta operator ( + ) for vec<T, k>`), and a `derive_x` for a type, are found in two places. One is the module that defines the argument's type. The other is the adapter modules the program imports explicitly. Finding more than one candidate is an ambiguity error, never first-match. Built-in integer types use the prelude's operators. Both arrive with modules (M8) and operators for a type.
6. **Locations.** Code a quote builds takes the expansion site's location. Spliced code keeps its own.

## Consequences

- An operator always means its declaration, whatever the program names its locals, and an unqualified name always means the one visible binding. Readers never have to work out which of two same-named bindings is meant.
- Some OCaml habits are errors in Pia, such as `let x = x + 1 in ...` and an inner loop reusing `i`. A mutable local, or a new name, replaces them.
- Renamed binders appear in diagnostics and counterexamples as `t#1`. A later change keeps the original name with a hidden scope id, prints it as `t (from +^)`, and lets the language server jump from it to the binder in the quote.
- Scope ids should come from the expansion site, not a global counter, before generated names can reach module interfaces. Otherwise an unrelated edit would change them and force recompiles (ADR 0010).
- Scope-set hygiene stays possible later. The names marked by rule 3 would become identifiers with a definition-site scope.
