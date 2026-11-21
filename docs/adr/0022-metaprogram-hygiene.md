# 22. Metaprogram hygiene: renamed binders, definition-site free names, `$!` to opt out

Date: 2026-11-21

Status: Proposed

## Context

[ADR 0007](0007-metaprogramming-fixed-point-expansion.md) makes metaprograms hygienic by default, with `$!name` breaking hygiene on purpose. It does not say what hygiene means for Pia. Two kinds of capture can happen when a quote is spliced into user code:

- A name the quote binds, such as `t` in `` `( let t = $a in t + $b ) ``, captures a `t` in the spliced `$b`.
- A free name in the quote, such as `add` in the prelude's `+`, is resolved at the expansion site. A local named `add` would change what `+` means.

Full syntax-object hygiene, as in Racket, tracks scope sets on every identifier. That is more machinery than v0 needs, and it would also reject the design's own `derive_eq` example: its `a` and `b` are bound in one quote and used in another.

## Decision

1. Names a quote binds are renamed to fresh names (`t#1`). This covers `let ... in`, parameters, lambda and loop variables, and quantifier binders. The names of quoted top-level items are kept, since they are the metaprogram's output.
2. A free name in a quote resolves at the definition site. A core builtin is marked `[prelude]`, and anything else is marked `[toplevel]`. IRGen resolves `[toplevel]` names among top-level functions only, never among locals.
3. `$!name` stands for the plain name, resolved or bound where the code lands. Quotes that work together, like the two in `derive_eq`, share names this way.
4. Code a quote builds takes the expansion site's location. Spliced code keeps its own.

## Consequences

- Operators keep their meaning whatever the program names its locals.
- Renamed binders appear in diagnostics and counterexamples as `t#1`. A metaprogram that wants readable names uses `$!`, as `derive_eq` does for `a`, `b` and `result`.
- Marking a name `[toplevel]` happens when the quote is built. A name that no top-level item defines fails in IRGen, at the expansion site.
- Scope-set hygiene stays possible later. The names marked by rule 2 would become identifiers with a definition-site scope.
