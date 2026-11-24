A persistent Pia REPL. Pia looks like OCaml; every definition is proved before it joins the environment, and a failed cell commits nothing and returns counterexamples.

- One `execute` is one cell: items, an expression to prove and run, or a command (`:env`, `:type e`, `:proof f`, `:redef code`, `:load file`).
- `let` is the only binding form: `let f (a : u8) (b : u8) : u16 = a + b`, then `f 40 2`. Types are values: `let level = type | Dark | Bright`.
- Integers are bounded (`u8`, `i64`, `usize`, `int{0..99}`); overflow, indexing and narrowing are goals.
- After the return type: `requires p`, `ensures p` (`result`, `old e`). Loops take `invariant p`; `while` also `decreases m`. Callers see only a callee's contract, except a loop-free function of scalars, whose body unfolds.
- No shadowing of locals, parameters, functions or builtins (`add`, `len`): use `x'`, or `:redef`.
- Comments are `(* *)` and `\` to the end of the line, not `//`.
- Put facts in types (`int{0..99}`) before `requires`.

Before writing more than a few lines, send `:help <topic>` with `execute` (also resources `pia://guide/<topic>`):
