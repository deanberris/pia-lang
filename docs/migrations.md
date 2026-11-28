# Migrations

Pia changes before 0.1.0, and sometimes after. Each change after which source that piac accepted is rejected, or means something else, ships a **migration rule** in the same pull request ([ADR 0073](adr/0073-prover-identity-abi-version-and-advisories.md#5-every-breaking-change-ships-a-migration)). A rule finds the old form in your source. If a mechanical rewrite is safe, it rewrites it. If not, it says what to write instead, for you or an agent to decide.

## Running it

`piac migrate <file>...` applies the rewrites of every rule, in the order the changes landed, in place, until none applies. It then proves each file it changed with `piac --verify`, because a rewrite is checked by proof, not trusted. Flags such as `--iface-path=<dir>` are passed on to that proof.

- `--from=<version>` runs only the rules introduced after that piac version. The version is `piac --version`'s first line, or the `prover` line of a certificate the old code was built with (`pia-cert dump`). Without it, every rule runs.
- `--check` writes nothing. It fails when a rewrite would apply, which keeps a repository migrated in CI.

A rule that needs a person prints a line in the shape of a lint, `file:line:col: [rule] what to do`, with the quick fix the language server offers for it. These lines never fail `--check`: only a person can tell whether the old meaning was meant.

## Deprecated forms

When an old form still parses for one release after its change, every build reports it as a `deprecated` warning that names its rule, and the language server offers the rewrite as a quick fix. After that release, the old form is an error. No flag turns the warning off, so old source is never accepted silently.

## The rules

| Rule | Since piac | What changed | What it does |
| --- | --- | --- | --- |
| `type-makes-distinct` | `0.0.0+634` ([ADR 0064](adr/0064-distinct-types.md)) | `let blk = type int{0..63}` used to be another name for `int{0..63}`; it is now a new type, and another name is `let blk = int{0..63}` | Suggests dropping `type` where you meant another name, as a quick fix. A record, a variant or a refinement after `type` was always a new type, so it is not flagged. Only `piac migrate` runs it, since in a build it would flag every distinct type. |

Its test is [tests/migrate/type_makes_distinct.pia](https://github.com/deanberris/pia-lang/blob/main/tests/migrate/type_makes_distinct.pia).

## Writing a rule

A rule lives in `src/migrate/rules/`, one file each, registered in `src/migrate/Migrate.cpp`. It has an id, the piac version that introduced the change, and a matcher over the parsed syntax tree, before metaprograms run. For each old form, it reports a lint named after the rule, with the rewrite as the lint's edits:

- A safe rewrite is marked preferred, and `piac migrate` applies it. It must be idempotent, and must leave everything outside its span as it was.
- A rewrite that depends on intent is marked not preferred. It is offered as a quick fix, never applied blindly.

A rule for a deprecated form sets `inBuilds`, so piac and the language server report it in every build. Each rule has a test in `tests/migrate`.
