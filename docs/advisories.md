# Advisories

A Pia object is proved before it is compiled, so its certificate stands for those proofs ([abi.md](abi.md#the-certificate-format)). If a piac or a solver had a soundness bug, an object it proved may rest on a goal that is false. An **advisory** says which piac or solver versions had the bug, and `pia-cert check` then refuses every object they proved until it is rebuilt with a fixed piac, or accepted by name ([ADR 0073](adr/0073-prover-identity-abi-version-and-advisories.md)).

## Published advisories

| Advisory | Severity | Affected | Fixed in | What went wrong |
| --- | --- | --- | --- | --- |
| [PIA-2026-0001](https://github.com/deanberris/pia-lang/blob/main/security/advisories/PIA-2026-0001.toml) | unsound | piac before `0.0.0+720` | [#496](https://github.com/deanberris/pia-lang/pull/496) | Termination was checked only for direct recursion, so two lemmas that call each other could prove `ensures false` |

Every published piac before `0.0.0+720` predates certificate format 3, and so records no piac version. `pia-cert check` already refuses those objects for having no Pia ABI version, so PIA-2026-0001 is a record of the bug more than a new refusal.

## What an advisory says

An advisory is a short file in [`security/advisories/`](https://github.com/deanberris/pia-lang/tree/main/security/advisories), reviewed like any other change:

```toml
id = "PIA-2026-0001"
summary = "Termination was checked only for direct recursion, so mutually recursive lemmas could prove false goals"
piac = { introduced = "0.0.0+0", fixed = "0.0.0+720" }
engines = ["intervals"]          # optional: only objects proved with one of these
solver = { z3 = { introduced = "4.15.0", fixed = "4.15.2" } }   # optional
severity = "unsound"             # "incomplete" is recorded but never revokes
fixed_by = "https://github.com/deanberris/pia-lang/pull/496"
```

A certificate **matches** when its `prover` falls in the piac range, from `introduced` up to but not including `fixed`, or one of its `solver` lines falls in that solver's range. An advisory that names `engines` matches only certificates whose `engines` line includes one of them. piac lists, in a fixed order, `intervals` (interval analysis), `z3`, `int-blast` ([ADR 0066](adr/0066-int-blasting-for-nonlinear-goals.md)), `proof-cache` (a goal answered by `--proof-cache`), `generic` (an instance proved by its generic's proof over sorts, [ADR 0043](adr/0043-generic-definitions-proved-once.md)), `lean`, and `theory:<name>` for each library theory whose axioms a proof used. A certificate with no `engines` line, from a piac before this list, could have used any engine, so it matches too. piac versions are compared by their commit count on `main` (`0.1.0+512.9f3c2e1a7b04` is commit 512), so every build on `main` has its place in a range. An unstamped piac records `dev`, which no range covers.

Publishing an advisory goes with the fix and a regression test in `tests/verify/` that the faulty piac proved and the fixed one refuses.

## Checking a build

The advisories are compiled into `pia-cert`, so every `pia_library` build checks its objects against every advisory older than the tools:

- `pia-cert check a.o b.o` refuses each object an advisory matches. The refusal names the module, the version that proved it, the advisory, and the piac to rebuild with.
- `pia-cert check --advisories=<dir> a.o b.o` adds the advisories in a newer directory, so an old toolchain can be checked against today's list. A file there replaces a compiled-in advisory with the same id.
- `pia-cert check --accept-advisory=PIA-2026-0001:Image.Pixels ...` lets that one module through. The acceptance is printed as a trusted item (`trusted advisory PIA-2026-0001 Image.Pixels`), so trusting a known-faulty proof is never silent. An acceptance that names an unknown advisory is an error, and one that matches nothing draws a warning.
- `pia-cert check --require-released ...` also refuses objects from an unstamped (`dev`) piac, for a deployment that wants only published compilers.
- `pia-cert advisories` lists the advisories the check applies, and `--advisories=<dir>` adds to the list.

Proofs are deterministic, so the fix for a refused object is to rebuild it with a fixed piac. In Bazel that happens anyway when piac changes.

## Not built yet

These parts of ADR 0073 come in later steps:

- Solver advisories should also make piac refuse proof cache entries from a revoked solver (step 4).
- `piac link --trust-report` should list accepted advisories (step 3 prints them from `pia-cert check` only).
- The runtime check at launch and in `Pia.Dl.open` waits for the certificate check in abi.md, Layer 2.
