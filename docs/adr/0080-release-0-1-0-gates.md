# 80. Releases ship their libraries in .0 and finish their demo in patches; the gates for 0.1.0

Date: 2026-11-28

Status: Proposed

## Context

Dean set out the road to 1.0 on 2026-11-27 as five releases, each defined by a demo, and agreed the plan on 2026-11-28 ([roadmap](../roadmap.md)). He also set a release policy: "libraries ship in the .0 release; patch releases continue until the demo is complete".

[ADR 0067](0067-release-0-1-0-a-proved-small-llm.md) defined 0.1.0 before that policy, as a single tag gated on the whole LLM demo, including the GPU matmuls (its section 6 and answer 2). The roadmap also puts the earlier flagship demos, stream delineation and sediment transport ([ADR 0016](0016-stream-delineation-flagship-demo.md), [ADR 0055](0055-sediment-transport-in-fixed-point.md)), in 0.1.0.

This ADR states the policy once for every release, sets how issues are tracked against releases, and restates 0.1.0's gates under the policy. ADRs 0081 to 0085 give the gates for 0.2.0 to 1.0.

## Decision

### 1. The release policy

- **A release `x.y.0` is tagged when its libraries are done**: built, every goal proved, documented on pia-lang.dev and in the skill pack, and covered by the proof benchmark. Its demo may still be in progress.
- **Patch releases `x.y.1`, `x.y.2`, ... follow** as the demo comes together. Each is a working, proved tree; a patch can add library functions the demo turns out to need, but not new language features.
- **The release whose demo is complete closes the series.** Its release notes say so, and the demo is written up on pia-lang.dev. Work for the next release can merge at any time, behind its own `.0`.
- **Every tag, `.0` or patch,** is cut by CI from `main` when `bazel test (Linux x86_64)`, `bazel test (macOS arm64)` and the proof benchmark are green, `piac --version` prints the tag, the trust report for the standard library lists only named trusted items, and the licence audit finds nothing GPL in the build, the release or anything it fetches.

### 2. Tracking

Each release has a GitHub project, `Pia 0.1.0` to `Pia 1.0`, and every issue carries three kinds of label:

| Label | Meaning |
| --- | --- |
| `release: 0.1.0` ... `release: 1.0`, `release: post-1.0` | The release the issue is part of |
| `P0` | Blocks the release's `.0` tag: a library or gate in section 1 |
| `P1` | Blocks the demo, so the series cannot close without it |
| `P2` | Should land in this release; it would weaken the release to slip it |
| `P3` | Could land in this release, or slip to the next without harm |
| `P4` | Nice to have, whenever there is time |
| `infra`, `performance`, `code health`, `documentation`, `demos` | The kind of work, where one fits: build, CI and tooling; speed of proofs, builds or generated code; cleanups and debt; the site, the skill pack and ADRs; the demos themselves |

A new issue gets a release and a priority when it is filed. An issue moves between releases by changing its label, with a comment that says why.

### 3. The gates for 0.1.0

0.1.0 is proved numerics on Apple Silicon, CPU and GPU.

**0.1.0 is tagged when its libraries are done:**

- Floats: ADR 0067's F1 to F6, so `f32` and `f64` have real-valued specifications, rounding error, γₙ reduction lemmas, `@fp(reassoc)` and `~= within` (ADR 0038, ADR 0012). Milestone M11 ([#12](https://github.com/deanberris/pia-lang/issues/12)) is closed.
- `Pia.Math` without libm: `sqrt` through `@lower` (ADR 0078), `exp`, `sin` and `cos` with Lean lemmas (X1 to X3).
- `Pia.Nn`'s kernels (K1 to K3) and `Pia.Llm` (M1 to M4), with the scalar path matching `run.c`'s greedy tokens on `stories260K`.
- `@lower` and `@schedule` (ADR 0065) steps 1 to 5, with proved integer and float `linalg.generic`, and `Pia.Linalg`.
- `spread` with collectives (M12, [#13](https://github.com/deanberris/pia-lang/issues/13)) on the CPU.
- Boxes of a concept (the ADR 0046 amendment), which Dean asked for before 0.1.0.
- The gates in section 1.

**The 0.1.x series closes when the demos are complete:**

- Stream delineation and sediment transport ([streams.pia.md](../streams.pia.md), [sediment.pia.md](../sediment.pia.md)) run sequentially, on every core with `spread`, and on the GPU, on Dean's M3, with the sediment run's animated GIF written by Pia's own encoder.
- ADR 0067's release checklist (section 6): `stories260K` on the scalar, SIMD and GPU paths, `stories15M` on the GPU with tokens per second against `run.c`, and the trust report listing exactly the items ADR 0067 names.
- GPU code generation through SPIR-V, SPIRV-Cross and Metal (ADR 0065 step 7 and the GPU ADR), with the matmuls on the GPU.
- `docs/llm.pia.md` on the site and doc-tested.

This amends ADR 0067's section 6 and its answer 2: the GPU matmuls still gate the end of 0.1.x, but no longer the 0.1.0 tag.

## Consequences

- People can use floats, `Pia.Math` and the kernels as soon as they are proved, without waiting for the GPU path.
- A `.0` that ships before its demo must not overclaim: its release notes list what the demo still needs.
- Every issue has to be placed in a release with a priority, so the projects show what blocks each tag. Triage is part of filing.
- Patch releases freeze language features, so a feature a demo turns out to need goes into the next `.0`, or the demo waits for it.

## Steps

1. Create the labels and one project per release, and label every open issue.
2. Add the release-notes template and the tagging checklist (section 1) to `tools/release/`, with the licence audit.
3. Tag 0.1.0 when section 3's library gates hold.
