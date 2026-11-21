# 25. Sanitizers check the edges of the proof

Date: 2026-11-21

Status: Proposed

## Context

Dean wants the runtime core to support compiler-rt's sanitizers (ASan, TSan, UBSan and others). Proved Pia code cannot have the bugs they find, but Pia programs call foreign code, trust `extern` contracts and `assume`s, and depend on the verifier, IRGen and codegen being right ([ADR 0023](0023-minimal-core-self-hosted-stdlib.md)). The detail is in [docs/stdlib.md](../stdlib.md#sanitizers-compiler-rt).

## Decision

- `piac --sanitize=address|thread|undefined|contracts` (a list). `address` and `thread` use LLVM's ASan and TSan passes, so Pia and C in one binary share one runtime. `undefined` turns every unproved goal into a run-time check. `contracts` checks every foreign `ensures` and every `assume` at run time.
- ASan does not instrument accesses whose bounds were proved, unless `--sanitize-proved` asks it to. That build is the check on the verifier. TSan instruments everything.
- `Pia.Mem` poisons arena memory for ASan. In a sanitized build, `Pia.Rt` leaves fatal signals to the sanitizer runtime and adds the Pia trap site through `__sanitizer_set_death_callback`. Sanitized builds carry DWARF.
- The runtimes are built from the pinned llvm-project with rules_foreign_cc, so they match the instrumentation.
- Bazel configs `asan`, `tsan` and `ubsan` set the C++ toolchain features, which `pia_object` maps to `--sanitize`. `contracts` is a Pia build setting.

## Consequences

- A sanitizer report in proved code is a compiler bug, which makes sanitized test runs a soundness test.
- Each sanitized configuration builds compiler-rt and doubles test time, so CI runs them on main first.
- MemorySanitizer and HWASan are out on macOS arm64. libFuzzer is the next candidate, for the trusted boundary and the image decoders.
