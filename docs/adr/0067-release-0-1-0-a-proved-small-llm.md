# 67. Release 0.1.0 is a small Llama-architecture LLM ported from PyTorch to Pia, proved where a proof means something, running inference on an M3 Mac on CPU SIMD and on the GPU through linalg

Date: 2026-11-24

Status: Accepted (2026-11-24, with Dean's answers to its questions below). Section 6 and answer 2 amended by [ADR 0080](0080-release-0-1-0-gates.md): the GPU matmuls complete the 0.1.x series rather than gate the 0.1.0 tag.

## Context

Dean asked for 0.1.0 to ship when Pia has floats and the linalg work, shown by a large language model ported from PyTorch to Pia: start with a small model, prove what can be proved, and have an inference stack that runs on his M3 Mac.

Where the pieces stand today (main at `738b5ec`):

- **Floats do not exist yet.** `0.5` is a spec-only `real`; a suffixed literal such as `0.5f32` is refused in `genRealConst` (`src/irgen/IRGen.cpp`), and there is no `f32` type in Sema, IRGen, the verifier or codegen. [ADR 0038](0038-float-kernels-against-real-theories.md) (Accepted) designs how float kernels are proved against real specifications, and none of its eight steps is built. [ADR 0012](0012-floating-point-reassociation.md)'s licences and milestone M11 ([#12](https://github.com/deanberris/pia-lang/issues/12)) are open.
- **Reals exist in specs.** `real` and unbounded `int` reach Z3 (ADR 0036, step 1), so spec functions over reals, which ADR 0038's error goals need, already work.
- **linalg is designed, not linked.** [ADR 0065](0065-lowerings-written-in-pia.md) (Proposed) gives `@lower` and `@schedule`, proved lowerings for integer `linalg.generic`, and the GPU route (tile, map to blocks and threads, `convert-gpu-to-spirv`, SPIRV-Cross to MSL, a trusted Metal shim). Its 4x4 integer matmul prototype proved 51 of 51 goals in 17.5 s. piac links none of `linalg`, `tensor`, `gpu` or `spirv` yet.
- **Nonlinear index goals** such as `i * dim + j < len w` are what a transformer's indexing is made of. [ADR 0066](https://github.com/deanberris/pia-lang/pull/421) (Accepted, in review as PR #421) turns on Z3 int-blasting for them, which proved 13 of 13 such goals in about a second each where bit-blasting timed out.
- **Libraries that help:** the JSON library (ADR 0045) reads a safetensors header, `Pia.Mem` allocators and `vec` (ADR 0041, 0046) hold weights and the KV cache, `Pia.Sys.Posix` reads files, and contract-driven tests (ADR 0056) run kernels against references.
- **libm is never trusted** (stdlib rule, 2026-11-21). `exp`, `sin` and `cos` must be written and proved in Pia. `sqrt` is an IEEE 754 operation, correctly rounded by the hardware (`fsqrt` on arm64), so it is in ADR 0038's `round` encoding like `+` and needs no library.
- **Nothing GPL** may be used, bundled or depended on, including the model, its tokenizer and any tool in the release path (Dean's standing rule).

## Decision

### 1. The model: Karpathy's TinyStories Llama checkpoints, `stories260K` first, then `stories15M`

The demo ports the PyTorch `Transformer` of [llama2.c](https://github.com/karpathy/llama2.c) (`model.py`), a Llama 2 architecture trained on the TinyStories dataset, and runs the checkpoints Karpathy published in [karpathy/tinyllamas](https://huggingface.co/karpathy/tinyllamas):

| Checkpoint | Shape | Weights (f32) | Tokenizer | Licence |
| --- | --- | --- | --- | --- |
| `stories260K` | dim 64, 5 layers, 8 heads, 4 KV heads (grouped-query attention), context 512 | about 1 MB | `tok512`, a 512-token SentencePiece BPE that Karpathy trained | MIT (code and weights) |
| `stories15M` | dim 288, 6 layers, 6 heads, context 256 | about 60 MB | Llama 2's 32,000-token SentencePiece vocabulary | MIT for code and weights; the vocabulary file came from Meta's Llama 2 release |

Why this family:

- **It is a real modern LLM, small enough to prove.** Token embedding, RMSNorm, rotary position embeddings (RoPE), grouped-query attention with a KV cache, SwiGLU feed-forward, residuals, a tied output projection, then sampling. This is the architecture of Llama, Mistral and Qwen, so the kernels are the ones a larger port needs, and every shape is a small constant.
- **It is PyTorch at the source.** `model.py` is the PyTorch module the checkpoints were trained with, so "ported from PyTorch" is literal: each method of `Transformer`, `Attention`, `FeedForward` and `RMSNorm` becomes a Pia function with the PyTorch line it ports beside it.
- **It has a reference implementation to test against.** `run.c` in the same repository runs the same checkpoints in f32, so token-for-token agreement under greedy decoding is a test, not a claim.
- **The licence is clean.** MIT, with no GPL anywhere. `stories260K` and `tok512` are entirely Karpathy's own work; `stories15M`'s vocabulary is Meta's, which is not GPL but is not MIT either, so the release ships `stories260K` in its tests and fetches `stories15M` only for the larger demo (open question 1).

Rejected: GPT-2 124M (MIT), which needs LayerNorm, GELU's `tanh`, learned positions and a 50,257-token byte-level BPE, at 500 MB of f32, with no proof that the extra kernels teach anything Llama's do not; and `roneneldan/TinyStories-1M` and its siblings, whose model cards state no licence.

f32 throughout for 0.1.0. bf16 or block-format weights (ADR 0038, step 8) are a later example.

### 2. Weights load from safetensors, checked once at load

A one-off script, `tools/llm/export.py` (PyTorch, BSD; not in the trusted base and not in the build), converts a llama2.c checkpoint to [safetensors](https://github.com/huggingface/safetensors) with the config in the header's `__metadata__`. The Pia side, `Pia.Format.Safetensors`, is pure Pia over bytes read through `Pia.Sys.Posix`:

- an 8-byte little-endian header length, a JSON header parsed by the JSON library into a typed record per tensor (dtype, shape, byte offsets), and the data region;
- proved total on every input: every offset pair is in bounds and ordered, every shape's element count times the dtype size equals its byte range, and a malformed file is an error value, never a crash (the same standard as ADR 0054's codecs);
- `Pia.Llm.Llama.load` then checks each tensor's name and shape against the config, and that every weight is finite with `|w| <= bound`, computing `bound` from the file. Those checks are what the type of the loaded weights records, so the forward pass starts from proved facts about its inputs, not from trust in the file.

### 3. What is proved, and what is not

Each property names the layer that proves it. "Every input" means every token sequence and every weight file that passes the load checks.

| Property | Proved how | Status of the claim |
| --- | --- | --- |
| **Shapes.** Every matmul, slice and cache access agrees with the config | Types and `requires`: the config is a record of constants, and each kernel takes slices whose lengths are stated in terms of it | Proved |
| **Bounds.** No out-of-bounds read or write, including the KV cache at position `pos < seq_len` and GQA's head mapping `h / (n_heads / n_kv_heads)` | Index goals, int-blasted (ADR 0066), with one bounds lemma per indexing map (ADR 0065's prototype finding) | Proved |
| **No NaN, no infinity, no overflow** anywhere in a forward pass | Float intervals (ADR 0038, layer 1) from the load-time weight bound: RMSNorm's output is bounded by `sqrt dim * max |g|`; softmax subtracts the row maximum, so every `exp` argument is `<= 0` and every probability is in `[0, 1]`; the residual stream's bound grows by a computed amount per layer; logits are finite | Proved, for the loaded weights' bound |
| **Termination and memory.** Generation stops after `steps <= seq_len` tokens; every allocation is fallible and handled | Ordinary measures and ADR 0026 | Proved |
| **Kernels equal their specification.** The SIMD, tiled and GPU kernels compute what the scalar Pia kernel says, up to a stated tolerance | ADR 0065's refinement goal for each `@lower`; under `@fp(reassoc)` the tolerance is the order-free γₙ bound (ADR 0038, section on reassociation) | Proved on CPU; on the GPU, proved against the device float model, which is trusted (section 4) |
| **Per-kernel float error.** Each of `matvec`, `rmsnorm`, `softmax`, `silu`, `rope` and `exp` is within a bound of its real-valued specification | ADR 0038 layers 2 and 3: per-operation δ with nlsat for straight-line code, Higham's γₙ lemmas for reductions, `~=` with derived bounds published in interfaces | Proved |
| **`exp`, `sin`, `cos` against the real functions** | Range reduction proved in Z3; the polynomial's distance from the real function proved in Lean with Mathlib (ADR 0061), because Z3 has no `exp` | Proved, with Lean lemmas listed by hash |
| **End-to-end error of the logits** against the real-valued model | Composed from the per-kernel bounds by ADR 0038's `lip`/`err` pair | Derived and reported, not claimed useful: through 5 layers of attention a worst-case bound is likely far looser than the observed error, so the release reports both |
| **Agreement with PyTorch** | Differential test against `run.c` and `model.py`: identical greedy tokens for a fixed prompt set, and the maximum absolute logit difference | Tested, not proved: reductions sum in a different order, so bit-equality is not the goal |
| **Tokenizer.** Encoding terminates, every emitted id is `< vocab_size`, and decoding an encoding gives back the input bytes | BPE merges as a loop with a decreasing measure; byte fallback makes the round trip total | Proved |
| **Sampling.** The sampled id is `< vocab_size`; temperature and top-p keep the distribution's support; the PRNG is the integer xorshift `run.c` uses | Contracts on `sample`; the PRNG is integer code | Proved; the randomness of the PRNG is not |
| **Model quality**: that the stories are coherent, that the weights mean anything | Nothing | Not provable. The demo says so on its first page |

### 4. Execution on the M3, in three stages

The same Pia functions are the specification at every stage. A later stage replaces a body's code, never its contract.

1. **Scalar CPU.** The plain Pia port, compiled by today's codegen (with f32 added) and run by the REPL's JIT. This is the stage that first matches `run.c` token for token. `stories260K` runs interactively at this stage.
2. **CPU SIMD.** `matvec`, `rmsnorm`, `softmax` and the attention dot products vectorised for NEON: first by LLVM's vectoriser under `@fp(reassoc)` (ADR 0012), then with ADR 0065's `@schedule` (tile and vectorise, step 5) where the vectoriser does not. Benchmarked in tokens per second against `run.c` built with `-O3 -ffast-math`.
3. **GPU.** The matmuls (the Q, K, V, O, gate, up, down and classifier projections) lower with `@lower` to `linalg.matvec`/`linalg.matmul` on `memref`, are scheduled with `tile_using_forall` and mapped to threads, go through `convert-gpu-to-spirv`, and SPIRV-Cross writes MSL, which a trusted Metal shim compiles and launches (ADR 0065, section 6). The device's float model (ADR 0038, "Mixed precision and devices") is a trusted theory: it states, for each operation, the precision the Metal Shading Language specification gives with fast math off (compiled with fast math off), and treats subnormals as possibly flushed, so the tolerance contracts account for both. Softmax, RMSNorm and sampling stay on the CPU for 0.1.0. For `stories260K` the GPU will be slower than the CPU, since each matmul is tiny; the GPU stage is measured on `stories15M`, where it can win.

Prompt processing runs the same per-token path as generation in 0.1.0 (batched prefill with `linalg.matmul` is a later step).

### 5. Dependency PRs

Sizes: **S** is about a day of work and one PR, **M** two to three days, **L** a week or more, possibly split. Owners are the threads already working in the area.

**Floats (M11, ADR 0012, ADR 0038)**

| # | PR | Size | Status |
| --- | --- | --- | --- |
| F1 | `f32` and `f64` types: suffixed literals, arithmetic, comparisons, conversions to and from integers, `to_bits`/`from_bits`, strict IEEE codegen (no flush-to-zero) | L | done (#440, #452) |
| F2 | The verifier's float encoding, step 1 of ADR 0038: `to_real`, `finite`, `eps`, `tiny`, the `Float` concept with builtin adapters, float intervals in the interval stage; bit-precise FP behind `@solver(fp_exact)` | L | done (#565): `to_real`, `finite`, `eps`, `tiny`; the `Float` concept, float intervals and `fp_exact` remain |
| F3 | Step 2: the `round` encoding with per-operation δ, nlsat for straight-line error goals | M | done (#565), as an absolute error bound per operation rather than a fresh δ, which Z3 decides far faster |
| F4 | Step 3: `Pia.Float.Error` with γₙ, and the summation, dot product and matrix-vector lemmas | M | sum and dot done (`lib/Pia/Float/Error.pia`); matvec is K1 |
| F5 | Step 4 plus ADR 0012's licence: `@fp(reassoc)` and `contract` in codegen, order-free bounds | M | not started |
| F6 | Step 6: `a ~= e within b`, derived bounds published in interfaces | M | not started |
| F7 | Step 5: device float models in placement, with the Apple GPU's model | S | not started; needed only for stage 3 |

**Maths without libm (`Pia.Math`)**

| # | PR | Size | Status |
| --- | --- | --- | --- |
| X1 | `sqrt` as a builtin IEEE operation, and `rsqrt` as `1 / sqrt` with its error | S | needs F1, F3 |
| X2 | `exp` for f32: reduction by `ln 2`, a degree-6 polynomial, scaling through the exponent bits; finite on `x <= 88.7`, error bound against a real `exp` theory whose model and polynomial lemma are proved in Lean | M | needs F1-F4 and ADR 0061's runner |
| X3 | `sin` and `cos` for f32 on the range RoPE uses (`|x| <= seq_len`), the same way | M | needs X2's machinery |

**Kernels (`Pia.Nn`) and the model (`Pia.Llm`)**

| # | PR | Size | Status |
| --- | --- | --- | --- |
| K1 | `matvec` with its γₙ tolerance and bounds lemmas | S | needs F4 |
| K2 | `rmsnorm`, `softmax` (max-subtracted, probabilities in `[0, 1]`, sum within tolerance of 1), `silu`/SwiGLU, residual add | M | needs X1, X2 |
| K3 | `rope` and grouped-query attention over a KV cache | M | needs X3, K1, K2 |
| M1 | `Pia.Format.Safetensors`, proved total, and `tools/llm/export.py` | M | integer-only, can start now |
| M2 | Tokenizer: `tok512` vocabulary loader, BPE encode, decode, the round trip | M | integer-only, can start now |
| M3 | Sampling: argmax, temperature, top-p, xorshift | S | needs F1 for the probabilities |
| M4 | `Pia.Llm.Llama`: config, weights, load checks, `forward`, `generate`; `examples/llm/stories.pia` as a command; the differential test against `run.c` | L | needs K1-K3, M1-M3 |

**Execution**

| # | PR | Size | Status |
| --- | --- | --- | --- |
| E1 | CPU SIMD: `@fp(reassoc)` kernels vectorised to NEON, tokens-per-second benchmark against `run.c` | M | needs F5, M4 |
| E2 | ADR 0065 steps 1-4 with float `linalg.generic` meanings (`arith.addf`/`mulf` under the `round` encoding), `Pia.Linalg.matvec` and `matmul` | L | ADR 0065 thread; needs F3 for the float meaning |
| E3 | ADR 0065 step 5: `@schedule` on CPU | M | ADR 0065 thread |
| E4 | The GPU ADR, then ADR 0065 step 7: SPIR-V, SPIRV-Cross, the Metal shim, `@place(gpu)` for the projections | L | GPU demo thread and ADR 0065 thread |
| E5 | The literate walkthrough, `docs/llm.pia.md`: the port beside `model.py`, the proof report, the trust report, the benchmark | M | last |

The critical path is F1, F2, F3, F4, X2, K2, K3, M4, then E1 and E4 in parallel. M1 and M2 run alongside floats from day one; E2 and E3 run alongside the kernels.

### 6. The 0.1.0 release checklist

0.1.0 is tagged when all of these hold:

- [ ] `stories260K` generates a story on Dean's M3 with the `stories` command built from `examples/llm/stories.pia`, matching `run.c`'s greedy tokens for the fixed prompt set, on the scalar, SIMD and GPU paths.
- [ ] `stories15M` runs on the GPU path, with its tokens per second reported against `run.c`.
- [ ] Every goal in `lib/Pia/Math`, `lib/Pia/Nn`, `lib/Pia/Llm` and `lib/Pia/Format` is proved, with no `--allow` flags; the report gives goals per file, wall-clock time, the costliest goals, and the split between Z3, intervals and Lean.
- [ ] `piac --trust-report` for the demo lists exactly: the IEEE `round` encoding, the Apple GPU float model, the Metal shim's `extern` contracts, the GPU lowering and schedule items, and nothing else.
- [ ] The proof benchmark (ADR 0032) includes the float kernels, and the gate passes on CI.
- [ ] M11 ([#12](https://github.com/deanberris/pia-lang/issues/12)) is closed; ADR 0065 is Accepted and its steps 1 to 5 and 7 are merged.
- [ ] `docs/llm.pia.md` is on the site and doc-tested, and the status page and the skill pack list floats, `Pia.Math`, `Pia.Nn` and `Pia.Llm`.
- [ ] Licences audited: no GPL in the build, the release or the fetched model; `stories15M`'s vocabulary licence stated where it is fetched.
- [ ] `piac --version` prints 0.1.0; release notes say what 0.1.0 proves and what it does not (section 3's last rows); macOS arm64 binaries attached to the GitHub release.

## Consequences

- 0.1.0 is gated on floats, which are the largest missing piece: F1 to F4 are about three weeks of PRs before the first float kernel proves. The integer parts of the model (safetensors, tokenizer) start now, so they are ready when the kernels are.
- The demo turns ADR 0038 and ADR 0065 from designs into code with a user, and the kernels it needs (`matvec`, `softmax`, `rmsnorm`, `exp`) are the start of a reusable `Pia.Nn`.
- The claims are bounded and stated: safety, shapes, finiteness and per-kernel error are proved; agreement with PyTorch is tested; quality is not addressed. The end-to-end bound is reported even when it is loose, because hiding it would overclaim.
- The trusted base grows by the GPU's float model and the Metal shim, both named in the trust report, as ADR 0038 and ADR 0065 already require.
- Lean becomes part of the release path for `exp`, `sin` and `cos`, so ADR 0061's runner must work on the iMac and in CI by then.

## Answers to the review questions

Dean accepted this ADR on 2026-11-24 and answered both questions. These answers are part of the decision.

1. **The headline is `stories260K`, with `stories15M` on the GPU.** Every test, proof report and CI run uses `stories260K`. `stories15M` is fetched, not committed, for the GPU benchmark, and the place that fetches it states its vocabulary's licence.
2. **The GPU path gates 0.1.0, for the matmuls.** The projections run on Metal through `@lower`, linalg, SPIR-V and SPIRV-Cross before the tag. ADR 0065 step 7 and the GPU ADR are on the critical path; softmax, RMSNorm and sampling stay on the CPU.
