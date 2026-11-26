# 70. Raw binary embedding: `@embed` for compile-time fixed byte blobs, hermetic roots, opaque verification and direct LLVM emission

Date: 2026-11-26

Status: Accepted (2026-11-26, from Dean's answers on the design questions)

## Context

Step 1 of the GPU toolchain ([ADR 0068](0068-gpu-compute-through-spirv-and-metal.md), PR [#430](https://github.com/deanberris/pia-lang/pull/430)) builds a compiled Metal library (`.metallib`) and embeds it into a binary by piping the file through `xxd -i` into a generated C source file wrapped in a `cc_library` (`tools/gpu/metal.bzl`), which C code then reads through `extern const unsigned char <symbol>[]` and `<symbol>_len` (`tests/gpu/embed_test.c`).

In review of PR #430, Dean asked that embedding a compiled `.metallib` (or any binary asset) become a first-class Pia feature so a pure Pia binary with a `main` entry point can bind and embed binary blobs directly without a `cc_library` or `xxd` wrapper:

- **GPU kernels ([ADR 0068](0068-gpu-compute-through-spirv-and-metal.md))**: a Pia program with `@place(gpu)` or a Metal shim needs the compiled `.metallib` embedded in the object file and passed as a read-only byte slice to the shim at launch.
- **0.1.0 LLM & codecs ([ADR 0067](0067-release-0-1-0-a-proved-small-llm.md))**: small model checkpoints (`stories260K`), tokenizer vocabularies (`tok512`), lookup tables and test fixtures benefit from the same mechanism.
- **Today's `ConstArrayOp` does not scale to binary blobs.** `src/codegen/Codegen.cpp` lowers literal arrays by materializing an MLIR `IntegerAttr` per element and emitting a `memref.global`. That is suitable for small tables, not for kilobyte- or megabyte-sized `.metallib` or weight files, and it cannot read external files. Meanwhile, `src/codegen/Codegen.cpp` already emits raw binary data directly as an LLVM `ConstantDataArray` global (with optional custom section and alignment) for proof certificates (`pia$cert`, [ADR 0024](0024-published-proof-certificates.md)).

## Decision

### 1. Surface syntax: `@embed(file = ..., ...)`

A top-level `let` binding embeds a raw binary file via the `@embed(...)` attribute on its return type, with no `=` body:

```pia
let add_metallib : [u8] @embed(file = "add.metallib")
```

Because `fixed` is Pia's default immutability qualifier, an embedded binding is always `fixed` (read-only); combining `@embed` with `mutable` is a type error.

Supported named arguments inside `@embed(...)`:

| Argument | Required | Meaning |
| --- | --- | --- |
| `file = "<path>"` | Yes | Relative path to the binary file, resolved hermetically (section 2). |
| `symbol = "<name>"` | No | Optional C/linker symbol name for the emitted byte array (section 4). When omitted, the compiler assigns a private mangled name. |
| `section = "<name>"` | No | Optional target object section (e.g. `"__DATA,__pia_metal"` on Mach-O or `".rodata.pia_metal"` on ELF). Defaults to the target's read-only data section. |
| `align = <power-of-two>` | No | Optional byte alignment (positive power of two, default `8`). |

At run time, the binding has type `[u8]` (a `fixed` read-only slice backed by static storage with lifetime `'static`) whose length equals the file's exact byte size `N`. A pure Pia `main` can pass it directly to Pia functions or `extern` shims (such as Metal's `device_load_library`), or inspect its bytes and length normally:

```pia
let add_metallib : [u8] @embed(file = "add.metallib", symbol = "pia_test_add_metallib")

let main () : i32 =
  if len add_metallib >= 4 &&
     add_metallib.[0] = 0x4d && add_metallib.[1] = 0x54 &&
     add_metallib.[2] = 0x4c && add_metallib.[3] = 0x42
  then 0 else 1
```

### 2. Hermetic file resolution (CLI and Bazel)

`piac` never reads arbitrary paths from the ambient filesystem. Every `@embed(file = "...")` path is resolved strictly against explicitly declared roots or mappings:

- **Relative paths only.** Absolute paths (starting with `/` or a drive prefix) and parent traversals (`..`) are compile-time errors.
- **CLI flags** (mirroring `--iface-path` in `tools/piac/pia.bzl`):
  - `--embed-path=<dir>` (repeatable): search roots checked in flag order for `<dir>/<file>`.
  - `--embed=<logical>=<physical>` (repeatable): explicit logical-to-physical mapping, taking precedence over `--embed-path` (useful when Bazel generates files under `bazel-bin/...` with target-dependent paths).
  - Resolving a file not found under any declared mapping or root is a hard error naming the missing path and the searched roots.
- **Bazel integration (`tools/piac/pia.bzl`):** `pia_library`, `pia_object` and `pia_binary` gain an `embeds` attribute (`label_list(allow_files = True)` or `label_keyed_string_dict`) that declares every embedded file as an explicit action input to `PiaCompile` (and to `PiaInterface` only when needed; see section 5) and forwards `--embed` / `--embed-path` to `piac`.
- **REPL / MCP (`pia`):** respects the same `--embed-path` / `--embed` flags; with none passed, `@embed` is refused rather than opening host files.

### 3. Compile-time metafunction access vs. opaque verification

Embedded blobs have two distinct compile-time roles, kept strictly separate so verification stays O(1) regardless of blob size:

- **In `let meta` (metafunctions): compile-time fixed byte array.** The metaprogram interpreter (`src/meta/Interpreter.cpp`) sees an `@embed` binding as a compile-time `fixed` byte array of exact length `N` whose elements are readable by metafunctions (length and byte indexing). A metaprogram can validate magic bytes (e.g. `"MTLB"` for a `.metallib`), parse a small header or manifest, or extract kernel names at compile time and fail compilation on a malformed blob — without ever sending those bytes to Z3.
- **In regular code and the Z3 verifier: opaque blob with exact length `N`.** To Sema, IRGen and the verifier, an `@embed` binding is an opaque `fixed` `[u8]` slice with one known fact: `len blob = N` (a constant `usize` equal to the file's byte count) and every element has type `u8` (`0 <= blob.[i] <= 255`). No per-byte axioms are emitted into SMT queries. Embedding a 1 MB `.metallib` or model file adds zero per-byte solver cost; any property of the bytes needed by runtime code is either checked by a metafunction at compile time or validated by proved Pia code at run time (as in `Pia.Format.Safetensors`, [ADR 0067](0067-release-0-1-0-a-proved-small-llm.md)).
- **Spec functions:** because the bytes are opaque outside metafunctions, `len blob` is exact in contracts (`len blob = N`), while `blob.[i]` is an uninterpreted `u8` value (deterministic: repeated reads `blob.[i]` at equal `i` return equal values).

### 4. Codegen and symbol binding

Codegen bypasses per-element MLIR attribute expansion and emits the raw bytes directly in LLVM IR:

- **MLIR representation:** a module-level binary asset table (or `DenseResourceElementsAttr` / `pia.embed_data` attribute referencing raw bytes held outside the MLIR IR printer's per-element array format) and a `pia.embed` op returning the `[u8]` slice descriptor `{ptr, len}` with static length `N`.
- **LLVM IR emission (`src/codegen/Codegen.cpp`):** lowers each embedded blob directly to a read-only `llvm::GlobalVariable` initialized with `llvm::ConstantDataArray::get(ctx, llvm::ArrayRef<uint8_t>(...))`:
  - `isConstant = true` (matches Pia's `fixed` semantics; placed in `.rodata` / `__TEXT,__const` by default, or the requested `section`).
  - `alignment = align` (default `8`).
  - **Linkage & symbol binding:**
    - Private `@embed` without `symbol`: `PrivateLinkage` (internal to the object file, zero dynamic symbol table pollution, respects issue #120).
    - Explicit `symbol = "<name>"` or exported in an interface: `ExternalLinkage` with the specified symbol name (or canonical module-mangled name if exported without `symbol`). When `symbol = "<name>"` is set, codegen also emits `<name>` pointing at the raw byte array and `<name>_len` (`uint64_t`) if C ABI interop is requested, or callers bind directly through the Pia slice `{ptr, len}` (C ABI `pia_slice_u8`).
    - When `section` is specified, the global is added to `llvm.used` so dead-stripping does not drop unreferenced section entries if an external loader scans the section.
- **Replaces `tools/gpu/metal.bzl`'s `cc_library` hack:** `metal_library` produces the `.metallib` file alone; a Pia target embeds it via `embeds = [":add_metallib"]` and `@embed(file = "add.metallib")`, eliminating `xxd -i`, generated `_embed.c`, and `cc_library`.

### 5. Interfaces and SHA-256 certificate hashing

- **Private `@embed` bindings** (not listed in `interface I = sig ... end`) do not appear in `.piai` and do not affect the module's interface hash. Rebuilding a private `.metallib` does not re-verify or rebuild importers, and `piac --emit=interface` does not need to read private embedded files.
- **Explicitly exported `@embed` bindings** may be listed in an interface as a read-only byte slice:
  ```pia
  interface Kernels = sig
    let add_metallib : [u8] @embed
  end
  ```
  When `piac --emit=interface` emits the `.piai` for an explicitly exported `@embed` binding, it records both its exact length and its **SHA-256 content hash** (lowercase 64-char hex, computed with `llvm::SHA256` as in `src/cert/Certificate.cpp`):
  ```pia
  let add_metallib : [u8] @embed(len = 4096, sha256 = "e3b0c442...")
  ```
  Because `__pia_cert` ([ADR 0024](0024-published-proof-certificates.md)) hashes the canonical `.piai` text with SHA-256, `pia-cert check` automatically enforces at link time that every importer was verified and compiled against the exact byte length and content hash of the exported embedded blob, catching stale objects with zero extra certificate format changes.

## Implementation order

Each step is one PR:

1. **Syntax, hermetic resolution & opaque verifier encoding:** parse `@embed(file = ..., symbol = ..., section = ..., align = ...)` on top-level `let` bindings; add `--embed-path` and `--embed` flags to `piac` and `pia`; resolve files hermetically in Sema; encode `@embed` in IRGen and the verifier as a `fixed` `[u8]` slice with exact constant `len = N` and opaque `u8` elements.
2. **Direct LLVM codegen & Bazel `embeds`:** add `pia.embed` lowering directly to `llvm::ConstantDataArray` in `src/codegen/Codegen.cpp` (with `symbol`, `section`, `align`); add `embeds` to `pia_library`, `pia_object` and `pia_binary` in `tools/piac/pia.bzl`.
3. **Exported interface `.piai` & SHA-256 hashing:** support `let name : [u8] @embed` in `interface ... = sig ... end`, emit `len` and `sha256` into `.piai` (only when explicitly exported), and verify `pia-cert check` rejects a mismatched embedded blob at link time.
4. **Metafunction compile-time byte access:** expose `@embed` bindings to `let meta` as compile-time fixed byte arrays (`len` and indexing), with a test validating `"MTLB"` magic in a metafunction at compile time.
5. **Migrate `tools/gpu/metal.bzl` and `tests/gpu/`:** drop the `xxd -i` / `_embed.c` / `cc_library` rule from `tools/gpu/metal.bzl` and replace `tests/gpu/embed_test.c` with a pure Pia `pia_binary` embedding the `.metallib` via `@embed`.

## Consequences

- Pure Pia binaries (`main` with no C glue) can embed `.metallib` archives, model weights, vocabularies and static fixtures directly, with full bounds verification on `len` and zero Z3 blowup.
- Metafunctions can inspect and validate embedded binary headers at compile time without pushing raw bytes into SMT queries.
- Private embedded blobs keep incremental builds fast (importers never see them), while explicitly exported embedded blobs are content-addressed by SHA-256 through the existing `.piai` and `__pia_cert` link check.
- `tools/gpu/metal.bzl` no longer depends on `xxd` or `cc_library` to embed compiled Metal libraries.
