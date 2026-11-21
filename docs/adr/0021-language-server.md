# 21. A language server, `pia-lsp`, with a VS Code client first

Date: 2026-11-21

Status: Proposed

## Context

Pia's promise is that programs are proved before they run. Today the proof results only appear when `piac --verify` runs in a terminal. The place a programmer wants to see "this `+` can overflow when `a = 248, b = 248`" is the editor, on the `+`, while they type.

The Language Server Protocol (LSP) lets one server work with many editors: VS Code, Visual Studio, Neovim, Emacs, Helix, Zed and others. Writing editor support once, as a server, is much cheaper than writing a plug-in per editor, and it keeps the language knowledge in the compiler's own C++ code instead of a reimplementation in TypeScript.

The compiler is split so that the front end (`src/syntax`) has no LLVM dependency and builds in seconds, while IRGen and the verifier need MLIR and Z3. Verification can take seconds per goal (the per-goal timeout is 10 s), so it cannot run on the editor's critical path.

## Decision

**A server binary, `//tools/pia-lsp`, speaks LSP 3.17 over stdio.** It is built from the compiler's own libraries, so the editor sees exactly what `piac` sees. The protocol code lives in `//src/lsp` with a small JSON reader and writer of its own, so the front-end part of the server builds and tests without LLVM, like `piac -DPIA_NO_MLIR`.

**Two kinds of analysis, on two schedules.**

- *Front end, on every change.* The server keeps each open document's text (full sync), reparses it on each change and publishes syntax errors at once. The same parse feeds document symbols, hover, go-to-definition and completion. Names are resolved over the syntax tree with the language's scoping: top-level `let`s are visible everywhere (IRGen allows calls before the definition), parameters in the contracts and body, `let ... in` in its body (and its value when `rec`), loop, lambda, quantifier and match binders in their bodies.
- *Proofs, in the background.* IRGen and the verifier run on a worker thread, by default when a document is opened or saved (`pia.verify.on`: `save`, `change` or `off`, and the `pia.verify` command on demand). Type errors from IRGen and every failed goal become diagnostics with source `pia-verify`; the counterexample is part of the message, and the goal kind (`nooverflow`, `inbounds`, `ensures`, ...) is the diagnostic code. Skipped goals are information diagnostics, since v0 cannot prove them yet. Proved goals are hints only if `pia.verify.showProved` is set. Results for a document version that has since changed are dropped, and an edit clears the old proof diagnostics, whose positions would be stale. Newer requests for a document replace older queued ones.

**Hover shows proofs.** Hovering a name shows its definition: a function's signature and contracts as written, or a parameter's annotation. Hovering an operator, call or index shows every goal the verifier raised there, with its status and the method that proved it (`intervals`, `presburger`, `smt`) or the counterexample. This is where "proved in advance" becomes visible.

**Positions.** The compiler counts byte offsets and 1-based byte columns. The server converts to LSP's UTF-16 positions per line, which every client supports.

**VS Code first, in `editors/vscode`.** A small extension in plain JavaScript (no TypeScript build step) uses `vscode-languageclient` to start `pia-lsp`, and adds a TextMate grammar and language configuration for highlighting, brackets and `(* *)` comments. Settings: `pia.server.path`, `pia.verify.on`, `pia.verify.showProved`, `pia.trace.server`. It is packaged as a `.vsix` with `vsce`.

**Visual Studio later, through the same server.** Visual Studio 2022 hosts LSP servers through its `ILanguageClient` extension API, so supporting it needs only a small VSIX that starts `pia-lsp`, with no change to the server.

## Consequences

- Diagnostics in the editor are the compiler's, from the same code, so they cannot drift from `piac`.
- The front-end features work in a build without MLIR, and their tests run in seconds. The proof features need the full build.
- A program with a syntax error gets no proof results until it parses. The parser's recovery (ADR 0019) still reports every broken item.
- Verification of one file is not incremental yet: each run re-verifies the whole file. Per-function caching keyed by the function's text and its callees' contracts comes with proof certificates (ADR 0010).
- Hover and definition work within one file. Cross-module navigation waits for modules and imports in the compiler.
- Semantic highlighting, rename, code actions (such as "add `@overflow(saturate)`" on an overflow goal) and inlay hints for inferred ranges are natural follow-ups on the same server.
