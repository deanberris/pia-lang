# Pia for VS Code

Editor support for [Pia](https://github.com/deanberris/pia-lang), from the `pia-lsp` language server ([ADR 0021](../../docs/adr/0021-language-server.md)):

- **Proofs in the editor.** When you open or save a file, the verifier runs in the background. A goal it cannot prove is an error on the expression that raised it, with the counterexample: `not proved: '+' does not overflow u8, counterexample: a = 248, b = 248, result = 496`. Skipped goals show as information.
- **Hover** on a name shows its definition with its contracts. Hover on an operator, call or index shows each goal there and how it was proved (`intervals`, `presburger`, `smt`).
- **Quick fix for shadowing** (ADR 0022): the lightbulb on a "shadows ..." error renames the new binding and its uses to the suggested name, such as `x'`.
- **Rename**, **find references** and highlighting of a name's uses, by scope.
- **Syntax errors** as you type, **go to definition**, an **outline** of the file, and **completion** of keywords and names.
- **Doc comments on hover.** A `(** ... *)` comment before a definition shows under its signature ([ADR 0029](../../docs/adr/0029-comments-as-syntax-and-literate-pia.md)).
- **Literate files.** A `*.pia.md` file is Markdown whose fenced `pia` blocks are code. The blocks are highlighted, and the server checks and proves them, with the prose before a block as its documentation.
- Syntax highlighting, bracket matching, and `(* *)`, `(** *)` and `\` comments (**Toggle Line Comment** uses `\`).

## Install

Build the server in a Pia checkout:

```sh
bazel build //tools/pia-lsp
```

Build and install the extension:

```sh
cd editors/vscode
npm install
npx vsce package            # writes pia-0.1.0.vsix
code --install-extension pia-0.1.0.vsix
```

Then point the extension at the server, in VS Code's settings:

```json
"pia.server.path": "/path/to/pia-lang/bazel-bin/tools/pia-lsp/pia-lsp"
```

Or put `pia-lsp` on your `PATH`. A relative path such as `bazel-bin/tools/pia-lsp/pia-lsp` is resolved against the first workspace folder.

To work on the extension itself, open this folder in VS Code and press F5 to start an Extension Development Host.

## Settings

| Setting | Default | |
| --- | --- | --- |
| `pia.server.path` | `pia-lsp` | The server binary |
| `pia.server.args` | `[]` | Extra arguments, such as `--timeout-ms=5000` (per goal) |
| `pia.verify.on` | `save` | `save`, `change` or `off`. **Pia: Verify This File** runs it on demand |
| `pia.verify.showProved` | `false` | Also show proved goals, as hints |
| `pia.trace.server` | `off` | Log the LSP traffic in the Pia output channel |

## Other editors

`pia-lsp` is a standard LSP server over stdio, so any LSP client can use it: Neovim (`vim.lsp.start{ cmd = {"pia-lsp"} }`), Helix, Emacs (`eglot`), Zed or Sublime Text. Visual Studio 2022 can host it through a small VSIX that uses its `ILanguageClient` API; that is planned, with no change to the server.

## Tests

`npm test` downloads a VS Code build, opens `test/fixture/demo.pia` with the extension and checks diagnostics, hover, definitions, the outline and the commands. Point it at a server: `PIA_LSP=../../bazel-bin/tools/pia-lsp/pia-lsp npm test` (on Linux without a display, under `xvfb-run -a`). The server's own tests are `bazel test //tests/lsp/...`.
