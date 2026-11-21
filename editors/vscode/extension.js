// The Pia extension for VS Code (ADR 0021): starts pia-lsp and connects
// it to the editor. Everything Pia-specific lives in the server.

'use strict';

const path = require('path');
const vscode = require('vscode');
const { LanguageClient, TransportKind } = require('vscode-languageclient/node');

let client;

function serverCommand() {
  const config = vscode.workspace.getConfiguration('pia');
  let command = config.get('server.path') || 'pia-lsp';
  if (command.startsWith('~')) {
    command = path.join(require('os').homedir(), command.slice(1));
  }
  const folders = vscode.workspace.workspaceFolders;
  if (!path.isAbsolute(command) && command.includes(path.sep) && folders) {
    command = path.join(folders[0].uri.fsPath, command);
  }
  return { command, args: config.get('server.args') || [] };
}

function verifySettings() {
  const config = vscode.workspace.getConfiguration('pia');
  return {
    on: config.get('verify.on'),
    showProved: config.get('verify.showProved'),
  };
}

function isPia(document) {
  return document.languageId === 'pia' || document.fileName.endsWith('.pia.md');
}

async function start(context) {
  const { command, args } = serverCommand();
  const executable = { command, args, transport: TransportKind.stdio };
  client = new LanguageClient(
    'pia',
    'Pia',
    { run: executable, debug: executable },
    {
      // Literate `.pia.md` files are Markdown with code in ```pia blocks
      // (ADR 0029); the server reads them as such.
      documentSelector: [
        { language: 'pia' },
        { language: 'markdown', pattern: '**/*.pia.md' },
      ],
      initializationOptions: { verify: verifySettings() },
      synchronize: { configurationSection: 'pia' },
    });
  try {
    await client.start();
  } catch (err) {
    vscode.window.showErrorMessage(
      `Pia: could not start '${command}'. Build it with ` +
      '`bazel build //tools/pia-lsp` and set "pia.server.path". ' + err);
  }
}

async function activate(context) {
  context.subscriptions.push(
    vscode.commands.registerCommand('pia.verify', () => {
      const editor = vscode.window.activeTextEditor;
      if (!client || !editor || !isPia(editor.document)) return;
      // The language client registers the server's own command.
      return vscode.commands.executeCommand(
        'pia.server.verify', editor.document.uri.toString());
    }),
    vscode.commands.registerCommand('pia.restart', async () => {
      if (client) await client.stop();
      await start(context);
    }),
    vscode.workspace.onDidChangeConfiguration(async (e) => {
      if (e.affectsConfiguration('pia.server')) {
        if (client) await client.stop();
        await start(context);
      }
    }));
  await start(context);
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
