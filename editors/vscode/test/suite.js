// Extension tests, run inside VS Code by test/runTest.js.

'use strict';

const assert = require('assert');
const path = require('path');
const vscode = require('vscode');

async function until(pred, ms = 20000) {
  const end = Date.now() + ms;
  for (;;) {
    const v = await pred();
    if (v) return v;
    if (Date.now() > end) throw new Error('timed out');
    await new Promise((r) => setTimeout(r, 200));
  }
}

async function run() {
  const file = path.join(__dirname, 'fixture', 'demo.pia');
  const doc = await vscode.workspace.openTextDocument(file);
  await vscode.window.showTextDocument(doc);
  assert.strictEqual(doc.languageId, 'pia');
  const ext = vscode.extensions.getExtension('pia-lang.pia');
  assert.ok(ext, 'extension not found');
  await ext.activate();
  console.log('server path:', vscode.workspace.getConfiguration('pia').get('server.path'));

  // The syntax error on the last item.
  const diags = await until(() => {
    const d = vscode.languages.getDiagnostics(doc.uri);
    return d.length ? d : null;
  });
  assert.strictEqual(diags[0].severity, vscode.DiagnosticSeverity.Error);
  assert.ok(diags[0].range.start.line >= 6, `line ${diags[0].range.start.line}`);
  console.log('diagnostic:', diags[0].message);

  // Hover on `add` in `twice` shows the signature and contract.
  const text = doc.getText();
  const at = doc.positionAt(text.indexOf('add x x'));
  const hovers = await until(async () => {
    const h = await vscode.commands.executeCommand(
      'vscode.executeHoverProvider', doc.uri, at);
    return h && h.length ? h : null;
  });
  const md = hovers.map((h) => h.contents.map((c) => c.value || c).join('')).join('');
  assert.ok(md.includes('let add (a : u8) (b : u8) : u16'), md);
  assert.ok(md.includes('ensures result >= a'), md);
  console.log('hover:', JSON.stringify(md));

  // Go to definition lands on the `let add` name.
  const defs = await vscode.commands.executeCommand(
    'vscode.executeDefinitionProvider', doc.uri, at);
  assert.strictEqual(defs.length, 1);
  const def = defs[0].range || defs[0].targetRange;
  assert.deepStrictEqual([def.start.line, def.start.character], [0, 4]);

  // The outline has the items that parse; `broken` does not.
  const symbols = await vscode.commands.executeCommand(
    'vscode.executeDocumentSymbolProvider', doc.uri);
  assert.deepStrictEqual(symbols.map((s) => s.name), ['add', 'twice']);

  // Both commands are there, and verifying on demand reaches the server.
  const commands = await vscode.commands.getCommands(true);
  for (const c of ['pia.verify', 'pia.restart', 'pia.server.verify'])
    assert.ok(commands.includes(c), c);
  await vscode.commands.executeCommand('pia.verify');

  console.log('all extension tests passed');
}

module.exports = { run };
