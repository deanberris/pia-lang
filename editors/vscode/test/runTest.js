// Runs the extension tests in a downloaded VS Code:
//   PIA_LSP=/path/to/pia-lsp node test/runTest.js
// (under xvfb-run on a machine without a display).

'use strict';

const path = require('path');
const { runTests } = require('@vscode/test-electron');

async function main() {
  const server = process.env.PIA_LSP;
  if (!server) throw new Error('set PIA_LSP to the pia-lsp binary');
  const root = path.resolve(__dirname, '..');
  const workspace = path.join(__dirname, 'fixture');
  const fs = require('fs');
  const os = require('os');
  // VS Code's IPC socket lives in the user-data dir and macOS caps socket
  // paths at 103 chars, so a deep checkout breaks the default
  // .vscode-test/user-data; use a short temp dir instead.
  const userData = fs.mkdtempSync(path.join(os.tmpdir(), 'pia-vsc-'));
  fs.mkdirSync(path.join(workspace, '.vscode'), { recursive: true });
  fs.writeFileSync(path.join(workspace, '.vscode', 'settings.json'),
    JSON.stringify({ 'pia.server.path': path.resolve(server), 'pia.trace.server': 'verbose' }, null, 2));
  await runTests({
    extensionDevelopmentPath: root,
    extensionTestsPath: path.join(__dirname, 'suite.js'),
    launchArgs: [workspace, '--disable-extensions', '--disable-gpu', `--user-data-dir=${userData}`],
  });
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
