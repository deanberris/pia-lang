"""End-to-end tests for pia-lsp (ADR 0021).

Starts the server, speaks LSP to it over pipes and checks the replies.

    python3 tests/lsp/lsp_test.py path/to/pia-lsp

The proof tests run only when the server reports the verifier
(`capabilities.experimental.piaVerifier`), so the same script tests a
front-end build made with -DPIA_NO_MLIR.
"""

import json
import queue
import subprocess
import sys
import threading
import time
import unittest

SERVER = None

GOOD = """\
(* A function with a contract, and a caller. *)
let add (a : u8) (b : u8) : u16
  ensures result >= a
= let s = a + b in s

let twice (x : u8) : u16 = add x x
"""

BROKEN = """\
let ok (a : u8) : u8 = a

let broken (a : u8) : u8 = (a +
"""

RANGE = """\
let scale (x : u8) : u16
  requires x < 100
= x * 2
"""

RANGE_FIXED = """\
let scale (x : int{0..99}) : u16
= x * 2
"""

SHADOW = """\
let helper (x : u8) : u8 = x

let inner (x : u8) : u8 = let x = 1 in x + x

let taken (x : u8) (x' : u8) : u8 = let x = x' in x
"""

SHADOW_FIXED = """\
let helper (x : u8) : u8 = x

let inner (x : u8) : u8 = let x' = 1 in x' + x'

let taken (x : u8) (x' : u8) : u8 = let x = x' in x
"""

DOCUMENTED = """\
(** Adds one, saturating at 255. *)
let bump (x : u8) : u8 = x +| 1  \\ never wraps

let twice (x : u8) : u8 = bump (bump x)
"""

LITERATE = """\
# Counters

`bump` adds one and stops at 255.

```pia
let bump (x : u8) : u8 = x +| 1
```

Using it twice:

```pia
let twice (x : u8) : u8 = bump (bump x)
```
"""

FAILING = """\
let bad (a : u8) (b : u8) : u8 = a + b

let good (a : u8) (b : u8) : u16 = a + b
"""


class Client:
    def __init__(self, path):
        self.proc = subprocess.Popen(
            [path, "--timeout-ms=5000"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        self.next_id = 0
        self.messages = queue.Queue()
        self.reader = threading.Thread(target=self._read, daemon=True)
        self.reader.start()

    def _read(self):
        out = self.proc.stdout
        while True:
            headers = {}
            while True:
                line = out.readline()
                if not line:
                    self.messages.put(None)
                    return
                line = line.decode().strip()
                if not line:
                    break
                key, _, value = line.partition(":")
                headers[key.strip().lower()] = value.strip()
            body = out.read(int(headers["content-length"]))
            self.messages.put(json.loads(body))

    def send(self, msg):
        msg["jsonrpc"] = "2.0"
        body = json.dumps(msg).encode()
        self.proc.stdin.write(b"Content-Length: %d\r\n\r\n" % len(body) + body)
        self.proc.stdin.flush()

    def notify(self, method, params=None):
        self.send({"method": method, "params": params or {}})

    def request(self, method, params=None, timeout=30):
        self.next_id += 1
        rid = self.next_id
        self.send({"id": rid, "method": method, "params": params or {}})
        return self.wait(lambda m: m.get("id") == rid and "method" not in m,
                         timeout)

    def wait(self, pred, timeout=30):
        deadline = time.time() + timeout
        while True:
            left = deadline - time.time()
            if left <= 0:
                raise AssertionError("timed out waiting for a message")
            msg = self.messages.get(timeout=left)
            if msg is None:
                raise AssertionError("server closed its output")
            if pred(msg):
                return msg

    def diagnostics(self, uri, pred=lambda d: True, timeout=30):
        msg = self.wait(
            lambda m: m.get("method") == "textDocument/publishDiagnostics"
            and m["params"]["uri"] == uri and pred(m["params"]["diagnostics"]),
            timeout)
        return msg["params"]["diagnostics"]

    def open(self, uri, text, version=1):
        self.notify("textDocument/didOpen", {"textDocument": {
            "uri": uri, "languageId": "pia", "version": version, "text": text}})

    def close(self):
        self.request("shutdown")
        self.notify("exit")
        code = self.proc.wait(timeout=10)
        self.proc.stdin.close()
        self.reader.join(timeout=5)
        self.proc.stdout.close()
        self.proc.stderr.close()
        return code


def pos(text, needle, nth=0, delta=0):
    """The LSP position of the nth occurrence of needle, plus delta."""
    at = -1
    for _ in range(nth + 1):
        at = text.index(needle, at + 1)
    at += delta
    line = text.count("\n", 0, at)
    col = at - (text.rindex("\n", 0, at) + 1 if line else 0)
    return {"line": line, "character": col}


class LspTest(unittest.TestCase):
    def setUp(self):
        self.client = Client(SERVER)
        init = self.client.request("initialize", {
            "processId": None, "rootUri": None, "capabilities": {},
            "initializationOptions": {"verify": {"on": "save"}}})
        self.caps = init["result"]["capabilities"]
        self.verifier = self.caps.get("experimental", {}).get("piaVerifier")
        self.client.notify("initialized")

    def tearDown(self):
        code = self.client.close()
        self.assertEqual(code, 0)

    def test_capabilities(self):
        self.assertTrue(self.caps["hoverProvider"])
        self.assertTrue(self.caps["definitionProvider"])
        self.assertEqual(self.caps["textDocumentSync"]["change"], 1)

    def test_syntax_error_then_fix(self):
        uri = "file:///tmp/broken.pia"
        self.client.open(uri, BROKEN)
        diags = self.client.diagnostics(uri)
        self.assertGreaterEqual(len(diags), 1)
        self.assertEqual(diags[0]["severity"], 1)
        self.assertEqual(diags[0]["source"], "pia")
        # The unclosed `(a +` on line 2 (0-based), reported there or at the
        # end of the file.
        self.assertGreaterEqual(diags[0]["range"]["start"]["line"], 2)
        # The items that parse on their own still have symbols and hover.
        syms = self.client.request("textDocument/documentSymbol", {
            "textDocument": {"uri": uri}})["result"]
        self.assertEqual([s["name"] for s in syms], ["ok"])
        hover = self.client.request("textDocument/hover", {
            "textDocument": {"uri": uri},
            "position": pos(BROKEN, "a\n")})["result"]
        self.assertIn("(parameter) a : u8", hover["contents"]["value"])
        self.client.notify("textDocument/didChange", {
            "textDocument": {"uri": uri, "version": 2},
            "contentChanges": [{"text": GOOD}]})
        self.assertEqual(self.client.diagnostics(uri), [])

    def test_hover_and_definition(self):
        uri = "file:///tmp/good.pia"
        self.client.open(uri, GOOD)
        self.client.diagnostics(uri)

        # `add` in `twice`'s body resolves to the definition on line 1.
        at = pos(GOOD, "add x x")
        hover = self.client.request("textDocument/hover", {
            "textDocument": {"uri": uri}, "position": at})["result"]
        text = hover["contents"]["value"]
        self.assertIn("let add (a : u8) (b : u8) : u16", text)
        self.assertIn("ensures result >= a", text)
        loc = self.client.request("textDocument/definition", {
            "textDocument": {"uri": uri}, "position": at})["result"]
        self.assertEqual(loc["range"]["start"], pos(GOOD, "add"))

        # A parameter shows its annotation; its use goes to its binding.
        at = pos(GOOD, "a + b", delta=0)
        hover = self.client.request("textDocument/hover", {
            "textDocument": {"uri": uri}, "position": at})["result"]
        self.assertIn("(parameter) a : u8", hover["contents"]["value"])
        loc = self.client.request("textDocument/definition", {
            "textDocument": {"uri": uri}, "position": at})["result"]
        self.assertEqual(loc["range"]["start"], pos(GOOD, "a : u8"))

        # A `let ... in` local.
        loc = self.client.request("textDocument/definition", {
            "textDocument": {"uri": uri},
            "position": pos(GOOD, "in s", delta=3)})["result"]
        self.assertEqual(loc["range"]["start"], pos(GOOD, "s = a"))

        # Nothing to say about a keyword.
        hover = self.client.request("textDocument/hover", {
            "textDocument": {"uri": uri},
            "position": pos(GOOD, "ensures")})["result"]
        self.assertIsNone(hover)

    def test_hover_shows_inherited_contract(self):
        # A definition with no contract takes its interface's (ADR 0077),
        # and its hover shows it in the definition's parameter names.
        src = ("module Counting : Counter\n"
               "interface Counter = sig\n"
               "  let count_to : (n : u32) -> u32\n"
               "    requires n < 1000\n"
               "    ensures result = n\n"
               "end\n"
               "let count_to (m : u32) : u32 = m\n"
               "let five (k : u32) : u32 = count_to 5\n")
        uri = "file:///tmp/inherited.pia"
        self.client.open(uri, src)
        self.client.diagnostics(uri)
        hover = self.client.request("textDocument/hover", {
            "textDocument": {"uri": uri},
            "position": pos(src, "count_to 5")})["result"]
        text = hover["contents"]["value"]
        self.assertIn("(* from interface Counter *)", text)
        self.assertIn("requires m < 1000", text)
        self.assertIn("ensures result = m", text)

    def test_doc_comment_hover(self):
        # A `(** ... *)` doc comment shows under the signature (ADR 0029).
        uri = "file:///tmp/documented.pia"
        self.client.open(uri, DOCUMENTED)
        self.assertEqual(self.client.diagnostics(uri), [])
        hover = self.client.request("textDocument/hover", {
            "textDocument": {"uri": uri},
            "position": pos(DOCUMENTED, "bump (bump")})["result"]
        text = hover["contents"]["value"]
        self.assertIn("let bump (x : u8) : u8", text)
        self.assertIn("Adds one, saturating at 255.", text)
        self.assertNotIn("never wraps", text)

    def test_literate_file(self):
        # A .pia.md file is Markdown with code in ```pia blocks; the prose
        # before a block documents it, and positions are the Markdown's.
        uri = "file:///tmp/counters.pia.md"
        self.client.open(uri, LITERATE)
        self.assertEqual(self.client.diagnostics(uri), [])
        hover = self.client.request("textDocument/hover", {
            "textDocument": {"uri": uri},
            "position": pos(LITERATE, "bump (bump")})["result"]
        self.assertIn("`bump` adds one and stops at 255.",
                      hover["contents"]["value"])
        loc = self.client.request("textDocument/definition", {
            "textDocument": {"uri": uri},
            "position": pos(LITERATE, "bump (bump")})["result"]
        self.assertEqual(loc["range"]["start"], pos(LITERATE, "bump (x"))
        syms = self.client.request("textDocument/documentSymbol", {
            "textDocument": {"uri": uri}})["result"]
        self.assertEqual([s["name"] for s in syms], ["bump", "twice"])
        # A syntax error inside a block is reported on its Markdown line,
        # and the other block still has symbols.
        broken = LITERATE.replace("bump (bump x)", "bump (bump x")
        self.client.notify("textDocument/didChange", {
            "textDocument": {"uri": uri, "version": 2},
            "contentChanges": [{"text": broken}]})
        diags = self.client.diagnostics(uri, lambda d: len(d) > 0)
        self.assertEqual(diags[0]["range"]["start"]["line"], 11)
        syms = self.client.request("textDocument/documentSymbol", {
            "textDocument": {"uri": uri}})["result"]
        self.assertEqual([s["name"] for s in syms], ["bump"])

    def test_symbols_and_completion(self):
        uri = "file:///tmp/good.pia"
        self.client.open(uri, GOOD)
        syms = self.client.request("textDocument/documentSymbol", {
            "textDocument": {"uri": uri}})["result"]
        self.assertEqual([s["name"] for s in syms], ["add", "twice"])
        self.assertEqual(syms[0]["kind"], 12)
        self.assertEqual(syms[0]["selectionRange"]["start"], pos(GOOD, "add"))
        items = self.client.request("textDocument/completion", {
            "textDocument": {"uri": uri},
            "position": pos(GOOD, "add x x")})["result"]["items"]
        labels = {i["label"] for i in items}
        self.assertTrue({"add", "twice", "x", "let", "spread"} <= labels)

    def test_utf16_positions(self):
        uri = "file:///tmp/utf.pia"
        text = "(* é😀 *) let f (x : u8) : u8 = x\n"
        self.client.open(uri, text)
        self.client.diagnostics(uri)
        # "(* é😀 *) let f (x : u8) : u8 = " is 30 UTF-16 units before `x`.
        prefix = text[:text.rindex("x")]
        units = len(prefix.encode("utf-16-le")) // 2
        loc = self.client.request("textDocument/definition", {
            "textDocument": {"uri": uri},
            "position": {"line": 0, "character": units}})["result"]
        start = text.index("x :")
        start_units = len(text[:start].encode("utf-16-le")) // 2
        self.assertEqual(loc["range"]["start"]["character"], start_units)

    def apply(self, text, edits):
        """Applies LSP text edits to text."""
        lines = text.split("\n")
        def off(p):
            return sum(len(l) + 1 for l in lines[:p["line"]]) + p["character"]
        for e in sorted(edits, key=lambda e: off(e["range"]["start"]),
                        reverse=True):
            b, en = off(e["range"]["start"]), off(e["range"]["end"])
            text = text[:b] + e["newText"] + text[en:]
        return text

    def test_references_and_rename(self):
        uri = "file:///tmp/shadow.pia"
        self.client.open(uri, SHADOW)
        self.client.diagnostics(uri)
        # The inner `x` of `inner`: its binder and both uses, not the
        # parameter it shadows.
        at = pos(SHADOW, "x + x")
        refs = self.client.request("textDocument/references", {
            "textDocument": {"uri": uri}, "position": at,
            "context": {"includeDeclaration": True}})["result"]
        starts = [r["range"]["start"] for r in refs]
        self.assertEqual(starts, [pos(SHADOW, "x = 1"), pos(SHADOW, "x + x"),
                                  pos(SHADOW, "x + x", delta=4)])
        refs = self.client.request("textDocument/references", {
            "textDocument": {"uri": uri}, "position": at,
            "context": {"includeDeclaration": False}})["result"]
        self.assertEqual(len(refs), 2)
        prep = self.client.request("textDocument/prepareRename", {
            "textDocument": {"uri": uri}, "position": at})["result"]
        self.assertEqual(prep["start"], at)
        edit = self.client.request("textDocument/rename", {
            "textDocument": {"uri": uri}, "position": at,
            "newName": "x'"})["result"]
        self.assertEqual(self.apply(SHADOW, edit["changes"][uri]), SHADOW_FIXED)
        bad = self.client.request("textDocument/rename", {
            "textDocument": {"uri": uri}, "position": at, "newName": "let"})
        self.assertIn("error", bad)

    def test_shadowing_quick_fix(self):
        uri = "file:///tmp/shadow.pia"
        self.client.open(uri, SHADOW)
        self.client.diagnostics(uri)
        # The diagnostic IRGen reports, pointing at the `let` of `let x = 1`.
        let_at = pos(SHADOW, "let x = 1")
        diag = {"range": {"start": let_at, "end": let_at}, "severity": 1,
                "source": "pia",
                "message": "'x' shadows a local of the same name; Pia does "
                           "not allow shadowing (ADR 0022), so rename it "
                           "to x'"}
        actions = self.client.request("textDocument/codeAction", {
            "textDocument": {"uri": uri},
            "range": {"start": let_at, "end": let_at},
            "context": {"diagnostics": [diag]}})["result"]
        self.assertEqual(len(actions), 1)
        a = actions[0]
        self.assertEqual(a["kind"], "quickfix")
        self.assertEqual(a["title"], "Rename 'x' to 'x''")
        self.assertEqual(self.apply(SHADOW, a["edit"]["changes"][uri]),
                         SHADOW_FIXED)
        # Other diagnostics get no action.
        diag["message"] = "expected an expression"
        actions = self.client.request("textDocument/codeAction", {
            "textDocument": {"uri": uri},
            "range": {"start": let_at, "end": let_at},
            "context": {"diagnostics": [diag]}})["result"]
        self.assertEqual(actions, [])

    def test_shadowing_quick_fix_from_compiler(self):
        if not self.verifier:
            self.skipTest("pia-lsp was built without the verifier")
        uri = "file:///tmp/shadow2.pia"
        self.client.open(uri, SHADOW)
        diags = self.client.diagnostics(
            uri, lambda ds: any("shadows" in d["message"] for d in ds),
            timeout=60)
        diags = [d for d in diags if "rename it to" in d["message"]
                 and d["range"]["start"]["line"] == 2]
        if not diags:
            self.skipTest("this compiler does not suggest a name yet")
        actions = self.client.request("textDocument/codeAction", {
            "textDocument": {"uri": uri}, "range": diags[0]["range"],
            "context": {"diagnostics": diags[:1]}})["result"]
        self.assertEqual(len(actions), 1)
        self.assertEqual(self.apply(SHADOW, actions[0]["edit"]["changes"][uri]),
                         SHADOW_FIXED)

    def test_lint_quick_fix(self):
        # ADR 0037: a constant bound on one parameter is a range type.
        uri = "file:///tmp/range.pia"
        self.client.open(uri, RANGE)
        diags = self.client.diagnostics(
            uri, lambda ds: any(d.get("source") == "pia-lint" for d in ds))
        lints = [d for d in diags if d.get("source") == "pia-lint"]
        self.assertEqual(len(lints), 1)
        d = lints[0]
        self.assertEqual(d["code"], "range_requires")
        self.assertEqual(d["severity"], 2)
        self.assertEqual(d["range"]["start"], pos(RANGE, "requires"))
        self.assertIn("int{0..99}", d["message"])
        actions = self.client.request("textDocument/codeAction", {
            "textDocument": {"uri": uri}, "range": d["range"],
            "context": {"diagnostics": [d]}})["result"]
        self.assertEqual(len(actions), 1)
        a = actions[0]
        self.assertEqual(a["kind"], "quickfix")
        self.assertTrue(a["isPreferred"])
        self.assertEqual(a["title"],
                         "Move the bound into the type: (x : int{0..99})")
        self.assertEqual(self.apply(RANGE, a["edit"]["changes"][uri]),
                         RANGE_FIXED)

    def test_unknown_request(self):
        reply = self.client.request("textDocument/foldingRange", {
            "textDocument": {"uri": "file:///none.pia"}})
        self.assertEqual(reply["error"]["code"], -32601)

    def test_proofs(self):
        if not self.verifier:
            self.skipTest("pia-lsp was built without the verifier")
        uri = "file:///tmp/failing.pia"
        self.client.open(uri, FAILING)
        diags = self.client.diagnostics(
            uri, lambda ds: any(d.get("source") == "pia-verify" for d in ds),
            timeout=60)
        failed = [d for d in diags if d.get("source") == "pia-verify"]
        self.assertEqual(len(failed), 1)
        d = failed[0]
        self.assertEqual(d["severity"], 1)
        self.assertEqual(d["code"], "nooverflow")
        self.assertIn("'+' does not overflow u8", d["message"])
        self.assertIn("counterexample: a = ", d["message"])
        self.assertEqual(d["range"]["start"], pos(FAILING, "+"))

        # Hover on the '+' shows the goal and its counterexample; hover on
        # the safe '+' shows how it was proved.
        hover = self.client.request("textDocument/hover", {
            "textDocument": {"uri": uri},
            "position": pos(FAILING, "+")})["result"]["contents"]["value"]
        self.assertIn("not proved", hover)
        self.assertIn("counterexample", hover)
        hover = self.client.request("textDocument/hover", {
            "textDocument": {"uri": uri},
            "position": pos(FAILING, "+", nth=1)})["result"]["contents"]["value"]
        self.assertIn("proved: '+' does not overflow u16", hover)
        self.assertIn("intervals", hover)

        # An edit drops the stale proof diagnostics until the next save.
        self.client.notify("textDocument/didChange", {
            "textDocument": {"uri": uri, "version": 2},
            "contentChanges": [{"text": FAILING + "\n"}]})
        diags = self.client.diagnostics(uri)
        self.assertEqual(diags, [])
        self.client.notify("textDocument/didSave", {
            "textDocument": {"uri": uri}})
        self.client.diagnostics(
            uri, lambda ds: any(d.get("source") == "pia-verify" for d in ds),
            timeout=60)

    def test_type_error(self):
        if not self.verifier:
            self.skipTest("pia-lsp was built without the verifier")
        uri = "file:///tmp/types.pia"
        text = "let f (x : u8) : u8 = nope x\n"
        self.client.open(uri, text)
        diags = self.client.diagnostics(uri, lambda ds: len(ds) > 0, timeout=60)
        self.assertEqual(diags[0]["severity"], 1)
        self.assertEqual(diags[0]["range"]["start"]["line"], 0)


if __name__ == "__main__":
    SERVER = sys.argv.pop(1)
    unittest.main()
