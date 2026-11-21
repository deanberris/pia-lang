"""End-to-end tests for `pia mcp`: the execute and poll tools over stdio.

    python3 tests/repl/mcp_test.py path/to/pia
"""

import json
import os
import subprocess
import sys
import tempfile
import unittest

PIA = None


class Server:
    def __init__(self):
        self.proc = subprocess.Popen([PIA, "mcp"], stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, text=True)
        self.next_id = 0

    def send(self, method, params=None, notify=False):
        msg = {"jsonrpc": "2.0", "method": method}
        if params is not None:
            msg["params"] = params
        if not notify:
            self.next_id += 1
            msg["id"] = self.next_id
        self.proc.stdin.write(json.dumps(msg) + "\n")
        self.proc.stdin.flush()
        if notify:
            return None
        reply = json.loads(self.proc.stdout.readline())
        assert reply["id"] == self.next_id, reply
        return reply

    def call(self, name, **args):
        return self.send("tools/call", {"name": name, "arguments": args})["result"]

    def close(self):
        self.proc.stdin.close()
        self.proc.wait(timeout=60)


class McpTest(unittest.TestCase):
    def setUp(self):
        self.server = Server()
        init = self.server.send("initialize", {
            "protocolVersion": "2025-06-18", "capabilities": {},
            "clientInfo": {"name": "test", "version": "0"}})
        self.assertIn("tools", init["result"]["capabilities"])
        self.server.send("notifications/initialized", notify=True)

    def tearDown(self):
        self.server.close()

    def test_lists_exactly_execute_and_poll(self):
        tools = self.server.send("tools/list")["result"]["tools"]
        self.assertEqual(sorted(t["name"] for t in tools), ["execute", "poll"])

    def test_execute_builds_a_session(self):
        r = self.server.call("execute", code="let sum (a : u8) (b : u8) : u16 = a + b",
                             json=True)
        self.assertFalse(r["isError"], r)
        self.assertEqual(r["structuredContent"]["status"], "done")
        r = self.server.call("execute", code="sum 40 2", json=True)
        events = r["structuredContent"]["result"]["events"]
        self.assertEqual(events[-1]["value"], "42")
        self.assertIn("- : u16 = 42", r["content"][0]["text"])

    def test_failures_are_errors_with_counterexamples(self):
        r = self.server.call("execute", code="let bad (a : u8) : u8 = a + 1")
        self.assertTrue(r["isError"])
        self.assertIn("counterexample", r["content"][0]["text"])

    def test_poll_a_job(self):
        r = self.server.call("execute", code="let x : u8 = 7", wait_ms=0, json=True)
        job = r["structuredContent"]["job"]
        r = self.server.call("poll", job=job, wait_ms=60000, json=True)
        self.assertEqual(r["structuredContent"]["status"], "done")
        self.assertEqual(r["structuredContent"]["result"]["events"][0]["value"], "7")

    def test_poll_unknown_job(self):
        r = self.server.call("poll", job=99, json=True)
        self.assertTrue(r["isError"])
        self.assertEqual(r["structuredContent"]["status"], "unknown")

    def test_text_only_by_default(self):
        # Clients that see structuredContent show it instead of the text, so
        # it is sent only on request.
        r = self.server.call("execute", code="let sum (a : u8) (b : u8) : u16 = a + b")
        self.assertNotIn("structuredContent", r)
        self.assertIn("sum : (a : u8) -> (b : u8) -> u16", r["content"][0]["text"])

    def test_running_job_number_is_in_the_text(self):
        r = self.server.call("execute", code="let y : u8 = 9", wait_ms=0)
        text = r["content"][0]["text"]
        if "call poll" in text:
            job = int(text.split()[1])
            r = self.server.call("poll", job=job, wait_ms=60000)
        self.assertIn("y : u8 = 9", r["content"][0]["text"])

    def test_load_a_literate_file(self):
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "two.pia.md")
            with open(path, "w") as f:
                f.write("# Two\n\nProse with `code` and a # heading.\n\n"
                        "```pia\nlet add2 (a : u8) : u8 requires a < 200 = a + 2\n```\n\n"
                        "```ocaml\nlet ignored = this is not Pia\n```\n\n"
                        "More prose.\n\n```pia\nlet four (a : u8) : u8\n"
                        "  requires a < 100\n= add2 a\n```\n")
            r = self.server.call("execute", code=":load " + path)
        self.assertFalse(r["isError"], r)
        text = r["content"][0]["text"]
        self.assertIn("add2 : (a : u8) -> u8", text)
        self.assertIn("four : (a : u8) -> u8", text)
        r = self.server.call("execute", code="four 40")
        self.assertIn("- : u8 = 42", r["content"][0]["text"])

    def test_unknown_method(self):
        self.assertIn("error", self.server.send("resources/list"))


if __name__ == "__main__":
    PIA = sys.argv.pop(1)
    unittest.main()
