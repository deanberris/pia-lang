"""End-to-end tests for `pia repl` (ADR 0031, docs/repl.md).

Drives the REPL through its JSON protocol, one session per test, and
checks the events each cell returns. Also checks the text front end on a
pipe.

    python3 tests/repl/repl_test.py path/to/pia
"""

import json
import subprocess
import sys
import unittest

PIA = None


class Repl:
    """A `pia repl --json` process."""

    def __init__(self, *flags):
        self.proc = subprocess.Popen(
            [PIA, "repl", "--json", *flags], stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.next_id = 0

    def run(self, code):
        self.next_id += 1
        self.proc.stdin.write(json.dumps({"id": self.next_id, "code": code}) + "\n")
        self.proc.stdin.flush()
        line = self.proc.stdout.readline()
        if not line:
            raise AssertionError("pia repl exited: " + self.proc.stderr.read())
        reply = json.loads(line)
        assert reply["id"] == self.next_id, reply
        return reply

    def close(self):
        self.proc.stdin.close()
        self.proc.wait(timeout=60)


def kinds(reply, kind):
    return [e for e in reply["events"] if e["kind"] == kind]


class ReplTest(unittest.TestCase):
    def setUp(self):
        self.repl = Repl()

    def tearDown(self):
        self.repl.close()

    def test_define_and_evaluate(self):
        r = self.repl.run("let sum (a : u8) (b : u8) : u16 = a + b")
        self.assertTrue(r["ok"], r)
        [d] = kinds(r, "defined")
        self.assertEqual(d["name"], "sum")
        self.assertEqual(d["type"], "(a : u8) -> (b : u8) -> u16")
        self.assertTrue(all(p["status"] == "proved" for p in kinds(r, "proof")))
        r = self.repl.run("sum 200 100")
        self.assertTrue(r["ok"], r)
        [v] = kinds(r, "value")
        self.assertEqual((v["type"], v["value"]), ("u16", "300"))

    def test_environment_builds_up(self):
        self.repl.run("let double (x : u8) : u16 = x + x")
        self.repl.run("let quad (x : u8) : u32 = double x + double x")
        r = self.repl.run("quad 255")
        self.assertEqual(kinds(r, "value")[0]["value"], "1020")

    def test_constants_show_their_value(self):
        r = self.repl.run("let limit : u8 = 200")
        [d] = kinds(r, "defined")
        self.assertEqual((d["name"], d["type"], d["value"]), ("limit", "u8", "200"))

    def test_failed_obligation_is_not_committed(self):
        r = self.repl.run("let bad (a : u8) (b : u8) : u8 = a + b")
        self.assertFalse(r["ok"])
        [p] = [p for p in kinds(r, "proof") if p["status"] == "failed"]
        self.assertIn("overflow", p["text"])
        self.assertEqual(p["where"]["cell"], 1)
        self.assertIn("a", p["counterexample"])
        r = self.repl.run(":env")
        self.assertIn("empty", kinds(r, "info")[0]["text"])

    def test_call_outside_precondition_fails_before_running(self):
        self.repl.run("let small (a : u8) : u8 requires a < 10 = a")
        r = self.repl.run("small 20")
        self.assertFalse(r["ok"])
        self.assertTrue(any(p["status"] == "failed" for p in kinds(r, "proof")))
        self.assertEqual(kinds(r, "value"), [])

    def test_no_shadowing(self):
        self.repl.run("let f (a : u8) : u8 = a")
        r = self.repl.run("let f (a : u8) : u8 = 0")
        self.assertFalse(r["ok"])
        self.assertIn("f'", kinds(r, "error")[0]["text"])
        self.assertIn(":redef", kinds(r, "error")[0]["text"])

    def test_redefinition_reverifies_dependents(self):
        r = self.repl.run("let step (a : u8) : u8\n"
                          "  requires a < 100\n"
                          "  ensures result > a && result <= a + 2\n"
                          "= a + 1")
        self.assertTrue(r["ok"], r)
        r = self.repl.run("let twice (a : u8) : u8 requires a < 50 = step (step a)")
        self.assertTrue(r["ok"], r)
        self.assertEqual(self.repl.run("twice 3")["events"][-1]["value"], "5")
        # A stronger precondition breaks twice's proof, so it is refused.
        r = self.repl.run(":redef let step (a : u8) : u8\n"
                          "  requires a < 10\n"
                          "  ensures result > a && result <= a + 2\n"
                          "= a + 1")
        self.assertFalse(r["ok"], r)
        self.assertTrue(any(p["status"] == "failed" and p["name"] == "twice"
                            for p in kinds(r, "proof")), r)
        self.assertEqual(self.repl.run("twice 3")["events"][-1]["value"], "5")
        # A new body that keeps the contract is committed, and callers use it.
        r = self.repl.run(":redef let step (a : u8) : u8\n"
                          "  requires a < 100\n"
                          "  ensures result > a && result <= a + 2\n"
                          "= a + 2")
        self.assertTrue(r["ok"], r)
        self.assertEqual(kinds(r, "redefined")[0]["name"], "step")
        self.assertEqual(self.repl.run("twice 3")["events"][-1]["value"], "7")

    def test_redefining_nothing(self):
        r = self.repl.run(":redef let ghost (a : u8) : u8 = a")
        self.assertFalse(r["ok"])
        self.assertIn("no 'ghost'", kinds(r, "error")[0]["text"])

    def test_type_command(self):
        self.repl.run("let sum (a : u8) (b : u8) : u16 = a + b")
        r = self.repl.run(":type sum")
        self.assertEqual(kinds(r, "type")[0]["type"], "(a : u8) -> (b : u8) -> u16")
        r = self.repl.run(":type sum 1 2")
        self.assertEqual(kinds(r, "type")[0]["type"], "u16")

    def test_proof_command(self):
        self.repl.run("let sum (a : u8) (b : u8) : u16 = a + b")
        r = self.repl.run(":proof sum")
        self.assertTrue(kinds(r, "proof"))
        self.assertTrue(all(p["name"] == "sum" for p in kinds(r, "proof")))

    def test_forget(self):
        self.repl.run("let f (a : u8) : u8 = a")
        self.repl.run("let g (a : u8) : u8 = f a")
        r = self.repl.run(":forget f")
        self.assertFalse(r["ok"])
        self.assertTrue(any("'g'" in e["text"] for e in kinds(r, "info")), r)
        self.assertTrue(self.repl.run(":forget g")["ok"])
        self.assertTrue(self.repl.run(":forget f")["ok"])
        self.assertIn("empty", kinds(self.repl.run(":env"), "info")[0]["text"])

    def test_reset(self):
        self.repl.run("let f (a : u8) : u8 = a")
        self.repl.run(":reset")
        self.assertTrue(self.repl.run("let f (a : u8) : u8 = a")["ok"])

    def test_records(self):
        self.repl.run("let pixel = type { r : u8; g : u8 }")
        r = self.repl.run("let make (v : u8) : pixel = { r = v; g = 7 }")
        self.assertTrue(r["ok"], r)
        r = self.repl.run("make 3")
        self.assertEqual(kinds(r, "value")[0]["value"], "{ r = 3; g = 7 }")

    def test_metaprograms_extend_the_environment(self):
        self.repl.run("let pixel = type { r : u8; g : u8 } @derive(eq)")
        r = self.repl.run("eq_pixel { r = 1; g = 2 } { r = 1; g = 2 }")
        self.assertTrue(r["ok"], r)
        self.assertEqual(kinds(r, "value")[0]["value"], "true")

    def test_user_operator(self):
        r = self.repl.run("let meta operator ( ** ) : prec 8 right = "
                          "let (a) (b) => `( mul $a $b )")
        self.assertTrue(r["ok"], r)
        r = self.repl.run("let six : u8 = 1 + 2 ** 3")
        self.assertTrue(r["ok"], r)
        self.assertEqual(kinds(r, "defined")[0]["value"], "7")

    def test_unproved_needs_allow(self):
        loop = ("let spin (n : u8) : u8 =\n"
                "  let i : mutable u8 = 0 in\n"
                "  while i < n do i <- i + 1 done; i")
        r = self.repl.run(loop)
        self.assertFalse(r["ok"], r)
        self.assertTrue(any(p["status"] == "unproved" for p in kinds(r, "proof")), r)
        self.repl.run(":allow spin")
        r = self.repl.run(loop)
        self.assertTrue(r["ok"], r)

    def test_errors_point_into_the_cell(self):
        self.repl.run("let f (a : u8) : u8 = a")
        r = self.repl.run("let g (a : u8) : u8 =\n  f a b")
        self.assertFalse(r["ok"])
        [e] = kinds(r, "error")[:1]
        self.assertEqual(e["where"]["cell"], 2)
        self.assertEqual(e["where"]["line"], 2)

    def test_bad_request(self):
        self.repl.proc.stdin.write("not json\n")
        self.repl.proc.stdin.flush()
        reply = json.loads(self.repl.proc.stdout.readline())
        self.assertFalse(reply["ok"])


class TextTest(unittest.TestCase):
    def test_pipe(self):
        script = (
            "(* a comment is not a cell *)\n"
            "let sum (a : u8) (b : u8) : u16\n"
            "  ensures result >= a\n"
            "= a + b\n"
            "sum 1 2\n"
            ":type sum\n")
        run = subprocess.run([PIA, "repl"], input=script, capture_output=True,
                             text=True, timeout=120)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn("sum : (a : u8) -> (b : u8) -> u16", run.stdout)
        self.assertIn("- : u16 = 3", run.stdout)

    def test_pipe_failure_exit_status(self):
        run = subprocess.run([PIA, "repl"], input="let bad (a : u8) : u8 = a + 1\n",
                             capture_output=True, text=True, timeout=120)
        self.assertEqual(run.returncode, 1)
        self.assertIn("failed: '+' does not overflow u8", run.stdout)
        self.assertIn("counterexample: a = 255", run.stdout)


if __name__ == "__main__":
    PIA = sys.argv.pop(1)
    unittest.main()
