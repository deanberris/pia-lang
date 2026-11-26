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

    def test_bare_expressions_evaluate(self):
        # An expression at column 1 is any expression, not only a
        # metaprogram's invocation as in a file: on its own, after a
        # definition in the same cell, and several to a cell.
        r = self.repl.run("1 + 2")
        self.assertTrue(r["ok"], r)
        self.assertEqual([(v["type"], v["value"]) for v in kinds(r, "value")],
                         [("i32", "3")])
        r = self.repl.run("let three : u8 = 3\nthree + 1")
        self.assertTrue(r["ok"], r)
        self.assertEqual([v["value"] for v in kinds(r, "value")], ["4"])
        r = self.repl.run("three * 2\nif three < 5 then 1 else 0")
        self.assertTrue(r["ok"], r)
        self.assertEqual([v["value"] for v in kinds(r, "value")], ["6", "1"])
        # A `-` at column 1 starts a new expression; an indented one carries
        # the subtraction on.
        r = self.repl.run("three\n-1")
        self.assertEqual([v["value"] for v in kinds(r, "value")], ["3", "-1"])
        r = self.repl.run("three\n  - 1")
        self.assertEqual([v["value"] for v in kinds(r, "value")], ["2"])

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

    def test_theory_and_trusting(self):
        # A theory, and `import T trusting`, work in the REPL as in a file
        # (ADR 0036): the import changes nothing in the module that declares
        # T, and a lemma over T is proved from its axioms.
        r = self.repl.run("@trusted\n"
                          "let theory T = sig\n"
                          "  let sort s\n"
                          "  let spec f : (x : s) -> u8\n"
                          "  let axiom small (x : s) ensures f x < 10\n"
                          "end")
        self.assertTrue(r["ok"], r)
        r = self.repl.run("import T trusting")
        self.assertTrue(r["ok"], r)
        r = self.repl.run("let lemma l (x : T.s) : unit ensures T.f x < 11 = ()")
        self.assertTrue(r["ok"], r)
        self.assertTrue(kinds(r, "proof"), r)
        self.assertTrue(all(p["status"] == "proved" for p in kinds(r, "proof")))

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

    def test_floats(self):
        # f32 and f64 values show as the shortest literal that reads back
        # as the same value, without the suffix: the type says which.
        r = self.repl.run("let third (x : f32) : f32 = x / 3.0")
        self.assertTrue(r["ok"], r)
        r = self.repl.run("third 1.0f32\n0.1 + 0.2f64\n-0.0f32\n1.0e30 * 1.0e10f32")
        self.assertTrue(r["ok"], r)
        self.assertEqual([(v["type"], v["value"]) for v in kinds(r, "value")],
                         [("f32", "0.33333334"), ("f64", "0.30000000000000004"),
                          ("f32", "-0.0"), ("f32", "inf")])
        self.repl.run("let point = type { x : f32; y : f64 }")
        r = self.repl.run("let make (s : f32) : point = { x = s; y = 2.0e-3 }")
        self.assertTrue(r["ok"], r)
        r = self.repl.run("make 0.5f32")
        self.assertTrue(r["ok"], r)
        self.assertEqual(kinds(r, "value")[0]["value"], "{ x = 0.5; y = 0.002 }")

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


STEP = ("let step (a : u64) : u64\n"
        "  requires a < 1000\n"
        "  ensures result = 1\n"
        "= 1")
TOTAL = ("let total (n : u64) : u64\n"
         "  requires n <= 8000000000\n"
         "= let s : mutable u64 = 0 in\n"
         "  for i in 0 .. n\n"
         "    invariant s <= 2 * i\n"
         "  do s <- s + step 5 done;\n"
         "  s")
# Long enough to still be running while the next few cells are checked:
# code a task runs counts its calls, which costs a few nanoseconds each.
LONG = 1000000000
# step is called by chunk, which many calls, so a change to step's contract
# swaps step and chunk together, between two calls of chunk.
CHUNK = ("let chunk (k : u64) : u64\n"
         "  requires k <= 1000\n"
         "  ensures result <= 2 * k\n"
         "= let s : mutable u64 = 0 in\n"
         "  for i in 0 .. k\n"
         "    invariant s <= 2 * i\n"
         "  do s <- s + step 5 done;\n"
         "  s")
MANY = ("let many (n : u64) : u64\n"
        "  requires n <= 8000000\n"
        "= let s : mutable u64 = 0 in\n"
        "  for i in 0 .. n\n"
        "    invariant s <= 2000 * i\n"
        "  do s <- s + chunk 1000 done;\n"
        "  s")
WEAKER = (":redef let step (a : u64) : u64 requires a < 1000 "
          "ensures result <= 2 = 2")


class LiveTest(unittest.TestCase):
    """Tasks, and redefinition while they run (ADR 0031)."""

    def setUp(self):
        self.repl = Repl()
        self.assertTrue(self.repl.run(STEP)["ok"])
        self.assertTrue(self.repl.run(TOTAL)["ok"])

    def tearDown(self):
        self.repl.close()

    def spawn(self):
        r = self.repl.run(f":spawn total {LONG}")
        self.assertTrue(r["ok"], r)
        [t] = kinds(r, "task")
        self.assertEqual(t["status"], "running")
        return t["name"]

    def test_tasks_finish_with_a_value(self):
        r = self.repl.run(":spawn total 1000")
        self.assertEqual(kinds(r, "task")[0]["name"], "1")
        r = self.repl.run(":wait 1")
        [t] = kinds(r, "task")
        self.assertEqual((t["status"], t["type"], t["value"]), ("done", "usize", "1000"))
        self.assertEqual(kinds(self.repl.run(":tasks"), "task")[0]["value"], "1000")

    def test_refinement_swaps_into_a_running_task(self):
        task = self.spawn()
        # The same contract and a new body: proved against the old contract,
        # so it is swapped in while the task runs.
        r = self.repl.run(":redef let step (a : u64) : u64 requires a < 1000 "
                          "ensures result = 1 = 2 - 1")
        self.assertTrue(r["ok"], r)
        [d] = kinds(r, "redefined")
        self.assertIn("swapped into running task " + task, d["text"])
        self.assertEqual(self.repl.run("total 10")["events"][-1]["value"], "10")
        r = self.repl.run(":wait " + task)
        self.assertEqual(kinds(r, "task")[0]["value"], str(LONG))

    def test_a_change_that_does_not_refine_waits_for_the_task(self):
        task = self.spawn()
        # total still verifies with this step, but the running task was
        # proved against `result = 1`, which the new body breaks.
        # It would have to be swapped together with total, which the task
        # never leaves.
        r = self.repl.run(WEAKER)
        self.assertFalse(r["ok"], r)
        text = kinds(r, "error")[0]["text"]
        self.assertIn("can only be swapped together", text)
        self.assertRegex(text, r"stayed inside [^;]*'total'")
        self.assertEqual(self.repl.run("total 10")["events"][-1]["value"], "10")
        self.repl.run(":wait " + task)
        r = self.repl.run(WEAKER)
        self.assertTrue(r["ok"], r)
        self.assertEqual(self.repl.run("total 10")["events"][-1]["value"], "20")

    def test_a_contract_change_swaps_with_its_callers(self):
        self.assertTrue(self.repl.run(CHUNK)["ok"])
        self.assertTrue(self.repl.run(MANY)["ok"])
        n = LONG // 1000
        r = self.repl.run(f":spawn many {n}")
        [t] = kinds(r, "task")
        # chunk still verifies with the weaker step, and many relies only on
        # chunk's contract, so step and chunk are swapped together at a
        # moment when the task is between two calls of chunk.
        r = self.repl.run(WEAKER)
        self.assertTrue(r["ok"], r)
        [d] = kinds(r, "redefined")
        self.assertIn("swapped into running task " + t["name"], d["text"])
        self.assertIn("no task was running 'chunk' or 'step'", d["text"])
        value = int(kinds(self.repl.run(":wait " + t["name"]), "task")[0]["value"])
        # Every chunk ran wholly old code or wholly new code.
        self.assertEqual(value % 1000, 0)
        self.assertGreater(value, LONG)
        self.assertLessEqual(value, 2 * LONG)

    def test_forget_waits_for_the_task(self):
        task = self.spawn()
        r = self.repl.run(":forget total")
        self.assertFalse(r["ok"], r)
        self.assertIn("running task", kinds(r, "error")[0]["text"])
        r = self.repl.run(":reset")
        self.assertFalse(r["ok"], r)
        self.repl.run(":wait " + task)
        self.assertTrue(self.repl.run(":forget total")["ok"])

    def test_unrelated_definitions_while_a_task_runs(self):
        task = self.spawn()
        r = self.repl.run("let other (a : u8) : u8 = a")
        self.assertTrue(r["ok"], r)
        self.assertEqual(self.repl.run("other 4")["events"][-1]["value"], "4")
        self.assertEqual(kinds(self.repl.run(":tasks"), "task")[0]["status"], "running")

    def test_metaprograms_redefine_with_pia_live(self):
        r = self.repl.run("let meta faster () = redefine `( let step (a : u64) : u64 "
                          "requires a < 1000 ensures $!result = 1 = 1 + 0 )")
        self.assertTrue(r["ok"], r)
        task = self.spawn()
        r = self.repl.run("faster ()")
        self.assertTrue(r["ok"], r)
        [d] = kinds(r, "redefined")
        self.assertEqual(d["name"], "step")
        self.assertIn("swapped into running task " + task, d["text"])
        # It stays redefined in later cells.
        self.assertTrue(self.repl.run("let after : u8 = 1")["ok"])
        r = self.repl.run(":source step")
        self.assertTrue(r["ok"], r)


COUNT = ("let count : mutable u8\n"
         "  invariant count <= 100\n"
         "= 0")
BUMP = "let bump () : unit = if count < 100 then count <- count + 1 else ()"
HITS = ("let hits : mutable u64\n"
        "  invariant hits <= 8000000000\n"
        "= 0")
HIT = "let hit () : unit = if hits < 8000000000 then hits <- hits + 1 else ()"
RUN = ("let run (n : u64) : unit\n"
       "  requires n <= 8000000000\n"
       "= for i in 0 .. n do hit () done")


class StateTest(unittest.TestCase):
    """Top-level state, its invariant, and migration (ADR 0031, "State")."""

    def setUp(self):
        self.repl = Repl()

    def tearDown(self):
        self.repl.close()

    def value(self, code):
        r = self.repl.run(code)
        self.assertTrue(r["ok"], r)
        return kinds(r, "value")[0]["value"]

    def test_state_persists_between_cells(self):
        r = self.repl.run(COUNT)
        self.assertTrue(r["ok"], r)
        [d] = kinds(r, "defined")
        self.assertEqual((d["name"], d["type"], d["value"]), ("count", "mutable u8", "0"))
        r = self.repl.run(BUMP)
        # The state is not a parameter the caller sees.
        self.assertEqual(kinds(r, "defined")[0]["type"], "() -> unit")
        self.value("bump ()")
        self.value("bump ()")
        self.assertEqual(self.value("count"), "2")
        self.value("count <- 7")
        self.assertEqual(self.value("count"), "7")
        self.assertEqual(self.value("count + 1"), "8")

    def test_the_invariant_is_kept(self):
        self.assertTrue(self.repl.run(COUNT)["ok"])
        r = self.repl.run("count <- 200")
        self.assertFalse(r["ok"], r)
        [p] = [e for e in kinds(r, "proof") if e["status"] == "failed"]
        self.assertEqual(p["where"], {"cell": 1, "line": 2, "column": 19})
        r = self.repl.run("let tick () : unit = count <- count + 1")
        self.assertFalse(r["ok"], r)
        r = self.repl.run("let bad : mutable u8\n  invariant bad <= 3\n= 4")
        self.assertFalse(r["ok"], r)
        self.assertEqual(self.value("count"), "0")

    def test_loops_keep_the_invariant(self):
        for code in (HITS, HIT, RUN):
            self.assertTrue(self.repl.run(code)["ok"], code)
        self.value("run 1000")
        self.assertEqual(self.value("hits"), "1000")

    def test_migration(self):
        self.assertTrue(self.repl.run(COUNT)["ok"])
        self.assertTrue(self.repl.run(BUMP)["ok"])
        self.value("bump ()")
        self.value("bump ()")
        r = self.repl.run(":redef let count : mutable u16 invariant count <= 1000 "
                          "= old count * 10")
        self.assertTrue(r["ok"], r)
        [d] = kinds(r, "redefined")
        self.assertEqual((d["type"], d["value"], d["text"]),
                         ("mutable u16", "20", "migrated from mutable u8"))
        self.value("bump ()")
        self.assertEqual(self.value("count"), "21")
        # Back to u8 cannot hold every value the old invariant allows.
        r = self.repl.run(":redef let count : mutable u8 invariant count <= 100 "
                          "= old count")
        self.assertFalse(r["ok"], r)
        self.assertEqual(self.value("count"), "21")
        # Without `old`, a redefinition starts again.
        r = self.repl.run(":redef let count : mutable u8 invariant count <= 100 = 5")
        self.assertTrue(r["ok"], r)
        self.assertEqual(self.value("count"), "5")
        r = self.repl.run("let fresh : mutable u8 = old fresh")
        self.assertFalse(r["ok"], r)

    def test_a_task_owns_its_state(self):
        for code in (HITS, HIT, RUN):
            self.assertTrue(self.repl.run(code)["ok"], code)
        r = self.repl.run(f":spawn run {LONG}")
        [t] = kinds(r, "task")
        for code in ("hits", "hits <- 0",
                     ":redef let hits : mutable u64 invariant hits <= 9000000000 "
                     "= old hits"):
            r = self.repl.run(code)
            self.assertFalse(r["ok"], r)
            self.assertIn("belongs to a running task", kinds(r, "error")[0]["text"])
        # A new body for hit that keeps its contract, and so the invariant,
        # is swapped into the task.
        r = self.repl.run(":redef let hit () : unit = "
                          "if hits < 7999999999 then hits <- hits + 1 else ()")
        self.assertTrue(r["ok"], r)
        self.assertIn("swapped into running task", kinds(r, "redefined")[0]["text"])
        # One that can break it is not.
        r = self.repl.run(":redef let hit () : unit = hits <- hits + 1")
        self.assertFalse(r["ok"], r)
        self.repl.run(":wait " + t["name"])
        self.assertEqual(self.value("hits"), str(LONG))

    def test_only_state_has_an_invariant(self):
        r = self.repl.run("let f (a : u8) : u8\n  invariant a <= 3\n= a")
        self.assertFalse(r["ok"], r)
        self.assertIn("belongs to a state", kinds(r, "error")[0]["text"])


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
    import os
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import shard
    shard.main(sys.modules[__name__])
