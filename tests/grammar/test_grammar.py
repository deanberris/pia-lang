"""Grammar tests: every example in docs/design.md, plus the valid and
invalid cases in this directory, against the reference grammar.

Run with: python3 tests/grammar/test_grammar.py
"""

import glob
import os
import re
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "grammar"))

from pia_grammar import make_parser  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
PARSER = make_parser(start=["start", "contract_fragment"])


def parse(src):
    stripped = re.sub(r"\(\*.*?\*\)", "", src, flags=re.S).lstrip()
    start = "contract_fragment" if stripped.startswith(("requires", "ensures")) else "start"
    return PARSER.parse(src, start=start)


def design_examples():
    with open(os.path.join(ROOT, "docs", "design.md")) as f:
        text = f.read()
    for m in re.finditer(r"^```ocaml\n(.*?)^```", text, flags=re.S | re.M):
        line = text.count("\n", 0, m.start()) + 1
        yield line, m.group(1)


def subtrees(tree, name):
    return [t for t in tree.iter_subtrees() if t.data == name]


class DesignExamples(unittest.TestCase):
    def test_every_design_example_parses(self):
        examples = list(design_examples())
        self.assertGreater(len(examples), 10)
        for line, src in examples:
            with self.subTest(design_md_line=line):
                parse(src)


class ValidCases(unittest.TestCase):
    def test_valid_cases_parse(self):
        files = sorted(glob.glob(os.path.join(HERE, "valid", "*.pia")))
        self.assertTrue(files)
        for path in files:
            with self.subTest(case=os.path.basename(path)):
                with open(path) as f:
                    parse(f.read())


class InvalidCases(unittest.TestCase):
    def test_invalid_cases_are_rejected(self):
        files = sorted(glob.glob(os.path.join(HERE, "invalid", "*.pia")))
        self.assertTrue(files)
        for path in files:
            with self.subTest(case=os.path.basename(path)):
                with open(path) as f:
                    src = f.read()
                with self.assertRaises(Exception):
                    parse(src)


class Disambiguation(unittest.TestCase):
    """The rules in docs/grammar.md, "Disambiguation"."""

    def test_longest_predicate_before_body(self):
        tree = parse("let f (g : t) : unit\n"
                     "  ensures total g = old (total g) - drained g\n"
                     "=\n  step g; finish g\n")
        ensures = subtrees(tree, "ensures")[0]
        self.assertEqual(ensures.children[1].data, "binop")
        self.assertEqual(ensures.children[1].children[1].value, "=")
        let = subtrees(tree, "let_item")[0]
        self.assertEqual(let.children[-1].data, "sequence")

    def test_predicate_without_comparison(self):
        tree = parse("let f (xs : [i32]) : unit\n  requires sorted xs\n= g xs\n")
        requires = subtrees(tree, "requires")[0]
        self.assertEqual(requires.children[1].data, "apply")

    def test_column_one_starts_an_item(self):
        tree = parse("let r = { a = 1 }\n\nmake `thing 4\n")
        self.assertEqual(len(subtrees(tree, "let_item")), 1)
        self.assertEqual(len(subtrees(tree, "expr_item")), 1)

    def test_indented_line_continues_an_item(self):
        tree = parse("let r = f\n  x\n  y\n")
        self.assertEqual(len(subtrees(tree, "apply")[0].children), 3)

    def test_adjacent_angle_is_instantiation(self):
        self.assertEqual(len(subtrees(parse("let w = sum<i64> xs\n"), "instantiate")), 1)
        self.assertEqual(len(subtrees(parse("let w = a < b\n"), "instantiate")), 0)

    def test_named_type_argument(self):
        tree = parse("let g : tiled<cell, 4, halo = 1> = make ()\n")
        self.assertEqual(len(subtrees(tree, "named_targ")), 1)

    def test_modifiers_bind_to_first_parameter(self):
        tree = parse("interface I = sig\n  let enc : borrowed in [u8] -> [u8]\nend\n")
        arrow = subtrees(tree, "arrow")[0]
        dom = arrow.children[0]
        self.assertEqual(len(subtrees(dom, "ownership")), 1)

    def test_quantifier_dot_needs_space(self):
        tree = parse("let p = forall i in 0..n. a.[i] = b.[i]\n")
        self.assertEqual(len(subtrees(tree, "quantifier")), 1)
        self.assertEqual(len(subtrees(tree, "range")), 1)

    def test_application_binds_tighter_than_operators(self):
        tree = parse("let x = f a + g b * h c\n")
        top = subtrees(tree, "let_item")[0].children[-1]
        self.assertEqual(top.data, "binop")
        self.assertEqual(top.children[1].value, "+")


if __name__ == "__main__":
    unittest.main(verbosity=2)
