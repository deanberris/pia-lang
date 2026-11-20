"""Reference parser for Pia: pia.lark driven by the tokens from pia_lexer.py."""

import os

from lark import Lark, Token
from lark.lexer import Lexer as LarkLexer

from pia_lexer import tokenize

_HERE = os.path.dirname(os.path.abspath(__file__))


class _PiaLarkLexer(LarkLexer):
    def __init__(self, lexer_conf):
        pass

    def lex(self, data):
        for t in tokenize(data):
            yield Token(t.type, t.value, start_pos=t.start, line=t.line,
                        column=t.column, end_pos=t.end)


def make_parser(start="start", ambiguity="resolve"):
    with open(os.path.join(_HERE, "pia.lark")) as f:
        grammar = f.read()
    return Lark(grammar, parser="earley", lexer=_PiaLarkLexer, start=start,
                ambiguity=ambiguity, propagate_positions=True)
