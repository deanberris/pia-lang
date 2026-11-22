"""Reference lexer for Pia.

This is the executable form of the lexical grammar in docs/grammar.md. It
feeds the reference parser in pia_grammar.py and exists so the grammar can be
tested before the C++ front end (milestone M2) is written. The C++ lexer must
produce the same token stream for every file in tests/grammar.
"""

import re
from dataclasses import dataclass

KEYWORDS = {
    "let": "LET", "rec": "REC", "meta": "META", "in": "IN", "type": "TYPE",
    "of": "OF", "where": "WHERE", "if": "IF", "then": "THEN", "else": "ELSE",
    "match": "MATCH", "with": "WITH", "for": "FOR", "spread": "SPREAD",
    "while": "WHILE", "do": "DO", "done": "DONE",
    "requires": "REQUIRES", "ensures": "ENSURES", "invariant": "INVARIANT",
    "decreases": "DECREASES", "assert": "ASSERT", "assume": "ASSUME",
    "forall": "FORALL", "exists": "EXISTS", "interface": "INTERFACE",
    "sig": "SIG", "module": "MODULE", "struct": "STRUCT", "end": "END",
    "import": "IMPORT", "operator": "OPERATOR", "true": "TRUE",
    "false": "FALSE", "borrowed": "BORROWED", "moved": "MOVED", "out": "OUT",
    "inout": "INOUT", "fixed": "FIXED", "mutable": "MUTABLE",
    # Errors and scope cleanup (ADR 0028).
    "handle": "HANDLE", "defer": "DEFER", "as": "AS",
    # Alphanumeric operators from the bootstrap table.
    "mod": "OP_MUL",
}

OPERATOR_CHARS = set("+-*/<>=|&^~!%?")

# Operators whose meaning is fixed by the grammar.
RESERVED_OPERATORS = {
    "->": "ARROW", "=>": "FATARROW", "<-": "LARROW", "=": "EQ", "|": "BAR",
    "?": "QUESTION",
}

# The bootstrap operator table. Once the meta engine exists (M7) this comes
# from the prelude's `let meta operator` declarations instead.
BOOTSTRAP_OPERATORS = {
    "==>": "OP_IMP", "<==>": "OP_IMP",
    "||": "OP_OR",
    "&&": "OP_AND",
    "<>": "OP_CMP", "<": "OP_CMP", ">": "OP_CMP", "<=": "OP_CMP",
    ">=": "OP_CMP",
    "+": "OP_ADD", "-": "OP_ADD", "+|": "OP_ADD", "-|": "OP_ADD",
    "*": "OP_MUL", "/": "OP_MUL", "%": "OP_MUL",
    "<<": "OP_SHIFT", ">>": "OP_SHIFT", "^": "OP_BXOR", "&": "OP_BAND",
    "~": "OP_TILDE",
}


def classify_operator(text):
    """Return the terminal for an operator spelling.

    Operators not in the bootstrap table get a level from their first
    character, as in OCaml. A `let meta operator` declaration overrides this.
    """
    if text in RESERVED_OPERATORS:
        return RESERVED_OPERATORS[text]
    if text in BOOTSTRAP_OPERATORS:
        return BOOTSTRAP_OPERATORS[text]
    first = text[0]
    if text.startswith("||"):
        return "OP_OR"
    if text.startswith("&&"):
        return "OP_AND"
    if first in "=<>|&$!":
        return "OP_CMP"
    if first in "+-":
        return "OP_ADD"
    return "OP_MUL"


# Tokens that may begin a top-level item when they start in column 1.
ITEM_STARTERS = {
    "LET", "INTERFACE", "MODULE", "IMPORT", "IDENT", "QIDENT", "SPLICE_IDENT",
    "SPLICE_OPEN", "QUOTE_OPEN", "INT", "FLOAT", "STRING", "LPAREN",
    "LBRACKET",
}

OPENERS = {"LPAREN", "LBRACKET", "LBRACE", "LBRACE_ADJ", "QUOTE_OPEN",
           "SPLICE_OPEN", "ATTR_OPEN", "SIG", "STRUCT", "DO"}
CLOSERS = {"RPAREN", "RBRACKET", "RBRACE", "END", "DONE"}


class LexError(Exception):
    def __init__(self, message, line, column):
        super().__init__(f"{line}:{column}: {message}")
        self.line = line
        self.column = column


@dataclass
class Tok:
    type: str
    value: str
    line: int
    column: int  # 1-based
    start: int
    end: int


def _is_ident_start(c):
    return c.isalpha() or c == "_"


def _is_ident_char(c):
    return c.isalnum() or c in "_'"


class Lexer:
    def __init__(self, text):
        self.text = text
        self.pos = 0
        self.line = 1
        self.line_start = 0
        self.out = []
        self.depth = 0
        # Stack of bracket depths at which an explicit type argument list
        # `name<...>` was opened.
        self.targs = []
        # Bracket depth of an open `for` header; `step` is a keyword only
        # between `for` and its `do`.
        self.for_headers = []

    # -- helpers ---------------------------------------------------------
    def peek(self, k=0):
        i = self.pos + k
        return self.text[i] if i < len(self.text) else ""

    def error(self, message):
        raise LexError(message, self.line, self.pos - self.line_start + 1)

    def advance(self, n=1):
        for _ in range(n):
            if self.pos < len(self.text) and self.text[self.pos] == "\n":
                self.line += 1
                self.line_start = self.pos + 1
            self.pos += 1

    def name_then_colon_follows(self):
        m = re.compile(r"\s*[A-Za-z_][A-Za-z0-9_']*\s*:(?!:)").match(self.text, self.pos)
        return m is not None

    def name_follows(self):
        i = self.pos
        while i < len(self.text) and self.text[i] in " \t\r\n":
            i += 1
        return i < len(self.text) and _is_ident_start(self.text[i])

    def emit(self, type_, start, line, column):
        value = self.text[start:self.pos]
        tok = Tok(type_, value, line, column, start, self.pos)
        if column == 1 and self.depth == 0 and self.out and \
                type_ in ITEM_STARTERS and self.out[-1].type != "SEP":
            self.out.append(Tok("SEP", "", line, column, start, start))
        if type_ in OPENERS:
            self.depth += 1
        elif type_ in CLOSERS:
            self.depth -= 1
            if self.depth < 0:
                raise LexError(f"unbalanced '{value}'", line, column)
            while self.targs and self.targs[-1] > self.depth:
                self.targs.pop()
        self.out.append(tok)
        return tok

    # -- scanning --------------------------------------------------------
    def skip_comment(self):
        depth = 0
        while True:
            if self.pos >= len(self.text):
                self.error("unterminated comment")
            if self.peek() == "(" and self.peek(1) == "*":
                depth += 1
                self.advance(2)
            elif self.peek() == "*" and self.peek(1) == ")":
                depth -= 1
                self.advance(2)
                if depth == 0:
                    return
            else:
                self.advance()

    def scan_number(self):
        if self.peek() == "0" and self.peek(1) in "xXbBoO":
            digits = {"x": "0123456789abcdefABCDEF_", "b": "01_",
                      "o": "01234567_"}[self.peek(1).lower()]
            self.advance(2)
            while self.peek() != "" and self.peek() in digits:
                self.advance()
            kind = "INT"
        else:
            while self.peek().isdigit() or self.peek() == "_":
                self.advance()
            kind = "INT"
            if self.peek() == "." and self.peek(1).isdigit():
                kind = "FLOAT"
                self.advance()
                while self.peek().isdigit() or self.peek() == "_":
                    self.advance()
            if self.peek() in "eE" and (self.peek(1).isdigit() or
                                        (self.peek(1) in "+-" and
                                         self.peek(2).isdigit())):
                kind = "FLOAT"
                self.advance(2)
                while self.peek().isdigit():
                    self.advance()
        # Type suffix: 42u8, 1i64, 2.0f32, 0usize.
        if self.peek() in "uif" and (self.peek(1).isdigit() or
                                     self.text.startswith("size", self.pos + 1)):
            self.advance()
            while _is_ident_char(self.peek()):
                self.advance()
        if _is_ident_char(self.peek()):
            self.error("malformed number literal")
        return kind

    def scan_ident(self):
        while _is_ident_char(self.peek()):
            self.advance()

    def tokenize(self):
        text = self.text
        while True:
            # Whitespace and comments.
            c = self.peek()
            if c == "":
                break
            if c in " \t\r\n":
                self.advance()
                continue
            if c == "(" and self.peek(1) == "*":
                self.skip_comment()
                continue
            if c == "\\":
                # A line comment runs to the end of the line (ADR 0029).
                while self.peek() not in ("", "\n"):
                    self.advance()
                continue

            start, line = self.pos, self.line
            column = self.pos - self.line_start + 1
            prev = text[start - 1] if start > 0 else ""

            if _is_ident_start(c):
                self.scan_ident()
                word = text[start:self.pos]
                kind = KEYWORDS.get(word, "IDENT")
                if word == "step" and self.for_headers and \
                        self.for_headers[-1] == self.depth:
                    kind = "STEP"
                # `spec` and `lemma` are keywords only between `let` (or
                # `let rec`) and the name they define.
                # `adapter` is a keyword only in `let adapter name : ...`.
                if word == "adapter" and self.out and \
                        self.out[-1].type == "LET" and \
                        self.name_then_colon_follows():
                    kind = "ADAPTER"
                if word in ("spec", "lemma") and self.out and \
                        self.out[-1].type in ("LET", "REC") and \
                        self.name_follows():
                    kind = word.upper()
                # `theory`, `sort` and `axiom` are keywords only between
                # `let` and a name (ADR 0036).
                if word in ("theory", "sort", "axiom") and self.out and \
                        self.out[-1].type == "LET" and self.name_follows():
                    kind = word.upper()
                if word == "model" and self.out and \
                        self.out[-1].type == "LET" and \
                        self.name_then_colon_follows():
                    kind = "MODEL"
                if kind in ("FOR", "SPREAD"):
                    self.for_headers.append(self.depth)
                elif kind == "DO" and self.for_headers and \
                        self.for_headers[-1] == self.depth:
                    self.for_headers.pop()
                self.emit(kind, start, line, column)
                if kind == "IDENT":
                    # `name<` with no space opens explicit type arguments.
                    if self.peek() == "<" and self.peek(1) not in "-=":
                        s, col = self.pos, self.pos - self.line_start + 1
                        self.advance()
                        self.targs.append(self.depth + 1)
                        self.emit("TARGS_OPEN", s, self.line, col)
                        self.depth += 1
                    # `name{` with no space: a range-refined type, int{0..255}.
                    elif self.peek() == "{":
                        s, col = self.pos, self.pos - self.line_start + 1
                        self.advance()
                        self.emit("LBRACE_ADJ", s, self.line, col)
                continue

            if c.isdigit():
                kind = self.scan_number()
                self.emit(kind, start, line, column)
                continue

            if c == '"':
                self.advance()
                while self.peek() != '"':
                    if self.peek() in ("", "\n"):
                        self.error("unterminated string literal")
                    if self.peek() == "\\":
                        self.advance()
                    self.advance()
                self.advance()
                self.emit("STRING", start, line, column)
                continue

            if c == "`":
                self.advance()
                if self.peek() == "(":
                    self.advance()
                    self.emit("QUOTE_OPEN", start, line, column)
                elif _is_ident_start(self.peek()):
                    self.scan_ident()
                    self.emit("QIDENT", start, line, column)
                else:
                    self.error("expected '(' or an identifier after '`'")
                continue

            if c == "$":
                self.advance()
                if self.peek() == "(":
                    self.advance()
                    self.emit("SPLICE_OPEN", start, line, column)
                elif _is_ident_start(self.peek()) or (
                        self.peek() == "!" and _is_ident_start(self.peek(1))):
                    # `$!name` escapes hygiene.
                    if self.peek() == "!":
                        self.advance()
                    self.scan_ident()
                    self.emit("SPLICE_IDENT", start, line, column)
                else:
                    self.error("expected '(' or an identifier after '$'")
                continue

            if c == "@":
                self.advance()
                if not _is_ident_start(self.peek()):
                    self.error("expected an attribute name after '@'")
                self.scan_ident()
                if self.peek() == "(":
                    self.advance()
                    self.emit("ATTR_OPEN", start, line, column)
                else:
                    self.emit("ATTR", start, line, column)
                continue

            if c == ".":
                if text.startswith("...", start):
                    self.advance(3)
                    self.emit("HOLE", start, line, column)
                elif self.peek(1) == ".":
                    self.advance(2)
                    self.emit("DOTDOT", start, line, column)
                elif self.peek(1) == "[":
                    self.advance(2)
                    self.emit("DOT_LBRACKET", start, line, column)
                    self.depth += 1  # closed by the matching RBRACKET
                elif self.peek(1) in ("", " ", "\t", "\r", "\n"):
                    # A dot followed by whitespace ends quantifier binders:
                    # forall i in 0..n. p i
                    self.advance()
                    self.emit("QDOT", start, line, column)
                else:
                    self.advance()
                    self.emit("DOT", start, line, column)
                continue

            if c in OPERATOR_CHARS:
                # Closing an explicit type argument list.
                if c == ">" and self.targs and self.targs[-1] == self.depth:
                    self.advance()
                    self.targs.pop()
                    self.depth -= 1
                    self.out.append(Tok("TARGS_CLOSE", ">", line, column,
                                        start, self.pos))
                    continue
                while self.peek() in OPERATOR_CHARS and self.peek() != "":
                    # Stop before a comment opener inside an operator run.
                    self.advance()
                op = text[start:self.pos]
                self.emit(classify_operator(op), start, line, column)
                continue

            simple = {
                "(": "LPAREN", ")": "RPAREN", "[": "LBRACKET",
                "]": "RBRACKET", "{": "LBRACE", "}": "RBRACE",
                ",": "COMMA", ":": "COLON",
            }
            if c == ";":
                if self.peek(1) == ";":
                    self.advance(2)
                    self.out.append(Tok("SEP", ";;", line, column, start,
                                        self.pos))
                else:
                    self.advance()
                    self.emit("SEMI", start, line, column)
                continue
            if c in simple:
                self.advance()
                self.emit(simple[c], start, line, column)
                continue

            self.error(f"unexpected character {c!r}")

        if self.targs:
            raise LexError("a type argument list opened by 'name<' is never "
                           "closed; write 'a < b', with spaces, for "
                           "less-than", self.line,
                           self.pos - self.line_start + 1)
        if self.depth != 0:
            raise LexError("unclosed bracket, 'sig', 'struct' or 'do' at end "
                           "of input", self.line,
                           self.pos - self.line_start + 1)
        return self.out


def tokenize(text):
    return Lexer(text).tokenize()
