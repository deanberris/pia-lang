#include "syntax/Parser.h"

#include <cctype>
#include <string>
#include <utility>
#include <vector>

#include "syntax/Comments.h"
#include "syntax/Lexer.h"

namespace pia::syntax {
namespace {

using K = TokenKind;
using N = NodeKind;

struct ParseError {
  SourceLoc loc;
  std::string message;
};

using Assoc = Fixity::Assoc;
using OpInfo = Fixity;  // level 0 means "not a binary operator"

// An operator with no declaration gets a level from its first character,
// as in OCaml (docs/grammar.md, "Operators").
// Levels are held in tenths (Fixity).
OpInfo defaultFixity(std::string_view op) {
  if (op.substr(0, 2) == "||") return {20, Assoc::Right};
  if (op.substr(0, 2) == "&&") return {30, Assoc::Right};
  switch (op[0]) {
    case '=': case '<': case '>': case '|': case '&': case '$': case '!':
      return {40, Assoc::None};
    case '+': case '-':
      return {60, Assoc::Left};
    default:
      return {70, Assoc::Left};
  }
}

// "6" is 60 and "6.5" is 65; anything else is 0.
int parseLevel(std::string_view text) {
  int whole = 0, tenth = 0;
  size_t i = 0;
  if (text.empty() || !std::isdigit(static_cast<unsigned char>(text[0])))
    return 0;
  for (; i < text.size() && std::isdigit(static_cast<unsigned char>(text[i]));
       ++i) {
    whole = whole * 10 + (text[i] - '0');
    if (whole > 99) return 0;
  }
  if (i < text.size()) {
    if (text[i] != '.' || i + 2 != text.size() ||
        !std::isdigit(static_cast<unsigned char>(text[i + 1])))
      return 0;
    tenth = text[i + 1] - '0';
  }
  return whole * 10 + tenth;
}

class Parser {
 public:
  Parser(std::vector<Token> toks, Diagnostics &diags,
         const OperatorTable &operators)
      : toks_(std::move(toks)), diags_(diags), operators_(operators) {}

  NodePtr program() {
    auto prog = makeNode(N::Program, loc());
    skipSeps();
    while (!at(K::Eof)) {
      try {
        firstItem_ = prog->kids.empty();
        prog->add(item());
        if (!at(K::Eof) && !at(K::Sep))
          fail("expected the end of the item; a new top-level item starts in "
               "column 1");
      } catch (const ParseError &e) {
        diags_.error(e.loc, e.message);
        while (!at(K::Eof) && !at(K::Sep)) ++pos_;
      }
      skipSeps();
    }
    return prog;
  }

  // REPL cells: a top-level expression may be any expression.
  void allowExpressionItems() { expressionItems_ = true; }

  NodePtr contractFragment() {
    auto out = makeNode(N::Contracts, loc());
    try {
      while (atContract()) out->add(contract());
      if (!at(K::Eof)) fail("expected 'requires', 'ensures' or 'decreases'");
    } catch (const ParseError &e) {
      diags_.error(e.loc, e.message);
    }
    return out;
  }

 private:
  // ------------------------------------------------------------ tokens

  const Token &tok(size_t k = 0) const {
    size_t i = pos_ + k;
    return i < toks_.size() ? toks_[i] : toks_.back();
  }
  K kind(size_t k = 0) const { return tok(k).kind; }
  bool at(K k) const { return kind() == k; }
  bool atOp(std::string_view op) const { return at(K::Op) && tok().text == op; }
  SourceLoc loc() const { return tok().loc; }
  std::string text() const { return std::string(tok().text); }

  [[noreturn]] void fail(std::string message) const {
    throw ParseError{loc(), std::move(message)};
  }

  Token take() {
    Token t = tok();
    if (pos_ < toks_.size() - 1) ++pos_;
    return t;
  }

  bool accept(K k) {
    if (!at(k)) return false;
    take();
    return true;
  }

  Token expect(K k, const char *what) {
    if (!at(k)) fail(std::string("expected ") + what);
    return take();
  }

  void skipSeps() {
    while (at(K::Sep)) take();
  }

  // Speculative parsing: run `f`; on a syntax error, rewind and return null.
  template <typename F>
  NodePtr attempt(F f) {
    size_t saved = pos_;
    bool savedContract = contractMode_, savedEnded = clauseEnded_;
    try {
      return f();
    } catch (const ParseError &) {
      pos_ = saved;
      contractMode_ = savedContract;
      clauseEnded_ = savedEnded;
      return nullptr;
    }
  }

  // Brackets reset the contract-clause rules: `(a = b = c)` is still an error.
  struct Bracket {
    Parser &p;
    bool contract, ended, bitOr;
    explicit Bracket(Parser &p)
        : p(p),
          contract(p.contractMode_),
          ended(p.clauseEnded_),
          bitOr(p.bitOr_) {
      p.contractMode_ = false;
      p.clauseEnded_ = false;
      p.bitOr_ = true;
    }
    ~Bracket() {
      p.contractMode_ = contract;
      p.clauseEnded_ = ended;
      p.bitOr_ = bitOr;
    }
  };

  static bool canStartAtom(K k) {
    switch (k) {
      case K::Ident: case K::Int: case K::Float: case K::String: case K::True:
      case K::False: case K::QIdent: case K::Hole: case K::LParen:
      case K::LBracket: case K::LBrace: case K::LBraceAdj: case K::QuoteOpen:
      case K::SpliceIdent: case K::SpliceOpen:
        return true;
      default:
        return false;
    }
  }

  bool canStartStmt() const {
    if (canStartAtom(kind()) || atOp("-")) return true;
    switch (kind()) {
      case K::Let: case K::Match: case K::If: case K::For: case K::Spread:
      case K::While: case K::Forall: case K::Exists: case K::Assert:
      case K::Assume:
      case K::Type:
      case K::Sig:
      case K::Defer:
      case K::With:
        return true;
      default:
        return false;
    }
  }

  // ------------------------------------------------------------ items

  NodePtr item() {
    switch (kind()) {
      case K::Let:
        if (kind(1) == K::Meta && kind(2) == K::Operator) return metaOperator();
        if (kind(1) == K::LParen) break;  // a function literal: an expression
        // `let adapter name : C t = struct ... end` (ADR 0034); `adapter`
        // is not a keyword.
        if (kind(1) == K::Ident && tok(1).text == "adapter" &&
            kind(2) == K::Ident && kind(3) == K::Colon)
          return adapterItem();
        // `let theory T = sig ... end` (ADR 0036); `theory`, `sort` and
        // `axiom` are keywords only between `let` and a name.
        if (kind(1) == K::Ident && tok(1).text == "theory" &&
            kind(2) == K::Ident)
          return theoryItem();
        // `let model m : T = struct ... end` (ADR 0036).
        if (kind(1) == K::Ident && tok(1).text == "model" &&
            kind(2) == K::Ident && kind(3) == K::Colon)
          return modelItem();
        if (kind(1) == K::Ident &&
            (tok(1).text == "sort" || tok(1).text == "axiom") &&
            kind(2) == K::Ident)
          fail("'" + std::string(tok(1).text) + "' declares part of a theory, "
               "so it belongs inside 'let theory T = sig ... end'");
        return let(/*allowItem=*/true, /*allowIn=*/false);
      case K::Interface:
        return interfaceItem();
      case K::Module:
        return moduleItem();
      // `@trusted` on a line of its own marks the whole file (ADR 0036).
      case K::Attr: {
        auto n = makeNode(N::FileAttr, loc(),
                          std::string(tok().text.substr(1)));
        take();
        return n;
      }
      case K::Import: {
        auto n = makeNode(N::Import, loc());
        take();
        n->text = path();
        // `import M.I as X` names the module X here, and `{ a, b }` also
        // brings a and b in unqualified (ADR 0039).
        if (at(K::As)) {
          SourceLoc l = loc();
          take();
          n->add(makeNode(N::Name, l,
                          std::string(expect(K::Ident, "a local module name")
                                          .text)))
              ->flags = "as";
        }
        if (at(K::LBrace) || at(K::LBraceAdj)) {
          take();
          while (!at(K::RBrace)) {
            SourceLoc l = loc();
            n->add(makeNode(N::Name, l,
                            std::string(expect(K::Ident, "a name to import")
                                            .text)));
            if (!accept(K::Comma)) break;
          }
          expect(K::RBrace, "'}'");
        }
        // `import M trusting` accepts every trusted axiom of the theories M
        // exports (ADR 0036); `trusting` is a keyword only here.
        if (at(K::Ident) && text() == "trusting") {
          take();
          n->flags = "trusting";
        }
        return n;
      }
      default:
        break;
    }
    auto n = makeNode(N::ExprItem, loc());
    // In a file, a top-level expression can only be a metaprogram's
    // invocation. A REPL cell can be any expression, such as `1 + 2`.
    n->add(expressionItems_ ? seq() : application());
    return n;
  }

  std::string path() {
    std::string p(expect(K::Ident, "a module path").text);
    while (at(K::Dot) && kind(1) == K::Ident) {
      take();
      p += ".";
      p += take().text;
    }
    return p;
  }

  // `let theory T = sig item* end`. An item is `let sort s [= t]`, an
  // abstract `let spec f : (a : t) -> r` with no body, a spec function, a
  // `let axiom name params requires ... ensures ...` (no body) or a lemma.
  NodePtr theoryItem() {
    auto n = makeNode(N::Theory, loc());
    take();  // let
    take();  // theory
    if (!at(K::Ident) && !at(K::SpliceIdent)) fail("expected a theory name");
    n->text = std::string(take().text);
    // `let theory T @solver(nlsat) = ...`: how Z3 solves its goals.
    NodePtr theoryAttrs;
    if (at(K::Attr) || at(K::AttrOpen)) {
      theoryAttrs = attrs();
      for (const NodePtr &a : theoryAttrs->kids)
        if (a->text != "solver")
          diags_.error(a->loc, "a theory takes only @solver, not @" + a->text);
    }
    expect(K::Eq, "'='");
    // `let theory Conn = machine ...`: a metaprogram builds it (step 5).
    // Its attributes stay beside the call, for the theory it builds.
    if (!at(K::Sig)) {
      n->flags = "call";
      n->add(application());
      if (theoryAttrs) n->add(std::move(theoryAttrs));
      return n;
    }
    expect(K::Sig, "'sig'");
    skipSeps();
    while (!at(K::End)) {
      if (NodePtr sp = memberSplice()) {
        n->add(std::move(sp));
        skipSeps();
        continue;
      }
      if (!at(K::Let)) fail("expected 'let' or 'end' in a theory");
      if (kind(1) == K::Ident && tok(1).text == "sort" &&
                 (kind(2) == K::Ident || kind(2) == K::SpliceIdent)) {
        auto sort = makeNode(N::SortItem, loc());
        take();
        take();
        sort->text = std::string(take().text);
        if (accept(K::Eq)) sort->add(type());
        n->add(std::move(sort));
      } else if (kind(1) == K::Ident && tok(1).text == "axiom" &&
                 (kind(2) == K::Ident || kind(2) == K::SpliceIdent)) {
        n->add(let(true, false, Bodyless::Axiom));
      } else if (kind(1) == K::Spec) {
        n->add(let(true, false, Bodyless::Abstract));
      } else {
        n->add(let(true, false));
      }
      skipSeps();
    }
    take();
    if (theoryAttrs) applyTheoryAttrs(*n, *theoryAttrs);
    return n;
  }

  // `let model m : T = struct item* end`: a sort for each of T's sorts,
  // `let sort s = t`, and a spec function with a body for each of its
  // abstract functions.
  NodePtr modelItem() {
    auto n = makeNode(N::Model, loc());
    take();  // let
    take();  // model
    n->text = std::string(take().text);
    expect(K::Colon, "':'");
    SourceLoc theoryAt = loc();
    n->add(makeNode(N::TypeName, theoryAt,
                    std::string(expect(K::Ident, "a theory").text)));
    expect(K::Eq, "'='");
    expect(K::Struct, "'struct'");
    skipSeps();
    while (!at(K::End)) {
      if (NodePtr sp = memberSplice()) {
        n->add(std::move(sp));
        skipSeps();
        continue;
      }
      if (!at(K::Let)) fail("expected 'let' or 'end' in a model");
      if (kind(1) == K::Ident && tok(1).text == "sort" &&
                 (kind(2) == K::Ident || kind(2) == K::SpliceIdent)) {
        auto sort = makeNode(N::SortItem, loc());
        take();
        take();
        sort->text = std::string(take().text);
        expect(K::Eq, "'=' and the type the sort is, as in 'let sort s = u8'");
        sort->add(type());
        n->add(std::move(sort));
      } else {
        n->add(let(true, false));
      }
      skipSeps();
    }
    take();
    return n;
  }

  // In a quote, `$xs` or `$(e)` in a theory's or model's body splices a
  // list of members.
  NodePtr memberSplice() {
    SourceLoc start = loc();
    if (at(K::SpliceIdent)) {
      auto n = makeNode(N::Splice, start, text());
      take();
      return n;
    }
    if (at(K::SpliceOpen)) {
      take();
      Bracket b(*this);
      auto n = makeNode(N::Splice, start);
      n->add(seq());
      expect(K::RParen, "')'");
      return n;
    }
    return nullptr;
  }

  // An item in a quote: a theory, a model, or a definition.
  NodePtr quotedItem(bool allowIn) {
    if (kind(1) == K::Ident && tok(1).text == "theory" &&
        (kind(2) == K::Ident || kind(2) == K::SpliceIdent))
      return theoryItem();
    if (kind(1) == K::Ident && tok(1).text == "model" &&
        (kind(2) == K::Ident || kind(2) == K::SpliceIdent) && kind(3) == K::Colon)
      return modelItem();
    if (kind(1) == K::Ident && (tok(1).text == "sort" || tok(1).text == "axiom") &&
        (kind(2) == K::Ident || kind(2) == K::SpliceIdent))
      return theoryMember();
    if (kind(1) == K::Spec && (kind(2) == K::Ident || kind(2) == K::SpliceIdent) &&
        kind(3) == K::Colon)
      return theoryMember();
    return let(/*allowItem=*/true, allowIn);
  }

  // One member of a theory, as in theoryItem.
  NodePtr theoryMember() {
    if (kind(1) == K::Ident && tok(1).text == "sort") {
      auto sort = makeNode(N::SortItem, loc());
      take();
      take();
      sort->text = std::string(take().text);
      if (accept(K::Eq)) sort->add(type());
      return sort;
    }
    if (kind(1) == K::Ident && tok(1).text == "axiom")
      return let(true, false, Bodyless::Axiom);
    return let(true, false, Bodyless::Abstract);
  }

  // A definition with no body: an abstract spec function, `let spec f :
  // (a : t) -> r`, or an axiom, whose contracts are all it says.
  enum class Bodyless { No, Abstract, Axiom };

  // `let [rec] [spec|lemma] [meta] name params [: annot attrs] contracts = body [in body]`
  NodePtr let(bool allowItem, bool allowIn, Bodyless bodyless = Bodyless::No) {
    SourceLoc start = loc();
    expect(K::Let, "'let'");
    std::string flags;
    if (bodyless == Bodyless::Axiom) {
      take();  // axiom
      flags = "axiom";
    }
    if (accept(K::Rec)) flags = "rec";
    if (accept(K::Spec)) flags += flags.empty() ? "spec" : " spec";
    else if (accept(K::Lemma)) flags += flags.empty() ? "lemma" : " lemma";
    if (accept(K::Meta)) flags += flags.empty() ? "meta" : " meta";
    if (!at(K::Ident) && !at(K::SpliceIdent)) fail("expected a name after 'let'");
    auto n = makeNode(N::LetItem, start, text());
    n->flags = flags;
    take();
    n->add(params());
    n->add(retAnnot());
    Node *contracts = n->add(makeNode(N::Contracts, loc()));
    while (atContract()) contracts->add(contract());
    // `with f, g`: reveal opaque spec functions in the body (ADR 0063).
    if (at(K::With))
      contracts->add(reveal(/*clause=*/true));

    NodePtr body;
    if (bodyless == Bodyless::Axiom) {
      // An axiom has no body, so its last clause is never split at `=`.
      n->add(makeNode(N::None, loc()));
      return n;
    }
    if (bodyless == Bodyless::Abstract && !at(K::Eq)) {
      n->flags += " abstract";
      n->add(makeNode(N::None, loc()));
      return n;
    }
    if (accept(K::Eq)) {
      body = seq();
    } else {
      body = splitBodyFromContract(*contracts);
      if (!body) fail("expected '=' and a definition");
    }
    n->add(withHandle(std::move(body)));

    if (allowIn && accept(K::In)) {
      n->kind = N::LetIn;
      n->add(seq());
    } else if (!allowItem) {
      fail("expected 'in'");
    }
    return n;
  }

  // The longest-predicate rule (ADR 0019): `requires sorted xs = g xs` with no
  // later `=` reads as the predicate `sorted xs` and the body `g xs`. Split at
  // the last `=` on the right spine of the final clause. A `decreases`
  // measure is an integer, so `decreases n = f (n - 1)` splits the same way.
  NodePtr splitBodyFromContract(Node &contracts) {
    if (contracts.kids.empty()) return nullptr;
    Node &clause = *contracts.kids.back();
    NodePtr *slot = &clause.kids[0];
    while ((*slot)->kind == N::Binary && (*slot)->text != "=" &&
           operatorInfo((*slot)->text).level < 40)
      slot = &(*slot)->kids[1];
    if ((*slot)->kind != N::Binary || (*slot)->text != "=") return nullptr;
    NodePtr eq = std::move(*slot);
    *slot = std::move(eq->kids[0]);
    NodePtr body = std::move(eq->kids[1]);
    if (accept(K::Semi) && canStartStmt()) {
      auto s = makeNode(N::Sequence, body->loc);
      s->add(std::move(body));
      s->add(seq());
      return s;
    }
    return body;
  }

  NodePtr params() {
    auto ps = makeNode(N::Params, loc());
    for (;;) {
      if (at(K::Ident) || at(K::SpliceIdent)) {
        ps->add(makeNode(N::Param, loc(), text()));
        take();
      } else if (at(K::LParen) && kind(1) == K::RParen) {
        ps->add(makeNode(N::ParamUnit, loc()));
        take();
        take();
      } else if (at(K::LParen) && kind(1) == K::Hole && kind(2) == K::RParen) {
        ps->add(makeNode(N::ParamHole, loc()));
        take();
        take();
        take();
      } else if (at(K::LParen) &&
                 (kind(1) == K::Ident || kind(1) == K::SpliceIdent) &&
                 kind(2) == K::Colon) {
        take();
        auto p = makeNode(N::Param, loc(), text());
        take();
        take();
        p->add(annot());
        paramContracts(*p);
        expect(K::RParen, "')' after the parameter's type");
        ps->add(std::move(p));
      } else if (atSpecParam()) {
        // `(spec ref : inout [u8; 4096])`: a spec parameter (ADR 0058),
        // which callers and the callee share as spec state.
        take();
        take(); // spec
        auto p = makeNode(N::Param, loc(), text());
        p->flags = "spec";
        take();
        take();
        p->add(annot());
        expect(K::RParen, "')' after the parameter's type");
        ps->add(std::move(p));
      } else {
        return ps;
      }
    }
  }

  // `(f : (x : u8) -> u8 requires x < 255 ensures result > x)`: a
  // function type's contracts (ADR 0044), on its innermost arrow.
  void paramContracts(Node &p) {
    if (p.kids[0]->kids[1]->kind != N::ArrowType || !atContract())
      return;
    Node *arrow = p.kids[0]->kids[1].get();
    while (arrow->kids[1]->kind == N::ArrowType)
      arrow = arrow->kids[1].get();
    Node *cs = arrow->add(makeNode(N::Contracts, loc()));
    while (atContract())
      cs->add(contract());
  }

  // `(spec name :`, which opens a spec parameter (ADR 0058). `spec` is not
  // a keyword here, so a parameter may still be named `spec`.
  bool atSpecParam() const {
    return at(K::LParen) && kind(1) == K::Ident && tok(1).text == "spec" &&
           (kind(2) == K::Ident || kind(2) == K::SpliceIdent) &&
           kind(3) == K::Colon;
  }

  NodePtr retAnnot() {
    if (!at(K::Colon) && !at(K::Attr) && !at(K::AttrOpen))
      return makeNode(N::None, loc());
    auto r = makeNode(N::RetAnnot, loc());
    if (accept(K::Colon))
      r->add(annot());
    else
      r->add(makeNode(N::None, loc()));
    r->add(attrs());
    return r;
  }

  // `invariant` is a contract of a state (ADR 0031); loops read their own.
  bool atContract() const {
    return at(K::Requires) || at(K::Ensures) || at(K::Decreases) ||
           at(K::Invariant) || at(K::Reads) || atCosts();
  }

  // `costs c <= e` (ADR 0062). `costs` is a keyword only here, before a
  // name and `<=`, so it takes no name away from code.
  bool atCosts() const {
    return at(K::Ident) && tok().text == "costs" && kind(1) == K::Ident &&
           kind(2) == K::Op && tok(2).text == "<=";
  }

  NodePtr contract() {
    if (atCosts()) {
      auto c = makeNode(N::Costs, loc());
      take(); // costs
      c->text = std::string(take().text);
      take(); // <=
      bool savedContract = contractMode_, savedEnded = clauseEnded_;
      contractMode_ = true;
      clauseEnded_ = false;
      c->add(stmt());
      contractMode_ = savedContract;
      clauseEnded_ = savedEnded;
      return c;
    }
    N k = at(K::Requires)    ? N::Requires
          : at(K::Ensures)   ? N::Ensures
          : at(K::Invariant) ? N::Invariant
          : at(K::Reads)     ? N::Reads
                             : N::Decreases;
    auto c = makeNode(k, loc());
    take();
    bool savedContract = contractMode_, savedEnded = clauseEnded_;
    contractMode_ = true;
    clauseEnded_ = false;
    c->add(stmt());
    // `reads xs.[c] where owner.[c] = v` (ADR 0060, section 3).
    if (k == N::Reads && accept(K::Where)) {
      clauseEnded_ = false;
      c->add(stmt());
    }
    contractMode_ = savedContract;
    clauseEnded_ = savedEnded;
    return c;
  }

  NodePtr metaOperator() {
    auto n = makeNode(N::MetaOperator, loc());
    take();  // let
    take();  // meta
    take();  // operator
    expect(K::LParen, "'(' before the operator");
    if (!at(K::Op) && !at(K::Eq) && !at(K::Bar)) fail("expected an operator");
    n->text = text();
    take();
    expect(K::RParen, "')' after the operator");
    if (accept(K::Colon)) {
      auto f = makeNode(N::Fixity, loc());
      std::string prec(expect(K::Ident, "'prec'").text);
      if (prec != "prec") fail("expected 'prec'");
      if (!at(K::Int) && !at(K::Float)) fail("expected a precedence level");
      std::string level(take().text);
      int tenths = parseLevel(level);
      if (tenths < 10)
        fail("a precedence level is a number from 1 to 99 with at most one "
             "decimal place, such as 6 or 6.5");
      std::string assoc(expect(K::Ident, "'left', 'right' or 'none'").text);
      if (assoc != "left" && assoc != "right" && assoc != "none")
        fail("expected 'left', 'right' or 'none'");
      f->text = "prec " + level + " " + assoc;
      n->add(std::move(f));
    } else {
      n->add(makeNode(N::None, loc()));
    }
    if (accept(K::For))
      n->add(type());
    else
      n->add(makeNode(N::None, loc()));
    expect(K::Eq, "'='");
    n->add(seq());
    return n;
  }

  NodePtr interfaceItem() {
    auto n = makeNode(N::Interface, loc());
    take();
    n->text = std::string(expect(K::Ident, "an interface name").text);
    n->add(attrs());  // `interface I @abi(c) = sig` (ADR 0039)
    expect(K::Eq, "'='");
    expect(K::Sig, "'sig'");
    sigItems(*n, /*isConcept=*/false);
    return n;
  }

  // `sig ... end` as a value: the body of a concept (ADR 0034).
  NodePtr sigValue() {
    auto n = makeNode(N::Sig, loc());
    expect(K::Sig, "'sig'");
    sigItems(*n, /*isConcept=*/true);
    return n;
  }

  // The items of a signature up to and including its `end`. A concept's
  // signature may also `include` another concept and state laws as
  // `let lemma name params ensures ...`.
  void sigItems(Node &n, bool isConcept) {
    while (!at(K::End)) {
      if (at(K::Hole)) {
        n.add(makeNode(N::Hole, loc()));
        take();
        continue;
      }
      SourceLoc start = loc();
      if (isConcept && at(K::Ident) && text() == "include") {
        take();
        NodePtr t = type();
        auto inc = makeNode(N::SigInclude, start);
        if (t->kind == N::TypeApp) {
          inc->text = t->kids[0]->text;
          for (size_t i = 1; i < t->kids.size(); ++i)
            inc->add(std::move(t->kids[i]));
        } else if (t->kind == N::TypeName) {
          inc->text = t->text;
        } else {
          fail("expected a concept after 'include'");
        }
        n.add(std::move(inc));
        continue;
      }
      expect(K::Let, isConcept ? "'let', 'include' or 'end' in a concept"
                             : "'let' or 'end' in a signature");
      if (isConcept && accept(K::Lemma)) {
        auto law = makeNode(N::SigLemma, start,
                            std::string(expect(K::Ident, "a law's name").text));
        law->add(params());
        Node *cs = law->add(makeNode(N::Contracts, loc()));
        while (atContract()) cs->add(contract());
        n.add(std::move(law));
        continue;
      }
      // `let meta C : concept` lists a concept, which an interface exports
      // with its definition (ADR 0039).
      bool meta = !isConcept && accept(K::Meta);
      // `let spec f : ...` lists a spec function, which is exported with
      // its definition, since importers reason with its body (ADR 0039).
      bool spec = !isConcept && !meta && accept(K::Spec);
      // `let lemma f : ...` lists a lemma, which is proved once in its
      // module, and which importers call as a fact: its precondition a
      // goal, its postcondition assumed (#305).
      bool lemma = !isConcept && !meta && !spec && accept(K::Lemma);
      // `let rec t = type ...` shows a recursive type (ADR 0047).
      bool rec = !isConcept && !meta && !spec && !lemma && accept(K::Rec);
      if (!at(K::Ident) && !at(K::SpliceIdent)) fail("expected a name");
      std::string name = text();
      take();
      if (meta && !at(K::Colon)) fail("expected ':' after a concept's name");
      if (spec && !at(K::Colon))
        fail("expected ':' after a spec function's name");
      if (lemma && !at(K::Colon))
        fail("expected ':' after a lemma's name");
      if (rec && !at(K::Eq))
        fail("expected '=' after a recursive type's name: an interface "
             "shows a recursive type with its definition");
      if (accept(K::Colon)) {
        auto v = makeNode(N::SigVal, start, name);
        if (meta) v->flags = "meta";
        if (spec) v->flags = "spec";
        if (lemma)
          v->flags = "lemma";
        v->add(annot());
        v->add(attrs());
        Node *cs = v->add(makeNode(N::Contracts, loc()));
        while (atContract()) cs->add(contract());
        // `let n : u32 = 4096` shows a value, which importers' proofs may
        // use (ADR 0039).
        if (!isConcept && !meta && !spec && !lemma && accept(K::Eq))
          v->add(seq());
        n.add(std::move(v));
      } else if (accept(K::Eq)) {
        auto t = makeNode(N::SigType, start, name);
        if (rec) t->flags = "rec";
        // A generic type is shown as it is defined, `let (t : type) =>
        // type ...` (ADR 0039).
        if (at(K::Let) && kind(1) == K::LParen)
          t->add(lambda(/*elemBody=*/false));
        else if (at(K::Type))
          t->add(typeValue());
        else
          // `let byte = u8`: another name for a type (ADR 0064).
          t->add(aliasValue(type()));
        n.add(std::move(t));
      } else {
        fail("expected ':' or '=' after the name");
      }
    }
    take();
  }

  NodePtr adapterItem() {
    auto n = makeNode(N::Adapter, loc());
    take();
    take();
    n->text = std::string(expect(K::Ident, "an adapter's name").text);
    expect(K::Colon, "':'");
    n->add(type());
    expect(K::Eq, "'='");
    expect(K::Struct, "'struct'");
    skipSeps();
    while (!at(K::End)) {
      n->add(item());
      skipSeps();
    }
    take();
    return n;
  }

  // `module Pixels.Core @attrs : I, J` as the first item of a file is its
  // header (ADR 0039): the rest of the file is the module's body.
  // `module M : I = struct ... end` is a module nested in the file.
  NodePtr moduleItem() {
    SourceLoc start = loc();
    bool first = firstItem_;
    firstItem_ = false;
    take();
    std::string name = path();
    NodePtr as = attrs();
    auto paths = makeNode(N::Paths, loc());
    if (accept(K::Colon)) {
      do {
        paths->add(makeNode(N::Path, loc(), path()));
      } while (accept(K::Comma));
    }
    if (!at(K::Eq)) {
      if (!first)
        diags_.error(start, "a module header must be the first item of its "
                            "file; a nested module is 'module M : I = struct "
                            "... end' (ADR 0039)");
      auto h = makeNode(N::ModuleHeader, start, name);
      h->add(std::move(as));
      h->add(std::move(paths));
      return h;
    }
    if (name.find('.') != std::string::npos)
      fail("a nested module's name is one identifier, not a path");
    if (!as->kids.empty())
      fail("attributes go on a module header, not on a nested module");
    auto n = makeNode(N::Module, start, name);
    n->add(std::move(paths));
    expect(K::Eq, "'='");
    expect(K::Struct, "'struct'");
    skipSeps();
    while (!at(K::End)) {
      n->add(item());
      skipSeps();
    }
    take();
    return n;
  }

  // ------------------------------------------------------------ types

  NodePtr modifiers() {
    auto m = makeNode(N::Modifiers, loc());
    auto addWord = [&](const char *w) {
      if (!m->text.empty()) m->text += " ";
      m->text += w;
      take();
    };
    if (at(K::Borrowed)) {
      // `borrowed(m)`, written with no space before the parenthesis: a
      // result borrowed from the parameter `m` (#70). `borrowed (t)` is
      // `borrowed` before a parenthesised type.
      bool lender = kind(1) == K::LParen &&
                    tok(1).loc.offset == tok().loc.offset + tok().text.size() &&
                    kind(2) == K::Ident && kind(3) == K::RParen;
      addWord("borrowed");
      if (lender) {
        take();
        m->add(makeNode(N::Name, loc(), text()));
        take();
        take();
      }
    } else if (at(K::Moved)) {
      addWord("moved");
    }
    if (at(K::In)) addWord("in");
    else if (at(K::Out)) addWord("out");
    else if (at(K::Inout)) addWord("inout");
    if (at(K::Fixed)) addWord("fixed");
    else if (at(K::Mutable)) addWord("mutable");
    if (at(K::Borrowed) || at(K::Moved) || at(K::In) || at(K::Out) ||
        at(K::Inout) || at(K::Fixed) || at(K::Mutable))
      fail("modifiers go in the order ownership, access, mutability, at most "
           "one of each");
    return m;
  }

  // annot = modifiers type [where stmt]. Modifiers before a function type
  // belong to its first parameter.
  NodePtr annot() {
    auto a = makeNode(N::Annot, loc());
    NodePtr mods = modifiers();
    NodePtr t = type();
    if (t->kind == N::ArrowType && !mods->text.empty()) {
      Node &dom = *t->kids[0];
      if (!dom.kids[0]->text.empty())
        fail("a function type's first parameter has modifiers twice");
      dom.kids[0] = std::move(mods);
      mods = makeNode(N::Modifiers, a->loc);
    }
    a->add(std::move(mods));
    a->add(std::move(t));
    if (accept(K::Where))
      a->add(stmt());
    else
      a->add(makeNode(N::None, loc()));
    return a;
  }

  NodePtr type() {
    SourceLoc start = loc();
    auto dom = makeNode(N::Domain, start);
    bool specDom = atSpecParam();
    if (specDom ||
        (at(K::LParen) && kind(1) == K::Ident && kind(2) == K::Colon)) {
      take();
      if (specDom) {
        // `(spec ref : inout [u8; 4096]) -> r` in a signature (ADR 0058).
        take();
        dom->flags = "spec";
      }
      dom->text = text();
      take();
      take();
      NodePtr inner = annot();
      expect(K::RParen, "')' after the parameter's type");
      for (NodePtr &k : inner->kids) dom->add(std::move(k));
      expect(K::Arrow, "'->' after a named parameter");
      auto arrow = makeNode(N::ArrowType, start);
      arrow->add(std::move(dom));
      arrow->add(type());
      return arrow;
    }
    NodePtr mods = modifiers();
    NodePtr t = unionType(/*allowUnion=*/true);
    if (accept(K::Arrow)) {
      dom->add(std::move(mods));
      dom->add(std::move(t));
      dom->add(makeNode(N::None, start));
      auto arrow = makeNode(N::ArrowType, start);
      arrow->add(std::move(dom));
      arrow->add(type());
      return arrow;
    }
    if (!mods->kids.empty()) {
      // `result (borrowed(m) [u8]) e`: a lender inside a result type.
      auto a = makeNode(N::Annot, start);
      a->add(std::move(mods));
      a->add(std::move(t));
      a->add(makeNode(N::None, start));
      return a;
    }
    if (!mods->text.empty()) fail("expected '->': modifiers only apply to a parameter");
    return t;
  }

  NodePtr unionType(bool allowUnion) {
    NodePtr first = appType();
    if (!allowUnion || !at(K::Bar) || !canStartTypeAtom(kind(1))) return first;
    auto u = makeNode(N::UnionType, first->loc);
    u->add(std::move(first));
    while (at(K::Bar) && canStartTypeAtom(kind(1))) {
      take();
      u->add(appType());
    }
    return u;
  }

  static bool canStartTypeAtom(K k) {
    switch (k) {
      case K::Ident: case K::Type: case K::LBracket: case K::LBrace:
      case K::LParen: case K::SpliceIdent: case K::SpliceOpen:
        return true;
      default:
        return false;
    }
  }

  NodePtr appType() {
    NodePtr head = typeAtom();
    if (head->kind == N::TypeKind) return head;
    std::vector<NodePtr> args;
    for (;;) {
      if (at(K::Int)) {
        args.push_back(makeNode(N::IntLit, loc(), text()));
        take();
      } else if (at(K::LParen) && kind(1) != K::RParen) {
        NodePtr t = attempt([&] {
          take();
          NodePtr inner = type();
          expect(K::RParen, "')'");
          return inner;
        });
        if (!t) {
          take();
          Bracket b(*this);
          t = seq();
          expect(K::RParen, "')'");
        }
        args.push_back(std::move(t));
      } else if (canStartTypeAtom(kind()) && !at(K::Type) && !atCosts()) {
        args.push_back(typeAtom());
      } else {
        break;
      }
    }
    if (args.empty()) return head;
    auto app = makeNode(N::TypeApp, head->loc);
    app->add(std::move(head));
    for (NodePtr &a : args) app->add(std::move(a));
    return app;
  }

  NodePtr typeAtom() {
    SourceLoc start = loc();
    switch (kind()) {
      case K::Ident: {
        std::string name = text();
        take();
        // A qualified name, such as a theory's sort `Lip.layer` (ADR 0036).
        while (at(K::Dot) && kind(1) == K::Ident) {
          take();
          name += "." + std::string(take().text);
        }
        if (at(K::TargsOpen)) {
          auto n = makeNode(N::TypeInst, start, name);
          targs(*n);
          return n;
        }
        if (accept(K::LBraceAdj)) {
          Bracket b(*this);
          auto n = makeNode(N::RangeType, start, name);
          n->add(binary(60));
          expect(K::DotDot, "'..' in a range type");
          n->add(binary(60));
          expect(K::RBrace, "'}'");
          return n;
        }
        return makeNode(N::TypeName, start, name);
      }
      case K::Type:
        take();
        return makeNode(N::TypeKind, start);
      case K::LBracket: {
        take();
        Bracket b(*this);
        NodePtr elem = type();
        if (accept(K::Semi)) {
          auto n = makeNode(N::ArrayType, start);
          n->add(std::move(elem));
          n->add(seq());
          expect(K::RBracket, "']'");
          return n;
        }
        expect(K::RBracket, "']' or ';' and a length");
        auto n = makeNode(N::SliceType, start);
        n->add(std::move(elem));
        return n;
      }
      case K::LBrace:
        return braceType();
      case K::LParen: {
        take();
        if (accept(K::RParen)) return makeNode(N::UnitType, start);
        Bracket b(*this);
        NodePtr t = type();
        expect(K::RParen, "')'");
        return t;
      }
      case K::SpliceIdent: {
        auto n = makeNode(N::Splice, start, text());
        take();
        return n;
      }
      case K::SpliceOpen: {
        take();
        Bracket b(*this);
        auto n = makeNode(N::Splice, start);
        n->add(seq());
        expect(K::RParen, "')'");
        return n;
      }
      default:
        fail("expected a type");
    }
  }

  // `{ f : t; ... }` is a record type; `{ x : t | p }` is a refinement.
  NodePtr braceType() {
    SourceLoc start = loc();
    take();
    Bracket b(*this);
    if (at(K::Ident) && kind(1) == K::Colon) {
      NodePtr refinement = attempt([&] {
        auto r = makeNode(N::RefinementType, loc(), text());
        take();
        take();
        r->add(unionType(/*allowUnion=*/false));
        expect(K::Bar, "'|'");
        r->add(stmt());
        expect(K::RBrace, "'}'");
        return r;
      });
      if (refinement) return refinement;
    }
    auto rec = makeNode(N::RecordType, start);
    // `type { $fs }` in a quote: fields a metaprogram computed, as
    // [name; type] pairs (docs/meta.md).
    if (at(K::SpliceIdent) && kind(1) == K::RBrace) {
      rec->add(makeNode(N::Splice, loc(), text()));
      take();
      expect(K::RBrace, "'}' after the spliced fields");
      return rec;
    }
    while (!at(K::RBrace)) {
      // `spec hist : [u8; 64]`: a spec field (ADR 0058). `spec` is a
      // keyword only before a name and a colon.
      bool spec = at(K::Ident) && tok().text == "spec" && kind(1) == K::Ident &&
                  kind(2) == K::Colon;
      if (spec)
        take();
      auto f = makeNode(N::FieldDecl, loc(), std::string(expect(K::Ident, "a field name").text));
      if (spec)
        f->flags = "spec";
      expect(K::Colon, "':' after the field name");
      f->add(annot());
      // `x : i32 @json(name = "x")`: attributes a derive reads (ADR 0045).
      if (at(K::Attr) || at(K::AttrOpen)) f->add(attrs());
      rec->add(std::move(f));
      if (!accept(K::Semi)) break;
    }
    expect(K::RBrace, "'}'");
    return rec;
  }

  void targs(Node &into) {
    expect(K::TargsOpen, "'<'");
    Bracket b(*this);
    do {
      if (at(K::Ident) && kind(1) == K::Eq) {
        auto named = makeNode(N::NamedArg, loc(), text());
        take();
        take();
        named->add(elem());
        into.add(std::move(named));
        continue;
      }
      NodePtr t = attempt([&] {
        NodePtr r = type();
        if (!at(K::Comma) && !at(K::TargsClose)) fail("not a type argument");
        return r;
      });
      into.add(t ? std::move(t) : elem());
    } while (accept(K::Comma));
    expect(K::TargsClose, "'>' to close the type arguments");
  }

  // The type `t` as a value that names it, `let byte = u8` (ADR 0064,
  // section 1): the type item `type t`, marked as another name for `t`
  // rather than a new type.
  NodePtr aliasValue(NodePtr t) {
    auto n = makeNode(N::TypeValue, t->loc);
    n->flags = "alias";
    n->add(std::move(t));
    n->add(makeNode(N::Attrs, loc()));
    n->add(makeNode(N::None, loc()));
    return n;
  }

  NodePtr typeValue() {
    auto n = makeNode(N::TypeValue, loc());
    expect(K::Type, "'type'");
    if (at(K::Bar)) {
      auto vs = makeNode(N::Variants, loc());
      // Attributes after the last constructor's name, with no payload
      // after them, are the type's, as they always were.
      NodePtr trailing;
      while (accept(K::Bar)) {
        // `| $c of t` in a quote: a constructor a metaprogram names.
        std::string cname = at(K::SpliceIdent)
                                ? std::string(take().text)
                                : std::string(expect(K::Ident, "a constructor name").text);
        auto c = makeNode(N::Ctor, loc(), cname);
        // `| Circle @json(name = "c") of ...` and `| Empty @json(...) |`:
        // attributes a derive reads, between the name and `of` or `|`
        // (ADR 0045).
        NodePtr cas;
        if (at(K::Attr) || at(K::AttrOpen)) cas = attrs();
        if (accept(K::Of))
          c->add(appType());
        else
          c->add(makeNode(N::None, loc()));
        if (cas && !at(K::Bar) && c->kids[0]->kind == N::None)
          trailing = std::move(cas);
        else if (cas)
          c->add(std::move(cas));
        vs->add(std::move(c));
      }
      n->add(std::move(vs));
      if (trailing) {
        NodePtr as = std::move(trailing);
        NodePtr where = makeNode(N::None, loc());
        for (NodePtr &a : attrs()->kids) as->add(std::move(a));
        if (accept(K::Where)) where = stmt();
        for (NodePtr &a : attrs()->kids) as->add(std::move(a));
        n->add(std::move(as));
        n->add(std::move(where));
        return n;
      }
    } else {
      n->add(type());
    }
    NodePtr as = attrs();
    NodePtr where = makeNode(N::None, loc());
    if (accept(K::Where)) where = stmt();
    for (NodePtr &a : attrs()->kids) as->add(std::move(a));
    n->add(std::move(as));
    n->add(std::move(where));
    return n;
  }

  NodePtr attrs() {
    auto as = makeNode(N::Attrs, loc());
    while (at(K::Attr) || at(K::AttrOpen)) {
      bool hasArgs = at(K::AttrOpen);
      auto a = makeNode(N::Attribute, loc(), std::string(tok().text.substr(1, tok().text.size() - (hasArgs ? 2 : 1))));
      take();
      if (hasArgs) {
        Bracket b(*this);
        if (!at(K::RParen)) {
          do {
            if (at(K::Ident) && kind(1) == K::Eq) {
              auto named = makeNode(N::NamedArg, loc(), text());
              take();
              take();
              named->add(stmt());
              a->add(std::move(named));
            } else {
              a->add(stmt());
            }
          } while (accept(K::Comma));
        }
        expect(K::RParen, "')' to close the attribute");
      }
      as->add(std::move(a));
    }
    return as;
  }

  // ------------------------------------------------------------ expressions

  NodePtr seq() {
    if (at(K::Let)) {
      if (kind(1) == K::LParen || kind(1) == K::LBracket)
        return lambda(/*elemBody=*/false);
      return let(/*allowItem=*/false, /*allowIn=*/true);
    }
    if (at(K::Match)) return match();
    if (at(K::With))
      return reveal(/*clause=*/false);
    NodePtr s = stmt();
    if (at(K::Semi)) {
      take();
      if (!canStartStmt()) return s;
      auto sq = makeNode(N::Sequence, s->loc);
      sq->add(std::move(s));
      sq->add(seq());
      return sq;
    }
    return s;
  }

  NodePtr elem() {
    if (at(K::Let) && (kind(1) == K::LParen || kind(1) == K::LBracket))
      return lambda(/*elemBody=*/true);
    return stmt();
  }

  NodePtr lambda(bool elemBody) {
    auto n = makeNode(N::Lambda, loc());
    take();  // let
    // `let [lo, borrowed keys, inout count] (x : u8) => ...` (ADR 0044,
    // section 6): what the lambda captures, and how. A bare name is
    // copied.
    if (at(K::LBracket)) {
      auto cs = makeNode(N::Captures, loc());
      take();
      Bracket b(*this);
      do {
        auto c = makeNode(N::Capture, loc());
        if (accept(K::Borrowed)) c->flags = "borrowed";
        else if (accept(K::Inout)) c->flags = "inout";
        else if (accept(K::Moved)) c->flags = "moved";
        if (!at(K::Ident))
          fail("expected a captured name, as in '[lim]', '[borrowed keys]' "
               "or '[inout count]'");
        c->text = text();
        take();
        cs->add(std::move(c));
      } while (accept(K::Comma));
      expect(K::RBracket, "']' after the captures");
      n->add(std::move(cs));
    }
    while (at(K::LParen)) {
      auto p = makeNode(N::LParam, loc());
      take();
      if (accept(K::RParen)) {
        p->add(makeNode(N::Unit, p->loc));
        p->add(makeNode(N::None, p->loc));
      } else {
        Bracket b(*this);
        // `(@unsized t : type)`, a type parameter that takes an unsized
        // type, such as a concept (ADR 0046, section 2).
        if (at(K::Attr) && text() == "@unsized") {
          take();
          p->flags = "unsized";
        }
        p->add(pattern());
        if (accept(K::Colon))
          p->add(annot());
        else
          p->add(makeNode(N::None, loc()));
        expect(K::RParen, "')' after the parameter");
      }
      n->add(std::move(p));
    }
    if (n->kids.empty()) fail("expected '(' and a parameter");
    // `let (x : u8) : u8 requires x < 255 => x + 1` (ADR 0044): a result
    // type and contracts, each present only when written.
    if (at(K::Colon)) {
      auto r = makeNode(N::RetAnnot, loc());
      take();
      r->add(annot());
      r->add(makeNode(N::Attrs, loc()));
      n->add(std::move(r));
    }
    if (atContract()) {
      auto cs = makeNode(N::Contracts, loc());
      while (atContract()) cs->add(contract());
      n->add(std::move(cs));
    }
    expect(K::FatArrow, "'=>' after the parameters");
    n->add(elemBody ? elem() : seq());
    return n;
  }

  NodePtr match() {
    auto n = makeNode(N::Match, loc());
    take();
    n->add(seq());
    expect(K::With, "'with'");
    arms(*n);
    return n;
  }

  // `| p -> e ...`, the arms of a `match` or a `handle`.
  void arms(Node &n) {
    accept(K::Bar);
    // An arm's body ends at the next `|`, even inside brackets.
    struct Restore {
      bool &flag;
      bool old;
      ~Restore() { flag = old; }
    } restore{bitOr_, bitOr_};
    bitOr_ = false;
    do {
      auto arm = makeNode(N::Arm, loc());
      arm->add(pattern());
      // `| p requires c ensures d -> e` (ADR 0035): the arm's contracts.
      NodePtr cs;
      if (at(K::Requires) || at(K::Ensures)) {
        cs = makeNode(N::Contracts, loc());
        while (at(K::Requires) || at(K::Ensures)) cs->add(contract());
      }
      expect(K::Arrow, "'->' after the pattern");
      arm->add(seq());
      if (cs) arm->add(std::move(cs));
      n.add(std::move(arm));
    } while (accept(K::Bar));
  }

  // `body handle | p -> e ...` (ADR 0028): the handler of the errors the
  // `?`s in `body` raise. It ends a function body, a `let` value, a
  // parenthesised expression or a loop body.
  NodePtr withHandle(NodePtr body) {
    if (!at(K::Handle)) return body;
    auto h = makeNode(N::Handle, loc());
    take();
    h->add(std::move(body));
    arms(*h);
    return h;
  }

  // `with f, g in e` (ADR 0063): the opaque spec functions f and g are
  // revealed in e. As a clause after a function's contracts, `with f, g`
  // reveals them in its whole body, and has no `in`.
  NodePtr reveal(bool clause) {
    auto n = makeNode(N::Reveal, loc());
    expect(K::With, "'with'");
    do {
      if (!at(K::Ident))
        fail("expected the name of a spec function after 'with'");
      NodePtr f = makeNode(N::Name, loc(), text());
      take();
      // `M.f`, an imported function, as an expression writes it.
      while (at(K::Dot) && kind(1) == K::Ident) {
        take();
        auto field = makeNode(N::Field, f->loc, text());
        take();
        field->add(std::move(f));
        f = std::move(field);
      }
      n->add(std::move(f));
    } while (accept(K::Comma));
    if (clause) {
      n->flags = "clause";
      return n;
    }
    expect(K::In, "'in' after the functions 'with' reveals");
    n->add(seq());
    return n;
  }

  NodePtr stmt() {
    SourceLoc start = loc();
    if (at(K::With))
      return reveal(/*clause=*/false);
    switch (kind()) {
      case K::If: {
        take();
        auto n = makeNode(N::If, start);
        n->add(seq());
        expect(K::Then, "'then'");
        n->add(stmt());
        if (accept(K::Else))
          n->add(stmt());
        else
          n->add(makeNode(N::None, loc()));
        return n;
      }
      case K::For:
      case K::Spread: {
        bool spread = at(K::Spread);
        take();
        auto n = makeNode(spread ? N::Spread : N::For, start);
        n->add(pattern());
        expect(K::In, "'in'");
        n->add(binary(20));
        if (spread) {
          n->add(attrs());
        } else if (accept(K::Step)) {
          n->add(binary(60));
        } else {
          n->add(makeNode(N::None, loc()));
        }
        n->add(loopAnnots(spread));
        expect(K::Do, "'do'");
        n->add(withHandle(seq()));
        expect(K::Done, "'done'");
        return n;
      }
      case K::While: {
        take();
        auto n = makeNode(N::While, start);
        n->add(seq());
        n->add(loopAnnots());
        expect(K::Do, "'do'");
        n->add(withHandle(seq()));
        expect(K::Done, "'done'");
        return n;
      }
      case K::Forall:
      case K::Exists:
        return quantifier();
      case K::Defer: {
        auto n = makeNode(N::Defer, start);
        take();
        n->add(binary(0));
        return n;
      }
      case K::Assert:
      case K::Assume: {
        auto n = makeNode(at(K::Assert) ? N::Assert : N::Assume, start);
        take();
        n->add(binary(0));
        return n;
      }
      case K::Type:
        return typeValue();
      case K::Sig:
        return sigValue();
      default:
        break;
    }
    NodePtr e = binary(0);
    if (at(K::LArrow)) {
      switch (e->kind) {
        case N::Name: case N::Field: case N::Index: case N::Splice:
          break;
        default:
          fail("the left of '<-' must be a name, a field or an index");
      }
      take();
      auto a = makeNode(N::Assign, e->loc);
      a->add(std::move(e));
      a->add(stmt());
      return a;
    }
    return e;
  }

  NodePtr loopAnnots(bool spread = false) {
    auto as = makeNode(N::LoopAnnots, loc());
    while (at(K::Invariant) || at(K::Decreases) || (spread && at(K::Ensures))) {
      // A spread's `ensures` holds for each iteration (ADR 0060).
      auto a = makeNode(at(K::Invariant)   ? N::Invariant
                        : at(K::Decreases) ? N::Decreases
                                           : N::Ensures,
                        loc());
      take();
      a->add(stmt());
      as->add(std::move(a));
    }
    return as;
  }

  NodePtr quantifier() {
    auto n = makeNode(N::Quantifier, loc(), text());
    take();
    while (!at(K::QDot)) {
      bool paren = accept(K::LParen);
      std::string name(expect(K::Ident, "a bound variable").text);
      if (accept(K::In)) {
        auto b = makeNode(N::RangeBinder, loc(), name);
        b->add(binary(50));
        n->add(std::move(b));
      } else {
        auto b = makeNode(N::Binder, loc(), name);
        if (accept(K::Colon))
          b->add(type());
        else if (paren)
          fail("expected ':' or 'in' after the bound variable");
        else
          b->add(makeNode(N::None, loc()));
        n->add(std::move(b));
      }
      if (paren) expect(K::RParen, "')'");
      if (!at(K::QDot) && !at(K::Ident) && !at(K::LParen))
        fail("expected '.' and a space after the bound variables");
    }
    if (n->kids.empty()) fail("expected a bound variable");
    take();
    n->add(stmt());
    return n;
  }

  // Precedence climbing over the operator table.
  OpInfo binaryInfo() const {
    if (at(K::Eq)) return operatorInfo("=");
    if (at(K::DotDot)) return {50, Assoc::None};
    // `|` is bitwise or only inside brackets, away from match arms: at the
    // top level it separates variants and arms (docs/grammar.md).
    if (at(K::Bar) && bitOr_) return operatorInfo("|");
    if (at(K::Op)) return operatorInfo(tok().text);
    return {};
  }

  NodePtr binary(int minLevel) {
    NodePtr lhs = unary();
    int usedNone = 0;  // level of a non-associative operator already used here
    while (!clauseEnded_) {
      OpInfo info = binaryInfo();
      if (info.level == 0 || info.level < minLevel) break;
      if (info.assoc == Assoc::None && usedNone == info.level) {
        // Inside a contract clause, a second `=` ends the predicate: it is
        // the body's `=` (ADR 0019, rule 1).
        if (contractMode_ && at(K::Eq)) {
          clauseEnded_ = true;
          break;
        }
        fail("comparisons do not associate; add parentheses");
      }
      // An `=` that starts a line ends the predicate: it is the body's
      // (#259). The predicate's own `=` never starts a line in this
      // library, and a definition the interface prints keeps the break.
      if (contractMode_ && at(K::Eq) && pos_ > 0 &&
          tok().loc.line != toks_[pos_ - 1].loc.line) {
        clauseEnded_ = true;
        break;
      }
      if (contractMode_ && at(K::Eq) && !canStartAtom(kind(1)) &&
          !(kind(1) == K::Op && tok(1).text == "-") && kind(1) != K::Forall &&
          kind(1) != K::Exists) {
        clauseEnded_ = true;
        break;
      }
      Token op = take();
      if (info.assoc == Assoc::None) usedNone = info.level;
      NodePtr rhs;
      bool quantified = false;
      if (info.level <= 40 && (at(K::Forall) || at(K::Exists))) {
        rhs = quantifier();
        quantified = true;
      } else {
        rhs = binary(info.assoc == Assoc::Right ? info.level : info.level + 1);
      }
      auto n = makeNode(op.kind == K::DotDot ? N::Range : N::Binary, op.loc,
                        op.kind == K::DotDot ? "" : std::string(op.text));
      n->add(std::move(lhs));
      n->add(std::move(rhs));
      lhs = std::move(n);
      if (quantified) break;
    }
    return lhs;
  }

  NodePtr unary() {
    if (atOp("-")) {
      auto n = makeNode(N::Neg, loc());
      take();
      n->add(unary());
      return n;
    }
    // `~x` is the core builtin `bnot x` (docs/stdlib.md, group 2).
    if (atOp("~")) {
      auto n = makeNode(N::Apply, loc());
      auto fn = makeNode(N::Name, loc(), "bnot");
      fn->flags = "prelude";  // the builtin, whatever is in scope
      n->add(std::move(fn));
      take();
      n->add(unary());
      return n;
    }
    // `@wrap e`, `@trap e`, `@saturate e` and `@proof e` set the overflow
    // mode of one expression (docs/design.md). It is the prelude builtin
    // `#overflow mode e`, as `~x` is `bnot x`.
    if (at(K::Attr) && isOverflowMode(tok().text.substr(1))) {
      auto n = makeNode(N::Apply, loc());
      auto fn = makeNode(N::Name, loc(), "#overflow");
      fn->flags = "prelude";
      n->add(std::move(fn));
      n->add(makeNode(N::Name, loc(), std::string(tok().text.substr(1))));
      take();
      n->add(unary());
      return n;
    }
    return application();
  }

  static bool isOverflowMode(std::string_view m) {
    return m == "wrap" || m == "trap" || m == "saturate" || m == "proof";
  }

  NodePtr application() {
    NodePtr f = postfix();
    // A cost clause after a predicate ends it: `ensures result <= len xs`
    // then `costs iterations <= len xs`.
    auto argument = [&] {
      return canStartAtom(kind()) && !(contractMode_ && atCosts());
    };
    if (argument()) {
      auto app = makeNode(N::Apply, f->loc);
      app->add(std::move(f));
      while (argument())
        app->add(postfix());
      f = std::move(app);
    }
    // `e?` passes an error on (ADR 0028). It applies to the whole
    // application, so `read_all m f?` is `(read_all m f)?`.
    while (atOp("?")) {
      auto t = makeNode(N::Try, loc());
      take();
      t->add(std::move(f));
      f = std::move(t);
    }
    return f;
  }

  NodePtr postfix() {
    NodePtr e = atom();
    for (;;) {
      if (at(K::Dot) && (kind(1) == K::Ident || kind(1) == K::SpliceIdent)) {
        take();
        auto f = makeNode(N::Field, e->loc, text());
        take();
        f->add(std::move(e));
        e = std::move(f);
      } else if (at(K::DotLBracket)) {
        take();
        Bracket b(*this);
        auto ix = makeNode(N::Index, e->loc);
        ix->add(std::move(e));
        ix->add(seq());
        expect(K::RBracket, "']'");
        e = std::move(ix);
      } else if (at(K::TargsOpen)) {
        auto inst = makeNode(N::Instantiate, e->loc);
        inst->add(std::move(e));
        targs(*inst);
        e = std::move(inst);
      } else {
        return e;
      }
    }
  }

  NodePtr atom() {
    SourceLoc start = loc();
    switch (kind()) {
    case K::Ident: {
      // `int{0..100}`: a range type as a value, as in `let percent =
      // int{0..100}` (ADR 0064). Anything else after `name{` is a
      // record literal applied to the name.
      if (kind(1) == K::LBraceAdj)
        if (NodePtr r = attempt([&] {
              NodePtr t = type();
              if (t->kind != N::RangeType)
                fail("not a range type");
              return t;
            }))
          return aliasValue(std::move(r));
      auto n = makeNode(N::Name, start, text());
      take();
      return n;
    }
      case K::Int: { auto n = makeNode(N::IntLit, start, text()); take(); return n; }
      case K::Float: { auto n = makeNode(N::FloatLit, start, text()); take(); return n; }
      case K::String: { auto n = makeNode(N::StringLit, start, text()); take(); return n; }
      case K::True:
      case K::False: { auto n = makeNode(N::BoolLit, start, text()); take(); return n; }
      case K::QIdent: {
        auto n = makeNode(N::QuotedIdent, start, std::string(tok().text.substr(1)));
        take();
        return n;
      }
      case K::Hole: take(); return makeNode(N::Hole, start);
      case K::LParen: {
        take();
        if (accept(K::RParen)) return makeNode(N::Unit, start);
        if ((at(K::Op) || at(K::Eq)) && kind(1) == K::RParen) {
          auto n = makeNode(N::OperatorValue, start, text());
          take();
          take();
          return n;
        }
        Bracket b(*this);
        NodePtr e = withHandle(seq());
        expect(K::RParen, "')'");
        return e;
      }
      case K::LBracket: {
        take();
        Bracket b(*this);
        auto n = makeNode(N::ListLit, start);
        while (!at(K::RBracket)) {
          n->add(elem());
          if (!accept(K::Semi)) break;
        }
        expect(K::RBracket, "']' or ';'");
        return n;
      }
      case K::LBrace:
      case K::LBraceAdj: {
        take();
        Bracket b(*this);
        NodePtr n;
        // `{ $fs }` in a quote: the fields a metaprogram computed, as a
        // list of [name; value] pairs (docs/meta.md).
        if (at(K::SpliceIdent) && kind(1) == K::RBrace) {
          n = makeNode(N::RecordLit, start);
          n->add(makeNode(N::Splice, loc(), text()));
          take();
          expect(K::RBrace, "'}' after the spliced fields");
          return n;
        }
        if (at(K::Ident) && kind(1) == K::Eq) {
          n = makeNode(N::RecordLit, start);
        } else {
          n = makeNode(N::RecordUpdate, start);
          n->add(postfix());
          expect(K::With, "'with' or a field initialiser");
        }
        while (!at(K::RBrace)) {
          auto f = makeNode(N::FieldInit, loc(), std::string(expect(K::Ident, "a field name").text));
          expect(K::Eq, "'=' after the field name");
          f->add(elem());
          n->add(std::move(f));
          if (!accept(K::Semi)) break;
        }
        expect(K::RBrace, "'}' or ';'");
        return n;
      }
      case K::QuoteOpen:
        return quote();
      case K::SpliceIdent: { auto n = makeNode(N::Splice, start, text()); take(); return n; }
      case K::SpliceOpen: {
        take();
        Bracket b(*this);
        auto n = makeNode(N::Splice, start);
        n->add(seq());
        expect(K::RParen, "')'");
        return n;
      }
      default:
        fail("expected an expression");
    }
  }

  // `( items )`, `( name : type )` or `( expression )`.
  NodePtr quote() {
    auto q = makeNode(N::Quote, loc());
    take();
    Bracket b(*this);
    if (at(K::Ident) && kind(1) == K::Colon) {
      auto d = makeNode(N::QuotedDecl, loc(), text());
      take();
      take();
      d->add(type());
      q->add(std::move(d));
    } else if (at(K::Let) && kind(1) == K::Meta && kind(2) == K::Operator) {
      while (at(K::Let)) {
        q->add(metaOperator());
        skipSeps();
      }
    } else if (at(K::Let) && kind(1) != K::LParen) {
      NodePtr first = quotedItem(/*allowIn=*/true);
      bool isItem = first->kind != N::LetIn;
      q->add(std::move(first));
      if (isItem) {
        skipSeps();
        while (at(K::Let)) {
          q->add(kind(1) == K::Meta && kind(2) == K::Operator
                     ? metaOperator()
                     : quotedItem(/*allowIn=*/false));
          skipSeps();
        }
      }
    } else {
      q->add(seq());
    }
    expect(K::RParen, "')' to close the quote");
    return q;
  }

  // ------------------------------------------------------------ patterns

  static bool canStartPatternAtom(K k) {
    switch (k) {
      case K::Ident: case K::Int: case K::String: case K::True: case K::False:
      case K::SpliceIdent: case K::LParen: case K::LBrace: case K::LBracket:
        return true;
      default:
        return false;
    }
  }

  // `p as x` matches `p` and binds `x` to the whole value. The node sits
  // at `x`, the name it binds.
  NodePtr pattern() {
    NodePtr p;
    // `$c x` in a quote: a constructor a metaprogram names, applied.
    bool spliced = at(K::SpliceIdent) && text().rfind("$!", 0) != 0;
    if ((at(K::Ident) || spliced) && canStartPatternAtom(kind(1))) {
      auto c = makeNode(N::PCtor, loc(), text());
      take();
      while (canStartPatternAtom(kind())) c->add(patternAtom());
      p = std::move(c);
    } else {
      p = patternAtom();
    }
    if (!accept(K::As)) return p;
    SourceLoc at = loc();
    auto a = makeNode(N::PAs, at,
                      std::string(expect(K::Ident, "a name after 'as'").text));
    a->add(std::move(p));
    return a;
  }

  NodePtr patternAtom() {
    SourceLoc start = loc();
    switch (kind()) {
      case K::Ident: { auto n = makeNode(N::PVar, start, text()); take(); return n; }
      case K::Int: case K::String: case K::True: case K::False: {
        auto n = makeNode(N::PLit, start, text());
        take();
        return n;
      }
      case K::SpliceIdent: { auto n = makeNode(N::PSplice, start, text()); take(); return n; }
      case K::LParen: {
        if (kind(1) == K::RParen) {  // `()`, as in `Ok ()`
          take();
          take();
          return makeNode(N::PLit, start, "()");
        }
        take();
        Bracket b(*this);
        NodePtr p = pattern();
        if (accept(K::Colon)) {
          auto t = makeNode(N::PTyped, start);
          t->add(std::move(p));
          t->add(type());
          p = std::move(t);
        }
        expect(K::RParen, "')'");
        return p;
      }
      case K::LBracket: {  // `[e]` and `[e; n]`, on types (ADR 0035)
        take();
        Bracket b(*this);
        NodePtr elem = pattern();
        NodePtr p;
        if (accept(K::Semi)) {
          p = makeNode(N::PArray, start);
          p->add(std::move(elem));
          p->add(pattern());
        } else {
          p = makeNode(N::PSlice, start);
          p->add(std::move(elem));
        }
        expect(K::RBracket, "']'");
        return p;
      }
      case K::LBrace: {
        take();
        Bracket b(*this);
        auto r = makeNode(N::PRecord, start);
        while (!at(K::RBrace)) {
          auto f = makeNode(N::PField, loc(), std::string(expect(K::Ident, "a field name").text));
          if (accept(K::Eq))
            f->add(pattern());
          else
            f->add(makeNode(N::None, loc()));
          r->add(std::move(f));
          if (!accept(K::Semi)) break;
        }
        expect(K::RBrace, "'}'");
        return r;
      }
      default:
        fail("expected a pattern");
    }
  }

  OpInfo operatorInfo(std::string_view op) const {
    auto it = operators_.find(op);
    return it != operators_.end() ? it->second : defaultFixity(op);
  }

  std::vector<Token> toks_;
  Diagnostics &diags_;
  const OperatorTable &operators_;
  size_t pos_ = 0;
  // Whether the item being parsed is the file's first, where a module
  // header may stand.
  bool firstItem_ = false;
  bool expressionItems_ = false; // a top-level expression may be any (REPL)
  bool contractMode_ = false;  // parsing a requires/ensures predicate
  bool clauseEnded_ = false;   // the predicate has ended at a body `=`
  bool bitOr_ = false;         // `|` is bitwise or here (binaryInfo)
};

}  // namespace

namespace {

NodePtr parseWith(std::string_view source, Diagnostics &diags,
                  const OperatorTable &operators, bool literate,
                  bool expressionItems) {
  std::vector<RawComment> comments;
  LexOptions options;
  options.literate = literate;
  options.cells = expressionItems;
  options.comments = &comments;
  std::vector<Token> toks = tokenize(source, diags, options);
  if (diags.hasErrors()) return makeNode(NodeKind::Program, SourceLoc{});
  Parser parser(toks, diags, operators);
  if (expressionItems)
    parser.allowExpressionItems();
  NodePtr tree = parser.program();
  attachComments(*tree, toks, comments, source);
  return tree;
}

// A program's own `let meta operator` declarations change how it parses,
// so parse again with them until the table stops changing. Only the last
// parse reports its errors.
NodePtr parseToFixedPoint(std::string_view source, Diagnostics &diags,
                          bool literate, bool expressionItems) {
  OperatorTable table = preludeOperators();
  for (int round = 0;; ++round) {
    Diagnostics local;
    NodePtr tree = parseWith(source, local, table, literate, expressionItems);
    OperatorTable next = preludeOperators();
    collectOperators(*tree, next);
    if (next == table || round == 3 || local.hasErrors()) {
      for (const Diagnostic &d : local.errors()) diags.error(d.loc, d.message);
      return tree;
    }
    table = std::move(next);
  }
}

} // namespace

NodePtr parseProgram(std::string_view source, Diagnostics &diags,
                     const OperatorTable &operators, bool literate) {
  return parseWith(source, diags, operators, literate,
                   /*expressionItems=*/false);
}

NodePtr parseProgram(std::string_view source, Diagnostics &diags,
                     bool literate) {
  return parseToFixedPoint(source, diags, literate,
                           /*expressionItems=*/false);
}

NodePtr parseCells(std::string_view source, Diagnostics &diags) {
  return parseToFixedPoint(source, diags, /*literate=*/false,
                           /*expressionItems=*/true);
}

NodePtr parseContractFragment(std::string_view source, Diagnostics &diags) {
  std::vector<RawComment> comments;
  LexOptions options;
  options.comments = &comments;
  std::vector<Token> toks = tokenize(source, diags, options);
  if (diags.hasErrors()) return makeNode(NodeKind::Contracts, SourceLoc{});
  NodePtr tree = Parser(toks, diags, preludeOperators()).contractFragment();
  attachComments(*tree, toks, comments, source);
  return tree;
}

void collectOperators(const Node &program, OperatorTable &table) {
  for (const NodePtr &item : program.kids) {
    if (item->kind != NodeKind::MetaOperator) continue;
    const Node &fixity = *item->kids[0];
    if (fixity.kind != NodeKind::Fixity) continue;
    // "prec <level> <assoc>"
    size_t a = fixity.text.find(' '), b = fixity.text.rfind(' ');
    Fixity f;
    f.level = parseLevel(fixity.text.substr(a + 1, b - a - 1));
    std::string assoc = fixity.text.substr(b + 1);
    f.assoc = assoc == "left"    ? Assoc::Left
              : assoc == "right" ? Assoc::Right
                                 : Assoc::None;
    table[item->text] = f;
  }
}

const OperatorTable &preludeOperators() {
  // The prelude's own operators appear only inside quotes, so it parses
  // with no table at all.
  static const OperatorTable table = [] {
    OperatorTable empty, out;
    Diagnostics diags;
    NodePtr prelude = parseProgram(preludeSource(), diags, empty);
    collectOperators(*prelude, out);
    return out;
  }();
  return table;
}

void applyTheoryAttrs(Node &theory, const Node &attrs) {
  for (NodePtr &m : theory.kids) {
    if (m->kind != NodeKind::LetItem || m->kids.size() < 2) continue;
    NodePtr &ret = m->kids[1];
    if (ret->kind != NodeKind::RetAnnot) {
      auto r = makeNode(NodeKind::RetAnnot, ret->loc);
      r->add(makeNode(NodeKind::None, ret->loc));
      r->add(makeNode(NodeKind::Attrs, ret->loc));
      ret = std::move(r);
    }
    Node &own = *ret->kids[1];
    for (const NodePtr &a : attrs.kids) {
      bool has = false;
      for (const NodePtr &b : own.kids) has |= b->text == a->text;
      if (!has) own.add(clone(*a));
    }
  }
}

}  // namespace pia::syntax
