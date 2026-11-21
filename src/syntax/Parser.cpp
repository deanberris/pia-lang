#include "syntax/Parser.h"

#include <string>
#include <utility>
#include <vector>

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
OpInfo defaultFixity(std::string_view op) {
  if (op.substr(0, 2) == "||") return {2, Assoc::Right};
  if (op.substr(0, 2) == "&&") return {3, Assoc::Right};
  switch (op[0]) {
    case '=': case '<': case '>': case '|': case '&': case '$': case '!':
      return {4, Assoc::None};
    case '+': case '-':
      return {6, Assoc::Left};
    default:
      return {7, Assoc::Left};
  }
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
    bool contract, ended;
    explicit Bracket(Parser &p)
        : p(p), contract(p.contractMode_), ended(p.clauseEnded_) {
      p.contractMode_ = false;
      p.clauseEnded_ = false;
    }
    ~Bracket() {
      p.contractMode_ = contract;
      p.clauseEnded_ = ended;
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
      case K::Assume: case K::Type:
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
        return let(/*allowItem=*/true, /*allowIn=*/false);
      case K::Interface:
        return interfaceItem();
      case K::Module:
        return moduleItem();
      case K::Import: {
        auto n = makeNode(N::Import, loc());
        take();
        n->text = path();
        return n;
      }
      default:
        break;
    }
    auto n = makeNode(N::ExprItem, loc());
    n->add(application());
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

  // `let [rec] [meta] name params [: annot attrs] contracts = body [in body]`
  NodePtr let(bool allowItem, bool allowIn) {
    SourceLoc start = loc();
    expect(K::Let, "'let'");
    std::string flags;
    if (accept(K::Rec)) flags = "rec";
    if (accept(K::Meta)) flags += flags.empty() ? "meta" : " meta";
    if (!at(K::Ident) && !at(K::SpliceIdent)) fail("expected a name after 'let'");
    auto n = makeNode(N::LetItem, start, text());
    n->flags = flags;
    take();
    n->add(params());
    n->add(retAnnot());
    Node *contracts = n->add(makeNode(N::Contracts, loc()));
    while (atContract()) contracts->add(contract());

    NodePtr body;
    if (accept(K::Eq)) {
      body = seq();
    } else {
      body = splitBodyFromContract(*contracts);
      if (!body) fail("expected '=' and a definition");
    }
    n->add(std::move(body));

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
  // the last `=` on the right spine of the final clause.
  NodePtr splitBodyFromContract(Node &contracts) {
    if (contracts.kids.empty()) return nullptr;
    Node &clause = *contracts.kids.back();
    if (clause.kind == N::Decreases) return nullptr;
    NodePtr *slot = &clause.kids[0];
    while ((*slot)->kind == N::Binary && (*slot)->text != "=" &&
           operatorInfo((*slot)->text).level < 4)
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
        expect(K::RParen, "')' after the parameter's type");
        ps->add(std::move(p));
      } else {
        return ps;
      }
    }
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

  bool atContract() const {
    return at(K::Requires) || at(K::Ensures) || at(K::Decreases);
  }

  NodePtr contract() {
    N k = at(K::Requires) ? N::Requires : at(K::Ensures) ? N::Ensures : N::Decreases;
    auto c = makeNode(k, loc());
    take();
    bool savedContract = contractMode_, savedEnded = clauseEnded_;
    contractMode_ = true;
    clauseEnded_ = false;
    c->add(stmt());
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
    if (!at(K::Op) && !at(K::Eq)) fail("expected an operator");
    n->text = text();
    take();
    expect(K::RParen, "')' after the operator");
    if (accept(K::Colon)) {
      auto f = makeNode(N::Fixity, loc());
      std::string prec(expect(K::Ident, "'prec'").text);
      if (prec != "prec") fail("expected 'prec'");
      std::string level(expect(K::Int, "a precedence level").text);
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
    expect(K::Eq, "'='");
    expect(K::Sig, "'sig'");
    while (!at(K::End)) {
      if (at(K::Hole)) {
        n->add(makeNode(N::Hole, loc()));
        take();
        continue;
      }
      SourceLoc start = loc();
      expect(K::Let, "'let' or 'end' in a signature");
      if (!at(K::Ident) && !at(K::SpliceIdent)) fail("expected a name");
      std::string name = text();
      take();
      if (accept(K::Colon)) {
        auto v = makeNode(N::SigVal, start, name);
        v->add(annot());
        v->add(attrs());
        Node *cs = v->add(makeNode(N::Contracts, loc()));
        while (atContract()) cs->add(contract());
        n->add(std::move(v));
      } else if (accept(K::Eq)) {
        auto t = makeNode(N::SigType, start, name);
        if (!at(K::Type)) fail("expected 'type' in a signature type definition");
        t->add(typeValue());
        n->add(std::move(t));
      } else {
        fail("expected ':' or '=' after the name");
      }
    }
    take();
    return n;
  }

  NodePtr moduleItem() {
    auto n = makeNode(N::Module, loc());
    take();
    n->text = std::string(expect(K::Ident, "a module name").text);
    Node *paths = n->add(makeNode(N::Paths, loc()));
    if (accept(K::Colon)) {
      do {
        paths->add(makeNode(N::Path, loc(), path()));
      } while (accept(K::Comma));
    }
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
    if (at(K::Borrowed)) addWord("borrowed");
    else if (at(K::Moved)) addWord("moved");
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
    if (at(K::LParen) && kind(1) == K::Ident && kind(2) == K::Colon) {
      take();
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
      } else if (canStartTypeAtom(kind()) && !at(K::Type)) {
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
        if (at(K::TargsOpen)) {
          auto n = makeNode(N::TypeInst, start, name);
          targs(*n);
          return n;
        }
        if (accept(K::LBraceAdj)) {
          Bracket b(*this);
          auto n = makeNode(N::RangeType, start, name);
          n->add(binary(6));
          expect(K::DotDot, "'..' in a range type");
          n->add(binary(6));
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
    while (!at(K::RBrace)) {
      auto f = makeNode(N::FieldDecl, loc(), std::string(expect(K::Ident, "a field name").text));
      expect(K::Colon, "':' after the field name");
      f->add(annot());
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

  NodePtr typeValue() {
    auto n = makeNode(N::TypeValue, loc());
    expect(K::Type, "'type'");
    if (at(K::Bar)) {
      auto vs = makeNode(N::Variants, loc());
      while (accept(K::Bar)) {
        auto c = makeNode(N::Ctor, loc(), std::string(expect(K::Ident, "a constructor name").text));
        if (accept(K::Of))
          c->add(appType());
        else
          c->add(makeNode(N::None, loc()));
        vs->add(std::move(c));
      }
      n->add(std::move(vs));
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
      if (kind(1) == K::LParen) return lambda(/*elemBody=*/false);
      return let(/*allowItem=*/false, /*allowIn=*/true);
    }
    if (at(K::Match)) return match();
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
    if (at(K::Let) && kind(1) == K::LParen) return lambda(/*elemBody=*/true);
    return stmt();
  }

  NodePtr lambda(bool elemBody) {
    auto n = makeNode(N::Lambda, loc());
    take();  // let
    while (at(K::LParen)) {
      auto p = makeNode(N::LParam, loc());
      take();
      if (accept(K::RParen)) {
        p->add(makeNode(N::Unit, p->loc));
        p->add(makeNode(N::None, p->loc));
      } else {
        Bracket b(*this);
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
    expect(K::FatArrow, "'=>' after the parameters");
    n->add(elemBody ? elem() : seq());
    return n;
  }

  NodePtr match() {
    auto n = makeNode(N::Match, loc());
    take();
    n->add(seq());
    expect(K::With, "'with'");
    accept(K::Bar);
    do {
      auto arm = makeNode(N::Arm, loc());
      arm->add(pattern());
      expect(K::Arrow, "'->' after the pattern");
      arm->add(seq());
      n->add(std::move(arm));
    } while (accept(K::Bar));
    return n;
  }

  NodePtr stmt() {
    SourceLoc start = loc();
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
        n->add(binary(2));
        if (spread) {
          n->add(attrs());
        } else if (accept(K::Step)) {
          n->add(binary(6));
        } else {
          n->add(makeNode(N::None, loc()));
        }
        n->add(loopAnnots());
        expect(K::Do, "'do'");
        n->add(seq());
        expect(K::Done, "'done'");
        return n;
      }
      case K::While: {
        take();
        auto n = makeNode(N::While, start);
        n->add(seq());
        n->add(loopAnnots());
        expect(K::Do, "'do'");
        n->add(seq());
        expect(K::Done, "'done'");
        return n;
      }
      case K::Forall:
      case K::Exists:
        return quantifier();
      case K::Assert:
      case K::Assume: {
        auto n = makeNode(at(K::Assert) ? N::Assert : N::Assume, start);
        take();
        n->add(binary(0));
        return n;
      }
      case K::Type:
        return typeValue();
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

  NodePtr loopAnnots() {
    auto as = makeNode(N::LoopAnnots, loc());
    while (at(K::Invariant) || at(K::Decreases)) {
      auto a = makeNode(at(K::Invariant) ? N::Invariant : N::Decreases, loc());
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
        b->add(binary(5));
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
    if (at(K::DotDot)) return {5, Assoc::None};
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
      if (info.level <= 4 && (at(K::Forall) || at(K::Exists))) {
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
    return application();
  }

  NodePtr application() {
    NodePtr f = postfix();
    if (!canStartAtom(kind())) return f;
    auto app = makeNode(N::Apply, f->loc);
    app->add(std::move(f));
    while (canStartAtom(kind())) app->add(postfix());
    return app;
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
      case K::Ident: { auto n = makeNode(N::Name, start, text()); take(); return n; }
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
        NodePtr e = seq();
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
      NodePtr first = let(/*allowItem=*/true, /*allowIn=*/true);
      bool isItem = first->kind == N::LetItem;
      q->add(std::move(first));
      if (isItem) {
        skipSeps();
        while (at(K::Let)) {
          q->add(kind(1) == K::Meta && kind(2) == K::Operator
                     ? metaOperator()
                     : let(/*allowItem=*/true, /*allowIn=*/false));
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
      case K::SpliceIdent: case K::LParen: case K::LBrace:
        return true;
      default:
        return false;
    }
  }

  NodePtr pattern() {
    if (at(K::Ident) && canStartPatternAtom(kind(1))) {
      auto c = makeNode(N::PCtor, loc(), text());
      take();
      while (canStartPatternAtom(kind())) c->add(patternAtom());
      return c;
    }
    return patternAtom();
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
  bool contractMode_ = false;  // parsing a requires/ensures predicate
  bool clauseEnded_ = false;   // the predicate has ended at a body `=`
};

}  // namespace

NodePtr parseProgram(std::string_view source, Diagnostics &diags,
                     const OperatorTable &operators) {
  std::vector<Token> toks = tokenize(source, diags);
  if (diags.hasErrors()) return makeNode(NodeKind::Program, SourceLoc{});
  return Parser(std::move(toks), diags, operators).program();
}

NodePtr parseProgram(std::string_view source, Diagnostics &diags) {
  // A program's own `let meta operator` declarations change how it parses,
  // so parse again with them until the table stops changing. Only the last
  // parse reports its errors.
  OperatorTable table = preludeOperators();
  for (int round = 0;; ++round) {
    Diagnostics local;
    NodePtr tree = parseProgram(source, local, table);
    OperatorTable next = preludeOperators();
    collectOperators(*tree, next);
    if (next == table || round == 3 || local.hasErrors()) {
      for (const Diagnostic &d : local.errors()) diags.error(d.loc, d.message);
      return tree;
    }
    table = std::move(next);
  }
}

NodePtr parseContractFragment(std::string_view source, Diagnostics &diags) {
  std::vector<Token> toks = tokenize(source, diags);
  if (diags.hasErrors()) return makeNode(NodeKind::Contracts, SourceLoc{});
  return Parser(std::move(toks), diags, preludeOperators()).contractFragment();
}

void collectOperators(const Node &program, OperatorTable &table) {
  for (const NodePtr &item : program.kids) {
    if (item->kind != NodeKind::MetaOperator) continue;
    const Node &fixity = *item->kids[0];
    if (fixity.kind != NodeKind::Fixity) continue;
    // "prec <level> <assoc>"
    size_t a = fixity.text.find(' '), b = fixity.text.rfind(' ');
    Fixity f;
    f.level = std::stoi(fixity.text.substr(a + 1, b - a - 1));
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

}  // namespace pia::syntax
