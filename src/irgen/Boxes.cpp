#include "irgen/Boxes.h"

#include <algorithm>
#include <functional>
#include <map>
#include <set>
#include <tuple>
#include <vector>

#include "syntax/Interfaces.h"
#include "syntax/Lexer.h"
#include "syntax/Parser.h"

namespace pia::irgen {

namespace {

using syntax::Node;
using syntax::NodeKind;
using syntax::NodePtr;
using syntax::Token;
using K = syntax::TokenKind;

// By requirement name, for the stubs flagged "box_uncallable"; the
// program is cloned after this pass, so the flag travels and the name
// finds the reason.
std::map<std::string, std::string> &uncallable() {
  static std::map<std::string, std::string> reasons;
  return reasons;
}

// By function name, for the functions flagged "box_op", whose bodies are a
// box's own ops; like uncallable(), it outlives the program's clone.
std::map<std::string, BoxOp> &boxOps() {
  static std::map<std::string, BoxOp> ops;
  return ops;
}

// The generic type items whose first parameter is `@unsized`.
std::set<std::string> unsizedTypes(const Node &program) {
  std::set<std::string> out;
  for (const NodePtr &item : program.kids)
    if (item->kind == NodeKind::LetItem && item->kids.size() > 3 &&
        item->kids[3]->kind == NodeKind::Lambda &&
        !item->kids[3]->kids.empty() &&
        item->kids[3]->kids[0]->kind == NodeKind::LParam &&
        item->kids[3]->kids[0]->flags == "unsized")
      out.insert(item->text);
  return out;
}

std::map<std::string, const Node *> concepts(const Node &program) {
  std::map<std::string, const Node *> out;
  for (const NodePtr &item : program.kids)
    if (syntax::isConceptItem(*item)) out[item->text] = item.get();
  return out;
}

// A concept's name as part of an identifier.
std::string mangle(const std::string &c) {
  std::string out;
  for (char ch : c) out += (ch == '.' ? '_' : ch);
  return out;
}

// How generated source names the concept `c`. An imported one is `M.C`,
// which the parser would read as a field of `M`, so it is spelled as one
// identifier and named back by renameConcept once parsed.
std::string conceptRef(const std::string &c) {
  return c.find('.') == std::string::npos ? c : "pia_concept_" + mangle(c);
}

void renameConcept(Node &n, const std::string &c) {
  if ((n.kind == NodeKind::Name || n.kind == NodeKind::TypeName) &&
      n.text == conceptRef(c))
    n.text = c;
  for (NodePtr &k : n.kids)
    renameConcept(*k, c);
}

// The text of a type as written, for the types requirements use.
std::string typeText(const Node &t, std::string *why) {
  switch (t.kind) {
    case NodeKind::TypeName:
      return t.text;
    case NodeKind::UnitType:
      return "unit";
    case NodeKind::SliceType:
      return "[" + typeText(*t.kids[0], why) + "]";
    case NodeKind::ArrayType:
      return "[" + typeText(*t.kids[0], why) + "; " + t.kids[1]->text + "]";
    case NodeKind::TypeApp: {
      std::string out = "(";
      for (size_t i = 0; i < t.kids.size(); ++i)
        out += (i ? " " : "") + typeText(*t.kids[i], why);
      return out + ")";
    }
    case NodeKind::Annot:
      return typeText(*t.kids[1], why);
    default:
      if (why) *why = "a requirement's type that boxes cannot spell yet";
      return "unit";
  }
}

bool mentionsName(const Node &n, const std::string &name) {
  if ((n.kind == NodeKind::TypeName || n.kind == NodeKind::Name) &&
      n.text == name)
    return true;
  for (const NodePtr &k : n.kids)
    if (mentionsName(*k, name)) return true;
  return false;
}

struct Param {
  std::string name, type, mods;
  bool receiver = false;
};

struct Requirement {
  std::string name;
  std::vector<Param> params;
  std::string result;
  std::vector<const Node *> contracts;
  std::string why;  // not empty: it cannot be called through a box
};

struct Law {
  std::string name, param;
  std::vector<const Node *> contracts;
};

// Rewrites a contract's tokens: names in `rename` become their
// replacement, so the text can move to another place.
struct Text {
  std::string_view source;
  std::vector<Token> tokens;

  // The contract `c`, up to `end`, with names renamed.
  std::string contract(const Node &c, uint32_t end,
                       const std::map<std::string, std::string> &rename) {
    std::string out;
    for (const Token &t : tokens) {
      if (t.loc.offset < c.loc.offset) continue;
      if (t.loc.offset >= end || t.kind == K::Eof) break;
      if (t.kind == K::Sep) continue;
      std::string word(t.text);
      if (t.kind == K::Ident)
        if (auto it = rename.find(word); it != rename.end()) word = it->second;
      out += (out.empty() ? "" : " ") + word;
    }
    return out;
  }

  // Where the item that holds `n` ends: the next token `end` or `let`.
  uint32_t endAfter(uint32_t start) {
    for (const Token &t : tokens)
      if (t.loc.offset > start && (t.kind == K::End || t.kind == K::Let))
        return t.loc.offset;
    return static_cast<uint32_t>(source.size());
  }
};

// The end of each contract in `cs`: the next one's start, or the item's.
std::vector<uint32_t> contractEnds(const std::vector<const Node *> &cs,
                                   Text &text) {
  std::vector<uint32_t> out;
  for (size_t i = 0; i < cs.size(); ++i)
    out.push_back(i + 1 < cs.size() ? cs[i + 1]->loc.offset
                                    : text.endAfter(cs[i]->loc.offset));
  return out;
}

// The source of the items that make `box C` (ADR 0046, steps 2 to 4).
std::string erasedSource(const std::string &cname, const Node &concept,
                         const std::string &box, Text &text,
                         std::map<std::string, std::string> &whyNot,
                         const std::vector<std::string> *closed, int words,
                         std::map<std::string, BoxOp> &ops,
                         syntax::Diagnostics &diags) {
  const std::string m = mangle(cname);
  const std::string theory = "erased_" + m;
  const std::string boxType = "box_" + m;
  std::string tparam;
  for (const NodePtr &p : concept.kids[0]->kids)
    if (p->kind == NodeKind::Param) {
      tparam = p->text;
      break;
    }
  std::vector<Requirement> reqs;
  std::vector<Law> laws;
  for (const NodePtr &r : concept.kids[3]->kids) {
    if (r->kind == NodeKind::SigVal) {
      Requirement q;
      q.name = r->text;
      const Node *cur = r->kids[0]->kids[1].get();
      int receivers = 0;
      for (; cur->kind == NodeKind::ArrowType; cur = cur->kids[1].get()) {
        const Node &d = *cur->kids[0];
        Param p;
        p.name = d.text;
        p.mods = d.kids[0]->text;
        p.receiver = d.kids[1]->kind == NodeKind::TypeName &&
                     d.kids[1]->text == tparam;
        if (p.receiver) {
          ++receivers;
        } else {
          if (mentionsName(*d.kids[1], tparam))
            q.why = "its parameter '" + p.name + "' holds a value of the "
                    "concept's type inside another type";
          p.type = typeText(*d.kids[1], &q.why);
        }
        q.params.push_back(p);
      }
      if (mentionsName(*cur, tparam))
        q.why = "its result is a value of the concept's type, which has no "
                "size known through a box";
      else
        q.result = typeText(*cur, &q.why);
      if (q.why.empty() && receivers != 1)
        q.why = receivers == 0
                    ? "it takes no value of the concept's type to call it on"
                    : "it takes " + std::to_string(receivers) +
                          " values of the concept's type, and two boxes may "
                          "hold values of different types";
      if (q.why.empty())
        for (const Param &p : q.params)
          if (p.receiver && !p.mods.empty())
            q.why = "its receiver is '" + p.mods + "', and a box forwards "
                    "only a receiver it lends for now";
      for (const NodePtr &c : r->kids[2]->kids) q.contracts.push_back(c.get());
      reqs.push_back(std::move(q));
    } else if (r->kind == NodeKind::SigLemma) {
      const Node &ps = *r->kids[0];
      if (ps.kids.size() != 1 || ps.kids[0]->kids.empty() ||
          !mentionsName(*ps.kids[0]->kids[0], tparam))
        continue;  // a law over two values says nothing of one box
      Law l;
      l.name = r->text;
      l.param = ps.kids[0]->text;
      for (const NodePtr &c : r->kids[1]->kids) l.contracts.push_back(c.get());
      laws.push_back(std::move(l));
    } else if (r->kind == NodeKind::SigInclude) {
      diags.error(r->loc, "a box over '" + cname + "' cannot forward the "
                          "concepts it includes yet (ADR 0046, step 4)");
    }
  }
  // The callable requirements, as the theory's functions.
  std::map<std::string, std::string> inTheory;   // req -> req_of
  std::map<std::string, std::string> outside;    // req -> theory.req_of
  for (const Requirement &q : reqs)
    if (q.why.empty()) {
      inTheory[q.name] = q.name + "_of";
      outside[q.name] = theory + "." + q.name + "_of";
    }
  auto args = [](const Requirement &q, const std::string &recv) {
    std::string out;
    for (const Param &p : q.params) out += " " + (p.receiver ? recv : p.name);
    return out;
  };
  auto rewritten = [&](const std::vector<const Node *> &cs,
                       std::map<std::string, std::string> rename) {
    std::string out;
    std::vector<uint32_t> ends = contractEnds(cs, text);
    for (size_t i = 0; i < cs.size(); ++i)
      out += "\n  " + text.contract(*cs[i], ends[i], rename);
    return out;
  };
  // The receiver is the box itself, `b`, a value of box_C: in the
  // theory, the uninterpreted functions take it whole, so one box is one
  // object to them.
  const std::string self = "self_";
  auto params = [&](const Requirement &q, const std::string &recvType) {
    std::string ps;
    for (const Param &p : q.params)
      ps += " (" + (p.receiver ? self : p.name) + " : " +
            (p.receiver ? recvType : p.type) + ")";
    return ps;
  };
  // The theory of the box's erased requirements, over `recvType`: the
  // box's own, and a copy over a one-byte shape for the consistency check.
  auto theorySource = [&](const std::string &name,
                          const std::string &recvType) {
    std::string out = "let theory " + name + " = sig\n";
    for (const Requirement &q : reqs) {
      if (!q.why.empty())
        continue;
      std::string sig;
      for (const Param &p : q.params)
        sig += "(" + (p.receiver ? self : p.name) + " : " +
               (p.receiver ? recvType : p.type) + ") -> ";
      out += "  let spec " + q.name + "_of : " + sig + q.result + "\n";
    }
    // A box's state (the amendment's theory of a box's state): whether it
    // holds an object, and which of this module's widened types that is.
    // Spec only: nothing at run time.
    const std::string arg = "(" + self + " : " + recvType + ")";
    out += "  let spec full_box : " + arg + " -> bool\n";
    if (closed)
      for (const std::string &t : *closed)
        out += "  let spec holds_" + t + " : " + arg + " -> bool\n";
    // A box that holds a type is full, and holds at most one type.
    if (closed)
      for (size_t i = 0; i < closed->size(); ++i) {
        const std::string &t = (*closed)[i];
        out += "  let axiom holds_" + t + "_full " + arg +
               "\n  ensures holds_" + t + " " + self + " ==> full_box " + self +
               "\n";
        for (size_t j = i + 1; j < closed->size(); ++j)
          out += "  let axiom holds_" + t + "_" + (*closed)[j] + " " + arg +
                 "\n  ensures holds_" + t + " " + self + " ==> holds_" +
                 (*closed)[j] + " " + self + " = false\n";
      }
    for (const Requirement &q : reqs) {
      bool ensures = false;
      for (const Node *c : q.contracts)
        ensures |= c->kind == NodeKind::Ensures;
      if (!q.why.empty() || !ensures)
        continue;
      std::map<std::string, std::string> rename = inTheory;
      std::string recv;
      for (const Param &p : q.params)
        if (p.receiver)
          recv = p.name;
      rename[recv] = self;
      rename["result"] = "(" + q.name + "_of" + args(q, self) + ")";
      out += "  let axiom " + q.name + "_contract" + params(q, recvType) +
             rewritten(q.contracts, rename) + "\n";
    }
    for (const Law &l : laws) {
      std::map<std::string, std::string> rename = inTheory;
      out += "  let axiom " + l.name + "_law (" + l.param + " : " + recvType +
             ")" + rewritten(l.contracts, rename) + "\n";
    }
    return out + "end\n\n";
  };
  std::string src = "@trusted\n" + theorySource(theory, boxType);
  // Its axioms speak of one box at a time and never of the box's words, so
  // they are consistent over the box exactly when they are over any other
  // inhabited type: the check runs over a one-byte shape, whose cost does
  // not grow with the box (#563).
  if (closed)
    src += "let " + boxType + "_shape = type { tag : u8 }\n\n" +
           theorySource(theory + "_shape", boxType + "_shape");
  // The box: before the module's widened types are known, a stand-in; then
  // one cache line of words (the cache-line amendment): the descriptor's
  // address, then the object.
  if (!closed) {
    src += "let " + boxType + " = type { tag : u8 }\n\n";
  } else {
    src += "let " + boxType + " = type {";
    for (int w = 0; w < words; ++w)
      src += std::string(w ? ";" : "") + " w" + std::to_string(w) + " : u64";
    src += " }\n\n";
  }
  // A box's state as contracts name it: `requires full b`, `ensures
  // unknown b` (every contract states it, the amendment's theory).
  src += "let spec full (b : " + boxType + ") : bool = " + theory +
         ".full_box b\n";
  // `unknown` is true of every box: it only says a contract states that
  // the caller cannot know the state, so it gives the solver nothing to
  // instantiate, even under a `forall` over a slice.
  src += "let spec unknown (b : " + boxType + ") : bool = true\n\n";
  if (!closed)
    src += "let is_full (b : " + boxType +
           ") : bool\n  ensures result = " + theory +
           ".full_box b\n= false\n\n";
  // The requirements a box can call, in the concept's order: the
  // descriptor's entries.
  std::vector<const Requirement *> callable;
  for (const Requirement &q : reqs)
    if (q.why.empty())
      callable.push_back(&q);
  for (const Requirement &q : reqs) {
    std::string recv;
    for (const Param &p : q.params)
      if (p.receiver) recv = p.name;
    if (!q.why.empty()) {
      // A stub, so that a call says why it cannot be made. It is never
      // called: IRGen reports the call (boxUncallable).
      whyNot[q.name] = q.why;
      if (!q.result.empty()) {
        std::string ps;
        for (const Param &p : q.params)
          ps += " (" + p.name + " : " + (p.receiver ? boxType : p.type) + ")";
        src += "let " + q.name + ps + " : " + q.result +
               "\n  requires false\n= abort ()\n\n";
      }
      continue;
    }
    std::vector<uint32_t> ends = contractEnds(q.contracts, text);
    auto requires = [&](std::map<std::string, std::string> rename) {
      std::string out;
      for (size_t i = 0; i < q.contracts.size(); ++i)
        if (q.contracts[i]->kind == NodeKind::Requires)
          out += "\n  " + text.contract(*q.contracts[i], ends[i], rename);
      return out;
    };
    std::map<std::string, std::string> onSelf = outside;
    onSelf[recv] = self;
    // The call through the box: through the descriptor in code; to the
    // verifier, a proxy whose result is the erased requirement's, so a
    // caller is told the contract and no more. The use check at widen
    // justifies it. Before the widened types are known, a stand-in.
    const std::string call = theory + "_call_" + q.name;
    src += "let " + call + params(q, boxType) + " : " + q.result +
           requires(onSelf) + "\n  requires " + theory + ".full_box " + self +
           "\n  ensures result = " + theory + "." + q.name + "_of" +
           args(q, self) + "\n= abort ()\n\n";
    if (closed) {
      BoxOp op;
      op.kind = BoxOp::Call;
      op.entry = static_cast<int>(
          std::find(callable.begin(), callable.end(), &q) - callable.begin());
      op.words = words;
      ops[call] = op;
      // Each type's thunk: the requirement called on a value of it, which
      // the descriptor's entry calls with the object it loads.
      for (const std::string &t : *closed) {
        std::map<std::string, std::string> onValue;
        onValue[recv] = self;
        std::string ps;
        for (const Param &p : q.params)
          ps += " (" + (p.receiver ? self : p.name) + " : " +
                (p.receiver ? t : p.type) + ")";
        src += "let " + theory + "_thunk_" + q.name + "_" + t + ps + " : " +
               q.result + requires(onValue) + "\n= " + q.name + args(q, self) +
               "\n\n";
      }
    }
    std::map<std::string, std::string> onBox = outside;
    std::string ps;
    for (const Param &p : q.params)
      ps += " (" + p.name + " : " + (p.receiver ? boxType : p.type) + ")";
    // Only a full box has an object to call: a goal at each call, proved
    // from the state the caller's contract or its own code gives the box.
    src += "let " + q.name + ps + " : " + q.result + requires(onBox) +
           "\n  requires " + theory + ".full_box " + recv +
           "\n  ensures result = " + theory + "." + q.name + "_of" +
           args(q, recv) + "\n= " + theory + "_call_" + q.name + args(q, recv) +
           "\n\n";
  }
  // The use check, the constraint `C t`, at each instance of widen.
  std::string full = "\n  requires len b.slot = 1 && b.state = 1";
  if (!closed) {
    src += "let widen (t : type where " + conceptRef(cname) +
           " t) (b : " + box + " t) : " + boxType + full + "\n  ensures " +
           theory + ".full_box result\n= { tag = 0 }\n";
    src += "let take (t : type where " + conceptRef(cname) +
           " t) (b : inout "
           "mutable " +
           boxType + ") (d : inout mutable " + box +
           " t) : "
           "result unit box_mismatch\n  requires len d.slot = 1 && d.state = "
           "0\n= Err Mismatch\n";
    src += "let consume (t : type where " + conceptRef(cname) +
           " t) (b : "
           "inout mutable " +
           boxType +
           ") : result t box_mismatch\n= Err "
           "Mismatch\n";
    src += "let is (t : type where " + conceptRef(cname) +
           " t) (b : " + boxType + ") : bool\n= false\n";
  } else {
    src += "let " + theory + "_check (t : type where " + conceptRef(cname) +
           " t) (b : " + box + " t) : unit = ()\n\n";
    // The empty box `take` and `consume` leave: the concept's one static
    // control block.
    const std::string empty = theory + "_empty";
    BoxOp e;
    e.kind = BoxOp::Empty;
    e.descriptor = "pia$e$" + m;
    e.entry = static_cast<int>(callable.size());
    ops[empty] = e;
    src += "let " + empty + " (b : " + boxType + ") : " + boxType +
           "\n  ensures " + theory + ".full_box result = false\n= abort ()\n\n";
    // Whether a box is full, read at run time (an indeterminate state's
    // query): its first word is not the empty control block's address.
    const std::string isEmpty = theory + "_is_empty";
    BoxOp ie;
    ie.kind = BoxOp::Holds;
    ie.descriptor = e.descriptor;
    ie.entry = e.entry;
    ie.emptyBlock = true;
    ops[isEmpty] = ie;
    src += "let " + isEmpty + " (b : " + boxType +
           ") : bool\n  ensures result = (" + theory +
           ".full_box b = false)\n= abort ()\n\n";
    src += "let is_full (b : " + boxType +
           ") : bool\n  ensures result = " + theory + ".full_box b\n= if " +
           isEmpty + " b then false else true\n\n";
    for (const std::string &t : *closed) {
      // The object, packed into the box with its descriptor.
      const std::string pack = theory + "_pack_" + t;
      BoxOp op;
      op.kind = BoxOp::Pack;
      op.descriptor = "pia$t$" + t + "$" + m;
      for (const Requirement *q : callable)
        op.thunks.push_back(theory + "_thunk_" + q->name + "_" + t);
      ops[pack] = op;
      const std::string holdsT = theory + ".holds_" + t;
      src += "let " + pack + " (v : " + t + ") : " + boxType + "\n  ensures " +
             holdsT + " result\n= abort ()\n\n";
      src += "let widen (b : " + box + " " + t + ") : " + boxType + full +
             "\n  ensures " + holdsT + " result\n= " + theory +
             "_check b;\n  " + pack + " b.slot.[0]\n\n";
      // Taking it out (Dean, 2026-11-28): when the box's descriptor is
      // `t`'s, `take b d` copies its object into the caller's empty box
      // `d`, and `consume<t> b` returns it, and both leave `b` empty. IRGen
      // treats `b` as moved from then, and only then: a mismatch is an
      // `Err` that leaves it as it was.
      const std::string holds = theory + "_holds_" + t;
      const std::string unpack = theory + "_unpack_" + t;
      BoxOp h;
      h.kind = BoxOp::Holds;
      h.descriptor = op.descriptor;
      ops[holds] = h;
      BoxOp u;
      u.kind = BoxOp::Unpack;
      ops[unpack] = u;
      src += "let " + holds + " (b : " + boxType +
             ") : bool\n  ensures result "
             "= " +
             theory + ".holds_" + t + " b\n= abort ()\n\n";
      src += "let " + unpack + " (b : " + boxType + ") : " + t +
             "\n  requires " + theory + ".holds_" + t + " b\n= abort ()\n\n";
      // On `Ok` the box is empty; on `Err`, its state is as it was.
      std::string unchanged =
          theory + ".full_box b = old (" + theory + ".full_box b)";
      for (const std::string &u : *closed)
        unchanged += " && " + theory + ".holds_" + u + " b = old (" + theory +
                     ".holds_" + u + " b)";
      const std::string emptied = theory + ".full_box b = false";
      src += "let take (b : inout mutable " + boxType +
             ") (d : inout mutable " + box + " " + t +
             ") : result unit box_mismatch"
             "\n  requires len d.slot = 1 && d.state = 0"
             "\n  ensures len d.slot = 1"
             "\n  ensures (match result with | Ok -> d.state = 1 && " +
             emptied + " | Err _ -> d.state = 0 && " + unchanged + ")\n= if " +
             holds + " b then\n    (d.slot.[0] <- " + unpack +
             " b;\n     b <- " + empty +
             " b;\n     d.state <- 1;"
             "\n     Ok ())\n  else Err Mismatch\n\n";
      // The where is written as the operator expands, since this source
      // is parsed after expansion.
      src += "let consume (t : type where eq t " + t + ") (b : inout mutable " +
             boxType + ") : result " + t +
             " box_mismatch\n  ensures (match result with | Ok _ -> " +
             emptied + " | Err _ -> " + unchanged + ")\n= if " + holds +
             " b then\n    (let v = " + unpack + " b in\n     b <- " + empty +
             " b;\n     Ok v)\n  else Err Mismatch\n\n";
      // Which type a box holds, read at run time: `is<t> b`.
      src += "let is (t : type where eq t " + t + ") (b : " + boxType +
             ") : bool\n  ensures result = " + holdsT + " b\n= " + holds +
             " b\n\n";
    }
  }
  return src;
}

// Rewrites `box C r` to `box_C`, and reports a concept anywhere else a
// type is expected. `inType` is whether `n` is in a type.
void rewriteTypes(Node &n, bool inType, const std::set<std::string> &unsized,
                  const std::map<std::string, const Node *> &cs,
                  std::set<std::string> &used, syntax::Diagnostics &diags) {
  if (n.kind == NodeKind::TypeApp && !n.kids.empty() &&
      n.kids[0]->kind == NodeKind::TypeName && unsized.count(n.kids[0]->text) &&
      n.kids.size() > 1 && n.kids[1]->kind == NodeKind::TypeName &&
      cs.count(n.kids[1]->text)) {
    std::string c = n.kids[1]->text;
    used.insert(c);
    n.kind = NodeKind::TypeName;
    n.text = "box_" + mangle(c);
    n.kids.clear();
    return;
  }
  if (inType && ((n.kind == NodeKind::TypeName && cs.count(n.text)) ||
                 (n.kind == NodeKind::TypeApp && !n.kids.empty() &&
                  n.kids[0]->kind == NodeKind::TypeName &&
                  cs.count(n.kids[0]->text)))) {
    std::string c = n.kind == NodeKind::TypeName ? n.text : n.kids[0]->text;
    diags.error(n.loc, "the concept '" + c + "' is not a type: a value of "
                       "some type that meets it has no size known here, so "
                       "it can only be held in a box, as in 'box " + c +
                       "' (ADR 0046)");
    return;
  }
  if (n.kind == NodeKind::Annot || n.kind == NodeKind::Domain) {
    // The modifiers, the type, and a `where`, which names concepts.
    for (size_t i = 0; i < n.kids.size(); ++i)
      rewriteTypes(*n.kids[i], i == 1, unsized, cs, used, diags);
    return;
  }
  bool typeContext = inType || n.kind == NodeKind::TypeValue ||
                     n.kind == NodeKind::SliceType ||
                     n.kind == NodeKind::ArrayType ||
                     n.kind == NodeKind::TypeApp;
  for (NodePtr &k : n.kids) rewriteTypes(*k, typeContext, unsized, cs, used, diags);
}

// Whether `mods`, a parameter's modifiers as written, has `word`.
bool hasWord(const std::string &mods, const std::string &word) {
  size_t at = 0;
  while ((at = mods.find(word, at)) != std::string::npos) {
    bool start = at == 0 || mods[at - 1] == ' ';
    bool end = at + word.size() == mods.size() || mods[at + word.size()] == ' ';
    if (start && end)
      return true;
    at += word.size();
  }
  return false;
}

// Whether `n` states the state of the box `name`: applies `full` or
// `unknown` to it (or the theory's facts they stand for).
bool statesState(const Node &n, const std::string &name) {
  // The box itself, or an element of a slice of boxes, `xs.[i]`.
  auto names = [&](const Node &a) {
    const Node *b = &a;
    if (b->kind == NodeKind::Index && !b->kids.empty())
      b = b->kids[0].get();
    return b->kind == NodeKind::Name && b->text == name;
  };
  if (n.kind == NodeKind::Apply && n.kids.size() == 2 && names(*n.kids[1])) {
    const Node &f = *n.kids[0];
    if ((f.kind == NodeKind::Name &&
         (f.text == "full" || f.text == "unknown")) ||
        (f.kind == NodeKind::Field && f.text == "full_box"))
      return true;
  }
  for (const NodePtr &k : n.kids)
    if (statesState(*k, name))
      return true;
  return false;
}

bool statedIn(const std::vector<const Node *> &contracts, NodeKind kind,
              const std::string &name) {
  for (const Node *c : contracts)
    if (c->kind == kind && statesState(*c, name))
      return true;
  return false;
}

using Params = std::vector<std::tuple<std::string, std::string, const Node *>>;

// Every contract states the state of each box over a concept in its
// signature (Dean, 2026-11-28): a box it takes, in a `requires`, and a box
// it hands out, as its result or an `inout` or `out` parameter, in an
// `ensures`. `params` are the parameters' names, modifiers and types, and
// `boxes` the box types.
void checkStated(const std::string &fn, syntax::SourceLoc at,
                 const Params &params, const Node *result,
                 const std::vector<const Node *> &contracts,
                 const std::set<std::string> &boxes,
                 syntax::Diagnostics &diags) {
  auto isBox = [&](const Node *t) {
    return t && t->kind == NodeKind::TypeName && boxes.count(t->text);
  };
  // A slice or array of boxes: each element is a box of its own, so its
  // state is stated element by element, `forall (i in 0 .. len xs). full
  // xs.[i]`.
  auto isBoxes = [&](const Node *t) {
    return t &&
           (t->kind == NodeKind::SliceType || t->kind == NodeKind::ArrayType) &&
           !t->kids.empty() && isBox(t->kids[0].get());
  };
  for (const auto &[name, mods, type] : params) {
    bool many = isBoxes(type);
    if (!isBox(type) && !many)
      continue;
    bool out = hasWord(mods, "out");
    // A caller sees what a function writes into a mutable slice.
    bool inout = hasWord(mods, "inout") || (many && hasWord(mods, "mutable"));
    if (many) {
      std::string each =
          "forall (i in 0 .. len " + name + "). full " + name + ".[i]";
      if (!out && !statedIn(contracts, NodeKind::Requires, name))
        diags.error(at, "'" + fn + "' takes the boxes in '" + name +
                            "' and states no state for them: add 'requires " +
                            each +
                            "', or 'unknown' for an element callers "
                            "may pass in any state (ADR 0046: each box in a "
                            "slice is its own, and every contract states its "
                            "state)");
      if ((out || inout) && !statedIn(contracts, NodeKind::Ensures, name))
        diags.error(at, "'" + fn + "' may write the boxes in '" + name +
                            "' and states no state it leaves them in: add "
                            "'ensures " +
                            each +
                            "' (ADR 0046: each box in a "
                            "slice is its own, and every contract states its "
                            "state)");
      continue;
    }
    if (!out && !statedIn(contracts, NodeKind::Requires, name))
      diags.error(at, "'" + fn + "' takes the box '" + name +
                          "' and states no state for it: add 'requires full " +
                          name + "', or 'requires unknown " + name +
                          "' when callers may pass any (ADR 0046: every "
                          "contract states a box's state)");
    if ((out || inout) && !statedIn(contracts, NodeKind::Ensures, name))
      diags.error(at, "'" + fn + "' hands back the box '" + name +
                          "' and states no state it leaves it in: add "
                          "'ensures full " +
                          name + "', 'ensures full " + name +
                          " = false' or 'ensures unknown " + name +
                          "' (ADR 0046: every contract states a box's state)");
  }
  if (isBox(result) && !statedIn(contracts, NodeKind::Ensures, "result"))
    diags.error(at, "'" + fn +
                        "' returns a box and states no state for it: "
                        "add 'ensures full result' or 'ensures unknown result' "
                        "(ADR 0046: every contract states a box's state)");
}

// The state check over the program's own functions and the functions its
// interfaces declare. A definition with no contract of its own inherits
// its interface's (ADR 0077), so the interface's is checked instead.
void checkStates(const Node &program, const std::set<std::string> &boxes,
                 syntax::Diagnostics &diags) {
  std::set<std::string> declared;
  for (const NodePtr &item : program.kids) {
    if (item->kind != NodeKind::Interface)
      continue;
    for (const NodePtr &k : item->kids) {
      if (k->kind != NodeKind::SigVal || k->kids.size() < 3 ||
          k->kids[0]->kids.size() < 2)
        continue;
      declared.insert(k->text);
      Params params;
      const Node *cur = k->kids[0]->kids[1].get();
      for (; cur->kind == NodeKind::ArrowType; cur = cur->kids[1].get()) {
        const Node &d = *cur->kids[0];
        if (d.kind != NodeKind::Domain || d.kids.size() < 2)
          continue;
        params.emplace_back(d.text, d.kids[0]->text, d.kids[1].get());
      }
      std::vector<const Node *> contracts;
      for (const NodePtr &c : k->kids[2]->kids)
        contracts.push_back(c.get());
      checkStated(k->text, k->loc, params, cur, contracts, boxes, diags);
    }
  }
  for (const NodePtr &item : program.kids) {
    if (item->kind != NodeKind::LetItem || item->kids.size() < 3 ||
        item->kids[0]->kind != NodeKind::Params)
      continue;
    const Node *ret = nullptr, *cs = nullptr;
    for (const NodePtr &k : item->kids) {
      if (k->kind == NodeKind::RetAnnot && !k->kids.empty() &&
          k->kids[0]->kind == NodeKind::Annot && k->kids[0]->kids.size() > 1)
        ret = k->kids[0]->kids[1].get();
      if (k->kind == NodeKind::Contracts)
        cs = k.get();
    }
    std::vector<const Node *> contracts;
    if (cs)
      for (const NodePtr &c : cs->kids)
        contracts.push_back(c.get());
    if (contracts.empty() && declared.count(item->text))
      continue;
    Params params;
    for (const NodePtr &p : item->kids[0]->kids) {
      if (p->kind != NodeKind::Param || p->kids.empty() ||
          p->kids[0]->kind != NodeKind::Annot || p->kids[0]->kids.size() < 2)
        continue;
      params.emplace_back(p->text, p->kids[0]->kids[0]->text,
                          p->kids[0]->kids[1].get());
    }
    checkStated(item->text, item->loc, params, ret, contracts, boxes, diags);
  }
}

}  // namespace

// The boxes made so far; like boxOps(), it outlives the program's clone.
static std::set<std::string> &conceptBoxes() {
  static std::set<std::string> names;
  return names;
}

bool isConceptBox(const std::string &name) {
  return conceptBoxes().count(name) != 0;
}

bool hasErasedBoxes(const Node &program) {
  return !unsizedTypes(program).empty();
}

std::string boxUncallable(const Node &item) {
  if (item.flags.find("box_uncallable") == std::string::npos) return "";
  auto it = uncallable().find(item.text);
  return it == uncallable().end() ? "" : it->second;
}

BoxOp boxOp(const Node &item) {
  if (item.flags.find("box_op") == std::string::npos)
    return {};
  auto it = boxOps().find(item.text);
  return it == boxOps().end() ? BoxOp{} : it->second;
}

void expandErasedBoxes(
    Node &program, std::string_view source, syntax::Diagnostics &diags,
    const std::map<std::string, std::vector<std::string>> *widened, int words) {
  std::set<std::string> unsized = unsizedTypes(program);
  std::map<std::string, const Node *> cs = concepts(program);
  std::set<std::string> used;
  for (NodePtr &item : program.kids) {
    if (syntax::isConceptItem(*item)) continue;
    rewriteTypes(*item, false, unsized, cs, used, diags);
  }
  if (diags.hasErrors() || used.empty()) return;
  // Once, in the first pass: the second sees the same program.
  if (!widened) {
    std::set<std::string> boxes;
    for (const std::string &c : used)
      boxes.insert("box_" + mangle(c));
    checkStates(program, boxes, diags);
    if (diags.hasErrors())
      return;
  }
  // A box is one cache line whose layout is the target's and whose
  // descriptor's is the concept's (the cache-line amendment), so another
  // module that sees the concept makes the same box: an interface may show
  // one, and a module may box values of a concept it imports. The interface
  // lists the box as a type of its own, as `box C` reads in its artifact;
  // to C (@abi(c)) it is an opaque block of that size.
  for (NodePtr &item : program.kids) {
    if (item->kind != NodeKind::Interface)
      continue;
    std::set<std::string> shown;
    for (const NodePtr &k : item->kids)
      if (k->kind == NodeKind::SigVal || k->kind == NodeKind::SigType)
        for (const std::string &u : used)
          if (mentionsName(*k, "box_" + mangle(u)))
            shown.insert("box_" + mangle(u));
    for (const std::string &b : shown) {
      syntax::Diagnostics local;
      NodePtr sig = syntax::parseProgram(
          "interface I = sig\n  let " + b + " : type\nend\n", local);
      if (!sig || sig->kids.empty()) continue;
      for (NodePtr &k : sig->kids[0]->kids)
        if (k->kind == NodeKind::SigVal || k->kind == NodeKind::SigType)
          item->kids.push_back(std::move(k));
    }
  }
  if (diags.hasErrors()) return;
  if (source.empty()) {
    diags.error(program.loc, "a box over a concept needs the program's "
                             "source, which this tool does not give yet");
    return;
  }
  Text text{source, {}};
  syntax::LexOptions lex;
  text.tokens = syntax::tokenize(source, diags, lex);
  std::string box = *unsized.begin();
  // What `take` and `consume` return when the box holds another type:
  // one error for every concept.
  bool defined = false;
  for (const NodePtr &item : program.kids)
    defined |= item->text == "box_mismatch";
  if (!defined) {
    syntax::Diagnostics local;
    NodePtr mismatch =
        syntax::parseProgram("let box_mismatch = type | Mismatch\n", local);
    if (mismatch)
      for (NodePtr &k : mismatch->kids)
        if (k->kind != NodeKind::FileAttr)
          program.kids.push_back(std::move(k));
  }
  for (const std::string &c : used) {
    std::map<std::string, std::string> whyNot;
    std::map<std::string, BoxOp> ops;
    const std::vector<std::string> *closed = nullptr;
    // The second pass knows what the module widens, which may be nothing:
    // a box it only receives, from a module that boxed values.
    static const std::vector<std::string> none;
    if (widened) {
      auto w = widened->find(c);
      closed = w != widened->end() ? &w->second : &none;
    }
    // An imported concept's nodes sit at the import, so its requirements'
    // contracts are read from its interface artifact's text instead.
    const Node *concept = cs.at(c);
    Text *from = &text;
    std::string definition = syntax::importedDefinitionText(c);
    NodePtr reread;
    Text imported{definition, {}};
    if (!definition.empty()) {
      syntax::Diagnostics quiet;
      reread = syntax::parseProgram(definition, quiet);
      if (!quiet.hasErrors() && reread && !reread->kids.empty() &&
          syntax::isConceptItem(*reread->kids[0])) {
        syntax::LexOptions lexImported;
        imported.tokens = syntax::tokenize(definition, quiet, lexImported);
        concept = reread->kids[0].get();
        from = &imported;
      }
    }
    conceptBoxes().insert("box_" + mangle(c));
    std::string src = erasedSource(c, *concept, box, *from, whyNot, closed,
                                   words, ops, diags);
    if (diags.hasErrors()) return;
    syntax::Diagnostics local;
    NodePtr extra = syntax::parseProgram(src, local);
    if (local.hasErrors() || !extra) {
      diags.error(cs.at(c)->loc, "the box over '" + c + "' could not be "
                                 "made from this concept's requirements:\n" +
                                 src);
      return;
    }
    for (NodePtr &k : extra->kids) {
      if (k->kind == NodeKind::FileAttr) continue;
      renameConcept(*k, c);
      // Its axioms hold of every type `widen` boxes, by the use check. The
      // box's theory is consistent when its shape's is, which the verifier
      // checks, so only the shape's is checked.
      if (k->kind == NodeKind::Theory)
        k->flags =
            closed && k->text == "erased_" + mangle(c) ? "box modelled" : "box";
      // A function whose body is a box's own op: a proxy to the verifier.
      if (k->kind == NodeKind::LetItem)
        if (auto o = ops.find(k->text); o != ops.end()) {
          boxOps()[k->text] = o->second;
          k->flags += k->flags.empty() ? "box_op" : " box_op";
        }
      if (k->kind == NodeKind::LetItem &&
          (k->text == "widen" || k->text == "erased_" + mangle(c) + "_check"))
        k->flags += k->flags.empty() ? "box_widen" : " box_widen";
      // The stubs for requirements a box cannot forward.
      if (k->kind == NodeKind::LetItem)
        if (auto w = whyNot.find(k->text); w != whyNot.end()) {
          uncallable()[k->text] =
              "'" + k->text + "' cannot be called through a box over '" + c +
              "': " + w->second + " (ADR 0046, section 4)";
          k->flags += k->flags.empty() ? "box_uncallable" : " box_uncallable";
        }
      program.kids.push_back(std::move(k));
    }
  }
}

}  // namespace pia::irgen
