#include "irgen/Boxes.h"

#include <algorithm>
#include <functional>
#include <map>
#include <set>
#include <vector>

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
  std::string src = "@trusted\n";
  src += "let theory " + theory + " = sig\n";
  for (const Requirement &q : reqs) {
    if (!q.why.empty()) continue;
    std::string sig;
    for (const Param &p : q.params)
      sig += "(" + (p.receiver ? self : p.name) + " : " +
             (p.receiver ? boxType : p.type) + ") -> ";
    src += "  let spec " + q.name + "_of : " + sig + q.result + "\n";
  }
  for (const Requirement &q : reqs) {
    bool ensures = false;
    for (const Node *c : q.contracts) ensures |= c->kind == NodeKind::Ensures;
    if (!q.why.empty() || !ensures) continue;
    std::map<std::string, std::string> rename = inTheory;
    std::string recv;
    for (const Param &p : q.params)
      if (p.receiver) recv = p.name;
    rename[recv] = self;
    rename["result"] = "(" + q.name + "_of" + args(q, self) + ")";
    src += "  let axiom " + q.name + "_contract" + params(q, boxType) +
           rewritten(q.contracts, rename) + "\n";
  }
  for (const Law &l : laws) {
    std::map<std::string, std::string> rename = inTheory;
    src += "  let axiom " + l.name + "_law (" + l.param + " : " + boxType +
           ")" + rewritten(l.contracts, rename) + "\n";
  }
  src += "end\n\n";
  // The box: before the module's widened types are known, a stand-in; then
  // one cache line of words (the cache-line amendment): the descriptor's
  // address, then the object.
  if (!closed || closed->empty()) {
    src += "let " + boxType + " = type { tag : u8 }\n\n";
  } else {
    src += "let " + boxType + " = type {";
    for (int w = 0; w < words; ++w)
      src += std::string(w ? ";" : "") + " w" + std::to_string(w) + " : u64";
    src += " }\n\n";
  }
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
           requires(onSelf) + "\n  ensures result = " + theory + "." + q.name +
           "_of" + args(q, self) + "\n= abort ()\n\n";
    if (closed && !closed->empty()) {
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
    src += "let " + q.name + ps + " : " + q.result + requires(onBox) +
           "\n  ensures result = " + theory + "." + q.name + "_of" +
           args(q, recv) + "\n= " + theory + "_call_" + q.name + args(q, recv) +
           "\n\n";
  }
  // The use check, the constraint `C t`, at each instance of widen.
  std::string full = "\n  requires len b.slot = 1 && b.state = 1";
  if (!closed || closed->empty()) {
    src += "let widen (t : type where " + cname + " t) (b : " + box + " t) : " +
           boxType + full + "\n= { tag = 0 }\n";
  } else {
    src += "let " + theory + "_check (t : type where " + cname + " t) (b : " +
           box + " t) : unit = ()\n\n";
    for (const std::string &t : *closed) {
      // The object, packed into the box with its descriptor.
      const std::string pack = theory + "_pack_" + t;
      BoxOp op;
      op.kind = BoxOp::Pack;
      op.descriptor = "pia$t$" + t + "$" + m;
      for (const Requirement *q : callable)
        op.thunks.push_back(theory + "_thunk_" + q->name + "_" + t);
      ops[pack] = op;
      src +=
          "let " + pack + " (v : " + t + ") : " + boxType + "\n= abort ()\n\n";
      src += "let widen (b : " + box + " " + t + ") : " + boxType + full +
             "\n= " + theory + "_check b;\n  " + pack + " b.slot.[0]\n\n";
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

}  // namespace

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
  // A box's layout is this module's union of the types it widens (step
  // 5), so another Pia module cannot share it until the table layout of
  // step 6: an interface may not show it, except to C (@abi(c)), whose
  // callers take the documented layout.
  for (NodePtr &item : program.kids) {
    if (item->kind != NodeKind::Interface) continue;
    bool c = false;
    for (const NodePtr &k : item->kids)
      if (k->kind == NodeKind::Attrs)
        for (const NodePtr &a : k->kids) c |= a->text == "abi";
    std::set<std::string> shown;
    for (const NodePtr &k : item->kids)
      if (k->kind == NodeKind::SigVal || k->kind == NodeKind::SigType)
        for (const std::string &u : used)
          if (mentionsName(*k, "box_" + mangle(u))) {
            if (!c) {
              diags.error(k->loc, "'" + k->text + "' shows a box over '" + u +
                                  "' to other modules, whose layout is this "
                                  "module's for now: a box crosses modules "
                                  "with the table layout of ADR 0046, step 6");
              continue;
            }
            shown.insert("box_" + mangle(u));
          }
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
  // Nor may this module box an imported concept's values for another.
  for (const NodePtr &item : program.kids)
    if (item->kind == NodeKind::Import)
      for (const std::string &u : used)
        if (cs.count(u) && item->text.find(u) != std::string::npos)
          diags.error(item->loc, "a box over '" + u + "' from another module "
                                 "needs the table layout of ADR 0046, step 6");
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
  for (const std::string &c : used) {
    std::map<std::string, std::string> whyNot;
    std::map<std::string, BoxOp> ops;
    const std::vector<std::string> *closed = nullptr;
    if (widened)
      if (auto w = widened->find(c); w != widened->end()) closed = &w->second;
    std::string src = erasedSource(c, *cs.at(c), box, text, whyNot, closed,
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
      // Its axioms hold of every type `widen` boxes, by the use check.
      if (k->kind == NodeKind::Theory) k->flags = "box";
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
