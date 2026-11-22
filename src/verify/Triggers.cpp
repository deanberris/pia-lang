#include "verify/Triggers.h"

#include <functional>
#include <map>
#include <optional>

#include "dialect/ContractDialect.h"
#include "dialect/PiaDialect.h"
#include "mlir/Dialect/Arith/IR/Arith.h"

namespace pia::verify {

using mlir::Operation;
using mlir::Value;

std::string theoryOf(mlir::func::FuncOp f) {
  if (!f) return "";
  if (auto a = f->getAttrOfType<mlir::StringAttr>("pia.theory"))
    return a.getValue().str();
  return "";
}

namespace {

std::string argName(mlir::BlockArgument a) {
  if (auto n = mlir::dyn_cast<mlir::NameLoc>(a.getLoc()))
    return n.getName().str();
  return "arg" + std::to_string(a.getArgNumber());
}

struct Term {
  std::set<unsigned> vars;          // the parameters it mentions
  std::set<std::string> functions;  // the theory functions in it
  std::string text;                 // canonical, as written
};

// `v` as a pattern term, if it can be one: a parameter, a constant, or a
// call of a theory function on such terms.
std::optional<Term> termOf(mlir::ModuleOp module, mlir::func::FuncOp axiom,
                           Value v) {
  if (auto a = mlir::dyn_cast<mlir::BlockArgument>(v)) {
    if (a.getOwner() != &axiom.getBody().front()) return std::nullopt;
    Term t;
    t.vars.insert(a.getArgNumber());
    t.text = argName(a);
    return t;
  }
  Operation *op = v.getDefiningOp();
  if (!op) return std::nullopt;
  if (auto c = mlir::dyn_cast<ConstantOp>(op)) {
    Term t;
    t.text = llvm::toString(c.getValue(), 10, true);
    return t;
  }
  if (auto c = mlir::dyn_cast<ExactConstantOp>(op)) {
    Term t;
    t.text = c.getValue().str();
    return t;
  }
  auto call = mlir::dyn_cast<mlir::func::CallOp>(op);
  if (!call) return std::nullopt;
  auto callee = module.lookupSymbol<mlir::func::FuncOp>(call.getCallee());
  if (theoryOf(callee).empty()) return std::nullopt;
  Term t;
  t.functions.insert(call.getCallee().str());
  t.text = call.getCallee().str();
  for (Value arg : call.getOperands()) {
    std::optional<Term> a = termOf(module, axiom, arg);
    if (!a) return std::nullopt;
    t.vars.insert(a->vars.begin(), a->vars.end());
    t.functions.insert(a->functions.begin(), a->functions.end());
    bool nested = arg.getDefiningOp<mlir::func::CallOp>() != nullptr;
    t.text += " " + (nested ? "(" + a->text + ")" : a->text);
  }
  return t;
}

}  // namespace

AxiomTriggers axiomTriggers(mlir::ModuleOp module, mlir::func::FuncOp axiom) {
  AxiomTriggers out;
  mlir::Block &entry = axiom.getBody().front();
  unsigned n = entry.getNumArguments();
  if (n == 0) return out;
  auto covers = [&](const std::set<unsigned> &vars) { return vars.size() == n; };

  // Written triggers: each @trigger is one pattern of one or more terms.
  bool written = false;
  for (auto t : entry.getOps<contract::TriggerOp>()) {
    written = true;
    Trigger trig;
    std::set<unsigned> vars;
    for (Value v : t.getTerms()) {
      std::optional<Term> term = termOf(module, axiom, v);
      if (!term || !v.getDefiningOp<mlir::func::CallOp>()) {
        out.triggers.clear();
        out.error = "a trigger is a call of a theory function on the "
                    "axiom's parameters, such as '@trigger(seq f g)'";
        return out;
      }
      vars.insert(term->vars.begin(), term->vars.end());
      trig.functions.insert(term->functions.begin(), term->functions.end());
      trig.terms.push_back(v);
      trig.text += (trig.text.empty() ? "" : ", ") + term->text;
    }
    if (!covers(vars)) {
      out.triggers.clear();
      out.error = "the trigger '" + trig.text + "' does not mention every "
                  "parameter of the axiom";
      return out;
    }
    out.triggers.push_back(std::move(trig));
  }
  if (written) return out;

  // Inferred, as Z3 would: every call that covers all the parameters,
  // would not instantiate the axiom without end, and contains no smaller
  // such call, once per distinct term. Calls inside a nested quantifier
  // may mention its bound variables, so they are not looked at.
  std::map<std::string, std::pair<Value, Term>> covering;
  std::vector<Value> calls;
  axiom.walk([&](mlir::func::CallOp call) {
    if (call->getParentOfType<contract::ForallOp>() ||
        call->getParentOfType<contract::ExistsOp>())
      return;
    if (call.getNumResults() != 1) return;
    calls.push_back(call.getResult(0));
    std::optional<Term> t = termOf(module, axiom, call.getResult(0));
    if (!t || !covers(t->vars)) return;
    covering.emplace(t->text, std::make_pair(call.getResult(0), *t));
  });
  // `pattern` matches `term`, binding the parameters it mentions.
  std::function<bool(Value, Value, std::map<unsigned, std::string> &)> match =
      [&](Value pattern, Value term,
          std::map<unsigned, std::string> &bound) -> bool {
    std::optional<Term> tt = termOf(module, axiom, term);
    if (!tt) return false;
    if (auto a = mlir::dyn_cast<mlir::BlockArgument>(pattern)) {
      auto [it, fresh] = bound.emplace(a.getArgNumber(), tt->text);
      return fresh || it->second == tt->text;
    }
    auto pc = pattern.getDefiningOp<mlir::func::CallOp>();
    auto tc = term.getDefiningOp<mlir::func::CallOp>();
    if (!pc || !tc) {
      std::optional<Term> pt = termOf(module, axiom, pattern);
      return pt && pt->text == tt->text;
    }
    if (pc.getCallee() != tc.getCallee() ||
        pc.getNumOperands() != tc.getNumOperands())
      return false;
    for (auto [p, t] : llvm::zip(pc.getOperands(), tc.getOperands()))
      if (!match(p, t, bound)) return false;
    return true;
  };
  // A matching loop: the axiom holds a larger instance of the pattern,
  // such as `in_w (residual f)` for `in_w f`, so each instance would make
  // the next.
  auto loops = [&](Value pattern) {
    for (Value t : calls) {
      std::map<unsigned, std::string> bound;
      if (!match(pattern, t, bound)) continue;
      for (auto &[arg, text] : bound)
        if (text != argName(entry.getArgument(arg))) {
          bool renamed = false;
          for (mlir::BlockArgument a : entry.getArguments())
            renamed |= text == argName(a);
          if (!renamed) return true;
        }
    }
    return false;
  };
  bool looping = false;
  for (auto &[text, entry2] : covering) {
    auto &[value, term] = entry2;
    if (loops(value)) {
      looping = true;
      continue;
    }
    bool minimal = true;
    std::function<void(Value, bool)> look = [&](Value v, bool top) {
      auto call = v.getDefiningOp<mlir::func::CallOp>();
      if (!call) return;
      if (!top)
        if (std::optional<Term> s = termOf(module, axiom, v);
            s && covers(s->vars) && !loops(v))
          minimal = false;
      for (Value a : call.getOperands()) look(a, false);
    };
    look(value, true);
    if (!minimal) continue;
    Trigger trig;
    trig.terms.push_back(value);
    trig.text = term.text;
    trig.functions = term.functions;
    out.triggers.push_back(std::move(trig));
  }
  if (out.triggers.empty())
    out.error = looping
                    ? "every term that mentions all its parameters would "
                      "instantiate it without end, since the axiom holds a "
                      "larger instance of it; give a trigger with "
                      "@trigger(...)"
                    : "no term of the axiom mentions all its parameters, so "
                      "the solver could never instantiate it; mention them "
                      "together in one call of a theory function, or give "
                      "a trigger with @trigger(...)";
  return out;
}

}  // namespace pia::verify
