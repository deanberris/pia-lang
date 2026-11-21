#include "irgen/IRGen.h"

#include <map>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "dialect/ContractDialect.h"
#include "dialect/PiaDialect.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/raw_ostream.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Verifier.h"
#include "sema/Sema.h"

namespace pia::irgen {

using mlir::Block;
using mlir::Location;
using mlir::OpBuilder;
using mlir::Type;
using mlir::Value;
using syntax::Node;
using syntax::NodeKind;

void loadDialects(mlir::MLIRContext &ctx) {
  ctx.loadDialect<PiaDialect, contract::ContractDialect, mlir::arith::ArithDialect,
                  mlir::func::FuncDialect, mlir::scf::SCFDialect>();
}

namespace {

constexpr unsigned kWidth = 128;

llvm::APInt widen(const llvm::APInt &v) { return v.sextOrTrunc(kWidth); }

// A lowered expression: its value and its type. Unit-typed expressions have
// no value and the type `none`.
struct TV {
  Value value;
  Type type;
};
using R = std::optional<TV>;

// A local name. Mutable locals are SSA values too: an assignment rebinds
// `value`, and structured control flow threads the binding through
// `scf.if` results and loop-carried values (docs/irgen.md).
struct Binding {
  std::string name;
  Value value;
  Type type;
  bool isMutable = false;
  std::string modifiers;  // a parameter's modifiers, empty for locals
  bool isParam = false;
};
using BindingPtr = std::shared_ptr<Binding>;

std::string plural(size_t n, const std::string &word) {
  return std::to_string(n) + " " + word + (n == 1 ? "" : "s");
}

bool isLiteral(const Node &n) {
  return n.kind == NodeKind::IntLit ||
         (n.kind == NodeKind::Neg && n.kids.size() == 1 &&
          n.kids[0]->kind == NodeKind::IntLit);
}

bool isComparison(const std::string &op) {
  return op == "=" || op == "<>" || op == "<" || op == "<=" || op == ">" ||
         op == ">=";
}

// The operator a core builtin stands for (src/syntax/Prelude.cpp), or null.
const char *builtinOperator(const std::string &name) {
  static const std::map<std::string, const char *> ops = {
      {"add", "+"},     {"sub", "-"},     {"add_sat", "+|"}, {"sub_sat", "-|"},
      {"mul", "*"},     {"div", "/"},     {"rem", "%"},      {"eq", "="},
      {"ne", "<>"},     {"lt", "<"},      {"gt", ">"},       {"le", "<="},
      {"ge", ">="},     {"and", "&&"},    {"or", "||"},      {"implies", "==>"},
      {"iff", "<==>"},
  };
  auto it = ops.find(name);
  return it == ops.end() ? nullptr : it->second;
}

bool isLogic(const std::string &op) {
  return op == "&&" || op == "||" || op == "==>" || op == "<==>";
}

bool isArith(const std::string &op) {
  return op == "+" || op == "-" || op == "*" || op == "/" || op == "%" ||
         op == "mod" || op == "+|" || op == "-|";
}

// Every name assigned with `x <- ...` inside `n`.
void collectAssigned(const Node &n, std::set<std::string> &out) {
  if (n.kind == NodeKind::Assign && !n.kids.empty()) {
    const Node &place = *n.kids[0];
    if (place.kind == NodeKind::Name) out.insert(place.text);
    // `p.r <- v` rebinds the record `p`.
    if (place.kind == NodeKind::Field && !place.kids.empty() &&
        place.kids[0]->kind == NodeKind::Name)
      out.insert(place.kids[0]->text);
  }
  for (const syntax::NodePtr &k : n.kids) collectAssigned(*k, out);
}

class Gen {
 public:
  Gen(mlir::MLIRContext &ctx, std::string_view filename,
      syntax::Diagnostics &diags)
      : ctx_(ctx),
        b_(&ctx),
        file_(mlir::StringAttr::get(&ctx, filename)),
        diags_(diags),
        types_(ctx, diags) {}

  mlir::OwningOpRef<mlir::ModuleOp> run(const Node &program) {
    mlir::OwningOpRef<mlir::ModuleOp> module =
        mlir::ModuleOp::create(mlir::FileLineColLoc::get(file_, 1, 1));
    module_ = *module;
    sigs_ = sema::collectSignatures(program, types_, diags_);
    if (diags_.hasErrors()) return nullptr;
    for (const syntax::NodePtr &item : program.kids) genFunction(item->text);
    if (diags_.hasErrors()) return nullptr;
    if (mlir::failed(mlir::verify(*module))) return nullptr;
    return module;
  }

 private:
  // --- helpers --------------------------------------------------------

  // `OpTy::create(builder, ...)` replaced `builder.create<OpTy>(...)` in
  // LLVM 21; the second still works but is deprecated.
  template <typename OpTy, typename... Args>
  OpTy create(Location l, Args &&...args) {
#if LLVM_VERSION_MAJOR >= 21
    return OpTy::create(b_, l, std::forward<Args>(args)...);
#else
    return b_.create<OpTy>(l, std::forward<Args>(args)...);
#endif
  }

  Location loc(const Node &n) {
    return mlir::FileLineColLoc::get(file_, n.loc.line, n.loc.column);
  }

  R fail(const Node &n, std::string message) {
    diags_.error(n.loc, std::move(message));
    return std::nullopt;
  }

  Type boolType() { return types_.boolType(); }
  Type unitType() { return types_.unitType(); }
  bool isUnit(Type t) { return types_.isUnit(t); }
  bool isBool(Type t) { return t && t.isInteger(1); }
  TV unit() { return {Value(), unitType()}; }

  std::string typeName(Type t) { return sema::typeName(t); }

  // The smallest range type holding both.
  IntType join(IntType a, IntType b) {
    llvm::APInt alo = widen(a.getLo()), blo = widen(b.getLo());
    llvm::APInt ahi = widen(a.getHi()), bhi = widen(b.getHi());
    return IntType::get(&ctx_, alo.slt(blo) ? alo : blo,
                        ahi.sgt(bhi) ? ahi : bhi);
  }

  // Converts `v` to `target`: integers convert between range types
  // (narrowing becomes a proof obligation); other types must match.
  R coerce(const TV &v, Type target, const Node &at) {
    if (v.type == target) return v;
    if (mlir::isa<IntType>(v.type) && mlir::isa<IntType>(target)) {
      Value c = create<ConvertOp>(
          loc(at), target, v.value,
          OverflowModeAttr::get(&ctx_, OverflowMode::proof));
      return TV{c, target};
    }
    return fail(at, "expected " + typeName(target) + ", found " +
                        typeName(v.type));
  }

  Value boolConst(Location l, bool v) {
    return create<mlir::arith::ConstantOp>(l, b_.getBoolAttr(v));
  }

  Value implies(Location l, Value a, Value c) {
    Value notA = create<mlir::arith::XOrIOp>(l, a, boolConst(l, true));
    return create<mlir::arith::OrIOp>(l, notA, c);
  }

  Value cmp(Location l, CmpPredicate p, Value a, Value c) {
    return create<CmpOp>(l, b_.getI1Type(),
                            CmpPredicateAttr::get(&ctx_, p), a, c);
  }

  Value toIndex(Location l, Value v) {
    return create<ToIndexOp>(l, b_.getIndexType(), v);
  }

  // --- scopes ---------------------------------------------------------

  void pushScope() { scopes_.emplace_back(); }
  void popScope() { scopes_.pop_back(); }

  BindingPtr bind(const std::string &name, Value v, Type t, bool isMutable) {
    auto b = std::make_shared<Binding>();
    b->name = name;
    b->value = v;
    b->type = t;
    b->isMutable = isMutable;
    scopes_.back()[name] = b;
    return b;
  }

  // Pia has no shadowing (ADR 0022): a binding written in the source may not
  // reuse the name of a local in scope, a function, a type or a core
  // builtin. Names a quote binds carry a `#` and are always fresh.
  bool checkFresh(const std::string &name, syntax::SourceLoc at) {
    if (name.find('#') != std::string::npos) return true;
    std::string what;
    if (lookup(name)) what = "a local of the same name";
    else if (sigs_.count(name)) what = "the function '" + name + "'";
    else if (types_.named(name) || types_.builtin(name))
      what = "the type '" + name + "'";
    else if (sema::isCoreBuiltin(name)) what = "a core builtin";
    else return true;
    diags_.error(at, "'" + name + "' shadows " + what +
                         "; Pia does not allow shadowing (ADR 0022)");
    return false;
  }

  BindingPtr lookup(const std::string &name) {
    for (auto it = scopes_.rbegin(); it != scopes_.rend(); ++it) {
      auto found = it->find(name);
      if (found != it->end()) return found->second;
    }
    return nullptr;
  }

  // The mutable locals that the given subtrees assign, in name order. These
  // become `scf.if` results and loop-carried values.
  std::vector<BindingPtr> carried(std::initializer_list<const Node *> nodes) {
    std::set<std::string> names;
    for (const Node *n : nodes)
      if (n) collectAssigned(*n, names);
    std::vector<BindingPtr> out;
    for (const std::string &name : names) {
      BindingPtr b = lookup(name);
      if (b && b->isMutable && !mlir::isa<ArrayType, SliceType>(b->type))
        out.push_back(b);
    }
    return out;
  }

  static llvm::SmallVector<Value> values(const std::vector<BindingPtr> &bs) {
    llvm::SmallVector<Value> out;
    for (const BindingPtr &b : bs) out.push_back(b->value);
    return out;
  }

  static void setValues(const std::vector<BindingPtr> &bs,
                        mlir::ValueRange vs) {
    for (size_t i = 0; i < bs.size(); ++i) bs[i]->value = vs[i];
  }

  // --- functions ------------------------------------------------------

  void genFunction(const std::string &name) {
    auto it = sigs_.find(name);
    if (it == sigs_.end()) return;
    sema::FuncSig &sig = it->second;
    const Node &item = *sig.item;
    Location l = loc(item);

    llvm::SmallVector<Type> argTypes;
    for (const sema::Param &p : sig.params) argTypes.push_back(p.type);
    auto resultTypes = [&](Type t) {
      return t && !isUnit(t) ? llvm::SmallVector<Type>{t}
                             : llvm::SmallVector<Type>{};
    };

    b_.setInsertionPointToEnd(module_.getBody());
    auto fn = create<mlir::func::FuncOp>(
        l, sig.name, b_.getFunctionType(argTypes, resultTypes(sig.result)));
    for (size_t i = 0; i < sig.params.size(); ++i)
      if (!sig.params[i].modifiers.empty())
        fn.setArgAttr(i, PiaDialect::getModifiersAttrName(),
                      b_.getStringAttr(sig.params[i].modifiers));
    Block *entry = fn.addEntryBlock();
    b_.setInsertionPointToStart(entry);

    scopes_.clear();
    pushScope();
    for (size_t i = 0; i < sig.params.size(); ++i) {
      const sema::Param &p = sig.params[i];
      // The verifier names counterexample values after the parameters.
      entry->getArgument(i).setLoc(mlir::NameLoc::get(
          b_.getStringAttr(p.name),
          mlir::FileLineColLoc::get(file_, p.loc.line, p.loc.column)));
      checkFresh(p.name, p.loc);
      BindingPtr b = bind(p.name, entry->getArgument(i), p.type,
                          sema::hasModifier(p.modifiers, "mutable"));
      b->modifiers = p.modifiers;
      b->isParam = true;
    }

    overflow_ = OverflowMode::proof;
    const Node &ret = *item.kids[1];
    if (ret.kind == NodeKind::RetAnnot && ret.kids.size() > 1 &&
        !genAttributes(*ret.kids[1]))
      return;

    const Node &contracts = *item.kids[2];
    for (const syntax::NodePtr &c : contracts.kids) {
      if (c->kind == NodeKind::Requires) {
        R p = genPredicate(*c->kids[0]);
        if (!p) return;
        create<contract::RequiresOp>(loc(*c), p->value);
      } else if (c->kind == NodeKind::Decreases) {
        R m = genContractExpr(*c->kids[0], Type());
        if (!m) return;
        create<contract::DecreasesOp>(loc(*c), m->value);
      }
    }

    const Node &bodyNode = *item.kids[3];
    R body = genExpr(bodyNode, sig.result);
    if (!body) return;
    Type result = sig.result;
    if (!result) {
      result = body->type;
      sig.result = result;
      fn.setType(b_.getFunctionType(argTypes, resultTypes(result)));
    }
    llvm::SmallVector<Value> rets;
    if (!isUnit(result)) {
      if (isUnit(body->type)) {
        fail(bodyNode, "'" + name + "' returns " + typeName(result) +
                           ", but its body has type unit");
        return;
      }
      R v = coerce(*body, result, bodyNode);
      if (!v) return;
      rets.push_back(v->value);
    } else if (!isUnit(body->type)) {
      fail(bodyNode, "'" + name + "' returns unit, but its body has type " +
                         typeName(body->type));
      return;
    }

    pushScope();
    if (!rets.empty()) bind("result", rets[0], result, false);
    for (const syntax::NodePtr &c : contracts.kids) {
      if (c->kind != NodeKind::Ensures) continue;
      R p = genPredicate(*c->kids[0]);
      if (!p) return;
      create<contract::EnsuresOp>(loc(*c), p->value);
    }
    popScope();
    create<mlir::func::ReturnOp>(l, rets);
  }

  // `@overflow(wrap)` on the return annotation sets the function's mode.
  bool genAttributes(const Node &attrs) {
    for (const syntax::NodePtr &a : attrs.kids) {
      if (a->text == "overflow" && a->kids.size() == 1 &&
          a->kids[0]->kind == NodeKind::Name) {
        const std::string &m = a->kids[0]->text;
        if (m == "proof") overflow_ = OverflowMode::proof;
        else if (m == "wrap") overflow_ = OverflowMode::wrap;
        else if (m == "saturate") overflow_ = OverflowMode::saturate;
        else if (m == "trap") overflow_ = OverflowMode::trap;
        else {
          fail(*a, "@overflow takes proof, wrap, saturate or trap");
          return false;
        }
        continue;
      }
      fail(*a, "the attribute @" + a->text + " is not supported yet");
      return false;
    }
    return true;
  }

  // --- expressions ----------------------------------------------------

  R genPredicate(const Node &n) {
    R p = genContractExpr(n, boolType());
    if (!p) return p;
    if (!isBool(p->type))
      return fail(n, "a contract must be a bool, found " + typeName(p->type));
    return p;
  }

  R genContractExpr(const Node &n, Type expected) {
    bool saved = contract_;
    contract_ = true;
    R r = genExpr(n, expected);
    contract_ = saved;
    return r;
  }

  R genExpr(const Node &n, Type expected) {
    switch (n.kind) {
      case NodeKind::IntLit: {
        auto lit = sema::parseIntLiteral(n.text);
        if (!lit) return fail(n, "invalid integer literal '" + n.text + "'");
        return genIntConst(n, lit->value, lit->suffix, expected);
      }
      case NodeKind::BoolLit:
        return TV{boolConst(loc(n), n.text == "true"), boolType()};
      case NodeKind::Unit:
        return unit();
      case NodeKind::Name:
        return genName(n);
      case NodeKind::Binary:
        return genBinary(n, n.text, *n.kids[0], *n.kids[1], expected);
      case NodeKind::Neg:
        return genNeg(n, expected);
      case NodeKind::Apply:
        return genApply(n, expected);
      case NodeKind::Index:
        return genIndex(n);
      case NodeKind::RecordLit:
        return genRecordLit(n, expected);
      case NodeKind::Field:
        return genField(n);
      case NodeKind::Assign:
        return genAssign(n);
      case NodeKind::If:
        return genIf(n, expected);
      case NodeKind::For:
        return genFor(n);
      case NodeKind::While:
        return genWhile(n);
      case NodeKind::Sequence: {
        R first = genExpr(*n.kids[0], Type());
        if (!first) return first;
        return genExpr(*n.kids[1], expected);
      }
      case NodeKind::LetIn:
        return genLetIn(n, expected);
      case NodeKind::Assert:
      case NodeKind::Assume: {
        R p = genPredicate(*n.kids[0]);
        if (!p) return p;
        if (n.kind == NodeKind::Assert)
          create<contract::AssertOp>(loc(n), p->value);
        else
          create<contract::AssumeOp>(loc(n), p->value);
        return unit();
      }
      case NodeKind::Quantifier:
        if (!contract_)
          return fail(n, "quantifiers are only allowed in contracts and "
                         "assertions");
        return genQuantifier(n, 0);
      case NodeKind::Range:
        return fail(n, "a range is only allowed in a for loop or a "
                       "quantifier for now");
      default:
        return fail(n, std::string("'") + syntax::nodeKindName(n.kind) +
                           "' is not supported yet (IRGen covers the scalar "
                           "subset)");
    }
  }

  R genIntConst(const Node &n, llvm::APInt v, const std::string &suffix,
                Type expected) {
    Type t;
    if (!suffix.empty()) {
      t = types_.builtin(suffix);
    } else if (mlir::isa_and_nonnull<IntType>(expected)) {
      t = expected;
    } else {
      // No context: i32 as in the design's `sum [1; 2; 3]`, else the
      // first of i64 and u64 that holds the value.
      for (const char *name : {"i32", "i64", "u64"}) {
        t = types_.builtin(name);
        if (mlir::cast<IntType>(t).contains(v)) break;
      }
    }
    auto it = mlir::cast<IntType>(t);
    if (!it.contains(v))
      return fail(n, llvm::toString(v, 10, true) + " does not fit in " +
                         typeName(t));
    Value c = create<ConstantOp>(
        loc(n), t, b_.getIntegerAttr(b_.getIntegerType(kWidth), v));
    return TV{c, t};
  }

  R genName(const Node &n) {
    if (n.flags.empty())
      if (BindingPtr b = lookup(n.text)) return TV{b->value, b->type};
    auto it = sigs_.find(n.text);
    if (it != sigs_.end()) {
      if (!it->second.params.empty())
        return fail(n, "functions as values are not supported yet; apply '" +
                           n.text + "' to all its arguments");
      return genCall(n, it->second, {});
    }
    return fail(n, "unknown name '" + n.text + "'");
  }

  // Lowers both operands. A literal takes its type from the other side, so
  // `0 < x` and `x < 0` both compare at x's type.
  std::optional<std::pair<TV, TV>> genOperands(const Node &lhs, const Node &rhs,
                                               Type expected) {
    if (isLiteral(lhs) && !isLiteral(rhs)) {
      R r = genExpr(rhs, expected);
      if (!r) return std::nullopt;
      R l = genExpr(lhs, r->type);
      if (!l) return std::nullopt;
      return std::make_pair(*l, *r);
    }
    R l = genExpr(lhs, expected);
    if (!l) return std::nullopt;
    R r = genExpr(rhs, l->type);
    if (!r) return std::nullopt;
    return std::make_pair(*l, *r);
  }

  // Brings two integers to their joined type.
  std::optional<std::pair<TV, TV>> unify(TV a, TV c, const Node &n,
                                         const std::string &op,
                                         const Node &lhs, const Node &rhs) {
    auto at = mlir::dyn_cast<IntType>(a.type);
    auto ct = mlir::dyn_cast<IntType>(c.type);
    if (!at || !ct) {
      fail(n, "'" + op + "' needs integer operands, found " +
                  typeName(a.type) + " and " + typeName(c.type));
      return std::nullopt;
    }
    IntType j = join(at, ct);
    R a2 = coerce(a, j, lhs);
    R c2 = coerce(c, j, rhs);
    if (!a2 || !c2) return std::nullopt;
    return std::make_pair(*a2, *c2);
  }

  // A binary operation. After metaprogram expansion it arrives as a call of
  // a core builtin, such as `add a b` for `a + b` (docs/meta.md); `n` is the
  // node it is reported at.
  R genBinary(const Node &n, const std::string &op, const Node &lhsNode,
              const Node &rhsNode, Type expected) {
    if (isLogic(op)) return genLogic(n, op, lhsNode, rhsNode);
    if (isComparison(op)) {
      auto ops = genOperands(lhsNode, rhsNode, Type());
      if (!ops) return std::nullopt;
      auto [a, c] = *ops;
      Location l = loc(n);
      if (isBool(a.type) && isBool(c.type) && (op == "=" || op == "<>")) {
        Value v = create<mlir::arith::CmpIOp>(
            l,
            op == "=" ? mlir::arith::CmpIPredicate::eq
                      : mlir::arith::CmpIPredicate::ne,
            a.value, c.value);
        return TV{v, boolType()};
      }
      if (mlir::isa<RecordType>(a.type) || mlir::isa<RecordType>(c.type))
        return genRecordEq(n, op, a, lhsNode, c, rhsNode);
      auto u = unify(a, c, n, op, lhsNode, rhsNode);
      if (!u) return std::nullopt;
      CmpPredicate p = op == "="    ? CmpPredicate::eq
                       : op == "<>" ? CmpPredicate::ne
                       : op == "<"  ? CmpPredicate::lt
                       : op == "<=" ? CmpPredicate::le
                       : op == ">"  ? CmpPredicate::gt
                                    : CmpPredicate::ge;
      return TV{cmp(l, p, u->first.value, u->second.value), boolType()};
    }
    if (isArith(op)) {
      auto ops = genOperands(lhsNode, rhsNode,
                             mlir::isa_and_nonnull<IntType>(expected)
                                 ? expected
                                 : Type());
      if (!ops) return std::nullopt;
      // Arithmetic happens at the join of the operand types and, when the
      // context expects a wider integer, at that type: `dst.[i] <- src.[i] * 3`
      // with u8 `src` and u16 `dst` multiplies at u16.
      TV lhs = ops->first, rhs = ops->second;
      if (auto want = mlir::dyn_cast_or_null<IntType>(expected)) {
        auto lt = mlir::dyn_cast<IntType>(lhs.type);
        auto rt = mlir::dyn_cast<IntType>(rhs.type);
        if (lt && rt) {
          IntType j = join(join(lt, rt), want);
          R l2 = coerce(lhs, j, lhsNode);
          R r2 = coerce(rhs, j, rhsNode);
          if (!l2 || !r2) return std::nullopt;
          lhs = *l2;
          rhs = *r2;
        }
      }
      auto u = unify(lhs, rhs, n, op, lhsNode, rhsNode);
      if (!u) return std::nullopt;
      Value a = u->first.value, c = u->second.value;
      Type t = u->first.type;
      Location l = loc(n);
      OverflowMode m =
          op == "+|" || op == "-|" ? OverflowMode::saturate : overflow_;
      auto mode = OverflowModeAttr::get(&ctx_, m);
      Value v;
      if (op == "+" || op == "+|") v = create<AddOp>(l, t, a, c, mode);
      else if (op == "-" || op == "-|") v = create<SubOp>(l, t, a, c, mode);
      else if (op == "*") v = create<MulOp>(l, t, a, c, mode);
      else if (op == "/") v = create<DivOp>(l, t, a, c, mode);
      else v = create<RemOp>(l, t, a, c, mode);
      return TV{v, t};
    }
    return fail(n, "the operator '" + op + "' is not supported yet");
  }

  // `&&`, `||` and `==>` short-circuit in code, so they lower to `scf.if`.
  // In contracts, which have no effects, they are plain `arith` logic.
  R genLogic(const Node &n, const std::string &op, const Node &lhsNode,
             const Node &rhsNode) {
    Location l = loc(n);
    R a = genExpr(lhsNode, boolType());
    if (!a) return a;
    if (!isBool(a->type))
      return fail(lhsNode, "'" + op + "' needs bool operands, found " +
                               typeName(a->type));
    auto genRhs = [&]() -> R {
      R c = genExpr(rhsNode, boolType());
      if (!c) return c;
      if (!isBool(c->type))
        return fail(rhsNode, "'" + op + "' needs bool operands, found " +
                                    typeName(c->type));
      return c;
    };
    if (contract_ || op == "<==>") {
      R c = genRhs();
      if (!c) return c;
      Value v;
      if (op == "&&") v = create<mlir::arith::AndIOp>(l, a->value, c->value);
      else if (op == "||") v = create<mlir::arith::OrIOp>(l, a->value, c->value);
      else if (op == "==>") v = implies(l, a->value, c->value);
      else
        v = create<mlir::arith::CmpIOp>(l, mlir::arith::CmpIPredicate::eq,
                                           a->value, c->value);
      return TV{v, boolType()};
    }
    std::set<std::string> assigned;
    collectAssigned(rhsNode, assigned);
    if (!assigned.empty())
      return fail(rhsNode, "an assignment on the right of '" + op +
                                  "' is not supported");
    // && : if a then rhs else false;  || : if a then true else rhs;
    // ==> : if a then rhs else true.
    bool rhsInThen = op != "||";
    auto rhsBlock = std::make_unique<Block>();
    auto constBlock = std::make_unique<Block>();
    {
      OpBuilder::InsertionGuard guard(b_);
      b_.setInsertionPointToEnd(rhsBlock.get());
      R c = genRhs();
      if (!c) return c;
      create<mlir::scf::YieldOp>(l, mlir::ValueRange{c->value});
      b_.setInsertionPointToEnd(constBlock.get());
      Value k = boolConst(l, op != "&&");
      create<mlir::scf::YieldOp>(l, mlir::ValueRange{k});
    }
    auto ifOp = makeIf(l, {boolType()}, a->value,
                       rhsInThen ? std::move(rhsBlock) : std::move(constBlock),
                       rhsInThen ? std::move(constBlock) : std::move(rhsBlock));
    return TV{ifOp.getResult(0), boolType()};
  }

  // Creates `scf.if` and moves the prepared blocks into its regions.
  mlir::scf::IfOp makeIf(Location l, mlir::TypeRange types, Value cond,
                         std::unique_ptr<Block> thenBlock,
                         std::unique_ptr<Block> elseBlock) {
    auto op = create<mlir::scf::IfOp>(l, types, cond,
                                         /*withElseRegion=*/true);
    op.getThenRegion().getBlocks().clear();
    op.getThenRegion().push_back(thenBlock.release());
    op.getElseRegion().getBlocks().clear();
    op.getElseRegion().push_back(elseBlock.release());
    return op;
  }

  R genNeg(const Node &n, Type expected) {
    const Node &operand = *n.kids[0];
    if (operand.kind == NodeKind::IntLit) {
      auto lit = sema::parseIntLiteral(operand.text);
      if (!lit) return fail(operand, "invalid integer literal");
      return genIntConst(n, -lit->value, lit->suffix, expected);
    }
    R v = genExpr(operand, expected);
    if (!v) return v;
    auto t = mlir::dyn_cast<IntType>(v->type);
    if (!t) return fail(n, "'-' needs an integer, found " + typeName(v->type));
    Value zero = create<ConstantOp>(
        loc(n), t, b_.getIntegerAttr(b_.getIntegerType(kWidth), 0));
    if (!t.contains(llvm::APInt(kWidth, 0)))
      return fail(n, "cannot negate a value of " + typeName(t) +
                         ", whose range does not include 0");
    Value r = create<SubOp>(loc(n), t, zero, v->value,
                               OverflowModeAttr::get(&ctx_, overflow_));
    return TV{r, t};
  }

  R genApply(const Node &n, Type expected) {
    const Node &fn = *n.kids[0];
    if (fn.kind != NodeKind::Name)
      return fail(fn, "only named functions can be called for now");
    size_t argc = n.kids.size() - 1;
    Location l = loc(n);
    // A name a quote made resolves where the metaprogram was defined, never
    // to a local at the expansion site (docs/meta.md, "Hygiene").
    bool local = fn.flags.empty() && lookup(fn.text);
    if (!local && fn.flags != "prelude") {
      auto it = sigs_.find(fn.text);
      if (it != sigs_.end()) {
        std::vector<const Node *> args;
        for (size_t i = 1; i < n.kids.size(); ++i)
          args.push_back(n.kids[i].get());
        return genCall(n, it->second, args);
      }
    }
    if (!local) {
      if (const char *op = builtinOperator(fn.text)) {
        if (argc != 2)
          return fail(n, "'" + fn.text + "' takes two arguments");
        return genBinary(n, op, *n.kids[1], *n.kids[2], expected);
      }
      if (fn.text == "len") {
        if (argc != 1) return fail(n, "'len' takes one argument");
        R buf = genExpr(*n.kids[1], Type());
        if (!buf) return buf;
        if (!mlir::isa<ArrayType, SliceType>(buf->type))
          return fail(*n.kids[1], "'len' needs an array or slice, found " +
                                      typeName(buf->type));
        Value i = create<LenOp>(l, b_.getIndexType(), buf->value);
        Type usize = types_.usize();
        return TV{create<FromIndexOp>(l, usize, i), usize};
      }
      if (fn.text == "old") {
        if (!contract_) return fail(n, "'old' is only allowed in contracts");
        if (argc != 1) return fail(n, "'old' takes one argument");
        R v = genExpr(*n.kids[1], Type());
        if (!v) return v;
        return TV{create<contract::OldOp>(l, v->type, v->value), v->type};
      }
    }
    return fail(fn, "'" + fn.text + "' is not a function");
  }

  R genCall(const Node &n, const sema::FuncSig &sig,
            const std::vector<const Node *> &args) {
    if (args.size() != sig.params.size())
      return fail(n, "'" + sig.name + "' takes " +
                         plural(sig.params.size(), "argument") + ", given " +
                         std::to_string(args.size()) +
                         "; partial application is not supported yet");
    if (!sig.result)
      return fail(n, "'" + sig.name + "' is used before its return type is "
                     "known; annotate it, as in 'let " + sig.name +
                     " ... : T = ...'");
    llvm::SmallVector<Value> operands;
    for (size_t i = 0; i < args.size(); ++i) {
      R a = genExpr(*args[i], sig.params[i].type);
      if (!a) return a;
      R c = coerce(*a, sig.params[i].type, *args[i]);
      if (!c) return c;
      operands.push_back(c->value);
    }
    return emitCall(n, sig, operands);
  }

  R emitCall(const Node &n, const sema::FuncSig &sig,
             llvm::ArrayRef<Value> operands) {
    llvm::SmallVector<Type> results;
    if (!isUnit(sig.result)) results.push_back(sig.result);
    auto call = create<mlir::func::CallOp>(loc(n), sig.name, results,
                                              operands);
    if (results.empty()) return unit();
    return TV{call.getResult(0), sig.result};
  }

  // `=` and `<>` on records call `eq_<name>`, which `@derive(eq)` makes.
  R genRecordEq(const Node &n, const std::string &op, TV a,
                const Node &lhsNode, TV c, const Node &rhsNode) {
    if (op != "=" && op != "<>")
      return fail(n, "records cannot be compared with '" + op + "'");
    auto rt = mlir::dyn_cast<RecordType>(a.type);
    if (!rt || a.type != c.type)
      return fail(n, "'" + op + "' compares two values of one record type, "
                     "found " + typeName(a.type) + " and " + typeName(c.type));
    std::string name = rt.getName().str();
    auto it = sigs_.find("eq_" + name);
    if (it == sigs_.end())
      return fail(n, "comparing records of type " + name + " with '" + op +
                         "' needs 'eq_" + name + "'; add @derive(eq) to '" +
                         name + "'");
    const sema::FuncSig &sig = it->second;
    if (sig.params.size() != 2 || sig.params[0].type != a.type ||
        sig.params[1].type != a.type || sig.result != boolType())
      return fail(n, "'eq_" + name + "' must take two " + name +
                         " values and return bool");
    (void)lhsNode;
    (void)rhsNode;
    R eq = emitCall(n, sig, {a.value, c.value});
    if (!eq || op == "=") return eq;
    Location l = loc(n);
    Value v = create<mlir::arith::XOrIOp>(l, eq->value, boolConst(l, true));
    return TV{v, boolType()};
  }

  Type elementType(Type buffer) {
    if (auto a = mlir::dyn_cast<ArrayType>(buffer)) return a.getElementType();
    if (auto s = mlir::dyn_cast<SliceType>(buffer)) return s.getElementType();
    return {};
  }

  // The index of `xs.[i]`, as an `index` value.
  std::optional<Value> genIndexValue(const Node &index) {
    if (index.kind == NodeKind::Range) {
      fail(index, "slicing with a range is not supported yet");
      return std::nullopt;
    }
    R i = genExpr(index, types_.usize());
    if (!i) return std::nullopt;
    if (!mlir::isa<IntType>(i->type)) {
      fail(index, "an index must be an integer, found " + typeName(i->type));
      return std::nullopt;
    }
    return toIndex(loc(index), i->value);
  }

  R genIndex(const Node &n) {
    R buf = genExpr(*n.kids[0], Type());
    if (!buf) return buf;
    Type elem = elementType(buf->type);
    if (!elem)
      return fail(*n.kids[0], "only arrays and slices can be indexed, found " +
                                  typeName(buf->type));
    auto idx = genIndexValue(*n.kids[1]);
    if (!idx) return std::nullopt;
    Value v = create<LoadOp>(loc(n), elem, buf->value, *idx);
    return TV{v, elem};
  }

  // `{ r = x; g = 0 }`: the record type comes from the context or, failing
  // that, from the one record whose fields are exactly these.
  R genRecordLit(const Node &n, Type expected) {
    auto rt = mlir::dyn_cast_or_null<RecordType>(expected);
    if (!rt) {
      std::set<std::string> written;
      for (const syntax::NodePtr &f : n.kids) written.insert(f->text);
      std::vector<RecordType> matches;
      for (const auto &[name, t] : types_.namedTypes()) {
        auto r = mlir::dyn_cast<RecordType>(t);
        if (!r || r.getName() != name) continue;
        std::set<std::string> fields;
        for (mlir::StringAttr f : r.getFieldNames()) fields.insert(f.str());
        if (fields == written) matches.push_back(r);
      }
      if (matches.size() != 1)
        return fail(n, matches.empty()
                           ? "no record type has exactly these fields"
                           : "more than one record type has these fields; "
                             "annotate the type, as in 'let p : T = { ... }'");
      rt = matches[0];
    }
    for (const syntax::NodePtr &f : n.kids)
      if (!rt.fieldIndex(f->text))
        return fail(*f, typeName(rt) + " has no field '" + f->text + "'");
    llvm::SmallVector<Value> fields;
    for (auto [name, ft] : llvm::zip(rt.getFieldNames(), rt.getFieldTypes())) {
      const Node *init = nullptr;
      for (const syntax::NodePtr &f : n.kids) {
        if (f->text != name.getValue()) continue;
        if (init)
          return fail(*f, "the field '" + f->text + "' is given twice");
        init = f.get();
      }
      if (!init)
        return fail(n, "the field '" + name.str() + "' of " + typeName(rt) +
                           " is missing");
      R v = genExpr(*init->kids[0], ft);
      if (!v) return v;
      R c = coerce(*v, ft, *init->kids[0]);
      if (!c) return c;
      fields.push_back(c->value);
    }
    return TV{create<RecordOp>(loc(n), rt, fields), rt};
  }

  R genField(const Node &n) {
    R obj = genExpr(*n.kids[0], Type());
    if (!obj) return obj;
    auto rt = mlir::dyn_cast<RecordType>(obj->type);
    if (!rt)
      return fail(n, "'." + n.text + "' needs a record, found " +
                         typeName(obj->type));
    std::optional<unsigned> i = rt.fieldIndex(n.text);
    if (!i) return fail(n, typeName(rt) + " has no field '" + n.text + "'");
    Type ft = rt.getFieldTypes()[*i];
    Value v = create<FieldOp>(loc(n), ft, obj->value, b_.getStringAttr(n.text));
    return TV{v, ft};
  }

  R genAssign(const Node &n) {
    const Node &place = *n.kids[0];
    const Node &valueNode = *n.kids[1];
    if (place.kind == NodeKind::Field) {
      // `p.r <- v` rebuilds the record `p` with one field replaced.
      const Node &obj = *place.kids[0];
      if (obj.kind != NodeKind::Name)
        return fail(obj, "only a field of a named record can be assigned");
      BindingPtr b = lookup(obj.text);
      if (!b) return fail(obj, "unknown name '" + obj.text + "'");
      auto rt = mlir::dyn_cast<RecordType>(b->type);
      if (!rt)
        return fail(place, "'." + place.text + "' needs a record, found " +
                               typeName(b->type));
      if (!b->isMutable)
        return fail(obj, "'" + obj.text + "' is not mutable; declare it "
                         "as 'let " + obj.text + " : mutable T = ...'");
      std::optional<unsigned> i = rt.fieldIndex(place.text);
      if (!i)
        return fail(place, typeName(rt) + " has no field '" + place.text + "'");
      Type ft = rt.getFieldTypes()[*i];
      R v = genExpr(valueNode, ft);
      if (!v) return v;
      R c = coerce(*v, ft, valueNode);
      if (!c) return c;
      Location l = loc(n);
      llvm::SmallVector<Value> fields;
      for (auto [j, name] : llvm::enumerate(rt.getFieldNames()))
        fields.push_back(j == *i ? c->value
                                 : create<FieldOp>(l, rt.getFieldTypes()[j],
                                                   b->value, name)
                                       .getResult());
      b->value = create<RecordOp>(l, rt, fields);
      return unit();
    }
    if (place.kind == NodeKind::Name) {
      BindingPtr b = lookup(place.text);
      if (!b) return fail(place, "unknown name '" + place.text + "'");
      if (!b->isMutable)
        return fail(place, "'" + place.text + "' is not mutable; declare it "
                           "as 'let " + place.text + " : mutable T = ...'");
      if (mlir::isa<ArrayType, SliceType>(b->type))
        return fail(place, "assigning a whole array is not supported yet");
      R v = genExpr(valueNode, b->type);
      if (!v) return v;
      R c = coerce(*v, b->type, valueNode);
      if (!c) return c;
      b->value = c->value;
      return unit();
    }
    if (place.kind == NodeKind::Index) {
      const Node &obj = *place.kids[0];
      if (obj.kind != NodeKind::Name)
        return fail(obj, "only a named array or slice can be written");
      BindingPtr b = lookup(obj.text);
      if (!b) return fail(obj, "unknown name '" + obj.text + "'");
      Type elem = elementType(b->type);
      if (!elem)
        return fail(obj, "only arrays and slices can be indexed, found " +
                             typeName(b->type));
      if (!b->isParam || !(sema::hasModifier(b->modifiers, "out") ||
                           sema::hasModifier(b->modifiers, "inout")))
        return fail(obj, "cannot write to '" + obj.text +
                             "': declare the parameter 'out' or 'inout'");
      auto idx = genIndexValue(*place.kids[1]);
      if (!idx) return std::nullopt;
      R v = genExpr(valueNode, elem);
      if (!v) return v;
      R c = coerce(*v, elem, valueNode);
      if (!c) return c;
      create<StoreOp>(loc(n), c->value, b->value, *idx);
      return unit();
    }
    return fail(place, "only a name or an element can be assigned");
  }

  R genIf(const Node &n, Type expected) {
    Location l = loc(n);
    R c = genExpr(*n.kids[0], boolType());
    if (!c) return c;
    if (!isBool(c->type))
      return fail(*n.kids[0], "an 'if' condition must be a bool, found " +
                                  typeName(c->type));
    const Node &thenNode = *n.kids[1];
    const Node *elseNode = n.kids.size() > 2 &&
                                   n.kids[2]->kind != NodeKind::None
                               ? n.kids[2].get()
                               : nullptr;
    std::vector<BindingPtr> vars = carried({&thenNode, elseNode});
    llvm::SmallVector<Value> before = values(vars);

    auto thenBlock = std::make_unique<Block>();
    auto elseBlock = std::make_unique<Block>();
    TV tv, ev = unit();
    llvm::SmallVector<Value> thenVars, elseVars;
    {
      OpBuilder::InsertionGuard guard(b_);
      b_.setInsertionPointToEnd(thenBlock.get());
      pushScope();
      R t = genExpr(thenNode, expected);
      popScope();
      if (!t) return t;
      tv = *t;
      thenVars = values(vars);
      setValues(vars, before);
      if (elseNode) {
        b_.setInsertionPointToEnd(elseBlock.get());
        pushScope();
        R e = genExpr(*elseNode, expected ? expected : tv.type);
        popScope();
        if (!e) return e;
        ev = *e;
      }
      elseVars = values(vars);
      setValues(vars, before);
    }

    Type rt;
    if (!elseNode) {
      if (!isUnit(tv.type))
        return fail(thenNode, "an 'if' without 'else' must have type unit, "
                              "found " + typeName(tv.type));
      rt = unitType();
    } else if (tv.type == ev.type) {
      rt = tv.type;
    } else if (mlir::isa<IntType>(tv.type) && mlir::isa<IntType>(ev.type)) {
      rt = join(mlir::cast<IntType>(tv.type), mlir::cast<IntType>(ev.type));
    } else {
      return fail(n, "the branches of 'if' have different types: " +
                         typeName(tv.type) + " and " + typeName(ev.type));
    }

    auto finish = [&](Block *block, TV v, const Node &at,
                      llvm::SmallVector<Value> &vs) -> bool {
      OpBuilder::InsertionGuard guard(b_);
      b_.setInsertionPointToEnd(block);
      llvm::SmallVector<Value> yields;
      if (!isUnit(rt)) {
        R cv = coerce(v, rt, at);
        if (!cv) return false;
        yields.push_back(cv->value);
      }
      yields.append(vs.begin(), vs.end());
      create<mlir::scf::YieldOp>(l, yields);
      return true;
    };
    if (!finish(thenBlock.get(), tv, thenNode, thenVars)) return std::nullopt;
    if (!finish(elseBlock.get(), ev, elseNode ? *elseNode : n, elseVars))
      return std::nullopt;

    llvm::SmallVector<Type> types;
    if (!isUnit(rt)) types.push_back(rt);
    for (const BindingPtr &b : vars) types.push_back(b->type);
    auto ifOp = makeIf(l, types, c->value, std::move(thenBlock),
                       std::move(elseBlock));
    size_t first = isUnit(rt) ? 0 : 1;
    setValues(vars, ifOp.getResults().drop_front(first));
    if (isUnit(rt)) return unit();
    return TV{ifOp.getResult(0), rt};
  }

  // The bounds of `lo..hi`, joined to one range type. Two literals count
  // as usize, the type loops and quantifiers most often range over.
  std::optional<std::pair<TV, TV>> genRange(const Node &range) {
    const Node &lo = *range.kids[0], &hi = *range.kids[1];
    Type expected = isLiteral(lo) && isLiteral(hi) ? types_.usize() : Type();
    auto ops = genOperands(lo, hi, expected);
    if (!ops) return std::nullopt;
    auto at = mlir::dyn_cast<IntType>(ops->first.type);
    auto ct = mlir::dyn_cast<IntType>(ops->second.type);
    if (!at || !ct) {
      fail(range, "a range needs integer bounds, found " +
                      typeName(ops->first.type) + " and " +
                      typeName(ops->second.type));
      return std::nullopt;
    }
    IntType j = join(at, ct);
    R a = coerce(ops->first, j, lo);
    R c = coerce(ops->second, j, hi);
    if (!a || !c) return std::nullopt;
    return std::make_pair(*a, *c);
  }

  bool genLoopAnnots(const Node &annots) {
    for (const syntax::NodePtr &a : annots.kids) {
      if (a->kind == NodeKind::Invariant) {
        R p = genPredicate(*a->kids[0]);
        if (!p) return false;
        create<contract::InvariantOp>(loc(*a), p->value);
      } else if (a->kind == NodeKind::Decreases) {
        R m = genContractExpr(*a->kids[0], Type());
        if (!m) return false;
        create<contract::DecreasesOp>(loc(*a), m->value);
      }
    }
    return true;
  }

  R genFor(const Node &n) {
    Location l = loc(n);
    const Node &pattern = *n.kids[0];
    const Node &iterable = *n.kids[1];
    const Node &stepNode = *n.kids[2];
    const Node &annots = *n.kids[3];
    const Node &body = *n.kids[4];
    if (pattern.kind != NodeKind::PVar)
      return fail(pattern, "a for loop binds a single name for now");
    if (iterable.kind != NodeKind::Range)
      return fail(iterable, "a for loop iterates over a range 'lo..hi' for now");
    auto bounds = genRange(iterable);
    if (!bounds) return std::nullopt;
    Type t = bounds->first.type;
    Value lb = toIndex(l, bounds->first.value);
    Value ub = toIndex(l, bounds->second.value);
    Value step;
    if (stepNode.kind != NodeKind::None) {
      R s = genExpr(stepNode, t);
      if (!s) return s;
      if (!mlir::isa<IntType>(s->type))
        return fail(stepNode, "a step must be an integer, found " +
                                  typeName(s->type));
      step = toIndex(loc(stepNode), s->value);
    } else {
      step = create<mlir::arith::ConstantIndexOp>(l, 1);
    }

    std::vector<BindingPtr> vars = carried({&annots, &body});
    auto forOp = create<mlir::scf::ForOp>(l, lb, ub, step, values(vars));
    Block *block = forOp.getBody();
    {
      OpBuilder::InsertionGuard guard(b_);
      // Without iteration arguments the builder adds an empty yield; it is
      // rebuilt below with the loop-carried values.
      if (!block->empty() && block->back().hasTrait<mlir::OpTrait::IsTerminator>())
        block->back().erase();
      b_.setInsertionPointToEnd(block);
      pushScope();
      setValues(vars, forOp.getRegionIterArgs());
      Value i = create<FromIndexOp>(loc(pattern), t, forOp.getInductionVar());
      if (!checkFresh(pattern.text, pattern.loc)) {
        popScope();
        return std::nullopt;
      }
      bind(pattern.text, i, t, false);
      bool ok = genLoopAnnots(annots);
      R r = ok ? genExpr(body, Type()) : std::nullopt;
      if (r) create<mlir::scf::YieldOp>(l, values(vars));
      popScope();
      if (!r) return r;
    }
    setValues(vars, forOp.getResults());
    return unit();
  }

  R genWhile(const Node &n) {
    Location l = loc(n);
    const Node &cond = *n.kids[0];
    const Node &annots = *n.kids[1];
    const Node &body = *n.kids[2];
    std::vector<BindingPtr> vars = carried({&cond, &annots, &body});
    llvm::SmallVector<Type> types;
    for (const BindingPtr &b : vars) types.push_back(b->type);
    bool ok = true;
    auto whileOp = create<mlir::scf::WhileOp>(
        l, types, values(vars),
        [&](OpBuilder &ob, Location, mlir::ValueRange args) {
          OpBuilder::InsertionGuard guard(b_);
          b_.setInsertionPoint(ob.getInsertionBlock(), ob.getInsertionPoint());
          pushScope();
          setValues(vars, args);
          R c;
          if (genLoopAnnots(annots)) c = genExpr(cond, boolType());
          if (c && !isBool(c->type)) {
            fail(cond, "a 'while' condition must be a bool, found " +
                           typeName(c->type));
            c = std::nullopt;
          }
          if (c)
            create<mlir::scf::ConditionOp>(l, c->value, values(vars));
          else
            ok = false;
          popScope();
        },
        [&](OpBuilder &ob, Location, mlir::ValueRange args) {
          if (!ok) return;
          OpBuilder::InsertionGuard guard(b_);
          b_.setInsertionPoint(ob.getInsertionBlock(), ob.getInsertionPoint());
          pushScope();
          setValues(vars, args);
          R r = genExpr(body, Type());
          if (r)
            create<mlir::scf::YieldOp>(l, values(vars));
          else
            ok = false;
          popScope();
        });
    if (!ok) return std::nullopt;
    setValues(vars, whileOp.getResults());
    return unit();
  }

  R genLetIn(const Node &n, Type expected) {
    const Node &params = *n.kids[0];
    const Node &ret = *n.kids[1];
    const Node &contracts = *n.kids[2];
    if (!params.kids.empty())
      return fail(n, "local functions are not supported yet; define '" +
                         n.text + "' at the top level");
    if (!contracts.kids.empty())
      return fail(*contracts.kids[0],
                  "contracts on a local 'let' are not supported yet");
    Type declared;
    std::string modifiers;
    if (ret.kind == NodeKind::RetAnnot && !ret.kids.empty() &&
        ret.kids[0]->kind == NodeKind::Annot) {
      modifiers = ret.kids[0]->kids[0]->text;
      declared = types_.resolveAnnot(*ret.kids[0]);
      if (!declared) return std::nullopt;
      if (ret.kids.size() > 1 && !ret.kids[1]->kids.empty())
        return fail(*ret.kids[1]->kids[0],
                    "attributes on a local 'let' are not supported yet");
    }
    const Node &valueNode = *n.kids[3];
    R v = genExpr(valueNode, declared);
    if (!v) return v;
    if (declared) {
      v = coerce(*v, declared, valueNode);
      if (!v) return v;
    }
    if (isUnit(v->type))
      return fail(valueNode, "'" + n.text + "' would have type unit");
    if (!checkFresh(n.text, n.loc)) return std::nullopt;
    pushScope();
    bind(n.text, v->value, v->type, sema::hasModifier(modifiers, "mutable"));
    R body = genExpr(*n.kids[4], expected);
    popScope();
    return body;
  }

  // One quantifier op per bound name, nested, so a later range can mention
  // an earlier name: `forall (i in 0..n) (j in 0..i). p`.
  R genQuantifier(const Node &n, size_t index) {
    const Node &binder = *n.kids[index];
    bool innermost = index + 2 == n.kids.size();
    bool isForall = n.text == "forall";
    Location l = loc(binder);

    Type t;
    std::optional<std::pair<TV, TV>> bounds;
    if (binder.kind == NodeKind::RangeBinder) {
      bounds = genRange(*binder.kids[0]);
      if (!bounds) return std::nullopt;
      t = bounds->first.type;
    } else if (binder.kind == NodeKind::Binder && !binder.kids.empty() &&
               binder.kids[0]->kind != NodeKind::None) {
      t = types_.resolve(*binder.kids[0]);
      if (!t) return std::nullopt;
    } else {
      return fail(binder, "'" + binder.text +
                              "' needs a type or a range, as in (" +
                              binder.text + " in 0..n)");
    }

    mlir::Operation *q =
        isForall
            ? create<contract::ForallOp>(l, b_.getI1Type()).getOperation()
            : create<contract::ExistsOp>(l, b_.getI1Type()).getOperation();
    OpBuilder::InsertionGuard guard(b_);
    Block *block = b_.createBlock(&q->getRegion(0), {}, {t}, {l});
    if (!checkFresh(binder.text, binder.loc)) return std::nullopt;
    pushScope();
    Value x = block->getArgument(0);
    bind(binder.text, x, t, false);
    R inner = innermost ? genPredicate(*n.kids.back())
                        : genQuantifier(n, index + 1);
    popScope();
    if (!inner) return inner;
    Value body = inner->value;
    if (bounds) {
      Value inRange = create<mlir::arith::AndIOp>(
          l, cmp(l, CmpPredicate::le, bounds->first.value, x),
          cmp(l, CmpPredicate::lt, x, bounds->second.value));
      body = isForall ? implies(l, inRange, body)
                      : create<mlir::arith::AndIOp>(l, inRange, body)
                            .getResult();
    }
    create<contract::YieldOp>(l, body);
    return TV{q->getResult(0), boolType()};
  }

  mlir::MLIRContext &ctx_;
  OpBuilder b_;
  mlir::StringAttr file_;
  syntax::Diagnostics &diags_;
  sema::TypeResolver types_;
  mlir::ModuleOp module_;
  std::map<std::string, sema::FuncSig> sigs_;
  std::vector<std::map<std::string, BindingPtr>> scopes_;
  bool contract_ = false;
  OverflowMode overflow_ = OverflowMode::proof;
};

}  // namespace

mlir::OwningOpRef<mlir::ModuleOp> generate(const syntax::Node &program,
                                           std::string_view filename,
                                           mlir::MLIRContext &ctx,
                                           syntax::Diagnostics &diags) {
  loadDialects(ctx);
  return Gen(ctx, filename, diags).run(program);
}

}  // namespace pia::irgen
