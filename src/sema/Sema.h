// Minimal semantic analysis for the scalar subset (milestone M4).
//
// It resolves written types to MLIR types, collects the signatures of
// top-level functions so IRGen can call a function before its definition,
// and checks parameter modifiers. Expressions are type checked by IRGen as
// it lowers them; a separate typed AST comes when the language outgrows
// the scalar subset (docs/architecture.md, "Front end").

#ifndef PIA_SEMA_SEMA_H
#define PIA_SEMA_SEMA_H

#include <functional>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <string_view>
#include <vector>

#include "llvm/ADT/APInt.h"
#include "mlir/IR/MLIRContext.h"
#include "llvm/ADT/DenseMap.h"
#include "mlir/IR/Types.h"
#include "syntax/Diagnostics.h"
#include "syntax/Syntax.h"

namespace pia::sema {

// Integer literal spellings: decimal, 0x, 0o and 0b, with `_` separators and
// an optional type suffix (`42u8`, `3usize`).
struct IntLiteral {
  llvm::APInt value;   // 128-bit, signed
  std::string suffix;  // "u8", "usize", ... or empty
};
std::optional<IntLiteral> parseIntLiteral(std::string_view spelling);

// A type as Pia spells it: `u8`, `int{-3..5}`, `[u8; 4]`, `bool`, `unit`,
// or a record's name.
std::string typeName(mlir::Type type);

// The spec-only type (`int` or `real`, ADR 0036) that `type` is or holds,
// through arrays, slices and record fields; null when there is none.
mlir::Type specOnlyPart(mlir::Type type);

// Whether a modifier list such as "borrowed in mutable" has `word`.
bool hasModifier(std::string_view modifiers, std::string_view word);

// A constructor of a variant type. A variant `let shape = type | A | B of t`
// is held as a record named `shape` with a field `tag`, int{0..n-1}, and one
// field per constructor with a payload, named after the constructor. The
// constructor's tag is its position. Only constructors, `match` and the
// verifier see those fields.
struct Ctor {
  std::string name;
  mlir::Type variant;  // the record type that holds the variant
  unsigned tag = 0;
  mlir::Type payload;  // null for a constructor without one
};

// A generic type, `let option = let (t : type) => type | None | Some of t`:
// a compile-time function from types to a type (ADR 0009). Each use with
// arguments, `option u8`, is an instance, a concrete type named
// `option<u8>`, made once.
struct Generic {
  std::string name;
  std::vector<std::string> params;
  const syntax::Node *value = nullptr;  // the TypeValue body
  syntax::SourceLoc loc;
};

// What an instance was made from: `option<u8>` is `option` applied to u8.
struct Instance {
  std::string generic;
  std::vector<mlir::Type> args;
};

// A constructor of a generic variant, before its type arguments are known.
struct GenericCtor {
  std::string name;
  std::string generic;
  unsigned tag = 0;
  const syntax::Node *payload = nullptr;  // null for none
};

class TypeResolver {
 public:
  TypeResolver(mlir::MLIRContext &ctx, syntax::Diagnostics &diags)
      : ctx_(ctx), diags_(diags) {}

  // A type expression from the syntax tree. Reports an error and returns a
  // null type for anything outside the subset.
  mlir::Type resolve(const syntax::Node &type);

  // The type of an `Annot` node, which must not carry a `where` refinement.
  mlir::Type resolveAnnot(const syntax::Node &annot);

  // Built-in integer types by name (`u8`, `i32`, `usize`, ...), or null.
  mlir::Type builtin(std::string_view name);

  // A named type from a `let name = type ...` item: a record or an alias.
  void define(const std::string &name, mlir::Type type) { named_[name] = type; }
  mlir::Type named(const std::string &name) const {
    auto it = named_.find(name);
    return it == named_.end() ? mlir::Type() : it->second;
  }
  const std::map<std::string, mlir::Type> &namedTypes() const { return named_; }

  // Variant constructors. `ctor` finds one of a non-generic variant by
  // name; `ctorIn` finds one of a given variant, generic instances too.
  // `global` is false for an instance's constructors, which share their
  // names with the other instances of the same generic.
  void defineCtor(Ctor c, bool global = true) {
    if (global) ctors_[c.name] = c;
    variants_[c.variant].push_back(std::move(c));
  }
  const Ctor *ctor(const std::string &name) const {
    auto it = ctors_.find(name);
    return it == ctors_.end() ? nullptr : &it->second;
  }
  const Ctor *ctorIn(const std::string &name, mlir::Type variant) const {
    auto it = variants_.find(variant);
    if (it != variants_.end())
      for (const Ctor &c : it->second)
        if (c.name == name) return &c;
    return nullptr;
  }
  bool isVariant(mlir::Type t) const { return variants_.count(t) != 0; }
  std::vector<const Ctor *> ctorsOf(mlir::Type variant) const {
    std::vector<const Ctor *> out;
    auto it = variants_.find(variant);
    if (it != variants_.end())
      for (const Ctor &c : it->second) out.push_back(&c);
    return out;
  }
  // Whether `name` is a constructor of any variant, generic or not.
  bool isCtorName(const std::string &name) const {
    return ctors_.count(name) || genericCtors_.count(name);
  }
  void defineGenericCtor(GenericCtor c) { genericCtors_[c.name] = std::move(c); }
  const GenericCtor *genericCtor(const std::string &name) const {
    auto it = genericCtors_.find(name);
    return it == genericCtors_.end() ? nullptr : &it->second;
  }

  // Generic types and their instances.
  void defineGeneric(Generic g) { generics_[g.name] = std::move(g); }
  const Generic *generic(const std::string &name) const {
    auto it = generics_.find(name);
    return it == generics_.end() ? nullptr : &it->second;
  }
  // `name` applied to `args`, made on first use. Null after an error.
  mlir::Type instantiate(const std::string &name,
                         llvm::ArrayRef<mlir::Type> args,
                         syntax::SourceLoc at);
  const Instance *instanceOf(mlir::Type t) const {
    auto it = instanceOf_.find(t);
    return it == instanceOf_.end() ? nullptr : &it->second;
  }

  // An error set `a | b` (ADR 0028): one variant holding the constructors
  // of each member, in the members' order by name. Null after an error.
  mlir::Type unionOf(llvm::ArrayRef<mlir::Type> members, syntax::SourceLoc at);
  // The variants a union was made of, or null for any other type.
  const std::vector<mlir::Type> *unionMembers(mlir::Type t) const {
    auto it = unions_.find(t);
    return it == unions_.end() ? nullptr : &it->second;
  }

  // Type parameters in scope while a generic's body is resolved: a name
  // here resolves to its argument.
  void pushTypeScope(std::map<std::string, mlir::Type> s) {
    typeScopes_.push_back(std::move(s));
  }
  void popTypeScope() { typeScopes_.pop_back(); }
  // Replaces every type scope, returning the old ones: a generic
  // function's signature sees only its own type parameters.
  std::vector<std::map<std::string, mlir::Type>> replaceTypeScopes(
      std::vector<std::map<std::string, mlir::Type>> s) {
    typeScopes_.swap(s);
    return s;
  }

  // Deduction: matches a written type that mentions `params` against an
  // actual type, binding each parameter it finds. False on a clash, such
  // as one parameter bound to two different types.
  bool unify(const syntax::Node &written, mlir::Type actual,
             const std::vector<std::string> &params,
             std::map<std::string, mlir::Type> &bound) const;

  // Type-level metaprograms (ADR 0035): `widen u8` in a type calls the
  // metaprogram `widen` with u8, through `call`, when `is` says `widen` is
  // one. `call` reports its own errors and returns null after one.
  using TypeFunctionCall = std::function<mlir::Type(
      const std::string &, llvm::ArrayRef<mlir::Type>, syntax::SourceLoc)>;
  void setTypeFunctions(std::function<bool(const std::string &)> is,
                        TypeFunctionCall call) {
    isTypeFunction_ = std::move(is);
    callTypeFunction_ = std::move(call);
  }
  bool isTypeFunction(const std::string &name) const {
    return isTypeFunction_ && isTypeFunction_(name);
  }

  mlir::Type usize() { return builtin("usize"); }
  mlir::Type i32() { return builtin("i32"); }
  mlir::Type boolType();
  mlir::Type unitType();
  bool isUnit(mlir::Type t) const;

 private:
  std::optional<llvm::APInt> constantBound(const syntax::Node &n);

  mlir::MLIRContext &ctx_;
  syntax::Diagnostics &diags_;
  std::map<std::string, mlir::Type> named_;
  std::map<std::string, Ctor> ctors_;
  llvm::DenseMap<mlir::Type, std::vector<Ctor>> variants_;
  std::map<std::string, GenericCtor> genericCtors_;
  std::map<std::string, Generic> generics_;
  std::map<std::string, mlir::Type> instances_;  // by `option<u8>`
  llvm::DenseMap<mlir::Type, Instance> instanceOf_;
  llvm::DenseMap<mlir::Type, std::vector<mlir::Type>> unions_;
  std::set<std::string> instantiating_;
  std::vector<std::map<std::string, mlir::Type>> typeScopes_;
  std::function<bool(const std::string &)> isTypeFunction_;
  TypeFunctionCall callTypeFunction_;
};

// Whether a top-level `let` defines a type: `let pixel = type { ... }`.
bool isTypeItem(const syntax::Node &item);

// Whether it defines a generic type: `let pair = let (a : type) (b : type)
// => type { ... }`.
bool isGenericTypeItem(const syntax::Node &item);

// The core builtins that operators expand to, and `len` and `old`
// (docs/meta.md). No definition may take their names.
bool isCoreBuiltin(std::string_view name);

struct Param {
  std::string name;
  mlir::Type type;
  std::string modifiers;  // as written, e.g. "borrowed in mutable"
  syntax::SourceLoc loc;
};

struct FuncSig {
  std::string name;
  std::vector<Param> params;
  mlir::Type result;  // null until known when the return type is omitted
  const syntax::Node *item = nullptr;
  // A generic function, `let first (a : type) (b : type) (p : pair a b) : a`,
  // has type parameters, and no parameter or result types of its own: each
  // instance has them, with `typeArgs` binding the type parameters.
  std::vector<std::string> typeParams;
  std::map<std::string, mlir::Type> typeArgs;
  bool isGeneric() const { return !typeParams.empty() && typeArgs.empty(); }
  // One of several functions that share the written name `item->text`
  // (ADR 0034). `name`, the symbol, then carries the parameter types.
  bool overloaded = false;
  const std::string &source() const { return item->text; }
  // A function of the adapter `adapter` (ADR 0034), named
  // `adapter.name`: it is called only through the adapter, never by its
  // own name.
  std::string adapter;
  // While this function is generated, names that call an adapter's
  // functions instead, by symbol: an instance or a law made for a type
  // that meets a concept through an adapter.
  std::map<std::string, std::vector<std::string>> adapted;
  // The adapter chosen for each concept and arguments, `Same<u8>`.
  std::map<std::string, std::string> adapterFor;
};

// Resolves the value parameters and result type of `item` into `sig`, with
// the type parameters in `sig.typeArgs` in scope. False after an error.
bool resolveSignature(FuncSig &sig, TypeResolver &types,
                      syntax::Diagnostics &diags);

// Whether a parameter is a type parameter: `(t : type)`.
bool isTypeParam(const syntax::Node &param);

// Defines the type items of `program` alone, as for the prelude's types.
void defineTypeItems(const syntax::Node &program, TypeResolver &types,
                     syntax::Diagnostics &diags);

// Defines every type item, in order, then collects the signature of every
// top-level function. Items outside the subset are reported here, so IRGen
// only sees definitions it can lower. The map is keyed by symbol, which is
// the written name unless the name is overloaded.
std::map<std::string, FuncSig> collectSignatures(const syntax::Node &program,
                                                 TypeResolver &types,
                                                 syntax::Diagnostics &diags);

}  // namespace pia::sema

#endif  // PIA_SEMA_SEMA_H
