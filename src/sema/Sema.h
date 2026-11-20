// Minimal semantic analysis for the scalar subset (milestone M4).
//
// It resolves written types to MLIR types, collects the signatures of
// top-level functions so IRGen can call a function before its definition,
// and checks parameter modifiers. Expressions are type checked by IRGen as
// it lowers them; a separate typed AST comes when the language outgrows
// the scalar subset (docs/architecture.md, "Front end").

#ifndef PIA_SEMA_SEMA_H
#define PIA_SEMA_SEMA_H

#include <map>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "llvm/ADT/APInt.h"
#include "mlir/IR/MLIRContext.h"
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

// A type as Pia spells it: `u8`, `int{-3..5}`, `[u8; 4]`, `bool`, `unit`.
std::string typeName(mlir::Type type);

// Whether a modifier list such as "borrowed in mutable" has `word`.
bool hasModifier(std::string_view modifiers, std::string_view word);

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

  mlir::Type usize() { return builtin("usize"); }
  mlir::Type i32() { return builtin("i32"); }
  mlir::Type boolType();
  mlir::Type unitType();
  bool isUnit(mlir::Type t) const;

 private:
  std::optional<llvm::APInt> constantBound(const syntax::Node &n);

  mlir::MLIRContext &ctx_;
  syntax::Diagnostics &diags_;
};

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
};

// Collects the signature of every top-level `let`. Items outside the subset
// are reported here, so IRGen only sees definitions it can lower.
std::map<std::string, FuncSig> collectSignatures(const syntax::Node &program,
                                                 TypeResolver &types,
                                                 syntax::Diagnostics &diags);

}  // namespace pia::sema

#endif  // PIA_SEMA_SEMA_H
