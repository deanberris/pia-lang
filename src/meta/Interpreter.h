// The metaprogram interpreter (milestone M7): a tree-walking evaluator for
// `let meta` functions over the syntax tree. docs/meta.md describes the
// values, the builtins, quotes, splices and hygiene.

#ifndef PIA_META_INTERPRETER_H
#define PIA_META_INTERPRETER_H

#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "syntax/Syntax.h"

namespace pia::meta {

struct Value;
using ValuePtr = std::shared_ptr<const Value>;
struct Env;
using EnvPtr = std::shared_ptr<Env>;

struct Value {
  enum class Kind { Unit, Int, Bool, Str, Syntax, List, Closure, Builtin, Type };
  Kind kind = Kind::Unit;
  int64_t i = 0;
  bool b = false;
  std::string s;                          // Str; Builtin: its name; Type: its
                                          // spelling, `u8` or `option<u8>`
  std::shared_ptr<syntax::Node> syntax;   // Syntax
  std::vector<ValuePtr> list;             // List; Closure, Builtin: bound args
  // Closure: a lambda or a `let` with parameters. An empty parameter name
  // stands for `()`.
  std::vector<std::string> params;
  const syntax::Node *body = nullptr;
  EnvPtr env;
  std::string name;                       // Closure: the metaprogram's name
};

// A chain of local bindings. A `let` with parameters binds itself, so its
// value is set after the node exists.
struct Env {
  std::string name;
  ValuePtr value;
  EnvPtr parent;
};

// A failure inside a metaprogram, reported at the expansion site.
struct MetaError {
  syntax::SourceLoc loc;
  std::string message;
};

// Thrown when a metaprogram asks for a type that is not defined yet. The
// expansion loop runs it again in the next pass.
struct Deferred {
  std::string type;
};

// What a type-level metaprogram can ask about types (ADR 0035). Types are
// values spelled as Pia spells them; the compiler maps a spelling back to
// its type. Outside the compiler's type checking these are unset, and type
// names are not values.
struct TypeInfo {
  // "int", "bool", "unit", "array", "slice", "record" or "variant".
  std::string kind;
  std::optional<std::string> element;  // an array's or a slice's
  // A record's field types, or a variant's payload types, in order.
  std::vector<std::string> fields;
  // A generic instance's type arguments, as in `pair<u8, u16>`.
  std::vector<std::string> args;
  // Its size in bytes, or nothing when it has no fixed size.
  std::optional<int64_t> size;
  // An array's length, and the generic an instance comes from (`option`).
  std::optional<int64_t> length;
  std::string generic;
};

struct TypeHost {
  // The spelling of the type a name denotes, such as `u8` or `pixel`.
  std::function<std::optional<std::string>(const std::string &)> named;
  // What a type is made of, by its spelling.
  std::function<TypeInfo(const std::string &)> info;
};

class Interpreter {
 public:
  // `isTypeDefined` says whether a type name resolves now: a builtin type or
  // a type item in the program.
  explicit Interpreter(std::function<bool(const std::string &)> isTypeDefined)
      : isTypeDefined_(std::move(isTypeDefined)) {}

  // Makes a top-level `let meta` item callable by name.
  void define(const syntax::Node &item);

  bool isMeta(const std::string &name) const { return globals_.count(name); }

  // Evaluates an expression with no local bindings.
  ValuePtr eval(const syntax::Node &expr);

  // Evaluates an expression with `bindings` in scope, as a fresh run.
  ValuePtr evalWith(
      const syntax::Node &expr,
      const std::vector<std::pair<std::string, ValuePtr>> &bindings);

  // Calls the top-level metaprogram `name`, as a fresh run.
  ValuePtr call(const std::string &name, std::vector<ValuePtr> args);

  // The number of parameters of the metaprogram `name`.
  size_t arity(const std::string &name) const;

  void setTypeHost(TypeHost host) { host_ = std::move(host); }
  static ValuePtr typeValue(std::string spelling);
  static const char *kindName(Value::Kind k);

  ValuePtr apply(const ValuePtr &fn, std::vector<ValuePtr> args);

  // Code built by quotes takes the location of the expansion site.
  void setSite(syntax::SourceLoc site) { site_ = site; }

  // What `listing ()` sees: the program's items as the current pass found
  // them, and the program node, whose comments end the file (ADR 0029).
  void setListing(std::vector<const syntax::Node *> items,
                  const syntax::Node *program) {
    listing_ = std::move(items);
    program_ = program;
  }

  // Makes the REPL-only builtins of Pia.Live available (ADR 0031).
  void setLive(bool live) { live_ = live; }

  // Names a quote leaves free resolve to these builtins wherever the code
  // lands (docs/meta.md, "Hygiene").
  static bool isCoreBuiltin(const std::string &name);

  static ValuePtr syntaxValue(syntax::NodePtr node);

  // The names of the metaprograms that ran since the last call.
  std::vector<std::string> takeRan();

 private:
  ValuePtr eval(const syntax::Node &n, const EnvPtr &env);
  ValuePtr lookup(const syntax::Node &n, const EnvPtr &env);
  ValuePtr closure(std::vector<std::string> params, const syntax::Node &body,
                   EnvPtr env, std::string name);
  ValuePtr callBuiltin(const std::string &name,
                       const std::vector<ValuePtr> &args,
                       const syntax::Node *at);
  ValuePtr binary(const syntax::Node &n, const EnvPtr &env);
  ValuePtr binop(const std::string &op, const ValuePtr &a, const ValuePtr &b);
  ValuePtr quote(const syntax::Node &n, const EnvPtr &env);
  ValuePtr match(const syntax::Node &n, const EnvPtr &env);
  bool matches(const syntax::Node &p, const ValuePtr &v, EnvPtr &env);
  // The code a value stands for when it is put into syntax: syntax itself,
  // a string as a name, a non-negative integer or a bool as a literal.
  syntax::NodePtr toCode(const ValuePtr &v, const std::string &who);
  // The type item `t` names: an item, or a type's name, found in the
  // listing.
  const syntax::Node *findTypeItem(const ValuePtr &t);
  // `range_of t`: the bounds of an integer type, as `[lo; hi]`.
  ValuePtr rangeOf(const ValuePtr &t);
  void tick(const syntax::Node &n);

  std::function<bool(const std::string &)> isTypeDefined_;
  std::map<std::string, const syntax::Node *> globals_;
  syntax::SourceLoc site_;
  std::vector<const syntax::Node *> listing_;
  const syntax::Node *program_ = nullptr;
  bool live_ = false;
  TypeHost host_;
  uint64_t fuel_ = 0;
  unsigned fresh_ = 0;
  std::vector<std::string> ran_;
  friend class QuoteBuilder;
};

}  // namespace pia::meta

#endif  // PIA_META_INTERPRETER_H
