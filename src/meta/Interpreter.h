// The metaprogram interpreter (milestone M7): a tree-walking evaluator for
// `let meta` functions over the syntax tree. docs/meta.md describes the
// values, the builtins, quotes, splices and hygiene.

#ifndef PIA_META_INTERPRETER_H
#define PIA_META_INTERPRETER_H

#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <string>
#include <vector>

#include "syntax/Syntax.h"

namespace pia::meta {

struct Value;
using ValuePtr = std::shared_ptr<const Value>;
struct Env;
using EnvPtr = std::shared_ptr<Env>;

struct Value {
  enum class Kind { Unit, Int, Bool, Str, Syntax, List, Closure, Builtin };
  Kind kind = Kind::Unit;
  int64_t i = 0;
  bool b = false;
  std::string s;                          // Str; Builtin: its name
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

  ValuePtr apply(const ValuePtr &fn, std::vector<ValuePtr> args);

  // Code built by quotes takes the location of the expansion site.
  void setSite(syntax::SourceLoc site) { site_ = site; }

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
  ValuePtr quote(const syntax::Node &n, const EnvPtr &env);
  void tick(const syntax::Node &n);

  std::function<bool(const std::string &)> isTypeDefined_;
  std::map<std::string, const syntax::Node *> globals_;
  syntax::SourceLoc site_;
  uint64_t fuel_ = 0;
  unsigned fresh_ = 0;
  std::vector<std::string> ran_;
  friend class QuoteBuilder;
};

}  // namespace pia::meta

#endif  // PIA_META_INTERPRETER_H
