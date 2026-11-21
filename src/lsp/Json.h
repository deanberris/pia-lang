// A small JSON value with a reader and a writer, enough for the Language
// Server Protocol. It has no dependencies, so the front-end part of pia-lsp
// builds without LLVM (ADR 0021).

#ifndef PIA_LSP_JSON_H
#define PIA_LSP_JSON_H

#include <map>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

namespace pia::lsp {

class Json {
 public:
  enum class Kind { Null, Bool, Number, String, Array, Object };
  using Array = std::vector<Json>;
  using Object = std::map<std::string, Json>;

  Json() = default;
  Json(std::nullptr_t) {}
  Json(bool b) : kind_(Kind::Bool), bool_(b) {}
  Json(int n) : kind_(Kind::Number), number_(n) {}
  Json(unsigned n) : kind_(Kind::Number), number_(n) {}
  Json(long n) : kind_(Kind::Number), number_(static_cast<double>(n)) {}
  Json(long long n) : kind_(Kind::Number), number_(static_cast<double>(n)) {}
  Json(unsigned long n) : kind_(Kind::Number), number_(static_cast<double>(n)) {}
  Json(unsigned long long n)
      : kind_(Kind::Number), number_(static_cast<double>(n)) {}
  Json(double n) : kind_(Kind::Number), number_(n) {}
  Json(const char *s) : kind_(Kind::String), string_(s) {}
  Json(std::string s) : kind_(Kind::String), string_(std::move(s)) {}
  Json(std::string_view s) : kind_(Kind::String), string_(s) {}
  Json(Array a) : kind_(Kind::Array), array_(std::move(a)) {}
  Json(Object o) : kind_(Kind::Object), object_(std::move(o)) {}

  Kind kind() const { return kind_; }
  bool isNull() const { return kind_ == Kind::Null; }
  bool isBool() const { return kind_ == Kind::Bool; }
  bool isNumber() const { return kind_ == Kind::Number; }
  bool isString() const { return kind_ == Kind::String; }
  bool isArray() const { return kind_ == Kind::Array; }
  bool isObject() const { return kind_ == Kind::Object; }

  bool asBool(bool fallback = false) const {
    return isBool() ? bool_ : fallback;
  }
  double asNumber(double fallback = 0) const {
    return isNumber() ? number_ : fallback;
  }
  const std::string &asString() const;
  const Array &asArray() const;
  const Object &asObject() const;
  Array &array();    // makes this an empty array if it is not one
  Object &object();  // makes this an empty object if it is not one

  // Object member, or a null value when absent or not an object.
  const Json &operator[](std::string_view key) const;
  Json &operator[](const std::string &key) { return object()[key]; }
  bool has(std::string_view key) const;

  // Compact serialisation; strings are escaped as JSON requires.
  std::string dump() const;
  void dump(std::string &out) const;

  // Parses a whole document. Returns nullopt on malformed input.
  static std::optional<Json> parse(std::string_view text);

 private:
  Kind kind_ = Kind::Null;
  bool bool_ = false;
  double number_ = 0;
  std::string string_;
  Array array_;
  Object object_;
};

}  // namespace pia::lsp

#endif  // PIA_LSP_JSON_H
