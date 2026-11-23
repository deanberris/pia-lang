#include "lsp/Json.h"

#include <cmath>
#include <cstdio>
#include <cstdlib>

namespace pia::lsp {

namespace {

const Json &nullJson() {
  static const Json null;
  return null;
}

void escape(std::string &out, std::string_view s) {
  out += '"';
  for (unsigned char c : s) {
    switch (c) {
    case '"':
      out += "\\\"";
      break;
    case '\\':
      out += "\\\\";
      break;
    case '\b':
      out += "\\b";
      break;
    case '\f':
      out += "\\f";
      break;
    case '\n':
      out += "\\n";
      break;
    case '\r':
      out += "\\r";
      break;
    case '\t':
      out += "\\t";
      break;
    default:
      if (c < 0x20) {
        char buf[8];
        std::snprintf(buf, sizeof buf, "\\u%04x", c);
        out += buf;
      } else {
        out += static_cast<char>(c);
      }
    }
  }
  out += '"';
}

void appendUtf8(std::string &out, uint32_t cp) {
  if (cp < 0x80) {
    out += static_cast<char>(cp);
  } else if (cp < 0x800) {
    out += static_cast<char>(0xC0 | (cp >> 6));
    out += static_cast<char>(0x80 | (cp & 0x3F));
  } else if (cp < 0x10000) {
    out += static_cast<char>(0xE0 | (cp >> 12));
    out += static_cast<char>(0x80 | ((cp >> 6) & 0x3F));
    out += static_cast<char>(0x80 | (cp & 0x3F));
  } else {
    out += static_cast<char>(0xF0 | (cp >> 18));
    out += static_cast<char>(0x80 | ((cp >> 12) & 0x3F));
    out += static_cast<char>(0x80 | ((cp >> 6) & 0x3F));
    out += static_cast<char>(0x80 | (cp & 0x3F));
  }
}

class Reader {
public:
  explicit Reader(std::string_view text) : s_(text) {}

  std::optional<Json> document() {
    std::optional<Json> v = value(0);
    space();
    if (!v || pos_ != s_.size())
      return std::nullopt;
    return v;
  }

private:
  void space() {
    while (pos_ < s_.size() && (s_[pos_] == ' ' || s_[pos_] == '\t' ||
                                s_[pos_] == '\n' || s_[pos_] == '\r'))
      ++pos_;
  }
  bool literal(std::string_view word) {
    if (s_.substr(pos_, word.size()) != word)
      return false;
    pos_ += word.size();
    return true;
  }

  std::optional<Json> value(int depth) {
    // Nesting is bounded so that a hostile or broken client cannot overflow
    // the stack of the recursive reader.
    if (depth > 200)
      return std::nullopt;
    space();
    if (pos_ >= s_.size())
      return std::nullopt;
    char c = s_[pos_];
    if (c == '{')
      return object(depth);
    if (c == '[')
      return array(depth);
    if (c == '"') {
      std::optional<std::string> str = string();
      if (!str)
        return std::nullopt;
      return Json(std::move(*str));
    }
    if (literal("true"))
      return Json(true);
    if (literal("false"))
      return Json(false);
    if (literal("null"))
      return Json();
    return number();
  }

  std::optional<Json> object(int depth) {
    ++pos_;
    Json::Object obj;
    space();
    if (pos_ < s_.size() && s_[pos_] == '}') {
      ++pos_;
      return Json(std::move(obj));
    }
    for (;;) {
      space();
      if (pos_ >= s_.size() || s_[pos_] != '"')
        return std::nullopt;
      std::optional<std::string> key = string();
      if (!key)
        return std::nullopt;
      space();
      if (pos_ >= s_.size() || s_[pos_] != ':')
        return std::nullopt;
      ++pos_;
      std::optional<Json> v = value(depth + 1);
      if (!v)
        return std::nullopt;
      obj[std::move(*key)] = std::move(*v);
      space();
      if (pos_ < s_.size() && s_[pos_] == ',') {
        ++pos_;
        continue;
      }
      if (pos_ < s_.size() && s_[pos_] == '}') {
        ++pos_;
        return Json(std::move(obj));
      }
      return std::nullopt;
    }
  }

  std::optional<Json> array(int depth) {
    ++pos_;
    Json::Array arr;
    space();
    if (pos_ < s_.size() && s_[pos_] == ']') {
      ++pos_;
      return Json(std::move(arr));
    }
    for (;;) {
      std::optional<Json> v = value(depth + 1);
      if (!v)
        return std::nullopt;
      arr.push_back(std::move(*v));
      space();
      if (pos_ < s_.size() && s_[pos_] == ',') {
        ++pos_;
        continue;
      }
      if (pos_ < s_.size() && s_[pos_] == ']') {
        ++pos_;
        return Json(std::move(arr));
      }
      return std::nullopt;
    }
  }

  std::optional<uint32_t> hex4() {
    if (pos_ + 4 > s_.size())
      return std::nullopt;
    uint32_t v = 0;
    for (int i = 0; i < 4; ++i) {
      char c = s_[pos_++];
      v <<= 4;
      if (c >= '0' && c <= '9')
        v |= c - '0';
      else if (c >= 'a' && c <= 'f')
        v |= c - 'a' + 10;
      else if (c >= 'A' && c <= 'F')
        v |= c - 'A' + 10;
      else
        return std::nullopt;
    }
    return v;
  }

  // The code point of a `\\u` escape whose `\\u` has been read. JSON writes
  // a character outside the Basic Multilingual Plane as a UTF-16 surrogate
  // pair of two escapes; a high surrogate without its low half is kept as
  // it is rather than rejecting the whole message.
  std::optional<uint32_t> codePoint() {
    std::optional<uint32_t> hi = hex4();
    if (!hi)
      return std::nullopt;
    if (*hi < 0xD800 || *hi >= 0xDC00 || s_.substr(pos_, 2) != "\\u")
      return hi;
    size_t save = pos_;
    pos_ += 2;
    std::optional<uint32_t> lo = hex4();
    if (!lo || *lo < 0xDC00 || *lo >= 0xE000) {
      pos_ = save;
      return hi;
    }
    return 0x10000 + ((*hi - 0xD800) << 10) + (*lo - 0xDC00);
  }

  std::optional<std::string> string() {
    ++pos_;
    std::string out;
    while (pos_ < s_.size()) {
      char c = s_[pos_++];
      if (c == '"')
        return out;
      if (static_cast<unsigned char>(c) < 0x20)
        return std::nullopt;
      if (c != '\\') {
        out += c;
        continue;
      }
      if (pos_ >= s_.size())
        return std::nullopt;
      switch (s_[pos_++]) {
      case '"':
        out += '"';
        break;
      case '\\':
        out += '\\';
        break;
      case '/':
        out += '/';
        break;
      case 'b':
        out += '\b';
        break;
      case 'f':
        out += '\f';
        break;
      case 'n':
        out += '\n';
        break;
      case 'r':
        out += '\r';
        break;
      case 't':
        out += '\t';
        break;
      case 'u': {
        std::optional<uint32_t> cp = codePoint();
        if (!cp)
          return std::nullopt;
        appendUtf8(out, *cp);
        break;
      }
      default:
        return std::nullopt;
      }
    }
    return std::nullopt;
  }

  std::optional<Json> number() {
    size_t start = pos_;
    if (pos_ < s_.size() && s_[pos_] == '-')
      ++pos_;
    bool digits = false;
    while (pos_ < s_.size() &&
           ((s_[pos_] >= '0' && s_[pos_] <= '9') || s_[pos_] == '.' ||
            s_[pos_] == 'e' || s_[pos_] == 'E' || s_[pos_] == '+' ||
            s_[pos_] == '-')) {
      digits |= s_[pos_] >= '0' && s_[pos_] <= '9';
      ++pos_;
    }
    if (!digits)
      return std::nullopt;
    std::string text(s_.substr(start, pos_ - start));
    char *end = nullptr;
    double v = std::strtod(text.c_str(), &end);
    if (end != text.c_str() + text.size())
      return std::nullopt;
    return Json(v);
  }

  std::string_view s_;
  size_t pos_ = 0;
};

// JSON has one number type. Integers print without a fraction, as LSP's
// line and character fields must, as long as a double holds them exactly
// (below 2^53, about 9e15). JSON cannot write NaN or infinity, so they print
// as null.
void appendNumber(std::string &out, double v) {
  if (!std::isfinite(v)) {
    out += "null";
    return;
  }
  if (v == std::floor(v) && std::fabs(v) < 9e15) {
    out += std::to_string(static_cast<long long>(v));
    return;
  }
  char buf[32];
  std::snprintf(buf, sizeof buf, "%.17g", v);
  out += buf;
}

} // namespace

const std::string &Json::asString() const {
  static const std::string empty;
  return isString() ? string_ : empty;
}

const Json::Array &Json::asArray() const {
  static const Array empty;
  return isArray() ? array_ : empty;
}

const Json::Object &Json::asObject() const {
  static const Object empty;
  return isObject() ? object_ : empty;
}

Json::Array &Json::array() {
  if (!isArray())
    *this = Json(Array{});
  return array_;
}

Json::Object &Json::object() {
  if (!isObject())
    *this = Json(Object{});
  return object_;
}

const Json &Json::operator[](std::string_view key) const {
  if (!isObject())
    return nullJson();
  auto it = object_.find(std::string(key));
  return it == object_.end() ? nullJson() : it->second;
}

bool Json::has(std::string_view key) const {
  return isObject() && object_.count(std::string(key));
}

std::string Json::dump() const {
  std::string out;
  dump(out);
  return out;
}

void Json::dump(std::string &out) const {
  switch (kind_) {
  case Kind::Null:
    out += "null";
    break;
  case Kind::Bool:
    out += bool_ ? "true" : "false";
    break;
  case Kind::Number:
    appendNumber(out, number_);
    break;
  case Kind::String:
    escape(out, string_);
    break;
  case Kind::Array: {
    out += '[';
    for (size_t i = 0; i < array_.size(); ++i) {
      if (i)
        out += ',';
      array_[i].dump(out);
    }
    out += ']';
    break;
  }
  case Kind::Object: {
    out += '{';
    bool first = true;
    for (const auto &[k, v] : object_) {
      if (!first)
        out += ',';
      first = false;
      escape(out, k);
      out += ':';
      v.dump(out);
    }
    out += '}';
    break;
  }
  }
}

std::optional<Json> Json::parse(std::string_view text) {
  return Reader(text).document();
}

} // namespace pia::lsp
