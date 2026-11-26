// Raw binary embedding: @embed attribute parsing and hermetic file resolution
// (ADR 0070).

#include "syntax/Embeds.h"

#include <cctype>
#include <filesystem>
#include <fstream>
#include <set>

namespace pia::syntax {

namespace {

// Unescapes a Pia string literal token (`"..."`). Returns nullopt if it
// contains an embedded NUL byte.
std::optional<std::string> unescapeString(std::string_view spelling) {
  if (spelling.size() < 2 || spelling.front() != '"' || spelling.back() != '"')
    return std::nullopt;
  std::string out;
  out.reserve(spelling.size() - 2);
  for (size_t i = 1; i + 1 < spelling.size(); ++i) {
    char c = spelling[i];
    if (c == '\\' && i + 2 < spelling.size()) {
      char e = spelling[++i];
      if (e == '0')
        return std::nullopt;
      out += e == 'n' ? '\n' : e == 't' ? '\t' : e == 'r' ? '\r' : e;
    } else {
      if (c == '\0')
        return std::nullopt;
      out += c;
    }
  }
  return out;
}

// Parses an unsuffixed non-negative integer literal (decimal, 0x, 0o, 0b, `_`).
std::optional<uint64_t> parseUnsignedLit(std::string_view s) {
  unsigned radix = 10;
  if (s.size() > 2 && s[0] == '0' &&
      (s[1] == 'x' || s[1] == 'o' || s[1] == 'b')) {
    radix = s[1] == 'x' ? 16 : s[1] == 'o' ? 8 : 2;
    s.remove_prefix(2);
  }
  uint64_t v = 0;
  bool any = false;
  for (char c : s) {
    if (isDigitSeparator(c))
      continue;
    unsigned d = 0;
    if (std::isdigit(static_cast<unsigned char>(c)))
      d = static_cast<unsigned>(c - '0');
    else if (radix == 16 && std::isxdigit(static_cast<unsigned char>(c)))
      d = static_cast<unsigned>(std::tolower(static_cast<unsigned char>(c)) -
                                'a' + 10);
    else
      return std::nullopt;
    if (d >= radix)
      return std::nullopt;
    if (v > (UINT64_MAX - d) / radix)
      return std::nullopt;
    v = v * radix + d;
    any = true;
  }
  if (!any)
    return std::nullopt;
  return v;
}

bool validSymbolName(std::string_view s) {
  if (s.empty())
    return false;
  unsigned char first = static_cast<unsigned char>(s[0]);
  if (!(std::isalpha(first) || first == '_' || first == '$'))
    return false;
  for (char ch : s) {
    unsigned char c = static_cast<unsigned char>(ch);
    if (!(std::isalnum(c) || c == '_' || c == '$'))
      return false;
  }
  return true;
}

std::optional<std::vector<uint8_t>>
readBinaryFile(const std::filesystem::path &p, std::string &errOut) {
  std::error_code ec;
  if (!std::filesystem::exists(p, ec) || ec) {
    errOut = "does not exist";
    return std::nullopt;
  }
  if (std::filesystem::is_directory(p, ec) || ec) {
    errOut = "is a directory";
    return std::nullopt;
  }
  std::ifstream in(p, std::ios::binary | std::ios::ate);
  if (!in) {
    errOut = "cannot be opened";
    return std::nullopt;
  }
  std::streampos endPos = in.tellg();
  if (endPos < 0) {
    errOut = "cannot be read";
    return std::nullopt;
  }
  size_t size = static_cast<size_t>(endPos);
  in.seekg(0, std::ios::beg);
  std::vector<uint8_t> bytes(size);
  if (size > 0 && !in.read(reinterpret_cast<char *>(bytes.data()),
                           static_cast<std::streamsize>(size))) {
    errOut = "failed while reading";
    return std::nullopt;
  }
  return bytes;
}

} // namespace

bool parseEmbedFlag(std::string_view arg, EmbedOptions &options,
                    bool &invalid) {
  invalid = false;
  if (arg.rfind("--embed-path=", 0) == 0) {
    std::string_view dir = arg.substr(13);
    if (dir.empty()) {
      invalid = true;
      return false;
    }
    options.searchPaths.emplace_back(dir);
    return true;
  }
  if (arg.rfind("--embed=", 0) == 0) {
    std::string_view spec = arg.substr(8);
    size_t eq = spec.find('=');
    if (eq == std::string_view::npos || eq == 0 || eq + 1 == spec.size()) {
      invalid = true;
      return false;
    }
    std::string logical(spec.substr(0, eq));
    std::string physical(spec.substr(eq + 1));
    options.explicitMaps[std::move(logical)] = std::move(physical);
    return true;
  }
  return false;
}

bool hasEmbedAttr(const Node &retAnnot) {
  if (retAnnot.kind != NodeKind::RetAnnot || retAnnot.kids.size() < 2)
    return false;
  const Node &attrs = *retAnnot.kids[1];
  if (attrs.kind != NodeKind::Attrs)
    return false;
  for (const NodePtr &a : attrs.kids)
    if (a->kind == NodeKind::Attribute && a->text == "embed")
      return true;
  return false;
}

const Node *findEmbedAttr(const Node &letItem) {
  if (letItem.kind != NodeKind::LetItem || letItem.kids.size() < 2)
    return nullptr;
  const Node &ret = *letItem.kids[1];
  if (ret.kind != NodeKind::RetAnnot || ret.kids.size() < 2)
    return nullptr;
  const Node &attrs = *ret.kids[1];
  if (attrs.kind != NodeKind::Attrs)
    return nullptr;
  for (const NodePtr &a : attrs.kids)
    if (a->kind == NodeKind::Attribute && a->text == "embed")
      return a.get();
  return nullptr;
}

size_t countEmbedAttrs(const Node &letItem) {
  if (letItem.kind != NodeKind::LetItem || letItem.kids.size() < 2)
    return 0;
  const Node &ret = *letItem.kids[1];
  if (ret.kind != NodeKind::RetAnnot || ret.kids.size() < 2)
    return 0;
  const Node &attrs = *ret.kids[1];
  if (attrs.kind != NodeKind::Attrs)
    return 0;
  size_t count = 0;
  for (const NodePtr &a : attrs.kids)
    if (a->kind == NodeKind::Attribute && a->text == "embed")
      ++count;
  return count;
}

std::optional<std::string> validateEmbedPath(std::string_view path) {
  if (path.empty())
    return "path must not be empty";
  if (path.front() == '/' || path.front() == '\\')
    return "absolute paths are not allowed; use a relative path with "
           "--embed-path or --embed";
  if (path.size() >= 2 && std::isalpha(static_cast<unsigned char>(path[0])) &&
      path[1] == ':')
    return "absolute paths with a drive prefix are not allowed; use a "
           "relative path with --embed-path or --embed";
  if (path.find('\\') != std::string_view::npos)
    return "use '/' as the path separator in @embed(file = \"...\")";
  if (path.find('\0') != std::string_view::npos)
    return "path must not contain NUL bytes";
  if (path.back() == '/')
    return "path must name a file, not a directory";
  size_t pos = 0;
  while (pos <= path.size()) {
    size_t slash = path.find('/', pos);
    std::string_view part = slash == std::string_view::npos
                                ? path.substr(pos)
                                : path.substr(pos, slash - pos);
    if (part == "..")
      return "parent directory traversal ('..') is not allowed in "
             "@embed(file = \"...\")";
    if (part.empty())
      return "path must not contain empty segments ('//')";
    if (slash == std::string_view::npos)
      break;
    pos = slash + 1;
  }
  return std::nullopt;
}

std::optional<EmbedSpec> parseEmbedAttr(const Node &attr, Diagnostics &diags) {
  if (attr.kind != NodeKind::Attribute || attr.text != "embed") {
    diags.error(attr.loc, "expected an @embed(...) attribute");
    return std::nullopt;
  }
  if (attr.kids.empty()) {
    diags.error(attr.loc,
                "@embed requires file = \"<path>\" (e.g. @embed(file = "
                "\"blob.bin\"))");
    return std::nullopt;
  }

  EmbedSpec spec;
  std::set<std::string> seen;
  bool ok = true;
  for (const NodePtr &arg : attr.kids) {
    if (arg->kind != NodeKind::NamedArg || arg->kids.size() != 1) {
      diags.error(
          arg->loc,
          "@embed arguments must be named: file = \"...\", "
          "symbol = \"...\", section = \"...\", align = <power-of-two>");
      ok = false;
      continue;
    }
    const std::string &key = arg->text;
    if (!seen.insert(key).second) {
      diags.error(arg->loc, "duplicate @embed argument '" + key + "'");
      ok = false;
      continue;
    }
    const Node &val = *arg->kids[0];
    if (key == "file") {
      if (val.kind != NodeKind::StringLit) {
        diags.error(val.loc, "@embed 'file' must be a string literal");
        ok = false;
        continue;
      }
      auto s = unescapeString(val.text);
      if (!s) {
        diags.error(val.loc, "@embed 'file' string literal is invalid");
        ok = false;
        continue;
      }
      if (auto why = validateEmbedPath(*s)) {
        diags.error(val.loc, "@embed(file = \"" + *s + "\"): " + *why);
        ok = false;
        continue;
      }
      spec.file = std::move(*s);
    } else if (key == "symbol") {
      if (val.kind != NodeKind::StringLit) {
        diags.error(val.loc, "@embed 'symbol' must be a string literal");
        ok = false;
        continue;
      }
      auto s = unescapeString(val.text);
      if (!s || !validSymbolName(*s)) {
        diags.error(val.loc,
                    "@embed 'symbol' must be a non-empty C/linker identifier "
                    "matching [A-Za-z_$][A-Za-z0-9_$]*");
        ok = false;
        continue;
      }
      spec.symbol = std::move(*s);
      spec.hasExplicitSymbol = true;
    } else if (key == "section") {
      if (val.kind != NodeKind::StringLit) {
        diags.error(val.loc, "@embed 'section' must be a string literal");
        ok = false;
        continue;
      }
      auto s = unescapeString(val.text);
      if (!s || s->empty() || s->find('\n') != std::string::npos ||
          s->find('\r') != std::string::npos) {
        diags.error(val.loc,
                    "@embed 'section' must be a non-empty single-line string");
        ok = false;
        continue;
      }
      spec.section = std::move(*s);
    } else if (key == "align") {
      if (val.kind != NodeKind::IntLit) {
        diags.error(val.loc,
                    "@embed 'align' must be a positive power-of-two integer");
        ok = false;
        continue;
      }
      auto n = parseUnsignedLit(val.text);
      // LLVM supports alignments up to 2^29, and 1 MiB covers every page/GPU
      // alignment in practice while guarding against absurd values.
      if (!n || *n == 0 || (*n & (*n - 1)) != 0 || *n > (1ULL << 20)) {
        diags.error(val.loc,
                    "@embed 'align' must be a positive power of two (at most "
                    "1048576)");
        ok = false;
        continue;
      }
      spec.align = *n;
    } else {
      diags.error(arg->loc,
                  "unknown @embed argument '" + key +
                      "'; expected 'file', 'symbol', 'section' or 'align'");
      ok = false;
    }
  }
  if (!seen.count("file")) {
    diags.error(attr.loc, "@embed requires file = \"<path>\"");
    ok = false;
  }
  if (!ok)
    return std::nullopt;
  return spec;
}

std::optional<std::vector<uint8_t>>
resolveEmbedFile(const std::string &logicalPath, const EmbedOptions &options,
                 SourceLoc loc, Diagnostics &diags) {
  if (auto why = validateEmbedPath(logicalPath)) {
    diags.error(loc, "@embed(file = \"" + logicalPath + "\"): " + *why);
    return std::nullopt;
  }

  // 1. Explicit `--embed=<logical>=<physical>` mapping takes precedence.
  if (auto it = options.explicitMaps.find(logicalPath);
      it != options.explicitMaps.end()) {
    std::string err;
    auto bytes = readBinaryFile(it->second, err);
    if (!bytes) {
      diags.error(loc, "embedded file '" + logicalPath + "' (mapped to '" +
                           it->second + "') " + err);
      return std::nullopt;
    }
    return bytes;
  }

  // 2. Search `--embed-path=<dir>` roots in flag order.
  for (const std::string &root : options.searchPaths) {
    std::filesystem::path candidate = std::filesystem::path(root) / logicalPath;
    std::error_code ec;
    if (!std::filesystem::exists(candidate, ec) || ec)
      continue;
    std::string err;
    auto bytes = readBinaryFile(candidate, err);
    if (!bytes) {
      diags.error(loc, "embedded file '" + logicalPath + "' at '" +
                           candidate.string() + "' " + err);
      return std::nullopt;
    }
    return bytes;
  }

  // Not found under any declared mapping or root.
  std::string msg = "embedded file '" + logicalPath + "' was not found";
  if (options.searchPaths.empty() && options.explicitMaps.empty()) {
    msg += "; pass --embed-path=<dir> or --embed=" + logicalPath + "=<path>";
  } else if (!options.searchPaths.empty()) {
    msg += "; searched --embed-path roots:";
    for (size_t i = 0; i < options.searchPaths.size(); ++i)
      msg += (i ? ", '" : " '") + options.searchPaths[i] + "'";
  } else {
    msg += "; no matching --embed=<logical>=<physical> mapping was given";
  }
  diags.error(loc, std::move(msg));
  return std::nullopt;
}

} // namespace pia::syntax
