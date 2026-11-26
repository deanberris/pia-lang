// Raw binary embedding: @embed(file = ..., symbol = ..., section = ..., align = ...)
// (ADR 0070).
//
// Parses @embed attributes on top-level fixed `let` bindings and resolves
// their relative paths hermetically against explicit --embed mappings and
// --embed-path search roots. No LLVM dependency, so the front end builds it
// standalone.

#ifndef PIA_SYNTAX_EMBEDS_H
#define PIA_SYNTAX_EMBEDS_H

#include <cstdint>
#include <map>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "syntax/Diagnostics.h"
#include "syntax/Syntax.h"

namespace pia::syntax {

// Hermetic file lookup configuration from CLI flags (`--embed-path`, `--embed`).
struct EmbedOptions {
  // Search directories checked in flag order (`--embed-path=<dir>`).
  std::vector<std::string> searchPaths;
  // Explicit logical-to-physical mappings (`--embed=<logical>=<physical>`),
  // checked before `searchPaths`.
  std::map<std::string, std::string> explicitMaps;
};

// Parsed arguments of `@embed(...)`.
struct EmbedSpec {
  std::string file;
  std::string symbol;
  std::string section;
  uint64_t align = 8;
  bool hasExplicitSymbol = false;
};

// A resolved binary blob ready for IRGen and direct LLVM emission.
struct EmbeddedBlob {
  std::string name;     // Pia binding name
  std::string file;     // logical relative path from @embed(file = "...")
  std::string symbol;   // emitted LLVM/linker symbol name
  std::string section;  // optional target object section
  uint64_t align = 8;
  bool isExternal = false;
  bool emitLenSymbol = false;
  std::vector<uint8_t> bytes;
};

// Parses `--embed-path=<dir>` or `--embed=<logical>=<physical>` into `options`.
// Returns true if `arg` was one of those flags and valid; returns false if
// `arg` is not an embed flag. Sets `invalid = true` if it started with
// `--embed-path=` or `--embed=` but was malformed.
bool parseEmbedFlag(std::string_view arg, EmbedOptions &options, bool &invalid);

// Whether a `RetAnnot` node carries an `@embed` attribute.
bool hasEmbedAttr(const Node &retAnnot);

// The `@embed` attribute on a `LetItem`, or null if it has none.
const Node *findEmbedAttr(const Node &letItem);

// Counts how many `@embed` attributes appear on a `LetItem`.
size_t countEmbedAttrs(const Node &letItem);

// Parses and validates `@embed(...)`. Reports errors to `diags` and returns
// nullopt on failure.
std::optional<EmbedSpec> parseEmbedAttr(const Node &attr, Diagnostics &diags);

// Validates that `path` is a safe relative path (no leading `/`, no drive
// prefix, no `\`, no `..`, no NUL). Returns an error message when invalid.
std::optional<std::string> validateEmbedPath(std::string_view path);

// Resolves `logicalPath` strictly via `options.explicitMaps` then
// `options.searchPaths` and reads its raw bytes. Reports an error at `loc`
// and returns nullopt if not found or unreadable.
std::optional<std::vector<uint8_t>> resolveEmbedFile(
    const std::string &logicalPath, const EmbedOptions &options, SourceLoc loc,
    Diagnostics &diags);

}  // namespace pia::syntax

#endif  // PIA_SYNTAX_EMBEDS_H
