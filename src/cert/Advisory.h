// Advisories: which proofs a faulty piac or solver may have got wrong
// (ADR 0073, sections 2 to 4).
//
// An advisory is a small TOML file in security/advisories/, reviewed like
// any other change and compiled into pia-cert:
//
//   id = "PIA-2026-0001"
//   summary = "Termination was checked only for direct recursion"
//   piac = { introduced = "0.0.0+0", fixed = "0.0.0+720" }
//   engines = ["intervals"]   # optional: only certificates naming one
//   solver = { z3 = { introduced = "4.15.0", fixed = "4.15.2" } }
//   lean = []                 # receipt hashes of single Lean proofs
//   severity = "unsound"      # or "incomplete", which never revokes
//   fixed_by = "https://github.com/deanberris/pia-lang/pull/496"
//
// A certificate matches an advisory when its prover is in the piac range,
// or one of its solvers in that solver's range, and, when the advisory
// names engines, the certificate's engines include one of them or the
// certificate does not list its engines. `pia-cert check` refuses an
// object whose certificate matches, unless it is accepted by name.
//
// Only the subset of TOML these files need is read: one `key = value` per
// line, with strings, arrays of strings and inline tables, and `#`
// comments.

#ifndef PIA_CERT_ADVISORY_H
#define PIA_CERT_ADVISORY_H

#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "cert/Certificate.h"

namespace pia::cert {

// The versions an advisory covers: from `introduced`, inclusive, to
// `fixed`, exclusive. An empty `fixed` means no fixed version exists yet.
struct Range {
  std::string introduced, fixed;
};

struct Advisory {
  std::string id;      // `PIA-2026-0001`
  std::string summary; // one line, for messages
  std::optional<Range> piac;
  std::vector<std::pair<std::string, Range>> solvers; // by solver name
  std::vector<std::string> engines;                   // empty: every engine
  std::vector<std::string> lean;                      // Lean receipt hashes
  std::string severity; // `unsound` or `incomplete`
  std::string fixedBy;  // the fix, usually a pull request
};

// The advisory in `text`, or nothing with `error` set.
std::optional<Advisory> parseAdvisory(std::string_view text,
                                      std::string &error);

// The advisories compiled into this tool from security/advisories/.
std::vector<Advisory> builtinAdvisories();

// The advisories in the `*.toml` files of `dir`, added to `into`. An
// advisory whose id is already in `into` replaces it, so a newer set can
// correct an old one. False, with `error` set, when one cannot be read.
bool readAdvisories(const std::string &dir, std::vector<Advisory> &into,
                    std::string &error);

// Orders two versions: negative, zero or positive. piac versions are
// `<release>+<commits on main>.<commit>`: two with commit counts are
// ordered by the count, which orders every build on main, and otherwise
// by the release. Solver versions are dotted numbers.
int compareVersions(std::string_view a, std::string_view b);

bool inRange(std::string_view version, const Range &r);

// Why `c` matches `a`, as the end of a sentence ("was proved by piac
// 0.0.0+402"), or nothing when it does not. An `incomplete` advisory and a
// `dev` prover never match: no range covers an unstamped build, which
// `--require-released` refuses instead.
std::optional<std::string> matches(const Certificate &c, const Advisory &a);

} // namespace pia::cert

#endif // PIA_CERT_ADVISORY_H
