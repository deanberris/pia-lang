// pia-cert: reads and checks the proof certificates in Pia objects
// (docs/abi.md, src/cert/Certificate.h, src/cert/Advisory.h).
//
//   pia-cert dump <object>         print the object's certificate
//   pia-cert check [options] <object>...
//                                  check that the objects link: every
//                                  interface one imports is provided by
//                                  another, with the hash it was proved
//                                  against, all for one Pia ABI version
//                                  and target, and none proved by a piac
//                                  or solver an advisory revokes.
//       --stamp=<file>             write the result to <file> too, for a
//                                  build to depend on
//       --advisories=<dir>         add the advisories in <dir>, newer than
//                                  the ones compiled in
//       --accept-advisory=<id>:<module>
//                                  let <module> through although <id>
//                                  revokes it; it becomes a trusted item
//       --require-released         refuse objects from an unstamped piac
//   pia-cert advisories [--advisories=<dir>]
//                                  list the advisories this check applies
//
// Exit status: 0 when the check passes, 1 when it fails, 2 on bad usage
// or an object or advisory that cannot be read.

#include <algorithm>
#include <fstream>
#include <iostream>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "cert/Advisory.h"
#include "cert/Certificate.h"

namespace {

using pia::cert::Advisory;
using pia::cert::Certificate;

int usage() {
  std::cerr << "usage: pia-cert dump <object>\n"
               "       pia-cert check [--stamp=<file>] [--advisories=<dir>]\n"
               "                      [--accept-advisory=<id>:<module>]\n"
               "                      [--require-released] <object>...\n"
               "       pia-cert advisories [--advisories=<dir>]\n";
  return 2;
}

void dump(const Certificate &c) {
  std::cout << "module " << (c.module.empty() ? "(program)" : c.module) << "\n";
  // Formats 1 and 2 record no ABI version or prover (ADR 0073).
  if (c.abi != 0)
    std::cout << "abi " << c.abi << " " << c.target << "\n";
  if (!c.prover.empty())
    std::cout << "prover piac " << c.prover << "\n";
  for (const pia::cert::Solver &v : c.solvers)
    std::cout << "solver " << v.name << " " << v.version << "\n";
  if (c.engines) {
    std::cout << "engines";
    for (size_t i = 0; i < c.engines->size(); ++i)
      std::cout << (i ? "," : " ") << (*c.engines)[i];
    std::cout << (c.engines->empty() ? " -\n" : "\n");
  }
  for (const pia::cert::Interface &i : c.provides)
    std::cout << "provides " << i.name << " " << i.hash << "\n";
  for (const pia::cert::Interface &i : c.requires_)
    std::cout << "requires " << i.name << " " << i.hash << "\n";
  for (const pia::cert::Trusted &t : c.trusted) {
    std::cout << "trusted " << t.kind << " " << t.name << " " << t.hash;
    for (size_t i = 0; i < t.detail.size(); ++i)
      std::cout << (i ? ", " : " (") << t.detail[i];
    std::cout << (t.detail.empty() ? "\n" : ")\n");
  }
}

std::string range(const pia::cert::Range &r) {
  return r.introduced + " to " + (r.fixed.empty() ? "now" : r.fixed);
}

void list(const std::vector<Advisory> &advisories) {
  for (const Advisory &a : advisories) {
    std::cout << a.id << " " << a.severity << "\n";
    std::cout << "  " << a.summary << "\n";
    if (a.piac)
      std::cout << "  piac " << range(*a.piac) << "\n";
    for (const auto &[name, r] : a.solvers)
      std::cout << "  " << name << " " << range(r) << "\n";
    if (!a.engines.empty()) {
      std::cout << "  engines";
      for (size_t i = 0; i < a.engines.size(); ++i)
        std::cout << (i ? "," : " ") << a.engines[i];
      std::cout << "\n";
    }
    if (!a.fixedBy.empty())
      std::cout << "  fixed by " << a.fixedBy << "\n";
  }
}

// The name an object is accepted by: its module, or its path for a
// program without a module header.
std::string nameOf(const std::string &path, const Certificate &c) {
  return c.module.empty() ? path : c.module;
}

} // namespace

int main(int argc, char **argv) {
  if (argc < 2)
    return usage();
  std::string command = argv[1];
  if (command != "dump" && command != "check" && command != "advisories")
    return usage();
  std::string stamp;
  bool requireReleased = false;
  std::vector<std::string> paths;
  std::vector<Advisory> advisories = pia::cert::builtinAdvisories();
  // Each accepted (advisory, module) pair, and whether it was used.
  std::vector<std::pair<std::pair<std::string, std::string>, bool>> accepted;
  for (int i = 2; i < argc; ++i) {
    std::string arg = argv[i];
    if (arg.rfind("--", 0) != 0) {
      paths.push_back(arg);
      continue;
    }
    if (arg.rfind("--advisories=", 0) == 0 && command != "dump") {
      std::string error;
      if (!pia::cert::readAdvisories(arg.substr(13), advisories, error)) {
        std::cerr << "pia-cert: " << error << "\n";
        return 2;
      }
    } else if (arg.rfind("--stamp=", 0) == 0 && command == "check") {
      stamp = arg.substr(8);
      if (stamp.empty())
        return usage();
    } else if (arg.rfind("--accept-advisory=", 0) == 0 && command == "check") {
      std::string what = arg.substr(18);
      size_t colon = what.find(':');
      if (colon == std::string::npos || colon == 0 ||
          colon + 1 == what.size()) {
        std::cerr << "pia-cert: --accept-advisory takes <id>:<module>\n";
        return 2;
      }
      accepted.push_back(
          {{what.substr(0, colon), what.substr(colon + 1)}, false});
    } else if (arg == "--require-released" && command == "check") {
      requireReleased = true;
    } else {
      return usage();
    }
  }
  if (command == "advisories") {
    if (!paths.empty())
      return usage();
    list(advisories);
    return 0;
  }
  if (paths.empty() || (command == "dump" && paths.size() != 1))
    return usage();
  // An acceptance must name a known advisory, so a typo does not let a
  // module through silently later, when an advisory with that id appears.
  for (const auto &entry : accepted) {
    const std::string &id = entry.first.first;
    if (std::none_of(advisories.begin(), advisories.end(),
                     [&](const Advisory &a) { return a.id == id; })) {
      std::cerr << "pia-cert: --accept-advisory names " << id
                << ", which is not a known advisory\n";
      return 2;
    }
  }

  std::vector<std::pair<std::string, Certificate>> objects;
  for (const std::string &path : paths) {
    pia::cert::Read r = pia::cert::readObject(path);
    if (!r.error.empty()) {
      std::cerr << "pia-cert: " << path << ": " << r.error << "\n";
      return 2;
    }
    // An object without a certificate is not Pia's (a C harness, say), and
    // the check has nothing to say about it.
    if (!r.cert) {
      if (command == "dump") {
        std::cerr << "pia-cert: " << path << " has no Pia certificate\n";
        return 2;
      }
      continue;
    }
    objects.emplace_back(path, std::move(*r.cert));
  }
  if (command == "dump") {
    dump(objects.front().second);
    return 0;
  }

  std::vector<std::string> problems = pia::cert::checkLink(objects);
  std::vector<std::string> trusted;
  for (const auto &[path, cert] : objects) {
    std::string name = nameOf(path, cert);
    if (requireReleased && (cert.prover.empty() || cert.prover == "dev"))
      problems.push_back("'" + path + "' was built by an unstamped piac (" +
                         (cert.prover.empty() ? "unknown" : cert.prover) +
                         "), and --require-released refuses those");
    for (const Advisory &a : advisories) {
      std::optional<std::string> why = pia::cert::matches(cert, a);
      if (!why)
        continue;
      auto accept = std::find_if(
          accepted.begin(), accepted.end(), [&](const auto &entry) {
            return entry.first.first == a.id && entry.first.second == name;
          });
      if (accept != accepted.end()) {
        accept->second = true;
        trusted.push_back("trusted advisory " + a.id + " " + name);
        continue;
      }
      std::string fix =
          a.piac && !a.piac->fixed.empty()
              ? "rebuild it with piac " + a.piac->fixed + " or later"
              : "rebuild it with a piac that fixes it";
      if (!a.fixedBy.empty())
        fix += " (" + a.fixedBy + ")";
      problems.push_back(
          "'" + path +
          "': " + (cert.module.empty() ? "the program" : cert.module) + " " +
          *why + ", which " + a.id + " revokes (" + a.summary + "): " + fix +
          ", or accept it with --accept-advisory=" + a.id + ":" + name);
    }
  }
  for (const auto &[pair, used] : accepted)
    if (!used)
      std::cerr << "pia-cert: warning: --accept-advisory=" << pair.first << ":"
                << pair.second << " matches no object, so it can be removed\n";
  for (const std::string &p : problems)
    std::cerr << "pia-cert: " << p << "\n";
  if (!problems.empty())
    return 1;
  std::string result;
  for (const std::string &t : trusted)
    result += "pia-cert: " + t + "\n";
  result += "pia-cert: " + std::to_string(objects.size()) +
            (objects.size() == 1 ? " object links\n" : " objects link\n");
  std::cout << result;
  if (!stamp.empty()) {
    std::ofstream out(stamp);
    out << result;
    if (!out) {
      std::cerr << "pia-cert: cannot write " << stamp << "\n";
      return 2;
    }
  }
  return 0;
}
