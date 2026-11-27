// pia-cert: reads and checks the proof certificates in Pia objects
// (docs/abi.md, src/cert/Certificate.h).
//
//   pia-cert dump <object>         print the object's certificate
//   pia-cert check [--stamp=<file>] <object>...
//                                  check that the objects link: every
//                                  interface one imports is provided by
//                                  another, with the hash it was proved
//                                  against. --stamp writes the result to
//                                  <file> too, for a build to depend on.
//
// Exit status: 0 when the check passes, 1 when it fails, 2 on bad usage
// or an object that cannot be read.

#include <fstream>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

#include "cert/Certificate.h"

namespace {

int usage() {
  std::cerr << "usage: pia-cert dump <object>\n"
               "       pia-cert check [--stamp=<file>] <object>...\n";
  return 2;
}

} // namespace

int main(int argc, char **argv) {
  if (argc < 3)
    return usage();
  std::string command = argv[1];
  if (command != "dump" && command != "check")
    return usage();
  if (command == "dump" && argc != 3)
    return usage();
  std::vector<std::pair<std::string, pia::cert::Certificate>> objects;
  std::string stamp;
  int first = 2;
  if (command == "check" && std::string(argv[2]).rfind("--stamp=", 0) == 0) {
    stamp = std::string(argv[2]).substr(8);
    if (stamp.empty() || argc < 4)
      return usage();
    first = 3;
  }
  for (int i = first; i < argc; ++i) {
    pia::cert::Read r = pia::cert::readObject(argv[i]);
    if (!r.error.empty()) {
      std::cerr << "pia-cert: " << argv[i] << ": " << r.error << "\n";
      return 2;
    }
    // An object without a certificate is not Pia's (a C harness, say), and
    // the check has nothing to say about it.
    if (!r.cert) {
      if (command == "dump") {
        std::cerr << "pia-cert: " << argv[i] << " has no Pia certificate\n";
        return 2;
      }
      continue;
    }
    objects.emplace_back(argv[i], std::move(*r.cert));
  }
  if (command == "dump") {
    const pia::cert::Certificate &c = objects.front().second;
    std::cout << "module " << (c.module.empty() ? "(program)" : c.module)
              << "\n";
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
    for (const pia::cert::LeanFact &f : c.lean) {
      std::cout << "proved lean " << f.name << " " << f.statement << " by "
                << f.theorem << " (" << f.toolchain << "; axioms";
      for (const std::string &a : f.axioms)
        std::cout << " " << a;
      std::cout << (f.axioms.empty() ? " none)\n" : ")\n");
    }
    return 0;
  }
  std::vector<std::string> problems = pia::cert::checkLink(objects);
  for (const std::string &p : problems)
    std::cerr << "pia-cert: " << p << "\n";
  if (!problems.empty())
    return 1;
  std::string result =
      "pia-cert: " + std::to_string(objects.size()) +
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
