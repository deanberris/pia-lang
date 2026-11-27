#include "cert/Certificate.h"

#include <array>
#include <map>
#include <sstream>

#include "llvm/ADT/StringExtras.h"
#include "llvm/Object/ObjectFile.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/SHA256.h"

namespace pia::cert {

namespace {

constexpr char kMagic[] = "PIAC";
constexpr size_t kHeader = 12; // magic, format, body length

void putU32(std::string &out, uint32_t v) {
  for (int i = 0; i < 4; ++i)
    out += char((v >> (8 * i)) & 0xff);
}

uint32_t getU32(std::string_view in, size_t at) {
  uint32_t v = 0;
  for (int i = 0; i < 4; ++i)
    v |= uint32_t(uint8_t(in[at + i])) << (8 * i);
  return v;
}

// The section's name as an object file lists it, without the segment.
bool isCertSection(llvm::StringRef name) {
  return name == "__pia_cert" || name == ".pia_cert";
}

// The rest of a `trusted <kind> <name> <hash> <detail>` line, whose first
// two words are already read as `kind` and `name`.
bool readTrusted(std::istringstream &words, const std::string &kind,
                 const std::string &name, Certificate &c) {
  std::string hash, detail;
  words >> hash >> detail;
  if (kind.empty() || name.empty() || hash.size() != 64 || detail.empty())
    return false;
  Trusted t{kind, name, hash, {}};
  if (detail != "-")
    for (llvm::StringRef d : llvm::split(detail, ','))
      t.detail.push_back(d.str());
  c.trusted.push_back(std::move(t));
  return true;
}

// The rest of an `abi <version> <triple>` line. Version 0 means "none", so
// it is not a version a certificate can state.
bool readAbi(const std::string &version, const std::string &triple,
             Certificate &c) {
  if (version.empty() || triple.empty() ||
      version.find_first_not_of("0123456789") != std::string::npos ||
      version.size() > 9)
    return false;
  c.abi = unsigned(std::stoul(version));
  c.target = triple;
  return c.abi != 0;
}

// The rest of a `proved lean <name> <hash> <theorem> <toolchain> <axioms>`
// line, whose first three words are already read.
bool readLean(std::istringstream &words, const std::string &name,
              Certificate &c) {
  std::string hash, theorem, toolchain, axioms;
  words >> hash >> theorem >> toolchain >> axioms;
  if (name.empty() || hash.size() != 64 || theorem.empty() ||
      toolchain.empty() || axioms.empty())
    return false;
  LeanFact f{name, hash, theorem, toolchain, {}};
  if (axioms != "-")
    for (llvm::StringRef a : llvm::split(axioms, ','))
      f.axioms.push_back(a.str());
  c.lean.push_back(std::move(f));
  return true;
}

std::string joined(const std::vector<std::string> &items) {
  std::string out;
  for (const std::string &i : items)
    out += (out.empty() ? "" : ",") + i;
  return out.empty() ? "-" : out;
}

} // namespace

std::string sectionFor(std::string_view triple) {
  bool macho = triple.find("apple") != std::string_view::npos ||
               triple.find("darwin") != std::string_view::npos ||
               triple.find("macos") != std::string_view::npos;
  return macho ? "__TEXT,__pia_cert" : ".pia_cert";
}

std::string interfaceHash(std::string_view text) {
  std::array<uint8_t, 32> digest = llvm::SHA256::hash(llvm::ArrayRef<uint8_t>(
      reinterpret_cast<const uint8_t *>(text.data()), text.size()));
  return llvm::toHex(digest, /*LowerCase=*/true);
}

std::string encode(const Certificate &c) {
  std::string body = "module";
  if (!c.module.empty())
    body += " " + c.module;
  body += "\n";
  if (c.abi != 0)
    body += "abi " + std::to_string(c.abi) + " " + c.target + "\n";
  if (!c.prover.empty())
    body += "prover piac " + c.prover + "\n";
  for (const Solver &s : c.solvers)
    body += "solver " + s.name + " " + s.version + "\n";
  if (c.engines) {
    std::string list;
    // An engine name is one word without commas, or the line would not
    // read back, so a name that is not one is left out.
    for (const std::string &e : *c.engines)
      if (!e.empty() && e.find_first_of(", \t\n") == std::string::npos)
        list += (list.empty() ? "" : ",") + e;
    body += "engines " + (list.empty() ? "-" : list) + "\n";
  }
  for (const Interface &i : c.provides)
    body += "provides " + i.name + " " + i.hash + "\n";
  for (const Interface &i : c.requires_)
    body += "requires " + i.name + " " + i.hash + "\n";
  for (const Trusted &t : c.trusted)
    body += "trusted " + t.kind + " " + t.name + " " + t.hash + " " +
            joined(t.detail) + "\n";
  for (const LeanFact &f : c.lean)
    body += "proved lean " + f.name + " " + f.statement + " " + f.theorem +
            " " + f.toolchain + " " + joined(f.axioms) + "\n";
  std::string out(kMagic, 4);
  putU32(out, kFormat);
  putU32(out, uint32_t(body.size()));
  return out + body;
}

std::optional<Certificate> decode(std::string_view bytes, std::string &error) {
  if (bytes.size() < kHeader || bytes.substr(0, 4) != kMagic) {
    error = "not a Pia certificate";
    return std::nullopt;
  }
  uint32_t format = getU32(bytes, 4);
  if (format < 1 || format > kFormat) {
    error = "certificate format " + std::to_string(format) +
            " is not supported (this tool reads formats 1 to " +
            std::to_string(kFormat) + ")";
    return std::nullopt;
  }
  uint32_t size = getU32(bytes, 8);
  if (bytes.size() < kHeader + size) {
    error = "the certificate is truncated";
    return std::nullopt;
  }
  Certificate c;
  std::istringstream lines(std::string(bytes.substr(kHeader, size)));
  std::string line;
  bool sawModule = false;
  while (std::getline(lines, line)) {
    std::istringstream words(line);
    std::string kind, name, hash;
    words >> kind >> name >> hash;
    if (kind == "module" && !sawModule) {
      c.module = name;
      sawModule = true;
    } else if (kind == "abi" && format >= 3 && c.abi == 0 &&
               readAbi(name, hash, c)) {
      continue;
    } else if (kind == "prover" && format >= 3 && name == "piac" &&
               !hash.empty() && c.prover.empty()) {
      c.prover = hash;
    } else if (kind == "solver" && format >= 3 && !name.empty() &&
               !hash.empty()) {
      c.solvers.push_back({name, hash});
    } else if (kind == "engines" && format >= 3 && !name.empty() &&
               hash.empty() && !c.engines) {
      c.engines.emplace();
      if (name != "-")
        for (llvm::StringRef e : llvm::split(name, ','))
          c.engines->push_back(e.str());
    } else if ((kind == "provides" || kind == "requires") &&
               hash.size() == 64) {
      (kind == "provides" ? c.provides : c.requires_).push_back({name, hash});
    } else if (kind == "trusted" && format >= 2 &&
               readTrusted(words, name, hash, c)) {
      continue;
    } else if (kind == "proved" && name == "lean" && format >= 3 &&
               readLean(words, hash, c)) {
      continue;
    } else {
      error = "the certificate has a malformed line: '" + line + "'";
      return std::nullopt;
    }
  }
  if (!sawModule) {
    error = "the certificate names no module";
    return std::nullopt;
  }
  return c;
}

Read readObject(const std::string &path) {
  Read r;
  llvm::Expected<llvm::object::OwningBinary<llvm::object::ObjectFile>> file =
      llvm::object::ObjectFile::createObjectFile(path);
  if (!file) {
    r.error = llvm::toString(file.takeError());
    return r;
  }
  for (const llvm::object::SectionRef &s : file->getBinary()->sections()) {
    llvm::Expected<llvm::StringRef> name = s.getName();
    if (!name) {
      llvm::consumeError(name.takeError());
      continue;
    }
    if (!isCertSection(*name))
      continue;
    llvm::Expected<llvm::StringRef> contents = s.getContents();
    if (!contents) {
      r.error = llvm::toString(contents.takeError());
      return r;
    }
    r.cert = decode(*contents, r.error);
    return r;
  }
  return r;
}

std::vector<std::string>
checkLink(const std::vector<std::pair<std::string, Certificate>> &objects) {
  std::vector<std::string> problems;
  // Every object must be for the same ABI and target. The first object
  // with an ABI version is the one the others are compared with, so the
  // message names a pair of objects that disagree.
  const std::pair<std::string, Certificate> *first = nullptr;
  for (const auto &object : objects) {
    const auto &[path, cert] = object;
    if (cert.abi == 0) {
      problems.push_back("'" + path +
                         "' records no Pia ABI version, so it was built by a "
                         "piac older than certificate format 3: compile it "
                         "again");
      continue;
    }
    if (!first) {
      first = &object;
      continue;
    }
    if (cert.abi != first->second.abi)
      problems.push_back("'" + path + "' was built for Pia ABI " +
                         std::to_string(cert.abi) + ", but '" + first->first +
                         "' for Pia ABI " + std::to_string(first->second.abi) +
                         ": compile them with the same piac");
    else if (cert.target != first->second.target)
      problems.push_back("'" + path + "' was built for " + cert.target +
                         ", but '" + first->first + "' for " +
                         first->second.target);
  }
  // Each interface, by name, the hash provided and the object providing it.
  std::map<std::string, std::pair<std::string, std::string>> provided;
  for (const auto &[path, cert] : objects)
    for (const Interface &i : cert.provides) {
      auto [it, fresh] = provided.emplace(i.name, std::pair{i.hash, path});
      if (!fresh && it->second.first != i.hash)
        problems.push_back("'" + it->second.second + "' and '" + path +
                           "' both provide '" + i.name +
                           "', with different hashes");
    }
  for (const auto &[path, cert] : objects)
    for (const Interface &i : cert.requires_) {
      auto it = provided.find(i.name);
      if (it == provided.end()) {
        problems.push_back("'" + path + "' imports '" + i.name +
                           "', which no object provides");
        continue;
      }
      if (it->second.first != i.hash)
        problems.push_back(
            "'" + path + "' was proved against '" + i.name + "' " +
            i.hash.substr(0, 12) + "..., but '" + it->second.second +
            "' provides " + it->second.first.substr(0, 12) +
            "...: the interface changed, so prove and compile '" + path +
            "' again");
    }
  return problems;
}

} // namespace pia::cert
