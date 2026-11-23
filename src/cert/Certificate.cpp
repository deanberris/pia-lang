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
  for (const Interface &i : c.provides)
    body += "provides " + i.name + " " + i.hash + "\n";
  for (const Interface &i : c.requires_)
    body += "requires " + i.name + " " + i.hash + "\n";
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
  if (uint32_t format = getU32(bytes, 4); format != kFormat) {
    error = "certificate format " + std::to_string(format) +
            " is not supported (this tool reads format " +
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
    } else if ((kind == "provides" || kind == "requires") &&
               hash.size() == 64) {
      (kind == "provides" ? c.provides : c.requires_).push_back({name, hash});
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
