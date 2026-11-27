// Proof certificates in Pia objects (docs/abi.md, ADR 0024 and ADR 0039
// step 6).
//
// Every object piac writes carries one certificate, in the section
// `__TEXT,__pia_cert` on Mach-O and `.pia_cert` on ELF. It says which
// module the object holds, the hash of each interface the module provides,
// and the hash of each interface it imports, as proved against. piac writes
// an object only when every goal is proved, so a certificate stands for
// those proofs. `pia-cert check` reads the certificates of the objects of a
// program and refuses one that was proved against an interface no object
// provides, or provides differently.
//
// Format 1 is a header, the four bytes "PIAC", the format version and the
// body's length as little-endian 32-bit integers, then a body of lines:
//
//   module Image.Pixels
//   provides Image.Pixels.Ops <SHA-256 of the .piai text, hex>
//   requires Image.Pixels.Ops <hash>
//
// A program without a module header writes `module` with no name.
//
// Format 2 adds the module's own trusted items, one line each (ADR 0024,
// ADR 0065). The first kind is a lowering, a function whose
// MLIR form replaced its proved body, with the SHA-256 of that MLIR and the
// ops it uses, or `-` for none:
//
//   trusted lowering matmul <hash> linalg.matmul,memref.expand_shape
//
// Format 3 adds who proved the module and for which ABI (ADR 0073), after
// the `module` line:
//
//   abi 1 arm64-apple-macos
//   prover piac 0.0.0+512.9f3c2e1a7b04
//   solver z3 5.4.1
//   engines intervals,z3
//
// `abi` is the Pia ABI version and the target triple, which the link check
// requires to be the same in every object. `prover` is piac's version, or
// `dev` in a build without stamping. `solver` names each SMT solver that
// may have decided a goal, with its version. `engines` is the set of proof
// engines that discharged at least one goal; a certificate without the line
// does not say, so an advisory naming engines matches it (ADR 0073). piac
// writes format 3; formats
// 1 and 2 are still read, as objects with no ABI version, which the link
// check refuses.
//
// A second kind, `native_decide`, is a lemma whose Lean proof trusts Lean's
// compiler, with its statement hash and the compiler's axioms (ADR 0061):
//
//   trusted native_decide six <hash> six._native.native_decide.ax_1_1
//
// Format 3 also holds the lemmas proved in Lean (ADR 0061, section 4), as
// `proved lean` lines, the spelling ADR 0073 gives them. They are
// not trusted, since Lean's kernel checked them, but a third status: the
// lemma, the SHA-256 of its Lean statement and the definitions it uses, the
// theorem that proves it, the Lean toolchain and the axioms the proof uses,
// or `-` for none:
//
//   proved lean sum_nonneg <hash> Proofs.sum_nonneg <toolchain> propext

#ifndef PIA_CERT_CERTIFICATE_H
#define PIA_CERT_CERTIFICATE_H

#include <optional>
#include <string>
#include <string_view>
#include <vector>

namespace pia::cert {

// The newest format this code reads and writes.
inline constexpr unsigned kFormat = 3;

// The Pia ABI version (docs/abi.md, ADR 0073): the calling convention, the
// canonical interface serialisation and what a certificate means. Bump it
// rarely and on purpose: the link check refuses objects built for another.
inline constexpr unsigned kAbiVersion = 1;

// The section a certificate is in, for the target `triple`.
std::string sectionFor(std::string_view triple);

struct Interface {
  std::string name; // `Image.Pixels.Ops`
  std::string hash; // SHA-256 of its canonical artifact, lowercase hex
};

// A trusted item of the module (docs/abi.md, "Trusted items").
struct Trusted {
  std::string kind;                // `lowering`, `native_decide`
  std::string name;                // the function
  std::string hash;                // SHA-256 of what is trusted, hex
  std::vector<std::string> detail; // for a lowering, the ops it uses
};

// A solver that may have decided one of the module's goals.
struct Solver {
  std::string name;    // `z3`
  std::string version; // `5.4.1`
};

// A lemma proved in Lean (ADR 0061, section 4).
struct LeanFact {
  std::string name;                // the lemma
  std::string statement;           // SHA-256 of its Lean closure, hex
  std::string theorem;             // the Lean theorem that proves it
  std::string toolchain;           // `leanprover/lean4:v4.36.0`
  std::vector<std::string> axioms; // what `#print axioms` reports
};

struct Certificate {
  std::string module; // empty for a program without a header
  unsigned abi = 0;   // the Pia ABI version; 0 in formats 1 and 2
  std::string target; // the target triple, with `abi`
  std::string prover; // piac's version, `dev` unstamped; empty before 3
  std::vector<Solver> solvers;
  // The proof engines used, or nothing when the certificate does not say.
  std::optional<std::vector<std::string>> engines;
  std::vector<Interface> provides, requires_;
  std::vector<Trusted> trusted;
  std::vector<LeanFact> lean;
};

// The SHA-256 of an interface artifact's text, in lowercase hex.
std::string interfaceHash(std::string_view text);

std::string encode(const Certificate &c);

// The certificate in `bytes`, or nothing, with `error` set, when they are
// not one.
std::optional<Certificate> decode(std::string_view bytes, std::string &error);

// The certificate in the object file at `path`, nothing when it has none,
// or an error.
struct Read {
  std::optional<Certificate> cert;
  std::string error;
};
Read readObject(const std::string &path);

// What is wrong with linking `objects` (path and certificate) together:
// an interface required but not provided, or provided with another hash
// than the one required, or provided twice with different hashes, or an
// object with no ABI version, or objects for different ABI versions or
// targets. Empty when nothing is.
std::vector<std::string>
checkLink(const std::vector<std::pair<std::string, Certificate>> &objects);

} // namespace pia::cert

#endif // PIA_CERT_CERTIFICATE_H
