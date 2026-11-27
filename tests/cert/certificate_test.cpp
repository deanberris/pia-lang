#include "cert/Certificate.h"

#include <string>
#include <utility>
#include <vector>

#include "gtest/gtest.h"

using namespace pia::cert;

namespace {

const std::string kHash(64, 'a');

Certificate make(std::string module, unsigned abi = kAbiVersion,
                 std::string target = "arm64-apple-macos") {
  Certificate c;
  c.module = std::move(module);
  c.abi = abi;
  c.target = std::move(target);
  c.prover = "0.0.0+512.9f3c2e1a7b04";
  c.solvers.push_back({"z3", "5.4.1"});
  return c;
}

// A certificate in format `format`, with `body` as its text.
std::string raw(unsigned format, const std::string &body) {
  std::string out = "PIAC";
  for (unsigned v : {format, unsigned(body.size())})
    for (int i = 0; i < 4; ++i)
      out += char((v >> (8 * i)) & 0xff);
  return out + body;
}

TEST(Certificate, Format3RoundTrips) {
  Certificate c = make("Image.Pixels");
  c.provides.push_back({"Image.Pixels.Ops", kHash});
  c.trusted.push_back({"lowering", "matmul", kHash, {"linalg.matmul"}});
  std::string error;
  std::optional<Certificate> d = decode(encode(c), error);
  ASSERT_TRUE(d) << error;
  EXPECT_EQ(d->module, "Image.Pixels");
  EXPECT_EQ(d->abi, kAbiVersion);
  EXPECT_EQ(d->target, "arm64-apple-macos");
  EXPECT_EQ(d->prover, "0.0.0+512.9f3c2e1a7b04");
  ASSERT_EQ(d->solvers.size(), 1u);
  EXPECT_EQ(d->solvers[0].name, "z3");
  EXPECT_EQ(d->solvers[0].version, "5.4.1");
  ASSERT_EQ(d->trusted.size(), 1u);
  EXPECT_EQ(encode(*d), encode(c));
}

TEST(Certificate, Format2ReadsWithNoAbi) {
  std::string error;
  std::optional<Certificate> d =
      decode(raw(2, "module M\nprovides M.I " + kHash + "\n"), error);
  ASSERT_TRUE(d) << error;
  EXPECT_EQ(d->abi, 0u);
  EXPECT_TRUE(d->prover.empty());
}

TEST(Certificate, AbiLinesNeedFormat3) {
  std::string error;
  EXPECT_FALSE(decode(raw(2, "module M\nabi 1 arm64-apple-macos\n"), error));
  EXPECT_FALSE(decode(raw(3, "module M\nabi 0 arm64-apple-macos\n"), error));
  EXPECT_FALSE(decode(raw(3, "module M\nabi x arm64-apple-macos\n"), error));
  EXPECT_FALSE(decode(raw(3, "module M\nprover gcc 1\n"), error));
}

TEST(Certificate, LeanFactsRoundTrip) {
  // ADR 0061, section 4: a lemma proved in Lean, and a trusted item for a
  // proof by native_decide.
  Certificate c = make("Sums");
  c.lean.push_back({"sum_nonneg",
                    kHash,
                    "Proofs.sum_nonneg",
                    "leanprover/lean4:v4.36.0",
                    {"propext", "Quot.sound"}});
  c.lean.push_back(
      {"dist_of", kHash, "Proofs.dist_of", "leanprover/lean4:v4.36.0", {}});
  c.trusted.push_back(
      {"native_decide", "six", kHash, {"six._native.native_decide.ax_1_1"}});
  std::string error;
  std::optional<Certificate> d = decode(encode(c), error);
  ASSERT_TRUE(d) << error;
  ASSERT_EQ(d->lean.size(), 2u);
  EXPECT_EQ(d->lean[0].name, "sum_nonneg");
  EXPECT_EQ(d->lean[0].statement, kHash);
  EXPECT_EQ(d->lean[0].theorem, "Proofs.sum_nonneg");
  EXPECT_EQ(d->lean[0].toolchain, "leanprover/lean4:v4.36.0");
  EXPECT_EQ(d->lean[0].axioms,
            (std::vector<std::string>{"propext", "Quot.sound"}));
  EXPECT_TRUE(d->lean[1].axioms.empty());
  ASSERT_EQ(d->trusted.size(), 1u);
  EXPECT_EQ(d->trusted[0].kind, "native_decide");
  EXPECT_EQ(encode(*d), encode(c));
}

TEST(Certificate, LeanLinesNeedFormat3) {
  std::string error;
  std::string line =
      "proved lean l " + kHash + " T leanprover/lean4:v4.36.0 -\n";
  EXPECT_FALSE(decode(raw(2, "module M\n" + line), error));
  EXPECT_TRUE(decode(raw(3, "module M\n" + line), error)) << error;
  EXPECT_FALSE(decode(raw(3, "module M\nproved lean l short T v -\n"), error));
  EXPECT_FALSE(
      decode(raw(3, "module M\nproved lean l " + kHash + " T\n"), error));
}

TEST(Certificate, LinkNeedsOneAbiAndTarget) {
  EXPECT_TRUE(checkLink({{"a.o", make("A")}, {"b.o", make("B")}}).empty());

  std::vector<std::string> abi =
      checkLink({{"a.o", make("A")}, {"b.o", make("B", kAbiVersion + 1)}});
  ASSERT_EQ(abi.size(), 1u);
  EXPECT_NE(abi[0].find("'b.o' was built for Pia ABI"), std::string::npos);

  std::vector<std::string> target = checkLink(
      {{"a.o", make("A")}, {"b.o", make("B", kAbiVersion, "x86_64-linux")}});
  ASSERT_EQ(target.size(), 1u);
  EXPECT_NE(target[0].find("x86_64-linux"), std::string::npos);
}

TEST(Certificate, LinkRefusesAnOldFormat) {
  std::vector<std::string> problems =
      checkLink({{"a.o", make("A")}, {"old.o", make("Old", 0, "")}});
  ASSERT_EQ(problems.size(), 1u);
  EXPECT_NE(problems[0].find("'old.o' records no Pia ABI version"),
            std::string::npos);
}

} // namespace
