// piac's version, as certificates and `piac --version` give it (ADR 0073).
//
// A release build stamps it from Bazel's workspace status
// (`--config=release`, workspace_status.sh): the release version from
// MODULE.bazel, the number of commits on the branch and the short commit,
// `0.0.0+512.9f3c2e1a7b04`, so builds from `main` are ordered and an
// advisory can name a range of them. Every other build is `dev`, so that
// day-to-day builds and tests keep their Bazel cache hits: a stamped piac
// would change with every commit, and every test that runs it with it.

#ifndef PIA_VERSION_VERSION_H
#define PIA_VERSION_VERSION_H

#include <string_view>

namespace pia::version {

// `0.0.0+512.9f3c2e1a7b04` in a stamped build, `dev` otherwise.
std::string_view prover();

} // namespace pia::version

#endif // PIA_VERSION_VERSION_H
