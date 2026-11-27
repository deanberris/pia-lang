#include "version/Version.h"

// Defines PIA_PROVER_VERSION, from stamp.sh.
#include "src/version/Stamp.inc"

namespace pia::version {

std::string_view prover() { return PIA_PROVER_VERSION; }

} // namespace pia::version
