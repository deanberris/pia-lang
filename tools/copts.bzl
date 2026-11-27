"""Compiler warning options for Pia's own C, C++ and Objective-C targets."""

# Targets with no LLVM or MLIR headers keep every -Wall/-Wextra warning on,
# including -Wunused-parameter, and treat all warnings as errors.
PIA_COPTS = [
    "-Wall",
    "-Wextra",
    "-Werror",
]

# Targets that include LLVM or MLIR headers (including mlir-tblgen's generated
# .inc files) suppress -Wunused-parameter, which those headers trip, while
# keeping every other -Wall/-Wextra warning as an error.
PIA_MLIR_COPTS = [
    "-Wall",
    "-Wextra",
    "-Wno-unused-parameter",
    "-Werror",
]
