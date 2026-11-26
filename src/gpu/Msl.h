// SPIR-V to the Metal Shading Language, by SPIRV-Cross linked into piac
// (ADR 0068, section 2). It is apart from the rest of src/gpu because
// SPIRV-Cross reports errors by exceptions, which only this file enables.

#ifndef PIA_GPU_MSL_H
#define PIA_GPU_MSL_H

#include <cstdint>
#include <string>
#include <vector>

namespace pia::gpu {

// A kernel's SPIR-V binary as MSL for macOS, MSL 3.0, its buffers bound in
// order: descriptor set 0, binding i is [[buffer(i)]], the order in which
// the Metal shim binds them. False with `error` set if SPIRV-Cross fails.
bool spirvToMsl(const std::vector<uint32_t> &spirv, std::string &msl,
                std::string &error);

} // namespace pia::gpu

#endif
