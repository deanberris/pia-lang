// SPIR-V to MSL (Msl.h).

#include "gpu/Msl.h"

#include <exception>

#include "spirv_msl.hpp"

namespace pia::gpu {

bool spirvToMsl(const std::vector<uint32_t> &spirv, std::string &msl,
                std::string &error) {
  try {
    spirv_cross::CompilerMSL compiler(spirv);
    spirv_cross::CompilerMSL::Options options = compiler.get_msl_options();
    options.platform = spirv_cross::CompilerMSL::Options::macOS;
    options.set_msl_version(3, 0);
    compiler.set_msl_options(options);
    spirv_cross::ShaderResources resources = compiler.get_shader_resources();
    for (const spirv_cross::Resource &r : resources.storage_buffers) {
      spirv_cross::MSLResourceBinding binding;
      binding.stage = spv::ExecutionModelGLCompute;
      binding.desc_set = compiler.get_decoration(r.id, spv::DecorationDescriptorSet);
      binding.binding = compiler.get_decoration(r.id, spv::DecorationBinding);
      binding.msl_buffer = binding.binding;
      compiler.add_msl_resource_binding(binding);
    }
    msl = compiler.compile();
    return true;
  } catch (const std::exception &e) {
    error = e.what();
    return false;
  }
}

} // namespace pia::gpu
