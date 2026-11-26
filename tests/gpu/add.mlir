// The GPU toolchain's smoke test (ADR 0068, step 1): one kernel, c = a + b
// over 1024 i32, written by hand as a gpu.module. piac --emit=spirv lowers
// it to SPIR-V, spirv-val checks the binary, SPIRV-Cross translates it to
// MSL, and the Metal compiler builds a .metallib.
module attributes {gpu.container_module} {
  gpu.module @kernels attributes {
    spirv.target_env = #spirv.target_env<
      #spirv.vce<v1.1, [Shader, Int64], [SPV_KHR_storage_buffer_storage_class]>,
      #spirv.resource_limits<>>
  } {
    gpu.func @add(%a : memref<1024xi32>, %b : memref<1024xi32>, %c : memref<1024xi32>) kernel
        attributes {spirv.entry_point_abi = #spirv.entry_point_abi<workgroup_size = [64, 1, 1]>} {
      %i = gpu.global_id x
      %x = memref.load %a[%i] : memref<1024xi32>
      %y = memref.load %b[%i] : memref<1024xi32>
      %z = arith.addi %x, %y : i32
      memref.store %z, %c[%i] : memref<1024xi32>
      gpu.return
    }
  }
}
