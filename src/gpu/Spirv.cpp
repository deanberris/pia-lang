// The gpu.module to SPIR-V lowering (Spirv.h).

#include "gpu/Spirv.h"

#include "mlir/Conversion/GPUToSPIRV/GPUToSPIRVPass.h"
#include "mlir/Conversion/MemRefToSPIRV/MemRefToSPIRVPass.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/GPU/IR/GPUDialect.h"
#include "mlir/Dialect/MemRef/IR/MemRef.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/Dialect/SPIRV/IR/SPIRVDialect.h"
#include "mlir/Dialect/SPIRV/IR/SPIRVOps.h"
#include "mlir/Dialect/SPIRV/Transforms/Passes.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Target/SPIRV/Serialization.h"

namespace pia::gpu {

void registerDialects(mlir::DialectRegistry &registry) {
  registry.insert<mlir::arith::ArithDialect, mlir::func::FuncDialect,
                  mlir::gpu::GPUDialect, mlir::memref::MemRefDialect,
                  mlir::scf::SCFDialect, mlir::spirv::SPIRVDialect>();
}

void registerPasses() {
  mlir::registerPass([] { return mlir::createConvertGPUToSPIRVPass(); });
  mlir::registerPass([] { return mlir::createMapMemRefStorageClassPass(); });
  mlir::spirv::registerSPIRVPasses();
}

mlir::LogicalResult lowerToSpirv(mlir::ModuleOp module) {
  mlir::PassManager pm(module->getContext());
  pm.addPass(mlir::createMapMemRefStorageClassPass());
  pm.addPass(mlir::createConvertGPUToSPIRVPass());
  mlir::OpPassManager &spv = pm.nest<mlir::spirv::ModuleOp>();
  spv.addPass(mlir::spirv::createSPIRVLowerABIAttributesPass());
  spv.addPass(mlir::spirv::createSPIRVUpdateVCEPass());
  return pm.run(module);
}

mlir::LogicalResult serializeSpirv(mlir::ModuleOp module,
                                   llvm::SmallVectorImpl<uint32_t> &binary) {
  mlir::spirv::ModuleOp found;
  int count = 0;
  module.walk([&](mlir::spirv::ModuleOp m) {
    found = m;
    ++count;
  });
  if (count != 1)
    return module.emitError("expected one spirv.module, found ") << count;
  return mlir::spirv::serialize(found, binary);
}

} // namespace pia::gpu
