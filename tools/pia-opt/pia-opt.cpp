// pia-opt: the MLIR optimiser driver for Pia's dialects.

#include "dialect/ContractDialect.h"
#include "dialect/ParDialect.h"
#include "dialect/PiaDialect.h"

#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ArmNeon/ArmNeonDialect.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/LLVMIR/LLVMDialect.h"
#include "mlir/Dialect/MemRef/IR/MemRef.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/Dialect/SMT/IR/SMTDialect.h"
#include "mlir/Dialect/Vector/IR/VectorOps.h"
#include "mlir/IR/DialectRegistry.h"
#include "mlir/Tools/mlir-opt/MlirOptMain.h"
#include "mlir/Transforms/Passes.h"

int main(int argc, char **argv) {
  mlir::DialectRegistry registry;
  registry.insert<mlir::arith::ArithDialect, mlir::arm_neon::ArmNeonDialect,
                  mlir::func::FuncDialect, mlir::LLVM::LLVMDialect,
                  mlir::memref::MemRefDialect, mlir::scf::SCFDialect,
                  mlir::smt::SMTDialect, mlir::vector::VectorDialect,
                  pia::PiaDialect, pia::contract::ContractDialect,
                  pia::par::ParDialect>();
  mlir::registerTransformsPasses();
  return mlir::asMainReturnCode(
      mlir::MlirOptMain(argc, argv, "Pia optimiser driver\n", registry));
}
