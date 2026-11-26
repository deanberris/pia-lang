// Spreads placed on the GPU (Place.h).

#include "gpu/Place.h"

#include "gpu/Msl.h"
#include "gpu/Spirv.h"

#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/GPU/IR/GPUDialect.h"
#include "mlir/Dialect/MemRef/IR/MemRef.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/Dialect/SPIRV/IR/SPIRVAttributes.h"
#include "mlir/Dialect/SPIRV/IR/SPIRVDialect.h"
#include "mlir/Dialect/SPIRV/IR/TargetAndABI.h"
#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OwningOpRef.h"
#include "mlir/Transforms/RegionUtils.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/raw_ostream.h"

namespace pia::gpu {

namespace {

using mlir::Location;
using mlir::OpBuilder;
using mlir::Operation;
using mlir::Type;
using mlir::Value;
namespace arith = mlir::arith;
namespace memref = mlir::memref;
namespace scf = mlir::scf;

const char *const kRule =
    " (a spread placed on the GPU runs integer arithmetic, loads and stores "
    "of integer buffers, and if, for and while: ADR 0068, section 1)";

// Inlines every call in the spread's body: the GPU has no call stack. A
// callee must have a body of one block; recursion is cut off by depth.
mlir::LogicalResult inlineCalls(scf::ForOp f, mlir::ModuleOp module) {
  for (int depth = 0; depth < 32; ++depth) {
    llvm::SmallVector<mlir::func::CallOp> calls;
    f.getBody()->walk([&](mlir::func::CallOp c) { calls.push_back(c); });
    if (calls.empty())
      return mlir::success();
    for (mlir::func::CallOp call : calls) {
      auto callee = module.lookupSymbol<mlir::func::FuncOp>(call.getCallee());
      if (!callee || callee.isExternal())
        return call.emitError("a spread placed on the GPU cannot call '")
               << call.getCallee()
               << "': it has no Pia body to run there, such as a foreign "
                  "function";
      if (!callee.getBody().hasOneBlock())
        return call.emitError("a spread placed on the GPU cannot call '")
               << call.getCallee() << "' yet: its body is not one block";
      mlir::Block &body = callee.getBody().front();
      OpBuilder b(call);
      mlir::IRMapping map;
      for (auto [arg, v] : llvm::zip(body.getArguments(), call.getOperands()))
        map.map(arg, v);
      for (Operation &op : body.without_terminator())
        b.clone(op, map);
      auto ret = mlir::cast<mlir::func::ReturnOp>(body.getTerminator());
      for (auto [r, v] : llvm::zip(call.getResults(), ret.getOperands()))
        r.replaceAllUsesWith(map.lookupOrDefault(v));
      call.erase();
    }
  }
  return f.emitError("a spread placed on the GPU calls functions too deeply, "
                     "or recursively, to inline: the GPU has no call stack");
}

// Takes the memref casts out of the body, so that each buffer is used
// directly by loads, stores and dims, and computes the length of each
// buffer from outside before the loop.
mlir::LogicalResult simplifyBuffers(scf::ForOp f) {
  llvm::SmallVector<memref::CastOp> casts;
  f.getBody()->walk([&](memref::CastOp c) { casts.push_back(c); });
  for (memref::CastOp c : casts) {
    for (Operation *user : c->getUsers())
      if (!mlir::isa<memref::LoadOp, memref::StoreOp, memref::DimOp,
                     memref::CastOp>(user))
        return user->emitError("a buffer cannot be used this way") << kRule;
    c.getResult().replaceAllUsesWith(c.getSource());
    c.erase();
  }
  llvm::SmallVector<memref::DimOp> dims;
  f.getBody()->walk([&](memref::DimOp d) { dims.push_back(d); });
  for (memref::DimOp d : dims) {
    if (f->isAncestor(d.getSource().getParentRegion()->getParentOp()))
      return d.emitError("a buffer made in the body cannot be used") << kRule;
    std::optional<int64_t> index = d.getConstantIndex();
    if (!index)
      return d.emitError("a buffer must be one-dimensional") << kRule;
    OpBuilder b(f);
    Value len = b.create<memref::DimOp>(d.getLoc(), d.getSource(), *index);
    d.getResult().replaceAllUsesWith(len);
    d.erase();
  }
  return mlir::success();
}

bool deviceInt(Type t) {
  auto i = mlir::dyn_cast<mlir::IntegerType>(t);
  return i && (i.getWidth() == 1 || i.getWidth() == 8 || i.getWidth() == 16 ||
               i.getWidth() == 32 || i.getWidth() == 64);
}

// A buffer the device can hold: one dimension of 8- to 64-bit integers.
bool deviceBuffer(Type t) {
  auto m = mlir::dyn_cast<mlir::MemRefType>(t);
  return m && m.getRank() == 1 && deviceInt(m.getElementType()) &&
         m.getElementType().getIntOrFloatBitWidth() >= 8;
}

// The device rules (ADR 0068, section 1), on the inlined body.
mlir::LogicalResult checkBody(scf::ForOp f) {
  mlir::LogicalResult result = mlir::success();
  f.getBody()->walk([&](Operation *op) {
    if (mlir::failed(result))
      return;
    llvm::StringRef dialect =
        op->getDialect() ? op->getDialect()->getNamespace() : llvm::StringRef();
    bool ok = dialect == "arith" ||
              mlir::isa<scf::IfOp, scf::ForOp, scf::WhileOp, scf::YieldOp,
                        scf::ConditionOp, memref::LoadOp, memref::StoreOp>(op);
    if (!ok) {
      result = op->emitError("'")
               << op->getName() << "' cannot run on the GPU" << kRule;
      return;
    }
    auto checkType = [&](Type t) {
      if (deviceInt(t) || mlir::isa<mlir::IndexType>(t))
        return true;
      if (mlir::isa<mlir::MemRefType>(t) &&
          mlir::isa<memref::LoadOp, memref::StoreOp>(op)) {
        if (deviceBuffer(t))
          return true;
        result = op->emitError("a buffer of ")
                 << mlir::cast<mlir::MemRefType>(t).getElementType()
                 << " cannot be used on the GPU" << kRule;
        return false;
      }
      result = op->emitError("a value of type ")
               << t << " cannot be used on the GPU" << kRule;
      return false;
    };
    for (Type t : op->getOperandTypes())
      if (!checkType(t))
        return;
    for (Type t : op->getResultTypes())
      if (!checkType(t))
        return;
  });
  return result;
}

// How a value from outside the loop reaches the kernel: a buffer, or a
// scalar in a one-element buffer of `held` (a bool as a byte, an index as
// an i64).
struct Capture {
  Value host;
  bool buffer = false;
  bool written = false;
  Type held;
};

Type heldType(Type t) {
  OpBuilder b(t.getContext());
  if (mlir::isa<mlir::IndexType>(t))
    return b.getI64Type();
  if (t.isInteger(1))
    return b.getI8Type();
  return t;
}

// The SPIR-V environment Metal supports through SPIRV-Cross: 8-, 16- and
// 64-bit integers in storage buffers.
mlir::spirv::TargetEnvAttr targetEnv(mlir::MLIRContext *ctx) {
  using mlir::spirv::Capability;
  using mlir::spirv::Extension;
  auto vce = mlir::spirv::VerCapExtAttr::get(
      mlir::spirv::Version::V_1_3,
      {Capability::Shader, Capability::Int8, Capability::Int16,
       Capability::Int64, Capability::StorageBuffer8BitAccess,
       Capability::StorageBuffer16BitAccess},
      {Extension::SPV_KHR_storage_buffer_storage_class,
       Extension::SPV_KHR_8bit_storage, Extension::SPV_KHR_16bit_storage},
      ctx);
  return mlir::spirv::TargetEnvAttr::get(
      vce, mlir::spirv::getDefaultResourceLimits(ctx));
}

// A private constant byte array in the module, and its address as an i64.
Value constantBytes(OpBuilder &b, mlir::ModuleOp module, Location loc,
                    llvm::StringRef name, llvm::ArrayRef<char> bytes) {
  auto i8 = b.getI8Type();
  auto type = mlir::MemRefType::get({static_cast<int64_t>(bytes.size())}, i8);
  auto tensor =
      mlir::RankedTensorType::get({static_cast<int64_t>(bytes.size())}, i8);
  OpBuilder mb = OpBuilder::atBlockBegin(module.getBody());
  mb.create<memref::GlobalOp>(
      loc, name, mb.getStringAttr("private"), type,
      mlir::DenseElementsAttr::getFromRawBuffer(tensor, bytes),
      /*constant=*/true, /*alignment=*/mb.getI64IntegerAttr(16));
  Value g = b.create<memref::GetGlobalOp>(loc, type, name);
  Value p = b.create<memref::ExtractAlignedPointerAsIndexOp>(loc, g);
  return b.create<arith::IndexCastOp>(loc, b.getI64Type(), p);
}

class Placer {
public:
  explicit Placer(mlir::ModuleOp module) : module_(module) {}

  mlir::LogicalResult place(scf::ForOp f) {
    if (mlir::failed(inlineCalls(f, module_)) ||
        mlir::failed(simplifyBuffers(f)) || mlir::failed(checkBody(f)))
      return mlir::failure();
    std::optional<int64_t> step = mlir::getConstantIntValue(f.getStep());
    if (!step || *step != 1)
      return f.emitError("a spread placed on the GPU steps by one");

    // What the body uses from outside: buffers and scalars.
    llvm::SetVector<Value> used;
    mlir::getUsedValuesDefinedAbove(f.getRegion(), used);
    std::vector<Capture> captures;
    for (Value v : used) {
      Capture c;
      c.host = v;
      if (mlir::isa<mlir::MemRefType>(v.getType())) {
        if (!deviceBuffer(v.getType()))
          return f.emitError("a buffer of ")
                 << mlir::cast<mlir::MemRefType>(v.getType()).getElementType()
                 << " cannot be used on the GPU" << kRule;
        c.buffer = true;
        for (Operation *user : v.getUsers())
          if (auto s = mlir::dyn_cast<memref::StoreOp>(user))
            if (s.getMemRef() == v && f->isAncestor(s))
              c.written = true;
      } else {
        if (!deviceInt(v.getType()) && !mlir::isa<mlir::IndexType>(v.getType()))
          return f.emitError("a value of type ")
                 << v.getType() << " cannot be used on the GPU" << kRule;
        c.held = heldType(v.getType());
      }
      captures.push_back(c);
    }

    std::string name = "pia_kernel_" + std::to_string(count_++);
    std::vector<uint8_t> metallib;
    if (mlir::failed(compileKernel(f, captures, name, metallib)))
      return mlir::failure();
    return callShim(f, captures, name, metallib);
  }

private:
  // The body as a gpu.func `name`, through SPIR-V and MSL to a .metallib.
  // Its arguments are the buffers and scalars in `captures`, then the
  // loop's bounds; thread g runs iteration lo + g, if it is below hi.
  mlir::LogicalResult compileKernel(scf::ForOp f,
                                    const std::vector<Capture> &captures,
                                    const std::string &name,
                                    std::vector<uint8_t> &metallib) {
    mlir::MLIRContext *ctx = module_.getContext();
    Location loc = f.getLoc();
    mlir::OwningOpRef<mlir::ModuleOp> tmp = mlir::ModuleOp::create(loc);
    (*tmp)->setAttr(mlir::gpu::GPUDialect::getContainerModuleAttrName(),
                    mlir::UnitAttr::get(ctx));
    OpBuilder b = OpBuilder::atBlockBegin(tmp->getBody());
    auto gm = b.create<mlir::gpu::GPUModuleOp>(loc, "pia_kernels");
    gm->setAttr(mlir::spirv::getTargetEnvAttrName(), targetEnv(ctx));

    auto i64 = b.getI64Type();
    llvm::SmallVector<Type> args;
    for (const Capture &c : captures) {
      if (c.buffer) {
        auto m = mlir::cast<mlir::MemRefType>(c.host.getType());
        args.push_back(mlir::MemRefType::get({mlir::ShapedType::kDynamic},
                                             m.getElementType()));
      } else {
        args.push_back(mlir::MemRefType::get({1}, c.held));
      }
    }
    args.push_back(mlir::MemRefType::get({1}, i64)); // lo
    args.push_back(mlir::MemRefType::get({1}, i64)); // hi

    b.setInsertionPointToStart(gm.getBody());
    auto kernel =
        b.create<mlir::gpu::GPUFuncOp>(loc, name, b.getFunctionType(args, {}));
    kernel->setAttr(mlir::gpu::GPUDialect::getKernelFuncAttrName(),
                    b.getUnitAttr());
    kernel->setAttr(mlir::spirv::getEntryPointABIAttrName(),
                    mlir::spirv::getEntryPointABIAttr(ctx, {64, 1, 1}));
    mlir::Block &entry = kernel.getBody().front();
    OpBuilder kb = OpBuilder::atBlockEnd(&entry);
    Value zero = kb.create<arith::ConstantIndexOp>(loc, 0);
    auto scalar = [&](unsigned arg, Type want) -> Value {
      Value v = kb.create<memref::LoadOp>(loc, entry.getArgument(arg),
                                          mlir::ValueRange{zero});
      if (mlir::isa<mlir::IndexType>(want))
        return kb.create<arith::IndexCastOp>(loc, want, v);
      if (want.isInteger(1))
        return kb.create<arith::TruncIOp>(loc, want, v);
      return v;
    };
    mlir::IRMapping map;
    for (unsigned i = 0; i < captures.size(); ++i)
      map.map(captures[i].host, captures[i].buffer
                                    ? Value(entry.getArgument(i))
                                    : scalar(i, captures[i].host.getType()));
    Value lo = scalar(captures.size(), kb.getIndexType());
    Value hi = scalar(captures.size() + 1, kb.getIndexType());
    Value g = kb.create<mlir::gpu::GlobalIdOp>(loc, mlir::gpu::Dimension::x);
    Value iv = kb.create<arith::AddIOp>(loc, g, lo);
    Value in = kb.create<arith::CmpIOp>(loc, arith::CmpIPredicate::ult, iv, hi);
    auto guard = kb.create<scf::IfOp>(loc, in, /*withElseRegion=*/false);
    map.map(f.getInductionVar(), iv);
    OpBuilder ib = guard.getThenBodyBuilder();
    for (Operation &op : f.getBody()->without_terminator())
      ib.clone(op, map);
    kb.create<mlir::gpu::ReturnOp>(loc);

    if (mlir::failed(lowerToSpirv(*tmp)))
      return f.emitError("the spread could not be lowered to SPIR-V for the "
                         "GPU");
    llvm::SmallVector<uint32_t> binary;
    if (mlir::failed(serializeSpirv(*tmp, binary)))
      return mlir::failure();
    std::string msl, error;
    if (!spirvToMsl(std::vector<uint32_t>(binary.begin(), binary.end()), msl,
                    error))
      return f.emitError("SPIRV-Cross could not translate the kernel to "
                         "Metal: ")
             << error;
    if (!compileMetal(msl, metallib, error))
      return f.emitError("the kernel did not compile for Metal: ") << error;
    return mlir::success();
  }

  // Replaces the loop with `pia_gpu_run(lib, name, args, threads)`, and the
  // status after it with the run's status. Each argument is a triple of
  // i64: the host address, the size in bytes, and whether the kernel
  // writes it, so the shim copies it back.
  mlir::LogicalResult callShim(scf::ForOp f,
                               const std::vector<Capture> &captures,
                               const std::string &name,
                               const std::vector<uint8_t> &metallib) {
    Operation *status = nullptr;
    for (Operation *op = f->getNextNode(); op && !status;
         op = op->getNextNode())
      if (auto call = mlir::dyn_cast<mlir::func::CallOp>(op))
        if (call.getCallee() == kStatusSymbol)
          status = call;
    if (!status)
      return f.emitError("internal error: no status after the placed spread");

    Location loc = f.getLoc();
    OpBuilder b(f);
    auto i64 = b.getI64Type();
    auto i32 = b.getI32Type();
    auto scope = b.create<memref::AllocaScopeOp>(loc, mlir::TypeRange{i32});
    b.setInsertionPointToStart(&scope.getBodyRegion().emplaceBlock());
    auto index = [&](int64_t v) -> Value {
      return b.create<arith::ConstantIndexOp>(loc, v);
    };
    auto word = [&](int64_t v) -> Value {
      return b.create<arith::ConstantIntOp>(loc, i64, v);
    };
    auto toI64 = [&](Value v) -> Value {
      return b.create<arith::IndexCastOp>(loc, i64, v);
    };

    size_t n = captures.size() + 2;
    auto argsType = mlir::MemRefType::get({static_cast<int64_t>(3 * n)}, i64);
    Value argv = b.create<memref::AllocaOp>(loc, argsType);
    unsigned slot = 0;
    auto put = [&](Value addr, Value bytes, bool written) {
      for (Value v : {addr, bytes, word(written ? 1 : 0)})
        b.create<memref::StoreOp>(loc, v, argv,
                                  mlir::ValueRange{index(slot++)});
    };
    auto scalar = [&](Value v, Type held) {
      if (mlir::isa<mlir::IndexType>(v.getType()))
        v = b.create<arith::IndexCastOp>(loc, held, v);
      else if (v.getType() != held)
        v = b.create<arith::ExtUIOp>(loc, held, v);
      auto type = mlir::MemRefType::get({1}, held);
      Value cell = b.create<memref::AllocaOp>(loc, type);
      b.create<memref::StoreOp>(loc, v, cell, mlir::ValueRange{index(0)});
      Value p = b.create<memref::ExtractAlignedPointerAsIndexOp>(loc, cell);
      put(toI64(p), word(held.getIntOrFloatBitWidth() / 8), false);
    };
    for (const Capture &c : captures) {
      if (!c.buffer) {
        scalar(c.host, c.held);
        continue;
      }
      auto m = mlir::cast<mlir::MemRefType>(c.host.getType());
      int64_t width = m.getElementType().getIntOrFloatBitWidth() / 8;
      auto meta = b.create<memref::ExtractStridedMetadataOp>(loc, c.host);
      Value base =
          b.create<memref::ExtractAlignedPointerAsIndexOp>(loc, c.host);
      Value off = b.create<arith::MulIOp>(loc, meta.getOffset(), index(width));
      Value addr = b.create<arith::AddIOp>(loc, base, off);
      Value bytes =
          b.create<arith::MulIOp>(loc, meta.getSizes()[0], index(width));
      put(toI64(addr), toI64(bytes), c.written);
    }
    scalar(f.getLowerBound(), i64);
    scalar(f.getUpperBound(), i64);
    Value count =
        b.create<arith::SubIOp>(loc, f.getUpperBound(), f.getLowerBound());
    Value threads = toI64(b.create<arith::MaxSIOp>(loc, count, index(0)));

    std::string sym = "__pia_gpu_" + std::to_string(count_ - 1);
    Value lib = constantBytes(
        b, module_, loc, sym + "_lib",
        llvm::ArrayRef<char>(reinterpret_cast<const char *>(metallib.data()),
                             metallib.size()));
    Value kname = constantBytes(b, module_, loc, sym + "_name",
                                llvm::ArrayRef<char>(name.data(), name.size()));
    Value argp =
        toI64(b.create<memref::ExtractAlignedPointerAsIndexOp>(loc, argv));

    auto runType =
        b.getFunctionType({i64, i64, i64, i64, i64, i64, i64}, {i32});
    if (!module_.lookupSymbol("pia_gpu_run")) {
      OpBuilder mb = OpBuilder::atBlockEnd(module_.getBody());
      auto decl = mb.create<mlir::func::FuncOp>(loc, "pia_gpu_run", runType);
      decl.setPrivate();
    }
    auto run = b.create<mlir::func::CallOp>(
        loc, "pia_gpu_run", mlir::TypeRange{i32},
        mlir::ValueRange{lib, word(metallib.size()), kname, word(name.size()),
                         argp, word(n), threads});
    b.create<memref::AllocaScopeReturnOp>(loc, run.getResults());

    status->getResult(0).replaceAllUsesWith(scope.getResult(0));
    status->erase();
    f.erase();
    return mlir::success();
  }

  mlir::ModuleOp module_;
  unsigned count_ = 0;
};

// Runs `xcrun` with `args`, its errors in `error`.
bool xcrun(llvm::ArrayRef<llvm::StringRef> args, const llvm::Twine &errFile,
           std::string &error) {
  llvm::ErrorOr<std::string> path = llvm::sys::findProgramByName("xcrun");
  std::string program = path ? *path : "/usr/bin/xcrun";
  if (!llvm::sys::fs::can_execute(program)) {
    error = "xcrun was not found: a spread placed on the GPU needs Xcode and "
            "its Metal toolchain (xcodebuild -downloadComponent "
            "MetalToolchain)";
    return false;
  }
  llvm::SmallVector<llvm::StringRef> argv{program};
  argv.append(args.begin(), args.end());
  std::string errPath = errFile.str();
  std::optional<llvm::StringRef> redirects[] = {std::nullopt, std::nullopt,
                                                llvm::StringRef(errPath)};
  std::string message;
  int rc = llvm::sys::ExecuteAndWait(program, argv, std::nullopt, redirects, 0,
                                     0, &message);
  if (rc == 0)
    return true;
  error = message;
  if (auto buf = llvm::MemoryBuffer::getFile(errPath))
    error += (*buf)->getBuffer().str();
  if (error.empty())
    error = "xcrun failed";
  return false;
}

} // namespace

bool compileMetal(const std::string &msl, std::vector<uint8_t> &metallib,
                  std::string &error) {
  llvm::SmallString<128> dir;
  if (llvm::sys::fs::createUniqueDirectory("pia-gpu", dir)) {
    error = "cannot make a temporary directory";
    return false;
  }
  auto file = [&](const char *leaf) {
    llvm::SmallString<128> p(dir);
    llvm::sys::path::append(p, leaf);
    return std::string(p);
  };
  std::string metal = file("kernel.metal"), air = file("kernel.air"),
              lib = file("kernel.metallib"), err = file("stderr.txt");
  bool ok = false;
  {
    std::error_code ec;
    llvm::raw_fd_ostream out(metal, ec);
    if (ec) {
      error = "cannot write " + metal + ": " + ec.message();
    } else {
      out << msl;
      out.close();
      ok = xcrun({"-sdk", "macosx", "metal", "-fno-fast-math", "-c", metal,
                  "-o", air},
                 err, error) &&
           xcrun({"-sdk", "macosx", "metallib", air, "-o", lib}, err, error);
    }
  }
  if (ok) {
    auto buf = llvm::MemoryBuffer::getFile(lib, /*IsText=*/false);
    if (!buf) {
      error = "cannot read " + lib;
      ok = false;
    } else {
      llvm::StringRef bytes = (*buf)->getBuffer();
      metallib.assign(bytes.begin(), bytes.end());
    }
  }
  llvm::sys::fs::remove_directories(dir);
  return ok;
}

mlir::LogicalResult lowerPlacedSpreads(mlir::ModuleOp module) {
  llvm::SmallVector<scf::ForOp> placed;
  module.walk([&](scf::ForOp f) {
    auto p = f->getAttrOfType<mlir::StringAttr>("pia.place");
    if (p && p.getValue() == "gpu")
      placed.push_back(f);
  });
  if (placed.empty())
    return mlir::success();
  mlir::MLIRContext *ctx = module.getContext();
  ctx->loadDialect<mlir::gpu::GPUDialect, mlir::spirv::SPIRVDialect>();
  Placer placer(module);
  for (scf::ForOp f : placed)
    if (mlir::failed(placer.place(f)))
      return mlir::failure();
  if (auto decl = module.lookupSymbol<mlir::func::FuncOp>(kStatusSymbol))
    if (decl.symbolKnownUseEmpty(module))
      decl.erase();
  return mlir::success();
}

} // namespace pia::gpu
