// The Metal host shim (metal_shim.h). Compiled with ARC: each handle is an
// object retained with CFBridgingRetain, and released with
// CFBridgingRelease when it is closed or freed.

#include <dispatch/dispatch.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#import <Foundation/Foundation.h>
#import <Metal/Metal.h>

#include "src/runtime/metal/metal_shim.h"

// A device and its queue.
@interface PiaGpuDevice : NSObject
@property(nonatomic, strong) id<MTLDevice> device;
@property(nonatomic, strong) id<MTLCommandQueue> queue;
@end
@implementation PiaGpuDevice
@end

// A library and the pipelines made from it, by kernel name.
@interface PiaGpuLibrary : NSObject
@property(nonatomic, strong) id<MTLDevice> device;
@property(nonatomic, strong) id<MTLLibrary> library;
@property(nonatomic, strong) NSMutableDictionary<NSString *, id<MTLComputePipelineState>> *pipelines;
@end
@implementation PiaGpuLibrary
@end

static uint64_t retain_handle(id object) {
  return object ? (uint64_t)(uintptr_t)CFBridgingRetain(object) : 0;
}

static id borrow(uint64_t handle) {
  return handle ? (__bridge id)(void *)(uintptr_t)handle : nil;
}

static void release_handle(uint64_t handle) {
  if (handle) CFBridgingRelease((void *)(uintptr_t)handle);
}

uint64_t pia_gpu_device_open(void) {
  @autoreleasepool {
    id<MTLDevice> device = MTLCreateSystemDefaultDevice();
    if (!device) return 0;
    id<MTLCommandQueue> queue = [device newCommandQueue];
    if (!queue) return 0;
    PiaGpuDevice *d = [PiaGpuDevice new];
    d.device = device;
    d.queue = queue;
    return retain_handle(d);
  }
}

void pia_gpu_device_close(uint64_t device) { release_handle(device); }

uint64_t pia_gpu_buffer_new(uint64_t device, uint64_t bytes) {
  @autoreleasepool {
    PiaGpuDevice *d = borrow(device);
    if (!d || bytes == 0) return 0;
    id<MTLBuffer> b = [d.device newBufferWithLength:bytes
                                            options:MTLResourceStorageModeShared];
    if (!b) return 0;
    memset(b.contents, 0, bytes);
    return retain_handle(b);
  }
}

uint64_t pia_gpu_buffer_contents(uint64_t buffer) {
  id<MTLBuffer> b = borrow(buffer);
  return b ? (uint64_t)(uintptr_t)b.contents : 0;
}

uint64_t pia_gpu_buffer_length(uint64_t buffer) {
  id<MTLBuffer> b = borrow(buffer);
  return b ? b.length : 0;
}

void pia_gpu_buffer_free(uint64_t buffer) { release_handle(buffer); }

uint64_t pia_gpu_library_load(uint64_t device, const uint8_t *bytes, uint64_t n) {
  @autoreleasepool {
    PiaGpuDevice *d = borrow(device);
    if (!d || !bytes || n == 0) return 0;
    dispatch_data_t data = dispatch_data_create(bytes, n, NULL,
                                                DISPATCH_DATA_DESTRUCTOR_DEFAULT);
    NSError *error = nil;
    id<MTLLibrary> library = [d.device newLibraryWithData:data error:&error];
    if (!library) return 0;
    PiaGpuLibrary *l = [PiaGpuLibrary new];
    l.device = d.device;
    l.library = library;
    l.pipelines = [NSMutableDictionary new];
    return retain_handle(l);
  }
}

void pia_gpu_library_free(uint64_t library) { release_handle(library); }

uint64_t pia_gpu_kernel_get(uint64_t library, const uint8_t *name, uint64_t n) {
  @autoreleasepool {
    PiaGpuLibrary *l = borrow(library);
    if (!l || !name) return 0;
    NSString *key = [[NSString alloc] initWithBytes:name
                                             length:n
                                           encoding:NSUTF8StringEncoding];
    if (!key) return 0;
    id<MTLComputePipelineState> pipeline = l.pipelines[key];
    if (!pipeline) {
      id<MTLFunction> f = [l.library newFunctionWithName:key];
      if (!f) return 0;
      NSError *error = nil;
      pipeline = [l.device newComputePipelineStateWithFunction:f error:&error];
      if (!pipeline) return 0;
      l.pipelines[key] = pipeline;
    }
    // The library keeps the pipeline alive; the handle is borrowed.
    return (uint64_t)(uintptr_t)(__bridge void *)pipeline;
  }
}

int32_t pia_gpu_dispatch(uint64_t device, uint64_t kernel,
                         const uint64_t *buffers, uint64_t nbuffers,
                         uint64_t threads, uint64_t group,
                         uint64_t timeout_ms) {
  @autoreleasepool {
    PiaGpuDevice *d = borrow(device);
    id<MTLComputePipelineState> pipeline = borrow(kernel);
    if (!d || !pipeline || group == 0) return PIA_GPU_FAULT;
    if (group > pipeline.maxTotalThreadsPerThreadgroup)
      group = pipeline.maxTotalThreadsPerThreadgroup;
    id<MTLCommandBuffer> cb = [d.queue commandBuffer];
    id<MTLComputeCommandEncoder> enc = [cb computeCommandEncoder];
    [enc setComputePipelineState:pipeline];
    for (uint64_t i = 0; i < nbuffers; ++i) {
      id<MTLBuffer> b = borrow(buffers[i]);
      if (!b) {
        [enc endEncoding];
        return PIA_GPU_FAULT;
      }
      [enc setBuffer:b offset:0 atIndex:i];
    }
    [enc dispatchThreads:MTLSizeMake(threads, 1, 1)
        threadsPerThreadgroup:MTLSizeMake(group, 1, 1)];
    [enc endEncoding];
    dispatch_semaphore_t done = dispatch_semaphore_create(0);
    [cb addCompletedHandler:^(__unused id<MTLCommandBuffer> finished) {
      dispatch_semaphore_signal(done);
    }];
    [cb commit];
    dispatch_time_t limit =
        timeout_ms ? dispatch_time(DISPATCH_TIME_NOW, (int64_t)timeout_ms * NSEC_PER_MSEC)
                   : DISPATCH_TIME_FOREVER;
    if (dispatch_semaphore_wait(done, limit) != 0) return PIA_GPU_TIMEOUT;
    return cb.status == MTLCommandBufferStatusCompleted ? PIA_GPU_OK : PIA_GPU_FAULT;
  }
}

// pia_gpu_run's device, libraries (by the address of their bytes) and
// kernels, made on first use and kept for the life of the program.
static uint64_t run_device;
static NSMutableDictionary<NSNumber *, NSNumber *> *run_libraries;
static _Atomic uint64_t run_wrapped, run_copied, run_copied_bytes;

void pia_gpu_run_stats(uint64_t *wrapped, uint64_t *copied,
                       uint64_t *copied_bytes) {
  *wrapped = run_wrapped;
  *copied = run_copied;
  *copied_bytes = run_copied_bytes;
}

// The device pia_gpu_run and the sequences use, opened on first use.
// PIA_GPU_OK, or PIA_GPU_UNAVAILABLE if there is no GPU.
static int32_t run_open(void) {
  @synchronized([PiaGpuDevice class]) {
    if (!run_device)
      run_device = pia_gpu_device_open();
    return run_device ? PIA_GPU_OK : PIA_GPU_UNAVAILABLE;
  }
}

// The pipeline of kernel `name` in the embedded library at `lib`, loaded
// once per library and cached by name, in *kernel.
static int32_t run_kernel(uint64_t lib, uint64_t lib_len, uint64_t name,
                          uint64_t name_len, uint64_t *kernel) {
  *kernel = 0;
  if (run_open() != PIA_GPU_OK)
    return PIA_GPU_UNAVAILABLE;
  @synchronized([PiaGpuDevice class]) {
    if (!run_libraries)
      run_libraries = [NSMutableDictionary new];
    NSNumber *key = @(lib);
    uint64_t library = run_libraries[key].unsignedLongLongValue;
    if (!library) {
      library = pia_gpu_library_load(run_device,
                                     (const uint8_t *)(uintptr_t)lib, lib_len);
      if (!library)
        return PIA_GPU_FAULT;
      run_libraries[key] = @(library);
    }
    *kernel =
        pia_gpu_kernel_get(library, (const uint8_t *)(uintptr_t)name, name_len);
  }
  return *kernel ? PIA_GPU_OK : PIA_GPU_FAULT;
}

static _Atomic uint64_t warm_count;

void pia_gpu_warm_stats(uint64_t *warmed) { *warmed = warm_count; }

void pia_gpu_warm(uint64_t lib, uint64_t lib_len, uint64_t name,
                  uint64_t name_len) {
  const char *off = getenv("PIA_GPU_WARM");
  if (off && strcmp(off, "0") == 0)
    return;
  // One serial queue, so kernels are built one at a time, below the
  // program's own threads.
  static dispatch_queue_t queue;
  static dispatch_once_t once;
  dispatch_once(&once, ^{
    queue =
        dispatch_queue_create("dev.pia-lang.gpu.warm",
                              dispatch_queue_attr_make_with_qos_class(
                                  DISPATCH_QUEUE_SERIAL, QOS_CLASS_UTILITY, 0));
  });
  // The library and name are constants of the program, so they outlive
  // the block.
  dispatch_async(queue, ^{
    @autoreleasepool {
      uint64_t kernel;
      if (run_kernel(lib, lib_len, name, name_len, &kernel) == PIA_GPU_OK)
        warm_count++;
    }
  });
}

int32_t pia_gpu_run(uint64_t lib, uint64_t lib_len, uint64_t name,
                    uint64_t name_len, uint64_t args, uint64_t nargs,
                    uint64_t threads) {
  @autoreleasepool {
    uint64_t kernel = 0;
    int32_t found = run_kernel(lib, lib_len, name, name_len, &kernel);
    if (found != PIA_GPU_OK)
      return found;
    if (threads == 0) return PIA_GPU_OK;
    PiaGpuDevice *d = borrow(run_device);
    const uint64_t *a = (const uint64_t *)(uintptr_t)args;
    NSMutableArray<id<MTLBuffer>> *buffers = [NSMutableArray new];
    uint64_t handles[64];
    if (nargs > 64) return PIA_GPU_FAULT;
    bool copied[64];
    const uint64_t page = (uint64_t)getpagesize();
    for (uint64_t i = 0; i < nargs; ++i) {
      uint64_t addr = a[3 * i], bytes = a[3 * i + 1];
      id<MTLBuffer> b = nil;
      copied[i] = false;
      if (bytes && addr % page == 0) {
        // Shared memory: the kernel reads and writes the host's own pages.
        uint64_t len = (bytes + page - 1) / page * page;
        b = [d.device newBufferWithBytesNoCopy:(void *)(uintptr_t)addr
                                        length:len
                                       options:MTLResourceStorageModeShared
                                   deallocator:nil];
        if (b) ++run_wrapped;
      }
      if (!b) {
        b = bytes ? [d.device newBufferWithBytes:(const void *)(uintptr_t)addr
                                          length:bytes
                                         options:MTLResourceStorageModeShared]
                  : [d.device newBufferWithLength:16
                                          options:MTLResourceStorageModeShared];
        if (!b) return PIA_GPU_OUT_OF_MEMORY;
        copied[i] = bytes != 0;
        if (copied[i]) {
          ++run_copied;
          run_copied_bytes += bytes;
        }
      }
      [buffers addObject:b];
      handles[i] = (uint64_t)(uintptr_t)(__bridge void *)b;
    }
    id<MTLComputePipelineState> pipeline = borrow(kernel);
    uint64_t group = pipeline.threadExecutionWidth;
    int32_t r = pia_gpu_dispatch(run_device, kernel, handles, nargs, threads,
                                 group ? group : 64, 0);
    if (r != PIA_GPU_OK) return r;
    for (uint64_t i = 0; i < nargs; ++i)
      if (copied[i] && a[3 * i + 2])
        memcpy((void *)(uintptr_t)a[3 * i], buffers[i].contents, a[3 * i + 1]);
    return PIA_GPU_OK;
  }
}

// A placed sequence being encoded (ADR 0068, section 9): one command
// buffer and one compute encoder, the buffers bound so far by host range,
// and the first error. The encoder is serial, so each dispatch runs after
// the one before it has finished and sees its writes.
@interface PiaGpuSequence : NSObject
@property(nonatomic, strong) id<MTLCommandBuffer> commands;
@property(nonatomic, strong) id<MTLComputeCommandEncoder> encoder;
@property(nonatomic, strong)
    NSMutableDictionary<NSString *, id<MTLBuffer>> *bound;
@property(nonatomic, strong)
    NSMutableDictionary<NSString *, NSNumber *> *offsets;
// The copied buffers: their host ranges and whether a kernel writes them.
@property(nonatomic, strong) NSMutableArray<NSString *> *copies;
@property(nonatomic, strong) NSMutableSet<NSString *> *written;
@property(nonatomic) int32_t status;
@end
@implementation PiaGpuSequence
@end

static _Atomic uint64_t seq_dispatches;

void pia_gpu_sequence_stats(uint64_t *dispatches) {
  *dispatches = seq_dispatches;
}

uint64_t pia_gpu_seq_begin(void) {
  @autoreleasepool {
    if (run_open() != PIA_GPU_OK)
      return 0;
    PiaGpuDevice *d = borrow(run_device);
    PiaGpuSequence *q = [PiaGpuSequence new];
    q.commands = [d.queue commandBuffer];
    q.encoder = [q.commands computeCommandEncoder];
    if (!q.commands || !q.encoder)
      return 0;
    q.bound = [NSMutableDictionary new];
    q.offsets = [NSMutableDictionary new];
    q.copies = [NSMutableArray new];
    q.written = [NSMutableSet new];
    q.status = PIA_GPU_OK;
    return retain_handle(q);
  }
}

// The Metal buffer for host range [addr, addr + bytes) in sequence q, made
// once: the pages it lies in, wrapped where they are, or else a copy. Its
// offset into that buffer is in *offset.
static id<MTLBuffer> seq_buffer(PiaGpuSequence *q, uint64_t addr,
                                uint64_t bytes, bool written,
                                uint64_t *offset) {
  NSString *key = [NSString stringWithFormat:@"%llx:%llx", addr, bytes];
  if (written)
    [q.written addObject:key];
  id<MTLBuffer> b = q.bound[key];
  if (b) {
    *offset = q.offsets[key].unsignedLongLongValue;
    return b;
  }
  PiaGpuDevice *d = borrow(run_device);
  const uint64_t page = (uint64_t)getpagesize();
  *offset = 0;
  if (bytes) {
    // Shared memory: every page the range touches is mapped where it is,
    // so the kernels and the host see the same cells.
    uint64_t base = addr / page * page;
    uint64_t len = (addr + bytes - base + page - 1) / page * page;
    b = [d.device newBufferWithBytesNoCopy:(void *)(uintptr_t)base
                                    length:len
                                   options:MTLResourceStorageModeShared
                               deallocator:nil];
    if (b) {
      *offset = addr - base;
      ++run_wrapped;
    }
  }
  if (!b) {
    b = bytes ? [d.device newBufferWithBytes:(const void *)(uintptr_t)addr
                                      length:bytes
                                     options:MTLResourceStorageModeShared]
              : [d.device newBufferWithLength:16
                                      options:MTLResourceStorageModeShared];
    if (!b)
      return nil;
    if (bytes) {
      [q.copies addObject:key];
      ++run_copied;
      run_copied_bytes += bytes;
    }
  }
  q.bound[key] = b;
  q.offsets[key] = @(*offset);
  return b;
}

void pia_gpu_seq_dispatch(uint64_t seq, uint64_t lib, uint64_t lib_len,
                          uint64_t name, uint64_t name_len, uint64_t args,
                          uint64_t nargs, uint64_t threads) {
  @autoreleasepool {
    PiaGpuSequence *q = borrow(seq);
    if (!q || q.status != PIA_GPU_OK || threads == 0)
      return;
    uint64_t kernel = 0;
    int32_t found = run_kernel(lib, lib_len, name, name_len, &kernel);
    if (found != PIA_GPU_OK) {
      q.status = found;
      return;
    }
    id<MTLComputePipelineState> pipeline = borrow(kernel);
    [q.encoder setComputePipelineState:pipeline];
    const uint64_t *a = (const uint64_t *)(uintptr_t)args;
    for (uint64_t i = 0; i < nargs; ++i) {
      uint64_t addr = a[3 * i], bytes = a[3 * i + 1], how = a[3 * i + 2];
      if (how == PIA_GPU_ARG_SCALAR) {
        // A scalar is copied into the command buffer now: the host may
        // reuse its cell before the GPU runs.
        [q.encoder setBytes:(const void *)(uintptr_t)addr
                     length:bytes
                    atIndex:i];
        continue;
      }
      uint64_t offset = 0;
      id<MTLBuffer> b =
          seq_buffer(q, addr, bytes, how == PIA_GPU_ARG_WRITTEN, &offset);
      if (!b) {
        q.status = PIA_GPU_OUT_OF_MEMORY;
        return;
      }
      [q.encoder setBuffer:b offset:offset atIndex:i];
    }
    uint64_t group = pipeline.threadExecutionWidth;
    [q.encoder dispatchThreads:MTLSizeMake(threads, 1, 1)
         threadsPerThreadgroup:MTLSizeMake(group ? group : 64, 1, 1)];
    ++seq_dispatches;
  }
}

int32_t pia_gpu_seq_end(uint64_t seq) {
  if (!seq)
    return PIA_GPU_UNAVAILABLE;
  @autoreleasepool {
    PiaGpuSequence *q = CFBridgingRelease((void *)(uintptr_t)seq);
    [q.encoder endEncoding];
    if (q.status != PIA_GPU_OK)
      return q.status;
    [q.commands commit];
    [q.commands waitUntilCompleted];
    if (q.commands.status != MTLCommandBufferStatusCompleted)
      return PIA_GPU_FAULT;
    // Copy back each copied buffer a kernel writes.
    for (NSString *key in q.copies) {
      if (![q.written containsObject:key])
        continue;
      unsigned long long addr = 0, bytes = 0;
      sscanf(key.UTF8String, "%llx:%llx", &addr, &bytes);
      memcpy((void *)(uintptr_t)addr, q.bound[key].contents, bytes);
    }
    return PIA_GPU_OK;
  }
}
