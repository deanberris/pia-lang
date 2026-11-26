// The Metal host shim (metal_shim.h). Compiled with ARC: each handle is an
// object retained with CFBridgingRetain, and released with
// CFBridgingRelease when it is closed or freed.

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

int32_t pia_gpu_run(uint64_t lib, uint64_t lib_len, uint64_t name,
                    uint64_t name_len, uint64_t args, uint64_t nargs,
                    uint64_t threads) {
  @autoreleasepool {
    uint64_t kernel = 0;
    @synchronized([PiaGpuDevice class]) {
      if (!run_device) run_device = pia_gpu_device_open();
      if (!run_device) return PIA_GPU_UNAVAILABLE;
      if (!run_libraries) run_libraries = [NSMutableDictionary new];
      NSNumber *key = @(lib);
      uint64_t library = run_libraries[key].unsignedLongLongValue;
      if (!library) {
        library = pia_gpu_library_load(run_device,
                                       (const uint8_t *)(uintptr_t)lib, lib_len);
        if (!library) return PIA_GPU_FAULT;
        run_libraries[key] = @(library);
      }
      kernel = pia_gpu_kernel_get(library, (const uint8_t *)(uintptr_t)name,
                                  name_len);
    }
    if (!kernel) return PIA_GPU_FAULT;
    if (threads == 0) return PIA_GPU_OK;
    PiaGpuDevice *d = borrow(run_device);
    const uint64_t *a = (const uint64_t *)(uintptr_t)args;
    NSMutableArray<id<MTLBuffer>> *buffers = [NSMutableArray new];
    uint64_t handles[64];
    if (nargs > 64) return PIA_GPU_FAULT;
    for (uint64_t i = 0; i < nargs; ++i) {
      uint64_t bytes = a[3 * i + 1];
      id<MTLBuffer> b =
          bytes ? [d.device newBufferWithBytes:(const void *)(uintptr_t)a[3 * i]
                                        length:bytes
                                       options:MTLResourceStorageModeShared]
                : [d.device newBufferWithLength:16
                                       options:MTLResourceStorageModeShared];
      if (!b) return PIA_GPU_OUT_OF_MEMORY;
      [buffers addObject:b];
      handles[i] = (uint64_t)(uintptr_t)(__bridge void *)b;
    }
    id<MTLComputePipelineState> pipeline = borrow(kernel);
    uint64_t group = pipeline.threadExecutionWidth;
    int32_t r = pia_gpu_dispatch(run_device, kernel, handles, nargs, threads,
                                 group ? group : 64, 0);
    if (r != PIA_GPU_OK) return r;
    for (uint64_t i = 0; i < nargs; ++i)
      if (a[3 * i + 2] && a[3 * i + 1])
        memcpy((void *)(uintptr_t)a[3 * i], buffers[i].contents, a[3 * i + 1]);
    return PIA_GPU_OK;
  }
}
