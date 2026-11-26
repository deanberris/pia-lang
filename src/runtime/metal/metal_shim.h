// The Metal host shim (ADR 0068, section 3): the few calls Pia makes to run
// a kernel on an Apple GPU. Objects are handles, a uint64_t that is 0 for
// none, so that Pia declares every call as an extern over integers and
// buffers. Everything here is trusted, and listed in Pia's trust report
// through the contracts of lib/Pia/Gpu.pia.
//
// v0 is synchronous: pia_gpu_dispatch returns once the GPU has finished,
// so no buffer is in use by the device when the CPU runs again.

#ifndef PIA_RUNTIME_METAL_SHIM_H
#define PIA_RUNTIME_METAL_SHIM_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

// The results of pia_gpu_dispatch, in Gpu.error's order (lib/Pia/Gpu.pia).
enum {
  PIA_GPU_OK = 0,
  PIA_GPU_UNAVAILABLE = 1,
  PIA_GPU_OUT_OF_MEMORY = 2,
  PIA_GPU_FAULT = 3,
  PIA_GPU_TIMEOUT = 4,
};

// The system's default GPU and a command queue on it, or 0 if there is none.
uint64_t pia_gpu_device_open(void);
void pia_gpu_device_close(uint64_t device);

// A buffer of `bytes` bytes in shared storage, zeroed, or 0 if it cannot be
// made. The CPU sees it at pia_gpu_buffer_contents, with no copy.
uint64_t pia_gpu_buffer_new(uint64_t device, uint64_t bytes);
uint64_t pia_gpu_buffer_contents(uint64_t buffer);
uint64_t pia_gpu_buffer_length(uint64_t buffer);
void pia_gpu_buffer_free(uint64_t buffer);

// A library from the bytes of a .metallib, such as one metal_library
// embedded (tools/gpu/metal.bzl), or 0 if Metal rejects it.
uint64_t pia_gpu_library_load(uint64_t device, const uint8_t *bytes,
                              uint64_t n);
void pia_gpu_library_free(uint64_t library);

// The kernel named `name` (n bytes, no NUL needed) in a library, as a
// compute pipeline, or 0 if there is no such kernel. Lookup is by name, so
// a library piac embeds later (#435) works the same way. Pipelines are
// cached per library and name; the library owns them.
uint64_t pia_gpu_kernel_get(uint64_t library, const uint8_t *name, uint64_t n);

// Runs `kernel` over `threads` threads, `group` to a threadgroup, with
// buffers[i] bound at index i, and waits for it to finish. Returns
// PIA_GPU_OK, PIA_GPU_FAULT if the command buffer failed, or
// PIA_GPU_TIMEOUT if it did not finish within timeout_ms (0: no limit).
// After a timeout the kernel may still be running, so its buffers must not
// be freed or read until the device is closed.
int32_t pia_gpu_dispatch(uint64_t device, uint64_t kernel,
                         const uint64_t *buffers, uint64_t nbuffers,
                         uint64_t threads, uint64_t group, uint64_t timeout_ms);

// What piac generates for a spread placed on the GPU (ADR 0068, step 3):
// runs the kernel `name` (name_len bytes) of the .metallib at lib (lib_len
// bytes, embedded in the program) over `threads` threads. args points to
// nargs triples of uint64_t: a host address, a size in bytes, and whether
// the kernel writes it. Each is bound in order as a buffer. On Apple
// silicon the CPU and GPU share memory, so a buffer that starts on a page
// boundary is wrapped where it is, without a copy: its length is rounded
// up to a page, and that last page is mapped because the buffer ends in
// it. Any other buffer is copied in before the kernel runs, and copied
// back after it when it is written. Either way is safe because the run is
// synchronous (ADR 0068, section 3): the caller waits, so nothing else
// touches the buffers while the kernel has them. The device, each library
// and each kernel are opened once and kept. Returns PIA_GPU_OK or the
// error, in Gpu.error's order.
int32_t pia_gpu_run(uint64_t lib, uint64_t lib_len, uint64_t name,
                    uint64_t name_len, uint64_t args, uint64_t nargs,
                    uint64_t threads);

// How pia_gpu_run has bound buffers since the program started: wrapped in
// place, or copied, and the bytes copied in.
void pia_gpu_run_stats(uint64_t *wrapped, uint64_t *copied,
                       uint64_t *copied_bytes);

#ifdef __cplusplus
}
#endif

#endif
