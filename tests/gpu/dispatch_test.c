// The step 1 kernel, c = a + b over 1024 i32, dispatched on this Mac's GPU
// (ADR 0068, step 2): once through the shim's C API, and once from Pia
// through Pia.Gpu (gpu_add.pia). Both must give c = a + b exactly.

#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "src/runtime/metal/metal_shim.h"

extern const unsigned char pia_test_add_metallib[];
extern const unsigned long pia_test_add_metallib_len;

int32_t gpu_add(const uint8_t *metallib, uint64_t nmetallib, const int32_t *a,
                uint64_t na, const int32_t *b, uint64_t nb, int32_t *c,
                uint64_t nc);

enum { N = 1024 };

static int check(const char *how, const int32_t *a, const int32_t *b,
                 const int32_t *c) {
  for (int i = 0; i < N; ++i)
    if (c[i] != a[i] + b[i]) {
      fprintf(stderr, "%s: c[%d] = %d, want %d\n", how, i, c[i], a[i] + b[i]);
      return 1;
    }
  printf("%s: c = a + b over %d i32\n", how, N);
  return 0;
}

int main(void) {
  static int32_t a[N], b[N], c[N];
  for (int i = 0; i < N; ++i) a[i] = i * 3 - 700, b[i] = 100000 - i * i;

  // The shim's C API.
  uint64_t dev = pia_gpu_device_open();
  if (!dev) {
    fprintf(stderr, "no GPU\n");
    return 1;
  }
  uint64_t lib = pia_gpu_library_load(dev, pia_test_add_metallib,
                                      pia_test_add_metallib_len);
  uint64_t k = pia_gpu_kernel_get(lib, (const uint8_t *)"add", 3);
  if (!lib || !k || pia_gpu_kernel_get(lib, (const uint8_t *)"nope", 4)) {
    fprintf(stderr, "the library or its kernel did not load\n");
    return 1;
  }
  uint64_t bufs[3];
  for (int i = 0; i < 3; ++i) bufs[i] = pia_gpu_buffer_new(dev, N * 4);
  memcpy((void *)(uintptr_t)pia_gpu_buffer_contents(bufs[0]), a, sizeof a);
  memcpy((void *)(uintptr_t)pia_gpu_buffer_contents(bufs[1]), b, sizeof b);
  int32_t r = pia_gpu_dispatch(dev, k, bufs, 3, N, 64, 10000);
  if (r != PIA_GPU_OK) {
    fprintf(stderr, "dispatch: %d\n", r);
    return 1;
  }
  memcpy(c, (void *)(uintptr_t)pia_gpu_buffer_contents(bufs[2]), sizeof c);
  if (check("shim", a, b, c)) return 1;
  for (int i = 0; i < 3; ++i) pia_gpu_buffer_free(bufs[i]);
  pia_gpu_library_free(lib);
  pia_gpu_device_close(dev);

  // From Pia.
  memset(c, 0, sizeof c);
  r = gpu_add(pia_test_add_metallib, pia_test_add_metallib_len, a, N, b, N, c,
              N);
  if (r != 0) {
    fprintf(stderr, "gpu_add: %d\n", r);
    return 1;
  }
  return check("Pia.Gpu", a, b, c);
}
