// The placed spread of placed.pia on the GPU against the same spread on
// the CPU (ADR 0068, section 6): integers must match bit for bit. Sizes
// that are not a multiple of the thread group check the kernel's bound,
// and an empty range checks that nothing runs. Each size runs with buffers
// on page boundaries, which the shim wraps in place, and with buffers one
// element past one, which it copies.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

void mix_cpu(const uint16_t *a, uint64_t na, const uint16_t *b, uint64_t nb,
             uint8_t k, uint32_t *c, uint64_t nc);
int32_t mix_gpu(const uint16_t *a, uint64_t na, const uint16_t *b, uint64_t nb,
                uint8_t k, uint32_t *c, uint64_t nc);

void pia_gpu_run_stats(uint64_t *wrapped, uint64_t *copied,
                       uint64_t *copied_bytes);

// `bytes` on a page boundary, or `skew` bytes past one.
static void *page_alloc(size_t bytes, size_t skew) {
  void *p = NULL;
  if (posix_memalign(&p, (size_t)getpagesize(), bytes + skew)) abort();
  return (char *)p + skew;
}

static void page_free(void *p, size_t skew) { free((char *)p - skew); }

static int check(uint64_t n, uint8_t k, int skewed) {
  size_t s16 = skewed ? 2 : 0, s32 = skewed ? 4 : 0;
  uint16_t *a = page_alloc(2 * n + 2, s16), *b = page_alloc(2 * n + 2, s16);
  uint32_t *cpu = malloc(4 * n + 4), *gpu = page_alloc(4 * n + 4, s32);
  uint32_t seed = 12345u + (uint32_t)n;
  for (uint64_t i = 0; i < n; ++i) {
    seed = seed * 1103515245u + 12345u;
    a[i] = (uint16_t)(seed >> 8);
    seed = seed * 1103515245u + 12345u;
    b[i] = (uint16_t)(seed >> 8);
    gpu[i] = 0xdeadbeef;
  }
  mix_cpu(a, n, b, n, k, cpu, n);
  int32_t r = mix_gpu(a, n, b, n, k, gpu, n);
  int bad = 0;
  if (r != 0) {
    fprintf(stderr, "n=%llu: mix_gpu returned %d\n", (unsigned long long)n, r);
    bad = 1;
  } else {
    for (uint64_t i = 0; i < n; ++i)
      if (cpu[i] != gpu[i]) {
        fprintf(stderr, "n=%llu: c[%llu] is %u on the GPU, %u on the CPU\n",
                (unsigned long long)n, (unsigned long long)i, gpu[i], cpu[i]);
        bad = 1;
        break;
      }
  }
  page_free(a, s16);
  page_free(b, s16);
  free(cpu);
  page_free(gpu, s32);
  if (!bad)
    printf("n=%llu k=%u %s: GPU = CPU\n", (unsigned long long)n, k,
           skewed ? "copied" : "in place");
  return bad;
}

int main(void) {
  int bad = 0;
  for (int skewed = 0; skewed < 2; ++skewed) {
    uint64_t w0, c0, b0, w1, c1, b1;
    pia_gpu_run_stats(&w0, &c0, &b0);
    bad |= check(1, 7, skewed);
    bad |= check(63, 0, skewed);
    bad |= check(1000, 255, skewed);
    bad |= check(1000003, 42, skewed);
    pia_gpu_run_stats(&w1, &c1, &b1);
    // Three buffers a run, four runs: all wrapped, or all copied.
    uint64_t wrapped = w1 - w0, big = b1 - b0;
    printf("%s: %llu buffers wrapped, %llu bytes copied\n",
           skewed ? "skewed" : "aligned", (unsigned long long)wrapped,
           (unsigned long long)big);
    if (skewed ? big < 3 * 1000003 * 2 : wrapped < 12 || big > 4096) {
      fprintf(stderr, "the buffers were not bound as expected\n");
      bad = 1;
    }
  }
  // An empty range: nothing runs, and the run succeeds.
  int32_t r = mix_gpu(NULL, 0, NULL, 0, 1, NULL, 0);
  if (r != 0) {
    fprintf(stderr, "empty: mix_gpu returned %d\n", r);
    bad = 1;
  }
  return bad;
}
