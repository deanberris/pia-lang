// The placed spread of placed.pia on the GPU against the same spread on
// the CPU (ADR 0068, section 6): integers must match bit for bit. Sizes
// that are not a multiple of the thread group check the kernel's bound,
// and an empty range checks that nothing runs.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void mix_cpu(const uint16_t *a, uint64_t na, const uint16_t *b, uint64_t nb,
             uint8_t k, uint32_t *c, uint64_t nc);
int32_t mix_gpu(const uint16_t *a, uint64_t na, const uint16_t *b, uint64_t nb,
                uint8_t k, uint32_t *c, uint64_t nc);

static int check(uint64_t n, uint8_t k) {
  uint16_t *a = malloc(2 * n + 2), *b = malloc(2 * n + 2);
  uint32_t *cpu = malloc(4 * n + 4), *gpu = malloc(4 * n + 4);
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
  free(a);
  free(b);
  free(cpu);
  free(gpu);
  if (!bad) printf("n=%llu k=%u: GPU = CPU\n", (unsigned long long)n, k);
  return bad;
}

int main(void) {
  int bad = 0;
  bad |= check(1, 7);
  bad |= check(63, 0);
  bad |= check(1000, 255);
  bad |= check(1000003, 42);
  // An empty range: nothing runs, and the run succeeds.
  int32_t r = mix_gpu(NULL, 0, NULL, 0, 1, NULL, 0);
  if (r != 0) {
    fprintf(stderr, "empty: mix_gpu returned %d\n", r);
    bad = 1;
  }
  return bad;
}
