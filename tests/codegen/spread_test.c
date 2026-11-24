// Runs spread.pia, compiled by piac --emit=obj, on MLIR's async runtime
// (ADR 0060): every iteration ran exactly once, whatever the split.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void square(const uint32_t *xs, uint64_t nxs, uint64_t *ys, uint64_t nys);
void zero_basins(const uint64_t *label, uint64_t nlabel, uint32_t *v,
                 uint64_t nv, uint64_t nb);

int main(void) {
  int failures = 0;
  for (uint64_t n = 0; n < 3000000; n = n * 3 + 1) {
    uint32_t *xs = malloc(n * sizeof *xs + 1);
    uint64_t *ys = malloc(n * sizeof *ys + 1);
    for (uint64_t i = 0; i < n; ++i)
      xs[i] = (uint32_t)(i * 2654435761u);
    square(xs, n, ys, n);
    for (uint64_t i = 0; i < n; ++i)
      if (ys[i] != (uint64_t)xs[i] * xs[i] && failures++ < 10)
        fprintf(stderr, "square: n = %llu, ys[%llu] is wrong\n",
                (unsigned long long)n, (unsigned long long)i);
    free(xs), free(ys);
  }
  // Each basin adds one to its own cells, so every cell ends at 1 whether
  // or not its label names a basin that runs; labels past nb stay 0.
  enum { N = 100000, NB = 37 };
  uint64_t *label = malloc(N * sizeof *label);
  uint32_t *v = calloc(N, sizeof *v);
  for (uint64_t c = 0; c < N; ++c)
    label[c] = (c * 7919) % (NB + 3);
  zero_basins(label, N, v, N, NB);
  for (uint64_t c = 0; c < N; ++c)
    if (v[c] != (label[c] < NB ? 1u : 0u) && failures++ < 10)
      fprintf(stderr, "zero_basins: v[%llu] = %u, label %llu\n",
              (unsigned long long)c, v[c], (unsigned long long)label[c]);
  free(label), free(v);
  if (failures)
    fprintf(stderr, "%d failures\n", failures);
  return failures != 0;
}
