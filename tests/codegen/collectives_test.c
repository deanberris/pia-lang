// Runs collectives.pia, compiled by piac --emit=obj, on MLIR's async
// runtime (ADR 0086): each phase of a spread is a parallel loop, so the
// results match a sequential run step for step.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void relax(uint32_t *a, uint64_t na, uint32_t *b, uint64_t nb, uint32_t steps);
void share(const uint32_t *xs, uint64_t nxs, uint64_t *ys, uint64_t nys);
void spans(const int32_t *xs, uint64_t nxs, int32_t *lo, uint64_t nlo,
           int32_t *hi, uint64_t nhi);
void any_zero(const uint32_t *xs, uint64_t nxs, uint8_t *ys, uint64_t nys);

static int failures;

static void fail(const char *what, uint64_t n, uint64_t i) {
  if (failures++ < 10)
    fprintf(stderr, "%s: n = %llu, cell %llu is wrong\n", what,
            (unsigned long long)n, (unsigned long long)i);
}

int main(void) {
  for (uint64_t n = 0; n < 200000; n = n * 3 + 1) {
    uint32_t *a = malloc(n * sizeof *a + 1), *b = malloc(n * sizeof *b + 1);
    uint32_t *ra = malloc(n * sizeof *ra + 1), *rb = malloc(n * sizeof *rb + 1);
    for (uint64_t i = 0; i < n; ++i)
      a[i] = ra[i] = (uint32_t)(i * 2654435761u), b[i] = 0;
    enum { STEPS = 7 };
    relax(a, n, b, n, STEPS);
    for (int t = 0; t < STEPS; ++t) {
      for (uint64_t i = 0; i < n; ++i) {
        uint32_t l = i > 0 ? ra[i - 1] : ra[i];
        uint32_t r = i + 1 < n ? ra[i + 1] : ra[i];
        rb[i] = l / 2 + r / 2;
      }
      for (uint64_t i = 0; i < n; ++i)
        ra[i] = rb[i];
    }
    for (uint64_t i = 0; i < n; ++i)
      if (a[i] != ra[i] || b[i] != rb[i])
        fail("relax", n, i);

    uint64_t *ys = malloc(n * sizeof *ys + 1), sum = 0;
    for (uint64_t i = 0; i < n; ++i)
      sum += a[i];
    share(a, n, ys, n);
    for (uint64_t i = 0; i < n; ++i)
      if (ys[i] != sum - a[i])
        fail("share", n, i);

    int32_t *xs = malloc(n * sizeof *xs + 1), *lo = malloc(n * sizeof *lo + 1),
            *hi = malloc(n * sizeof *hi + 1);
    int32_t mn = INT32_MAX, mx = INT32_MIN;
    for (uint64_t i = 0; i < n; ++i) {
      xs[i] = (int32_t)(a[i] ^ 0x5bd1e995u);
      if (xs[i] < mn)
        mn = xs[i];
      if (xs[i] > mx)
        mx = xs[i];
    }
    spans(xs, n, lo, n, hi, n);
    for (uint64_t i = 0; i < n; ++i)
      if (lo[i] != mn || hi[i] != mx)
        fail("spans", n, i);

    uint8_t *z = malloc(n + 1);
    int zero = 0;
    for (uint64_t i = 0; i < n; ++i)
      zero |= a[i] == 0;
    any_zero(a, n, z, n);
    for (uint64_t i = 0; i < n; ++i)
      if (z[i] != zero)
        fail("any_zero", n, i);
    if (n > 0) {
      a[n / 2] = 0;
      any_zero(a, n, z, n);
      for (uint64_t i = 0; i < n; ++i)
        if (z[i] != 1)
          fail("any_zero with a zero", n, i);
    }
    free(a), free(b), free(ra), free(rb), free(ys), free(xs), free(lo),
        free(hi), free(z);
  }
  if (failures)
    fprintf(stderr, "%d failures\n", failures);
  return failures != 0;
}
