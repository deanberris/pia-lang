// Runs the kernels in fp_licence.pia, compiled by piac --emit=obj, against
// scalar references in C. The licensed kernels may sum in any order and
// fuse into FMAs (ADR 0012), so they are checked against the bound that
// holds for every order, |computed - exact| <= gamma_n * sum |x_i * y_i|
// with gamma_n = n u / (1 - n u) (Higham, Accuracy and Stability of
// Numerical Algorithms, 2nd ed., section 3.1), where the exact value is
// computed in a wider type. The strict kernel must equal C's in-order
// loop bit for bit: BUILD.bazel compiles this file with -ffp-contract=off.

#if defined(__clang__)
#pragma STDC FP_CONTRACT OFF
#endif

#include <float.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

float dot(const float *xs, uint64_t nxs, const float *ys, uint64_t nys);
float strict_dot(const float *xs, uint64_t nxs, const float *ys,
                 uint64_t nys);
void axpy_rows(uint64_t n, const double *a, uint64_t na, const double *b,
               uint64_t nb, double *c, uint64_t nc);

static int failures = 0;

// A fixed sequence, so a failure reproduces: values in [-1, 1).
static uint64_t state = 0x9e3779b97f4a7c15u;
static double next(void) {
  state = state * 6364136223846793005u + 1442695040888963407u;
  return (double)(state >> 11) / (double)(1ull << 52) - 1.0;
}

static double gamma_n(uint64_t n, double u) { return n * u / (1.0 - n * u); }

static void check_dot(uint64_t n) {
  float *xs = malloc(n * sizeof(float) + 1), *ys = malloc(n * sizeof(float) + 1);
  for (uint64_t i = 0; i < n; ++i) {
    xs[i] = (float)next();
    ys[i] = (float)next();
  }
  // Each product of two floats is exact in a double, and the sum of n of
  // them is within n * 2^-53 of exact, far below the f32 bound.
  double exact = 0.0, magnitude = 0.0;
  float in_order = 0.0f;
  for (uint64_t i = 0; i < n; ++i) {
    exact += (double)xs[i] * (double)ys[i];
    magnitude += fabs((double)xs[i] * (double)ys[i]);
    in_order = in_order + xs[i] * ys[i];
  }
  float licensed = dot(xs, n, ys, n);
  double bound = gamma_n(n, FLT_EPSILON / 2) * magnitude + n * DBL_EPSILON * magnitude;
  if (fabs((double)licensed - exact) > bound) {
    printf("dot(n = %llu) = %.9g, exact %.17g, beyond the bound %.3g\n",
           (unsigned long long)n, licensed, exact, bound);
    ++failures;
  }
  float strict = strict_dot(xs, n, ys, n);
  if (memcmp(&strict, &in_order, sizeof strict) != 0) {
    printf("strict_dot(n = %llu) = %a, C's in-order loop %a\n",
           (unsigned long long)n, strict, in_order);
    ++failures;
  }
  free(xs);
  free(ys);
}

static void check_matmul(uint64_t n) {
  size_t cells = n * n;
  double *a = malloc(cells * sizeof(double) + 1);
  double *b = malloc(cells * sizeof(double) + 1);
  double *c = calloc(cells + 1, sizeof(double));
  for (size_t i = 0; i < cells; ++i) {
    a[i] = next();
    b[i] = next();
  }
  axpy_rows(n, a, cells, b, cells, c, cells);
  // Each cell is a sum of n products, accumulated in k order; contraction
  // removes roundings, so the strict bound holds. The reference is in
  // long double where it is wider, and the bound allows for it where not.
  for (uint64_t i = 0; i < n; ++i)
    for (uint64_t j = 0; j < n; ++j) {
      long double exact = 0.0L, magnitude = 0.0L;
      for (uint64_t k = 0; k < n; ++k) {
        exact += (long double)a[i * n + k] * (long double)b[k * n + j];
        magnitude += fabsl((long double)a[i * n + k] * b[k * n + j]);
      }
      double bound = 2.0 * gamma_n(n, DBL_EPSILON / 2) * (double)magnitude;
      double got = c[i * n + j];
      if (fabs(got - (double)exact) > bound) {
        printf("axpy_rows(n = %llu) c[%llu][%llu] = %.17g, exact %.17Lg, "
               "beyond the bound %.3g\n",
               (unsigned long long)n, (unsigned long long)i,
               (unsigned long long)j, got, exact, bound);
        ++failures;
      }
    }
  free(a);
  free(b);
  free(c);
}

int main(void) {
  // Lengths below, at and past the vector width, and with a remainder.
  static const uint64_t lengths[] = {0, 1, 3, 4, 7, 8, 15, 16, 17, 31,
                                     32, 33, 100, 1000, 4099, 65536};
  for (size_t i = 0; i < sizeof lengths / sizeof *lengths; ++i)
    check_dot(lengths[i]);
  static const uint64_t sizes[] = {1, 2, 3, 5, 8, 17, 64};
  for (size_t i = 0; i < sizeof sizes / sizeof *sizes; ++i)
    check_matmul(sizes[i]);
  if (failures) {
    printf("%d failures\n", failures);
    return 1;
  }
  printf("fp_licence: all kernels within their bounds\n");
  return 0;
}
