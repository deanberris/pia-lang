// The C entry point of the Pia port: plb2's matmul.c main and mat_gen,
// with the multiply in matmul.pia's mm_mul. The matrices are flat and
// row-major, as mat_alloc lays them out (one calloc per matrix).

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void mm_mul(uint64_t n, const double *a, int64_t a_len, const double *b,
            int64_t b_len, double *c, int64_t c_len);

static double *mat_gen(int n) {
  double *a = calloc((size_t)n * n, sizeof(double));
  double tmp = 1.0 / n / n;
  if (!a)
    abort();
  for (int i = 0; i < n; ++i)
    for (int j = 0; j < n; ++j)
      a[(size_t)i * n + j] = tmp * (i - j) * (i + j);
  return a;
}

int main(int argc, char *argv[]) {
  int n = 1500;
  if (argc > 1)
    n = atoi(argv[1]);
  if (n <= 0 || n > 46340)
    abort();
  int64_t len = (int64_t)n * n;
  double *a = mat_gen(n), *b = mat_gen(n);
  double *c = calloc((size_t)len, sizeof(double));
  if (!c)
    abort();
  mm_mul((uint64_t)n, a, len, b, len, c, len);
  printf("%f\n", c[(size_t)(n >> 1) * n + (n >> 1)]);
  free(c);
  free(b);
  free(a);
  return 0;
}
