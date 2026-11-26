// Runs matmul from lower_linalg.pia against C. The same harness links the
// object compiled from its MLIR form (lower_linalg_test) and the one
// compiled from its Pia body with --lower=off (lower_linalg_body_test), so
// both forms agree with C and with each other on every input tried
// (ADR 0065).

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void matmul(const int8_t *a, const int8_t *b, int32_t *c);

static int check(const int8_t *a, const int8_t *b) {
  int32_t c[16], want[16];
  for (int i = 0; i < 16; ++i)
    c[i] = 0x5a5a5a5a;
  matmul(a, b, c);
  int failures = 0;
  for (int i = 0; i < 4; ++i)
    for (int j = 0; j < 4; ++j) {
      int32_t sum = 0;
      for (int p = 0; p < 4; ++p)
        sum += (int32_t)a[i * 4 + p] * b[p * 4 + j];
      want[i * 4 + j] = sum;
      if (c[i * 4 + j] != sum) {
        fprintf(stderr, "c[%d][%d] = %d, expected %d\n", i, j, c[i * 4 + j],
                sum);
        ++failures;
      }
    }
  return failures;
}

int main(void) {
  int8_t a[16], b[16];
  int failures = 0;
  // The extremes, where a wrong extension or a narrow sum would show.
  const int8_t corners[] = {-128, -1, 0, 1, 127};
  for (int x = 0; x < 5; ++x)
    for (int y = 0; y < 5; ++y) {
      for (int i = 0; i < 16; ++i) {
        a[i] = corners[x];
        b[i] = corners[y];
      }
      failures += check(a, b);
    }
  srand(65);
  for (int n = 0; n < 10000 && failures < 10; ++n) {
    for (int i = 0; i < 16; ++i) {
      a[i] = (int8_t)(rand() & 0xff);
      b[i] = (int8_t)(rand() & 0xff);
    }
    failures += check(a, b);
  }
  return failures != 0;
}
