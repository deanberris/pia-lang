// Runs add4 and mul_add4 from lower_vector.pia against C, bit for bit. The
// same harness links the object compiled from their vector lowerings
// (lower_vector_run_test) and the one compiled from their Pia bodies with
// --lower=off (lower_vector_body_run_test), so both forms agree with C and
// with each other (ADR 0087, step 1).

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

void add4(const float *a, const float *b, float *c);
void mul_add4(const float *a, const float *b, const float *c, float *d);

static uint32_t bits(float x) {
  uint32_t u;
  memcpy(&u, &x, sizeof u);
  return u;
}

// Equal bits, or both NaN: a NaN's payload is the target's choice.
static int same(float x, float y) {
  return bits(x) == bits(y) || (isnan(x) && isnan(y));
}

int main(void) {
  const float values[] = {0.0f,        -0.0f,     1.0f,      -1.0f,
                          0.1f,        3.0e38f,   -3.0e38f,  1.0e-45f,
                          1.17e-38f,   INFINITY,  -INFINITY, NAN,
                          16777216.0f, 0.333333f, -2.5f,     1.0e-7f};
  const int n = sizeof values / sizeof values[0];
  int failures = 0;
  for (int i = 0; i < n; ++i)
    for (int j = 0; j < n; ++j) {
      float a[4], b[4], c[4], s[4], d[4];
      for (int l = 0; l < 4; ++l) {
        a[l] = values[(i + l) % n];
        b[l] = values[(j + 3 * l) % n];
        c[l] = values[(i + j + l) % n];
      }
      add4(a, b, s);
      mul_add4(a, b, c, d);
      for (int l = 0; l < 4; ++l) {
        volatile float p = a[l] * b[l];
        float want_s = a[l] + b[l], want_d = p + c[l];
        if (!same(s[l], want_s)) {
          fprintf(stderr, "add4 lane %d: %a + %a = %a, expected %a\n", l, a[l],
                  b[l], s[l], want_s);
          ++failures;
        }
        if (!same(d[l], want_d)) {
          fprintf(stderr, "mul_add4 lane %d: %a * %a + %a = %a, expected %a\n",
                  l, a[l], b[l], c[l], d[l], want_d);
          ++failures;
        }
      }
    }
  if (failures)
    fprintf(stderr, "%d failures\n", failures);
  return failures != 0;
}
