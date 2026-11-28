// Runs the kernels in vectorise.pia, compiled by piac --emit=obj, against
// C's scalar loops bit for bit. Both sides are strict IEEE: elementwise
// kernels round each element once whatever the vector width, so the
// vectorised code must agree exactly. BUILD.bazel compiles this file with
// -ffp-contract=off.

#if defined(__clang__)
#pragma STDC FP_CONTRACT OFF
#endif

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

void clamp_scale(const float *xs, uint64_t nxs, float k, float *dst,
                 uint64_t ndst);
void clamp_scale_u8(const uint8_t *xs, uint64_t nxs, uint16_t *dst,
                    uint64_t ndst);

enum { kMax = 1027 };

int main(void) {
  static float xs[kMax], got[kMax], want[kMax];
  static uint8_t bytes[kMax];
  static uint16_t wide[kMax], wide_want[kMax];
  int failures = 0;
  // Ordinary values on both sides of [0, 1], the ends themselves, signed
  // zeros, infinities and a NaN.
  for (int i = 0; i < kMax; ++i)
    xs[i] = (float)(i % 37) / 12.0f - 1.0f;
  xs[3] = 0.0f;
  xs[4] = -0.0f;
  xs[5] = 1.0f;
  xs[6] = INFINITY;
  xs[7] = -INFINITY;
  xs[8] = NAN;
  for (int i = 0; i < kMax; ++i)
    bytes[i] = (uint8_t)(i * 7);
  // Lengths below, at and past each vector width, with remainders.
  static const uint64_t lengths[] = {0, 1, 3, 4, 7, 8, 15, 16, 17, 31, 32,
                                     33, 63, 64, 65, 100, 1000, kMax};
  for (size_t l = 0; l < sizeof lengths / sizeof *lengths; ++l) {
    uint64_t n = lengths[l];
    float k = 2.5f;
    for (uint64_t i = 0; i < n; ++i) {
      float x = xs[i];
      float c = x < 0.0f ? 0.0f : x > 1.0f ? 1.0f : x;
      want[i] = c * k;
      uint16_t b = bytes[i];
      wide_want[i] = (uint16_t)((b > 200 ? 200 : b) * 3);
    }
    clamp_scale(xs, n, k, got, n);
    clamp_scale_u8(bytes, n, wide, n);
    for (uint64_t i = 0; i < n; ++i) {
      if (memcmp(&got[i], &want[i], sizeof(float)) != 0) {
        printf("clamp_scale(n = %llu)[%llu] = %a, C %a\n",
               (unsigned long long)n, (unsigned long long)i, got[i],
               want[i]);
        ++failures;
      }
      if (wide[i] != wide_want[i]) {
        printf("clamp_scale_u8(n = %llu)[%llu] = %u, C %u\n",
               (unsigned long long)n, (unsigned long long)i, wide[i],
               wide_want[i]);
        ++failures;
      }
    }
  }
  if (failures) {
    printf("%d failures\n", failures);
    return 1;
  }
  printf("vectorise: every kernel equals C bit for bit\n");
  return 0;
}
