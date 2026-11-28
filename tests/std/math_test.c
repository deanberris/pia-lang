// Runs Pia.Math's square roots against C's sqrtf, bit for bit: `sqrt`,
// compiled to the hardware instruction by its @lower, and `sqrt_soft`, the
// proved integer algorithm that is its body. A NaN result only has to be
// a NaN, since the payload differs between targets. The inputs are the
// special values, every power of two and its neighbours, and a sweep of
// one bit pattern in 251 over all 2^32.

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

float pia$Pia$Math$sqrt(float x);
float pia$Pia$Math$sqrt_soft(float x);

static uint32_t bitsOf(float x) {
  uint32_t b;
  memcpy(&b, &x, sizeof b);
  return b;
}

static float floatOf(uint32_t b) {
  float x;
  memcpy(&x, &b, sizeof x);
  return x;
}

static int failures = 0;

static void check(const char *name, uint32_t in, float got, float want) {
  if (isnan(want) ? isnan(got) : bitsOf(got) == bitsOf(want))
    return;
  if (++failures <= 20)
    fprintf(stderr, "%s(0x%08x) = 0x%08x, sqrtf gives 0x%08x\n", name, in,
            bitsOf(got), bitsOf(want));
}

static void one(uint32_t b) {
  float x = floatOf(b);
  float want = sqrtf(x);
  check("sqrt", b, pia$Pia$Math$sqrt(x), want);
  check("sqrt_soft", b, pia$Pia$Math$sqrt_soft(x), want);
}

int main(void) {
  static const uint32_t specials[] = {
      0x00000000, 0x80000000, 0x7f800000, 0xff800000, 0x7fc00000, 0xffc00000,
      0x7f800001, 0x7fbfffff, 0x00000001, 0x00000002, 0x00000003, 0x007fffff,
      0x00800000, 0x3f800000, 0x40800000, 0x7f7fffff, 0x80000001, 0xbf800000,
  };
  for (size_t i = 0; i < sizeof specials / sizeof specials[0]; ++i)
    one(specials[i]);
  long n = 0;
  for (uint32_t e = 0; e < 256; ++e)
    for (uint32_t d = 0; d < 5; ++d) {
      uint32_t p = e << 23;
      one(p + d);
      one(p - d);
      one(p | 0x7fffffu);
      n += 3;
    }
  for (uint64_t b = 0; b <= 0xffffffffu; b += 251, ++n)
    one((uint32_t)b);
  if (failures) {
    fprintf(stderr, "%d of %ld inputs differ from sqrtf\n", failures, n);
    return 1;
  }
  printf("sqrt and sqrt_soft match sqrtf on %ld inputs\n", n);
  return 0;
}
