// Runs Pia.Math's square roots against C's sqrtf and sqrt, bit for bit:
// `sqrt`, compiled to the hardware instruction by its @lower, and
// `sqrt_soft`, the proved integer algorithm that is its body, on f32 and
// f64. A NaN result only has to be a NaN, since the payload differs
// between targets. The f32 inputs are the special values, every power of
// two and its neighbours, and one bit pattern in 251 over all 2^32; the f64
// inputs are the special values, every power of two and its neighbours,
// the smallest subnormals, and 8M patterns from a xorshift generator.

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

float pia$Pia$Math$sqrt__f32(float x);
float pia$Pia$Math$sqrt_soft__f32(float x);
double pia$Pia$Math$sqrt__f64(double x);
double pia$Pia$Math$sqrt_soft__f64(double x);

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
  check("sqrt", b, pia$Pia$Math$sqrt__f32(x), want);
  check("sqrt_soft", b, pia$Pia$Math$sqrt_soft__f32(x), want);
}

static uint64_t bitsOf64(double x) {
  uint64_t b;
  memcpy(&b, &x, sizeof b);
  return b;
}

static double doubleOf(uint64_t b) {
  double x;
  memcpy(&x, &b, sizeof x);
  return x;
}

static void check64(const char *name, uint64_t in, double got, double want) {
  if (isnan(want) ? isnan(got) : bitsOf64(got) == bitsOf64(want))
    return;
  if (++failures <= 20)
    fprintf(stderr, "%s(0x%016llx) = 0x%016llx, sqrt gives 0x%016llx\n", name,
            (unsigned long long)in, (unsigned long long)bitsOf64(got),
            (unsigned long long)bitsOf64(want));
}

static void one64(uint64_t b) {
  double x = doubleOf(b);
  double want = sqrt(x);
  check64("sqrt", b, pia$Pia$Math$sqrt__f64(x), want);
  check64("sqrt_soft", b, pia$Pia$Math$sqrt_soft__f64(x), want);
}

static long sweep64(void) {
  static const uint64_t specials[] = {
      0x0000000000000000, 0x8000000000000000, 0x7ff0000000000000,
      0xfff0000000000000, 0x7ff8000000000000, 0xfff8000000000000,
      0x7ff0000000000001, 0x7ff7ffffffffffff, 0x000fffffffffffff,
      0x0010000000000000, 0x3ff0000000000000, 0x4010000000000000,
      0x7fefffffffffffff, 0x8000000000000001, 0xbff0000000000000,
  };
  long n = 0;
  for (size_t i = 0; i < sizeof specials / sizeof specials[0]; ++i, ++n)
    one64(specials[i]);
  for (uint64_t e = 0; e < 2048; ++e)
    for (uint64_t d = 0; d < 5; ++d) {
      uint64_t p = e << 52;
      one64(p + d);
      one64(p - d);
      one64(p | 0xfffffffffffffull);
      n += 3;
    }
  for (uint64_t b = 1; b < (1u << 16); ++b, ++n)
    one64(b);
  uint64_t s = 0x9e3779b97f4a7c15ull;
  for (long i = 0; i < 8000000; ++i, ++n) {
    s ^= s << 13;
    s ^= s >> 7;
    s ^= s << 17;
    one64(s);
  }
  return n;
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
  long n64 = sweep64();
  if (failures) {
    fprintf(stderr, "%d of %ld f32 and %ld f64 inputs differ from C\n",
            failures, n, n64);
    return 1;
  }
  printf("sqrt and sqrt_soft match sqrtf on %ld inputs and sqrt on %ld\n", n,
         n64);
  return 0;
}
