// Runs the functions in floats.pia, compiled by piac --emit=obj, and
// compares each result with C's bit for bit, over special values (zeros,
// subnormals, infinities, NaN) and a sweep of ordinary ones. C here is
// strict too: BUILD.bazel compiles this file with -ffp-contract=off, so
// `a * b + c` is two roundings on both sides.

#pragma STDC FP_CONTRACT OFF

#include <float.h>
#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

float add32(float a, float b);
float sub32(float a, float b);
float mul32(float a, float b);
float div32(float a, float b);
float neg32(float a);
double add64(double a, double b);
double div64(double a, double b);
float muladd32(float a, float b, float c);
double muladd64(double a, double b, double c);
bool lt32(float a, float b);
bool le32(float a, float b);
bool gt64(double a, double b);
bool ge64(double a, double b);
bool eq32(float a, float b);
bool ne32(float a, float b);
float tenth32(float x);
double tenth64(double x);
float zero(bool negative);
float halve(float x);
double poly(double x);
float clamp01(float x);
float dot(const float *xs, uint64_t nxs, const float *ys, uint64_t nys);
void scale(const float *xs, uint64_t nxs, float k, float *dst, uint64_t ndst);

float sum3(float a, float b, float c);

struct point {
  float x, y;
};
float norm2(float x, float y);
void mid(float px, float py, float qx, float qy, struct point *out);
float of_i32(int32_t n);
double of_u64(uint64_t n);
double widen(float x);
float narrow(double x);
int32_t trunc_i32(float x);
uint8_t trunc_u8(double x);
uint32_t to_bits32(float x);
float from_bits32(uint32_t u);
uint64_t to_bits64(double x);
double from_bits64(uint64_t u);
float fabs32(float x);
float mean(const float *xs, uint64_t n);

static int failures = 0;

#define EXPECT(cond, ...)                                                      \
  do {                                                                         \
    if (!(cond) && failures++ < 10) {                                          \
      fprintf(stderr, __VA_ARGS__);                                            \
      fputc('\n', stderr);                                                     \
    }                                                                          \
  } while (0)

static uint32_t bits32(float x) {
  uint32_t u;
  memcpy(&u, &x, sizeof u);
  return u;
}

static uint64_t bits64(double x) {
  uint64_t u;
  memcpy(&u, &x, sizeof u);
  return u;
}

// The same value: the same bits, or both NaN (whose payload C does not fix).
static bool same32(float a, float b) {
  return (isnan(a) && isnan(b)) || bits32(a) == bits32(b);
}

static bool same64(double a, double b) {
  return (isnan(a) && isnan(b)) || bits64(a) == bits64(b);
}

int main(void) {
  float special[] = {0.0f,    -0.0f,    1.0f,        -1.0f,
                     0.1f,    3.0f,     FLT_MIN,     FLT_MIN / 4.0f,
                     FLT_MAX, -FLT_MAX, INFINITY,    -INFINITY,
                     NAN,     1.0e-40f, 16777216.0f, 0.333333343f};
  size_t n = sizeof special / sizeof special[0];
  for (size_t i = 0; i < n; ++i) {
    float a = special[i];
    EXPECT(same32(neg32(a), -a), "neg32(%a)", a);
    EXPECT(same32(halve(a), a * 0.5f), "halve(%a)", a);
    float c = a < 0.0f ? 0.0f : a > 1.0f ? 1.0f : a;
    EXPECT(same32(clamp01(a), c), "clamp01(%a)", a);
    for (size_t j = 0; j < n; ++j) {
      float b = special[j];
      EXPECT(same32(add32(a, b), a + b), "add32(%a, %a)", a, b);
      EXPECT(same32(sub32(a, b), a - b), "sub32(%a, %a)", a, b);
      EXPECT(same32(mul32(a, b), a * b), "mul32(%a, %a)", a, b);
      EXPECT(same32(div32(a, b), a / b), "div32(%a, %a)", a, b);
      EXPECT(lt32(a, b) == (a < b), "lt32(%a, %a)", a, b);
      EXPECT(le32(a, b) == (a <= b), "le32(%a, %a)", a, b);
      EXPECT(eq32(a, b) == (a == b), "eq32(%a, %a)", a, b);
      EXPECT(ne32(a, b) == (a != b), "ne32(%a, %a)", a, b);
      double x = a, y = b;
      EXPECT(same64(add64(x, y), x + y), "add64(%a, %a)", x, y);
      EXPECT(same64(div64(x, y), x / y), "div64(%a, %a)", x, y);
      EXPECT(gt64(x, y) == (x > y), "gt64(%a, %a)", x, y);
      EXPECT(ge64(x, y) == (x >= y), "ge64(%a, %a)", x, y);
    }
  }

  // 1 + 2^-12 squared is 1 + 2^-11 + 2^-24, and minus (1 + 2^-11) leaves
  // 2^-24 when fused, but 0 when the product is rounded first.
  float e = 1.0f + 0x1p-12f;
  float m = -(1.0f + 0x1p-11f);
  EXPECT(same32(muladd32(e, e, m), 0.0f), "muladd32 was fused: %a",
         muladd32(e, e, m));
  EXPECT(same32(fmaf(e, e, m), 0x1p-24f), "fmaf(%a, %a, %a)", e, e, m);
  double d = 1.0 + 0x1p-27;
  double dm = -(1.0 + 0x1p-26);
  EXPECT(same64(muladd64(d, d, dm), 0.0), "muladd64 was fused: %a",
         muladd64(d, d, dm));
  for (int i = -50; i <= 50; ++i) {
    float a = (float)i * 0.37f, b = 1.0f / ((float)i + 0.5f), c = (float)i;
    EXPECT(same32(muladd32(a, b, c), a * b + c), "muladd32(%a, %a, %a)", a, b,
           c);
    double x = (double)i * 0.37;
    EXPECT(same64(poly(x), ((2.5 * x - 1.0) * x + 0.125) * x - 3.0e2),
           "poly(%a)", x);
  }

  EXPECT(bits32(tenth32(0.0f)) == bits32(0.1f), "tenth32 = %a", tenth32(0.0f));
  EXPECT(bits64(tenth64(0.0)) == bits64(0.1), "tenth64 = %a", tenth64(0.0));
  EXPECT(bits32(zero(true)) == 0x80000000u, "zero(true) = %a", zero(true));
  EXPECT(bits32(zero(false)) == 0u, "zero(false) = %a", zero(false));
  // Subnormals are kept, not flushed to zero.
  EXPECT(halve(FLT_MIN) == FLT_MIN / 2.0f && halve(FLT_MIN) != 0.0f,
         "halve(FLT_MIN) = %a", halve(FLT_MIN));

  float xs[64], ys[64], out[64];
  float s = 0.0f;
  for (int i = 0; i < 64; ++i) {
    xs[i] = 1.0f / (float)(i + 1);
    ys[i] = (float)(i % 7) - 3.25f;
    s = s + xs[i] * ys[i];
  }
  EXPECT(same32(dot(xs, 64, ys, 64), s), "dot = %a, expected %a",
         dot(xs, 64, ys, 64), s);
  EXPECT(same32(dot(xs, 0, ys, 0), 0.0f), "empty dot");
  scale(xs, 64, 3.0f, out, 64);
  for (int i = 0; i < 64; ++i)
    EXPECT(same32(out[i], xs[i] * 3.0f), "scale[%d]", i);

  EXPECT(same32(sum3(1.0f, 0x1p-24f, 0x1p-24f), (1.0f + 0x1p-24f) + 0x1p-24f),
         "sum3 = %a", sum3(1.0f, 0x1p-24f, 0x1p-24f));
  EXPECT(same32(norm2(3.0f, 4.0f), 25.0f), "norm2(3, 4) = %a",
         norm2(3.0f, 4.0f));
  struct point p;
  mid(1.0f, 2.0f, 4.0f, -2.0f, &p);
  EXPECT(same32(p.x, 2.5f) && same32(p.y, 0.0f), "mid = {%a, %a}", p.x, p.y);

  // Conversions, against C's casts.
  int32_t ints[] = {0, 1, -1, 16777217, -16777217, 2147483647, INT32_MIN,
                    123456789};
  for (size_t i = 0; i < sizeof ints / sizeof ints[0]; ++i)
    EXPECT(same32(of_i32(ints[i]), (float)ints[i]), "of_i32(%d)", ints[i]);
  uint64_t longs[] = {0, 1, 9007199254740993ull, UINT64_MAX,
                      0x8000000000000001ull};
  for (size_t i = 0; i < sizeof longs / sizeof longs[0]; ++i)
    EXPECT(same64(of_u64(longs[i]), (double)longs[i]), "of_u64(%llu)",
           (unsigned long long)longs[i]);
  for (size_t i = 0; i < n; ++i) {
    float a = special[i];
    EXPECT(same64(widen(a), (double)a), "widen(%a)", a);
    EXPECT(same32(narrow((double)a), a), "narrow(%a)", a);
    EXPECT(to_bits32(a) == bits32(a), "to_bits32(%a)", a);
    EXPECT(bits32(from_bits32(bits32(a))) == bits32(a), "from_bits32(%a)", a);
    EXPECT(to_bits64((double)a) == bits64((double)a), "to_bits64(%a)", a);
    EXPECT(bits64(from_bits64(bits64((double)a))) == bits64((double)a),
           "from_bits64(%a)", a);
    EXPECT(same32(fabs32(a), fabsf(a)), "fabs32(%a)", a);
    if (a >= -2147483648.0f && a < 2147483648.0f)
      EXPECT(trunc_i32(a) == (int32_t)a, "trunc_i32(%a)", a);
    if (a > -1.0f && a < 256.0f)
      EXPECT(trunc_u8((double)a) == (uint8_t)a, "trunc_u8(%a)", (double)a);
  }
  EXPECT(same32(narrow(0.1), 0.1f), "narrow(0.1) = %a", narrow(0.1));
  EXPECT(trunc_i32(-2147483648.0f) == INT32_MIN, "trunc_i32(-2^31)");
  EXPECT(trunc_i32(-2.75f) == -2, "trunc_i32(-2.75)");
  EXPECT(trunc_u8(255.9) == 255, "trunc_u8(255.9)");
  EXPECT(trunc_u8(-0.9) == 0, "trunc_u8(-0.9)");
  float total = 0.0f;
  for (int i = 0; i < 64; ++i) total = total + xs[i];
  EXPECT(same32(mean(xs, 64), total / 64.0f), "mean = %a", mean(xs, 64));

  if (failures) {
    fprintf(stderr, "%d failures\n", failures);
    return 1;
  }
  printf("floats: all results match C\n");
  return 0;
}
