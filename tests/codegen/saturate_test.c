// Runs the functions in saturate.pia, compiled by piac --emit=obj, and
// compares them with C reference implementations over every input (or a
// sweep, for the wider types).

#include <stdint.h>
#include <stdio.h>

uint8_t add_px(uint8_t a, uint8_t b);
uint8_t sub_px(uint8_t a, uint8_t b);
int8_t add_i8(int8_t a, int8_t b);
int16_t mul_i16(int16_t a, int16_t b);
uint8_t add_wrap(uint8_t a, uint8_t b);
uint16_t add_wide(uint8_t a, uint8_t b);
int32_t half(int32_t x);
void add_rows(const uint8_t *a, uint64_t na, const uint8_t *b, uint64_t nb,
              uint8_t *dst, uint64_t ndst);
uint32_t sum4(const uint16_t *xs);

struct pixel {
  uint8_t r, g, b, a;
};
void blend(uint8_t pr, uint8_t pg, uint8_t pb, uint8_t pa, uint8_t qr,
           uint8_t qg, uint8_t qb, uint8_t qa, struct pixel *out);
uint16_t luma(uint8_t r, uint8_t g, uint8_t b, uint8_t a);

static int failures = 0;

#define EXPECT(cond, ...)          \
  do {                             \
    if (!(cond) && failures++ < 10) { \
      fprintf(stderr, __VA_ARGS__);  \
      fputc('\n', stderr);           \
    }                                \
  } while (0)

static long clamp(long x, long lo, long hi) {
  return x < lo ? lo : x > hi ? hi : x;
}

int main(void) {
  for (int a = 0; a < 256; ++a) {
    for (int b = 0; b < 256; ++b) {
      EXPECT(add_px(a, b) == clamp(a + b, 0, 255), "add_px(%d, %d) = %d", a, b,
             add_px(a, b));
      EXPECT(sub_px(a, b) == clamp(a - b, 0, 255), "sub_px(%d, %d) = %d", a, b,
             sub_px(a, b));
      EXPECT(add_wrap(a, b) == (uint8_t)(a + b), "add_wrap(%d, %d) = %d", a, b,
             add_wrap(a, b));
      EXPECT(add_wide(a, b) == a + b, "add_wide(%d, %d) = %d", a, b,
             add_wide(a, b));
      int sa = a - 128, sb = b - 128;
      EXPECT(add_i8(sa, sb) == clamp(sa + sb, -128, 127),
             "add_i8(%d, %d) = %d", sa, sb, add_i8(sa, sb));
    }
  }
  for (long a = -32768; a < 32768; a += 97) {
    for (long b = -32768; b < 32768; b += 89) {
      EXPECT(mul_i16(a, b) == clamp(a * b, -32768, 32767),
             "mul_i16(%ld, %ld) = %d", a, b, mul_i16(a, b));
    }
  }
  const int32_t xs[] = {0, 1, -1, 2, -3, 7, -7, INT32_MAX, INT32_MIN};
  for (unsigned i = 0; i < sizeof xs / sizeof xs[0]; ++i)
    EXPECT(half(xs[i]) == xs[i] / 2, "half(%d) = %d", xs[i], half(xs[i]));

  uint8_t ra[300], rb[300], dst[300];
  for (int i = 0; i < 300; ++i) {
    ra[i] = (uint8_t)(i * 7);
    rb[i] = (uint8_t)(i * 13 + 5);
  }
  add_rows(ra, 300, rb, 300, dst, 300);
  for (int i = 0; i < 300; ++i)
    EXPECT(dst[i] == clamp(ra[i] + rb[i], 0, 255), "add_rows: dst[%d] = %d", i,
           dst[i]);

  const uint16_t four[4] = {65535, 65535, 65535, 3};
  EXPECT(sum4(four) == 3u * 65535u + 3u, "sum4 = %u", sum4(four));

  for (int v = 0; v < 256; v += 5) {
    struct pixel out = {0, 0, 0, 0};
    blend(v, 255 - v, v / 2, 7, 100, 100, v, 9, &out);
    EXPECT(out.r == clamp(v + 100, 0, 255) && out.g == clamp(355 - v, 0, 255) &&
               out.b == clamp(v / 2 + v, 0, 255) && out.a == 255,
           "blend(%d) = {%d, %d, %d, %d}", v, out.r, out.g, out.b, out.a);
    EXPECT(luma(v, 255, 255 - v, 1) == v + 255 + (255 - v), "luma(%d) = %d", v,
           luma(v, 255, 255 - v, 1));
  }

  if (failures) {
    fprintf(stderr, "%d mismatches\n", failures);
    return 1;
  }
  printf("all codegen checks passed\n");
  return 0;
}
