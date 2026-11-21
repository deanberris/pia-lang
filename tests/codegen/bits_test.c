// Runs the functions in bits.pia, compiled by piac --emit=obj, and compares
// them with C over every input (or a sweep, for the wider types).

#include <stdint.h>
#include <stdio.h>

uint8_t band8(uint8_t a, uint8_t b);
uint8_t bor8(uint8_t a, uint8_t b);
uint8_t bxor8(uint8_t a, uint8_t b);
uint8_t bnot8(uint8_t x);
int32_t bnot32(int32_t x);
int16_t band_i16(int16_t a, int16_t b);
uint16_t shl16(uint8_t x, uint8_t n);
int32_t shr_i32(int32_t x, uint8_t n);
uint32_t shr_u32(uint32_t x, uint8_t n);
uint8_t rotl8(uint8_t x, uint8_t n);

static int failures = 0;

#define EXPECT(cond, ...)             \
  do {                                \
    if (!(cond) && failures++ < 10) { \
      fprintf(stderr, __VA_ARGS__);   \
      fputc('\n', stderr);            \
    }                                 \
  } while (0)

int main(void) {
  for (int a = 0; a < 256; ++a) {
    EXPECT(bnot8(a) == (uint8_t)~a, "bnot8(%d) = %d", a, bnot8(a));
    for (int b = 0; b < 256; ++b) {
      EXPECT(band8(a, b) == (a & b), "band8(%d, %d) = %d", a, b, band8(a, b));
      EXPECT(bor8(a, b) == (a | b), "bor8(%d, %d) = %d", a, b, bor8(a, b));
      EXPECT(bxor8(a, b) == (a ^ b), "bxor8(%d, %d) = %d", a, b, bxor8(a, b));
    }
    for (int n = 0; n < 8; ++n) {
      EXPECT(shl16(a, n) == (uint16_t)(a << n), "shl16(%d, %d) = %d", a, n,
             shl16(a, n));
      uint8_t rot = (uint8_t)((a << n) | (a >> ((8 - n) % 8)));
      EXPECT(rotl8(a, n) == rot, "rotl8(%d, %d) = %d", a, n, rotl8(a, n));
    }
  }
  for (int a = -32768; a < 32768; a += 97)
    for (int b = -32768; b < 32768; b += 89)
      EXPECT(band_i16(a, b) == (int16_t)(a & b), "band_i16(%d, %d) = %d", a, b,
             band_i16(a, b));
  const int32_t xs[] = {0, 1, -1, 2, -2, 7, -7, 12345, -12345, INT32_MAX,
                        INT32_MIN};
  for (unsigned i = 0; i < sizeof xs / sizeof xs[0]; ++i) {
    int32_t x = xs[i];
    EXPECT(bnot32(x) == ~x, "bnot32(%d) = %d", x, bnot32(x));
    for (int n = 0; n < 32; ++n) {
      EXPECT(shr_i32(x, n) == (x >> n), "shr_i32(%d, %d) = %d", x, n,
             shr_i32(x, n));
      uint32_t u = (uint32_t)x;
      EXPECT(shr_u32(u, n) == (u >> n), "shr_u32(%u, %d) = %u", u, n,
             shr_u32(u, n));
    }
  }
  if (failures) {
    fprintf(stderr, "%d mismatches\n", failures);
    return 1;
  }
  printf("all bit checks passed\n");
  return 0;
}
