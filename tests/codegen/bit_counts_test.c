// Runs the functions in bit_counts.pia, compiled by piac --emit=obj, and
// compares them with the C compiler's builtins over every u8 and u16 input
// and a sweep of the wider types.

#include <stdint.h>
#include <stdio.h>

uint8_t clz8(uint8_t x);
uint8_t ctz8(uint8_t x);
uint8_t pop8(uint8_t x);
uint8_t clz16(uint16_t x);
uint8_t ctz16(uint16_t x);
uint8_t pop16(uint16_t x);
uint16_t swap16(uint16_t x);
uint8_t clz32(uint32_t x);
uint8_t ctz32(uint32_t x);
uint8_t pop32(uint32_t x);
uint32_t swap32(uint32_t x);
uint32_t rotl32(uint32_t x, uint8_t n);
uint32_t rotr32(uint32_t x, uint8_t n);
uint8_t clz64(uint64_t x);
uint8_t ctz64(uint64_t x);
uint8_t pop64(uint64_t x);
uint64_t swap64(uint64_t x);
uint64_t rotl64(uint64_t x, uint8_t n);
uint8_t rotr8(uint8_t x, uint8_t n);

static int failures = 0;

#define EXPECT(cond, ...)             \
  do {                                \
    if (!(cond) && failures++ < 10) { \
      fprintf(stderr, __VA_ARGS__);   \
      fputc('\n', stderr);            \
    }                                 \
  } while (0)

// Zero counts the whole width, unlike __builtin_clz.
static int ref_clz(uint64_t x, int w) { return x ? __builtin_clzll(x) - (64 - w) : w; }
static int ref_ctz(uint64_t x, int w) { return x ? __builtin_ctzll(x) : w; }

static void check32(uint32_t x) {
  EXPECT(clz32(x) == ref_clz(x, 32), "clz32(%u) = %d", x, clz32(x));
  EXPECT(ctz32(x) == ref_ctz(x, 32), "ctz32(%u) = %d", x, ctz32(x));
  EXPECT(pop32(x) == __builtin_popcount(x), "pop32(%u) = %d", x, pop32(x));
  EXPECT(swap32(x) == __builtin_bswap32(x), "swap32(%u) = %u", x, swap32(x));
  for (int n = 0; n < 32; ++n) {
    uint32_t l = n ? (x << n) | (x >> (32 - n)) : x;
    uint32_t r = n ? (x >> n) | (x << (32 - n)) : x;
    EXPECT(rotl32(x, n) == l, "rotl32(%u, %d) = %u", x, n, rotl32(x, n));
    EXPECT(rotr32(x, n) == r, "rotr32(%u, %d) = %u", x, n, rotr32(x, n));
  }
}

static void check64(uint64_t x) {
  EXPECT(clz64(x) == ref_clz(x, 64), "clz64(%llu) = %d",
         (unsigned long long)x, clz64(x));
  EXPECT(ctz64(x) == ref_ctz(x, 64), "ctz64(%llu) = %d",
         (unsigned long long)x, ctz64(x));
  EXPECT(pop64(x) == __builtin_popcountll(x), "pop64(%llu) = %d",
         (unsigned long long)x, pop64(x));
  EXPECT(swap64(x) == __builtin_bswap64(x), "swap64(%llu)",
         (unsigned long long)x);
  for (int n = 0; n < 64; ++n) {
    uint64_t l = n ? (x << n) | (x >> (64 - n)) : x;
    EXPECT(rotl64(x, n) == l, "rotl64(%llu, %d)", (unsigned long long)x, n);
  }
}

int main(void) {
  for (int x = 0; x < 256; ++x) {
    EXPECT(clz8(x) == ref_clz(x, 8), "clz8(%d) = %d", x, clz8(x));
    EXPECT(ctz8(x) == ref_ctz(x, 8), "ctz8(%d) = %d", x, ctz8(x));
    EXPECT(pop8(x) == __builtin_popcount(x), "pop8(%d) = %d", x, pop8(x));
    for (int n = 0; n < 8; ++n) {
      uint8_t r = n ? (uint8_t)((x >> n) | (x << (8 - n))) : (uint8_t)x;
      EXPECT(rotr8(x, n) == r, "rotr8(%d, %d) = %d", x, n, rotr8(x, n));
    }
  }
  for (int x = 0; x < 65536; ++x) {
    EXPECT(clz16(x) == ref_clz(x, 16), "clz16(%d) = %d", x, clz16(x));
    EXPECT(ctz16(x) == ref_ctz(x, 16), "ctz16(%d) = %d", x, ctz16(x));
    EXPECT(pop16(x) == __builtin_popcount(x), "pop16(%d) = %d", x, pop16(x));
    EXPECT(swap16(x) == __builtin_bswap16(x), "swap16(%d) = %d", x, swap16(x));
  }
  uint64_t s = 0x9e3779b97f4a7c15ull;
  check32(0);
  check32(UINT32_MAX);
  check64(0);
  check64(UINT64_MAX);
  for (int i = 0; i < 4096; ++i) {
    s ^= s << 13;
    s ^= s >> 7;
    s ^= s << 17;
    check32((uint32_t)s);
    check64(s);
    check64(1ull << (i % 64));
  }
  if (failures) {
    fprintf(stderr, "%d failures\n", failures);
    return 1;
  }
  return 0;
}
