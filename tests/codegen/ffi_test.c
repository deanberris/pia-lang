// Links with ffi_run.pia, compiled by piac --emit=obj: defines the C
// functions it declares with `extern`, and checks what its functions return.

#include <stdint.h>
#include <stdio.h>

uint32_t total(const uint8_t *xs, uint64_t n);
uint32_t tail_total(const uint8_t *xs, uint64_t n);
int32_t pct(int32_t x);
int32_t twice_raw(int32_t x);

uint32_t sum_bytes(const uint8_t *xs, uint64_t n) {
  uint32_t s = 0;
  for (uint64_t i = 0; i < n; ++i) s += xs[i];
  return s;
}
int32_t clamp_c(int32_t x) { return x < 0 ? 0 : x > 100 ? 100 : x; }
int32_t raw_c(int32_t x) { return x * 2; }

static int failures = 0;
#define EXPECT(got, want)                                              \
  do {                                                                 \
    long long g = (long long)(got), w = (long long)(want);             \
    if (g != w) {                                                      \
      fprintf(stderr, "%s = %lld, want %lld\n", #got, g, w);           \
      ++failures;                                                      \
    }                                                                  \
  } while (0)

int main(void) {
  uint8_t bytes[] = {1, 2, 3, 250};
  EXPECT(total(bytes, 4), 256);
  EXPECT(tail_total(bytes, 4), 255);
  EXPECT(pct(-5), 0);
  EXPECT(pct(500), 100);
  EXPECT(pct(42), 42);
  EXPECT(twice_raw(21), 42);
  if (failures == 0) printf("ffi: all passed\n");
  return failures != 0;
}
