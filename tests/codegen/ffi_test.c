// Links with ffi_run.pia, compiled by piac --emit=obj: defines the C
// functions it declares with `extern`, and checks what its functions return.

#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>

uint32_t total(const uint8_t *xs, uint64_t n);
uint32_t tail_total(const uint8_t *xs, uint64_t n);
int32_t pct(int32_t x);
int32_t twice_raw(int32_t x);
int64_t va_two(int64_t a, int64_t b);
int64_t va_three(int64_t a, int64_t b, int64_t c);
uint64_t va_mix(uint32_t a, const uint8_t *xs, uint64_t n);
int32_t plus_answer(int32_t x);
int32_t counted(int32_t x);

uint32_t sum_bytes(const uint8_t *xs, uint64_t n) {
  uint32_t s = 0;
  for (uint64_t i = 0; i < n; ++i) s += xs[i];
  return s;
}
int32_t clamp_c(int32_t x) { return x < 0 ? 0 : x > 100 ? 100 : x; }
static int32_t count = 0;
int32_t raw_c(int32_t x) {
  ++count;
  return x * 2;
}
// Like __errno_location: a pointer to a value that calls change.
int32_t *counter_c(void) { return &count; }
int32_t answer(void) { return 42; }

// Variadic: n int64_t arguments follow.
int64_t sum_va(int32_t n, ...) {
  va_list ap;
  va_start(ap, n);
  int64_t s = 0;
  for (int32_t i = 0; i < n; ++i) s += va_arg(ap, int64_t);
  va_end(ap);
  return s;
}

// Variadic: a uint32_t, then a buffer and its length.
uint64_t mix_va(int32_t n, ...) {
  va_list ap;
  va_start(ap, n);
  uint64_t s = va_arg(ap, uint32_t);
  const uint8_t *xs = va_arg(ap, const uint8_t *);
  uint64_t len = va_arg(ap, uint64_t);
  for (uint64_t i = 0; i < len; ++i) s += xs[i];
  va_end(ap);
  return n == 3 ? s : 0;
}

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
  EXPECT(counted(5), 2);
  EXPECT(va_two(40, 2), 42);
  EXPECT(va_three(1LL << 40, 2, -3), (1LL << 40) - 1);
  EXPECT(va_mix(1000, bytes, 4), 1256);
  EXPECT(plus_answer(-2), 40);
  if (failures == 0) printf("ffi: all passed\n");
  return failures != 0;
}
