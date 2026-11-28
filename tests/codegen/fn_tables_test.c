// Runs fn_tables.pia, compiled by piac --emit=obj: calls through function
// references stored in records and a handler table (ADR 0071), checked
// against the same steps in C.

#include <stdint.h>
#include <stdio.h>

uint8_t dispatch(uint8_t op, uint8_t y);
uint8_t rewrite(uint8_t n, uint8_t y);
uint8_t one(uint8_t op, uint8_t y);

static uint8_t keep(uint8_t x) { return x; }
static uint8_t succ(uint8_t x) { return (uint8_t)(x + 1); }
static uint8_t twice(uint8_t x) { return (uint8_t)(x + x); }
static uint8_t add3(uint8_t x) { return (uint8_t)(x + 3); }

static uint8_t ref_dispatch(uint8_t op, uint8_t y) {
  uint8_t (*t[4])(uint8_t) = {keep, succ, twice, add3};
  return y < 100 ? t[op % 4](y) : y;
}

static uint8_t ref_rewrite(uint8_t n, uint8_t y) {
  uint8_t (*t[4])(uint8_t) = {keep, succ, twice, add3};
  for (int i = 0; i < n; ++i) {
    if (y < 100)
      y = t[i % 4](y);
    t[i % 4] = t[(i + 1) % 4];
  }
  return y;
}

static uint8_t ref_one(uint8_t op, uint8_t y) {
  uint8_t (*h)(uint8_t) = op == 1 ? succ : op == 2 ? twice : keep;
  return y < 100 ? h(y) : y;
}

int main(void) {
  int failures = 0;
  for (int a = 0; a < 256; ++a)
    for (int y = 0; y < 256; ++y) {
      uint8_t ua = (uint8_t)a, uy = (uint8_t)y;
      if (dispatch(ua, uy) != ref_dispatch(ua, uy)) {
        fprintf(stderr, "dispatch %d %d = %d, expected %d\n", a, y,
                dispatch(ua, uy), ref_dispatch(ua, uy));
        ++failures;
      }
      if (rewrite(ua, uy) != ref_rewrite(ua, uy)) {
        fprintf(stderr, "rewrite %d %d = %d, expected %d\n", a, y,
                rewrite(ua, uy), ref_rewrite(ua, uy));
        ++failures;
      }
      if (one(ua, uy) != ref_one(ua, uy)) {
        fprintf(stderr, "one %d %d = %d, expected %d\n", a, y, one(ua, uy),
                ref_one(ua, uy));
        ++failures;
      }
    }
  if (failures == 0)
    printf("fn_tables: all passed\n");
  return failures != 0;
}
