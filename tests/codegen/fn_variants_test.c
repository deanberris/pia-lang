// Runs fn_variants.pia, compiled by piac --emit=obj: function references
// in variant payloads (ADR 0071), checked against the same steps in C.

#include <stdint.h>
#include <stdio.h>

uint8_t act(uint8_t op, uint8_t y);
uint8_t maybe(uint8_t op, uint8_t y);

static uint8_t ref_act(uint8_t op, uint8_t y) {
  if (y >= 100)
    return y;
  if (op == 1)
    return (uint8_t)(y + 1);
  if (op == 2) {
    uint8_t z = (uint8_t)(y + y);
    return z < 100 ? (uint8_t)(z + z) : z;
  }
  return y;
}

static uint8_t ref_maybe(uint8_t op, uint8_t y) {
  if (y >= 100)
    return y;
  return op % 2 == 1 ? (uint8_t)(y + 1) : y;
}

int main(void) {
  int failures = 0;
  for (int a = 0; a < 256; ++a)
    for (int y = 0; y < 256; ++y) {
      uint8_t ua = (uint8_t)a, uy = (uint8_t)y;
      if (act(ua, uy) != ref_act(ua, uy)) {
        fprintf(stderr, "act %d %d = %d, expected %d\n", a, y, act(ua, uy),
                ref_act(ua, uy));
        ++failures;
      }
      if (maybe(ua, uy) != ref_maybe(ua, uy)) {
        fprintf(stderr, "maybe %d %d = %d, expected %d\n", a, y, maybe(ua, uy),
                ref_maybe(ua, uy));
        ++failures;
      }
    }
  if (failures == 0)
    printf("fn_variants: all passed\n");
  return failures != 0;
}
