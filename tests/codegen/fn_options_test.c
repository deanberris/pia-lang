// Runs fn_options.pia, compiled by piac --emit=obj: an `option` of a bare
// arrow (ADR 0071), checked against the same steps in C.

#include <stdint.h>
#include <stdio.h>

uint8_t pick(uint8_t k, uint8_t y);

static uint8_t ref_pick(uint8_t k, uint8_t y) {
  if (k == 1)
    return (uint8_t)(y / 2);
  if (k == 2)
    return (uint8_t)(255 - y);
  return y;
}

int main(void) {
  int failures = 0;
  for (int k = 0; k < 256; ++k)
    for (int y = 0; y < 256; ++y)
      if (pick((uint8_t)k, (uint8_t)y) != ref_pick((uint8_t)k, (uint8_t)y)) {
        fprintf(stderr, "pick %d %d = %d, expected %d\n", k, y,
                pick((uint8_t)k, (uint8_t)y), ref_pick((uint8_t)k, (uint8_t)y));
        ++failures;
      }
  if (failures == 0)
    printf("fn_options: all passed\n");
  return failures != 0;
}
