// Calls Blend, which calls Image.Pixels, each compiled on its own by
// pia_library (ADR 0039), against C reference implementations.
#include <stdint.h>
#include <stdio.h>

uint8_t blend(uint8_t x, uint8_t y);
uint8_t grey(uint8_t v);

static uint8_t mix(uint8_t a, uint8_t b) { return a / 2 + b / 2; }

int main(void) {
  int failures = 0;
  for (int x = 0; x < 256; ++x)
    for (int y = 0; y < 256; ++y)
      if (blend(x, y) != mix(x, y)) {
        if (failures++ < 5) printf("blend(%d, %d) = %d\n", x, y, blend(x, y));
      }
  for (int v = 0; v <= 200; ++v)
    if (grey(v) != mix(v, mix(v, v))) {
      if (failures++ < 10) printf("grey(%d) = %d\n", v, grey(v));
    }
  printf("%d failures\n", failures);
  return failures != 0;
}
