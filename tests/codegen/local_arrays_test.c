// Runs the functions in local_arrays.pia, compiled by piac --emit=obj.
// Arrays returned by value go through buffers each caller makes.

#include <stdint.h>
#include <stdio.h>

uint16_t fill(uint8_t v);
uint16_t pair(uint8_t x, uint8_t y);
uint16_t copied(uint8_t x);
uint16_t grey(uint8_t v);
uint16_t returned(uint8_t v);
uint8_t kept(uint8_t v);
uint16_t deep(uint8_t n);

int main(void) {
  int failures = 0;
  for (int v = 0; v < 256; ++v) {
    if (fill(v) != 3 * v) { fprintf(stderr, "fill(%d) = %d\n", v, fill(v)); ++failures; }
    if (pair(v, 2) != v + 4) { fprintf(stderr, "pair(%d, 2) = %d\n", v, pair(v, 2)); ++failures; }
    if (copied(v) != v + 1) { fprintf(stderr, "copied(%d) = %d\n", v, copied(v)); ++failures; }
    if (grey(v) != 3 * v + 1) { fprintf(stderr, "grey(%d) = %d\n", v, grey(v)); ++failures; }
    if (returned(v) != 2 * v) { fprintf(stderr, "returned(%d) = %d\n", v, returned(v)); ++failures; }
    if (kept(v) != v) { fprintf(stderr, "kept(%d) = %d\n", v, kept(v)); ++failures; }
    if (deep(v) != 2 * v) { fprintf(stderr, "deep(%d) = %d\n", v, deep(v)); ++failures; }
    if (failures > 10) break;
  }
  return failures != 0;
}
