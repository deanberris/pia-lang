// Runs the functions in arena.pia, compiled by piac --emit=obj: a
// with_arena's memory is zeroed each time it is entered.

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

uint8_t fresh(uint8_t x);
uint8_t sum_two(uint8_t x, uint8_t y);
uint8_t fresh_each_time(size_t n, uint8_t x);

static int failures = 0;

#define EXPECT(cond, ...)             \
  do {                                \
    if (!(cond) && failures++ < 10) { \
      fprintf(stderr, __VA_ARGS__);   \
      fputc('\n', stderr);            \
    }                                 \
  } while (0)

int main(void) {
  for (unsigned x = 0; x < 256; ++x) {
    EXPECT(fresh((uint8_t)x) == 0, "fresh(%u) != 0", x);
    EXPECT(fresh_each_time(5, (uint8_t)x) == 0, "fresh_each_time(5, %u) != 0", x);
  }
  for (unsigned x = 0; x <= 100; x += 7)
    for (unsigned y = 0; y <= 100; y += 9)
      EXPECT(sum_two((uint8_t)x, (uint8_t)y) == x + y, "sum_two(%u, %u) = %u",
             x, y, sum_two((uint8_t)x, (uint8_t)y));
  if (failures) fprintf(stderr, "%d failures\n", failures);
  return failures != 0;
}
