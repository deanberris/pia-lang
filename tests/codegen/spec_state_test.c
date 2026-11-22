// Runs the functions in spec_state.pia, compiled by piac --emit=obj.
// Spec-only parameters and fields are erased (ADR 0041), so C passes and
// receives only the code's own values.

#include <stdint.h>
#include <stdio.h>

struct tally {
  uint8_t v;  // steps is spec-only, so it is not here
};

uint64_t take_two(uint8_t a, uint8_t b);
uint8_t skip(uint8_t x);
uint8_t count_up(uint8_t x);

static int failures = 0;

#define EXPECT(cond, ...)             \
  do {                                \
    if (!(cond) && failures++ < 10) { \
      fprintf(stderr, __VA_ARGS__);   \
      fputc('\n', stderr);            \
    }                                 \
  } while (0)

int main(void) {
  for (unsigned a = 0; a < 64; a += 5)
    for (unsigned b = 0; b < 64; b += 3) {
      if (a == b) continue;
      uint64_t want = (UINT64_C(1) << a) | (UINT64_C(1) << b);
      EXPECT(take_two((uint8_t)a, (uint8_t)b) == want, "take_two(%u, %u)", a, b);
    }
  for (unsigned x = 0; x < 255; ++x)
    EXPECT(skip((uint8_t)x) == x + 1, "skip(%u) = %u", x, skip((uint8_t)x));
  for (unsigned x = 0; x < 200; ++x)
    EXPECT(count_up((uint8_t)x) == x + 10, "count_up(%u) = %u", x,
           count_up((uint8_t)x));
  if (failures) return 1;
  puts("spec_state: ok");
  return 0;
}
