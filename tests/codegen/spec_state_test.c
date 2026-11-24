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
// tagged's steps are spec-only: C passes the vs and their length.
void mark_all(uint8_t *v, int64_t n);
// Spec state is erased (ADR 0058): record's spec log is not passed.
void traced_copy(const uint8_t *src, int64_t ns, uint8_t *dst, int64_t nd);
void record(uint8_t i, uint16_t v);
uint16_t first_of_two(uint16_t a, uint16_t b);
// owned's owner and counted's seen are spec fields: C sees neither.
void mark_owned(uint8_t *v, int64_t n);
uint8_t count_from(uint8_t z);

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
  uint8_t vs[5] = {1, 2, 3, 4, 5};
  mark_all(vs, 5);
  for (int i = 0; i < 5; ++i) EXPECT(vs[i] == 7, "mark_all: vs[%d] = %u", i, vs[i]);
  uint8_t src[8] = {9, 8, 7, 6, 5, 4, 3, 2}, dst[8] = {0};
  traced_copy(src, 8, dst, 8);
  for (int i = 0; i < 8; ++i)
    EXPECT(dst[i] == src[i], "traced_copy: dst[%d] = %u", i, dst[i]);
  record(3, 42);
  EXPECT(first_of_two(5, 6) == 5, "first_of_two(5, 6) = %u", first_of_two(5, 6));
  uint8_t ws[4] = {0, 1, 2, 3};
  mark_owned(ws, 4);
  for (int i = 0; i < 4; ++i) EXPECT(ws[i] == 9, "mark_owned: ws[%d] = %u", i, ws[i]);
  for (unsigned z = 0; z < 16; ++z)
    EXPECT(count_from((uint8_t)z) == z + 1, "count_from(%u) = %u", z,
           count_from((uint8_t)z));
  if (failures) return 1;
  puts("spec_state: ok");
  return 0;
}
