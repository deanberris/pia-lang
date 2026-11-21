// Runs the functions in slices.pia, compiled by piac --emit=obj.

#include <stdint.h>
#include <stdio.h>

void fill(uint8_t *dst, uint64_t n, uint8_t v);
void fill_middle(uint8_t *xs, uint8_t v);
void fill_inner(uint8_t *xs, uint64_t n, uint64_t a, uint64_t b, uint8_t v);
uint16_t first_of(const uint16_t *xs, uint64_t n, uint64_t a, uint64_t b);
uint64_t count(const uint16_t *xs, uint64_t n, uint64_t a, uint64_t b);
uint32_t safe_div(uint32_t a, uint32_t b);

static int failures = 0;

#define EXPECT(cond, ...)             \
  do {                                \
    if (!(cond) && failures++ < 10) { \
      fprintf(stderr, __VA_ARGS__);   \
      fputc('\n', stderr);            \
    }                                 \
  } while (0)

int main(void) {
  uint8_t xs[8] = {0, 0, 0, 0, 0, 0, 0, 0};
  fill_middle(xs, 9);
  for (int i = 0; i < 8; ++i)
    EXPECT(xs[i] == (i >= 2 && i < 6 ? 9 : 0), "fill_middle: xs[%d] = %d", i,
           xs[i]);

  uint8_t ys[20] = {0};
  fill_inner(ys, 20, 5, 12, 4);
  for (int i = 0; i < 20; ++i)
    EXPECT(ys[i] == (i >= 6 && i < 11 ? 4 : 0), "fill_inner: ys[%d] = %d", i,
           ys[i]);

  uint16_t zs[10];
  for (int i = 0; i < 10; ++i) zs[i] = (uint16_t)(1000 + i);
  for (int a = 0; a < 10; ++a)
    for (int b = a; b <= 10; ++b) {
      EXPECT(count(zs, 10, a, b) == (uint64_t)(b - a), "count(%d, %d)", a, b);
      if (a < b)
        EXPECT(first_of(zs, 10, a, b) == 1000 + a, "first_of(%d, %d) = %d", a,
               b, first_of(zs, 10, a, b));
    }

  EXPECT(safe_div(17, 5) == 3, "safe_div(17, 5) = %u", safe_div(17, 5));

  if (failures) {
    fprintf(stderr, "%d mismatches\n", failures);
    return 1;
  }
  printf("all slice checks passed\n");
  return 0;
}
