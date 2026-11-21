// Runs the functions in variants.pia, compiled by piac --emit=obj. A
// variant is its tag (the constructor's position) and then its payloads.

#include <stdint.h>
#include <stdio.h>

struct opt {
  uint8_t tag;
  uint32_t some;
};
struct shape {
  uint8_t tag;
  uint16_t circle, square;
};

uint64_t area(uint8_t tag, uint16_t circle, uint16_t square);
void first_some(uint8_t atag, uint32_t a, uint8_t btag, uint32_t b,
                struct opt *out);
void square_of(uint16_t n, struct shape *out);

static int failures = 0;

#define EXPECT(cond, ...)             \
  do {                                \
    if (!(cond) && failures++ < 10) { \
      fprintf(stderr, __VA_ARGS__);   \
      fputc('\n', stderr);            \
    }                                 \
  } while (0)

int main(void) {
  for (unsigned v = 0; v < 65536; v += 257) {
    EXPECT(area(0, v, 0) == 3ull * v * v, "area(Circle %u)", v);
    EXPECT(area(1, 0, v) == (uint64_t)v * v, "area(Square %u)", v);
  }
  EXPECT(area(2, 0, 0) == 0, "area(Empty)");

  struct opt o = {9, 9};
  first_some(1, 7, 1, 8, &o);
  EXPECT(o.tag == 1 && o.some == 7, "first_some(Some 7, Some 8)");
  first_some(0, 0, 1, 8, &o);
  EXPECT(o.tag == 1 && o.some == 8, "first_some(None, Some 8)");
  first_some(0, 0, 0, 0, &o);
  EXPECT(o.tag == 0, "first_some(None, None)");

  struct shape s = {9, 9, 9};
  square_of(0, &s);
  EXPECT(s.tag == 2, "square_of(0).tag = %d", s.tag);
  square_of(12, &s);
  EXPECT(s.tag == 1 && s.square == 12, "square_of(12) = {%d, %d}", s.tag,
         s.square);

  if (failures) {
    fprintf(stderr, "%d mismatches\n", failures);
    return 1;
  }
  printf("all variant checks passed\n");
  return 0;
}
