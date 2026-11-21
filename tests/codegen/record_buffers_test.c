// Runs the functions in record_buffers.pia, compiled by piac --emit=obj.
// A buffer of records is one buffer per field (struct of arrays).

#include <stdint.h>
#include <stdio.h>

void opaque_all(uint8_t *r, uint64_t n, uint8_t *g, uint8_t *b, uint8_t *a,
                uint8_t v);
void set_alpha(uint8_t *r, uint8_t *g, uint8_t *b, uint8_t *a, uint64_t i,
               uint8_t v);
uint16_t luma(const uint8_t *r, uint64_t n, const uint8_t *g,
              const uint8_t *b, const uint8_t *a, uint64_t i);
void middle(uint8_t *r, uint8_t *g, uint8_t *b, uint8_t *a, uint8_t v);

static int failures = 0;

#define EXPECT(cond, ...)             \
  do {                                \
    if (!(cond) && failures++ < 10) { \
      fprintf(stderr, __VA_ARGS__);   \
      fputc('\n', stderr);            \
    }                                 \
  } while (0)

int main(void) {
  uint8_t r[8] = {0}, g[8] = {0}, b[8] = {0}, a[8] = {0};
  opaque_all(r, 5, g, b, a, 7);
  for (int i = 0; i < 8; ++i) {
    int in = i < 5;
    EXPECT(r[i] == (in ? 7 : 0) && g[i] == (in ? 7 : 0) &&
               b[i] == (in ? 7 : 0) && a[i] == (in ? 255 : 0),
           "opaque_all: pixel %d = %d %d %d %d", i, r[i], g[i], b[i], a[i]);
  }

  set_alpha(r, g, b, a, 2, 9);
  EXPECT(a[2] == 9 && r[2] == 7 && a[1] == 255, "set_alpha: %d %d %d", a[2],
         r[2], a[1]);

  r[3] = 200;
  g[3] = 100;
  b[3] = 50;
  EXPECT(luma(r, 8, g, b, a, 3) == 350, "luma = %d", luma(r, 8, g, b, a, 3));

  uint8_t mr[8] = {0}, mg[8] = {0}, mb[8] = {0}, ma[8] = {0};
  middle(mr, mg, mb, ma, 3);
  for (int i = 0; i < 8; ++i) {
    int in = i >= 2 && i < 6;
    EXPECT(mr[i] == (in ? 3 : 0) && ma[i] == (in ? 255 : 0),
           "middle: pixel %d = %d %d", i, mr[i], ma[i]);
  }

  if (failures) {
    fprintf(stderr, "%d mismatches\n", failures);
    return 1;
  }
  printf("all record buffer checks passed\n");
  return 0;
}
