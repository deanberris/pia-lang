// Runs fn_null.pia, compiled by piac --emit=obj: an `option` of a function
// reference is one address, NULL for the constructor without a payload
// (ADR 0071). C passes NULL, and the addresses Pia returns, back to Pia.

#include <stdint.h>
#include <stdio.h>

typedef uint8_t (*step)(uint8_t);
struct slot {
  step h;
  uint8_t n;
};

step get(uint8_t k);
uint8_t apply(step h, uint8_t y);
_Bool present(step h);
step get_has(uint8_t k);
uint8_t apply_has(step h, uint8_t y);
void make(uint8_t k, struct slot *out);
uint8_t use(step h, uint8_t n);

static int failures = 0;

#define EXPECT(cond, ...)             \
  do {                                \
    if (!(cond) && failures++ < 10) { \
      fprintf(stderr, __VA_ARGS__);   \
      fputc('\n', stderr);            \
    }                                 \
  } while (0)

int main(void) {
  EXPECT(get(0) == NULL && get(3) == NULL, "get(0), get(3) are None");
  EXPECT(get(1) != NULL && get(2) != NULL, "get(1), get(2) are Some");
  EXPECT(!present(NULL) && present(get(1)), "present");
  EXPECT(get_has(0) == NULL && get_has(1) != NULL, "get_has");
  for (int y = 0; y < 256; ++y) {
    EXPECT(apply(NULL, y) == y, "apply(NULL, %d)", y);
    EXPECT(apply(get(1), y) == y / 2, "apply(half, %d)", y);
    EXPECT(apply(get(2), y) == 255 - y, "apply(flip, %d)", y);
    EXPECT(apply_has(NULL, y) == y, "apply_has(NULL, %d)", y);
    EXPECT(apply_has(get_has(1), y) == y / 2, "apply_has(half, %d)", y);
    EXPECT(use(NULL, y) == y, "use(NULL, %d)", y);
    EXPECT(use(get_has(1), y) == y / 2, "use(half, %d)", y);
  }
  struct slot s = {NULL, 9};
  make(1, &s);
  EXPECT(s.h != NULL && s.n == 1 && use(s.h, 40) == 20, "make(1)");
  make(0, &s);
  EXPECT(s.h == NULL && s.n == 0, "make(0)");

  if (failures) {
    fprintf(stderr, "%d mismatches\n", failures);
    return 1;
  }
  printf("fn_null: all passed\n");
  return 0;
}
