// Runs the functions in consts.pia, compiled by piac --emit=obj.

#include <stdint.h>
#include <stdio.h>

uint8_t lookup(uint8_t i);
int8_t sign_at(uint8_t i);
uint16_t middle_sum(void);

static int failures = 0;

#define EXPECT(cond, ...)             \
  do {                                \
    if (!(cond) && failures++ < 10) { \
      fprintf(stderr, __VA_ARGS__);   \
      fputc('\n', stderr);            \
    }                                 \
  } while (0)

int main(void) {
  static const uint8_t crc4[16] = {0, 3, 6, 5, 12, 15, 10, 9,
                                   11, 8, 13, 14, 7, 4, 1, 2};
  for (int i = 0; i < 16; ++i)
    EXPECT(lookup(i) == crc4[i], "lookup(%d) = %d", i, lookup(i));
  static const int8_t signs[4] = {-128, -1, 0, 127};
  for (int i = 0; i < 4; ++i)
    EXPECT(sign_at(i) == signs[i], "sign_at(%d) = %d", i, sign_at(i));
  EXPECT(middle_sum() == 12 + 15 + 10 + 9, "middle_sum = %d", middle_sum());
  if (failures) {
    fprintf(stderr, "%d mismatches\n", failures);
    return 1;
  }
  printf("all constant checks passed\n");
  return 0;
}
