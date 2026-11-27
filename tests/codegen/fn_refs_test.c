// Runs fn_refs.pia, compiled by piac --emit=obj: calls through mutable
// function references (ADR 0071), checked against the same steps in C.

#include <stdint.h>
#include <stdio.h>

uint8_t pick(uint8_t op, uint8_t y);
uint8_t apply_ops(uint8_t n, uint8_t y);

static uint8_t ref_pick(uint8_t op, uint8_t y) {
  if (y >= 100)
    return y;
  if (op == 1)
    return (uint8_t)(y + 1);
  if (op == 2)
    return (uint8_t)(y + y);
  return y;
}

static uint8_t ref_apply(uint8_t n, uint8_t y) {
  int twice = 0;
  for (int i = 0; i < n; ++i) {
    if (y < 100)
      y = twice ? (uint8_t)(y + y) : (uint8_t)(y + 1);
    twice = i % 2 == 0;
  }
  return y;
}

int main(void) {
  int failures = 0;
  for (int op = 0; op < 4; ++op)
    for (int y = 0; y < 256; ++y)
      if (pick((uint8_t)op, (uint8_t)y) != ref_pick((uint8_t)op, (uint8_t)y)) {
        fprintf(stderr, "pick %d %d = %d, expected %d\n", op, y,
                pick((uint8_t)op, (uint8_t)y),
                ref_pick((uint8_t)op, (uint8_t)y));
        ++failures;
      }
  for (int n = 0; n < 20; ++n)
    for (int y = 0; y < 256; ++y)
      if (apply_ops((uint8_t)n, (uint8_t)y) !=
          ref_apply((uint8_t)n, (uint8_t)y)) {
        fprintf(stderr, "apply_ops %d %d = %d, expected %d\n", n, y,
                apply_ops((uint8_t)n, (uint8_t)y),
                ref_apply((uint8_t)n, (uint8_t)y));
        ++failures;
      }
  if (failures == 0)
    printf("fn_refs: all passed\n");
  return failures != 0;
}
