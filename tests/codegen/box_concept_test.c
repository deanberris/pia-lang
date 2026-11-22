// Runs box_concept.pia, compiled by piac --emit=obj: a slice of
// `box Shape` holding a square of side 3 and a 2 by 5 rectangle, whose
// areas sum to 19 through the boxes. A buffer of records is one buffer per
// field, and `box Shape` here is a tagged union of square and rect: a tag,
// square's side, and rect's w and h, one byte each.

#include <stdint.h>
#include <stdio.h>

uint32_t run(uint8_t *sq_side, uint64_t sq_len, uint8_t *rc_w, uint64_t rc_len,
             uint8_t *rc_h, uint8_t *xs_tag, uint64_t xs_len, uint8_t *xs_side,
             uint8_t *xs_w, uint8_t *xs_h);

int main(void) {
  uint8_t sq_side[1] = {0};
  uint8_t rc_w[1] = {0}, rc_h[1] = {0};
  uint8_t tag[2] = {0}, side[2] = {0}, w[2] = {0}, h[2] = {0};
  uint32_t sum = run(sq_side, 1, rc_w, 1, rc_h, tag, 2, side, w, h);
  int failures = 0;
  if (sum != 19) {
    fprintf(stderr, "run: expected 19, got %u\n", sum);
    ++failures;
  }
  // The boxes hold a square, then a rect.
  if (tag[0] != 0 || side[0] != 3 || tag[1] != 1 || w[1] != 2 || h[1] != 5) {
    fprintf(stderr, "boxes: tags %u %u, side %u, w %u, h %u\n", tag[0],
            tag[1], side[0], w[1], h[1]);
    ++failures;
  }
  return failures ? 1 : 0;
}
