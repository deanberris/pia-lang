// Runs box_concept.pia, compiled by piac --emit=obj: a slice of
// `box Shape` holding a square of side 3 and a 2 by 5 rectangle, whose
// areas sum to 19 through the boxes. A buffer of records is one buffer per
// field, and `box Shape` is one cache line of 64-bit words (ADR 0046, the
// cache-line amendment): 8 words on x86_64, 16 on Apple silicon. Word 0 is
// the boxed type's descriptor, and the object starts at word 1 in its C
// layout: square's side is its low byte, and rect's w and h its two low
// bytes.

#include <stdint.h>
#include <stdio.h>

#if defined(__APPLE__) && defined(__aarch64__)
#define WORDS 16
#define REST uint64_t *, uint64_t *, uint64_t *, uint64_t *, uint64_t *, \
             uint64_t *, uint64_t *, uint64_t *, uint64_t *, uint64_t *, \
             uint64_t *, uint64_t *, uint64_t *, uint64_t *, uint64_t *
#define REST_ARGS(w) w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8], w[9], \
                     w[10], w[11], w[12], w[13], w[14], w[15]
#else
#define WORDS 8
#define REST uint64_t *, uint64_t *, uint64_t *, uint64_t *, uint64_t *, \
             uint64_t *, uint64_t *
#define REST_ARGS(w) w[1], w[2], w[3], w[4], w[5], w[6], w[7]
#endif

// The slice of boxes: word 0's buffer and the slice's length, then the
// other words' buffers.
uint32_t run(uint8_t *sq_side, uint64_t sq_len, uint8_t *rc_w, uint64_t rc_len,
             uint8_t *rc_h, uint64_t *xs_w0, uint64_t xs_len, REST);

int main(void) {
  uint8_t sq_side[1] = {0};
  uint8_t rc_w[1] = {0}, rc_h[1] = {0};
  uint64_t w[WORDS][2] = {{0}};
  uint32_t sum = run(sq_side, 1, rc_w, 1, rc_h, w[0], 2, REST_ARGS(w));
  int failures = 0;
  if (sum != 19) {
    fprintf(stderr, "run: expected 19, got %u\n", sum);
    ++failures;
  }
  // Each box names its own type's descriptor, and holds its object.
  if (w[0][0] == 0 || w[0][1] == 0 || w[0][0] == w[0][1]) {
    fprintf(stderr, "descriptors: %llx %llx\n", (unsigned long long)w[0][0],
            (unsigned long long)w[0][1]);
    ++failures;
  }
  if ((w[1][0] & 0xff) != 3 || (w[1][1] & 0xffff) != (2 | 5 << 8)) {
    fprintf(stderr, "objects: %llx %llx\n", (unsigned long long)w[1][0],
            (unsigned long long)w[1][1]);
    ++failures;
  }
  return failures ? 1 : 0;
}
