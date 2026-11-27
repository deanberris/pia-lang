// Runs box_error_payload.pia, compiled by piac --emit=obj: an error set
// whose Cxx case holds a box Exception, filled with a not_found (id 4,
// code 404) or an overflow (limit 77, code 77), and handled by calling
// code through the box. A buffer of records is one buffer per field, so
// each allocator's memory is one array per field and its length.

#include <stdint.h>
#include <stdio.h>

uint32_t run(uint16_t *nf_id, uint64_t nf_len, uint32_t *ov_limit,
             uint64_t ov_len, uint8_t x);

int main(void) {
  // x = 0: Closed; 1: a boxed not_found; 2: a boxed overflow; 3: Ok.
  const uint32_t want[4] = {2, 404, 77, 1};
  int failures = 0;
  for (uint8_t x = 0; x < 4; ++x) {
    uint16_t id[1] = {0};
    uint32_t limit[1] = {0};
    uint32_t got = run(id, 1, limit, 1, x);
    if (got != want[x]) {
      fprintf(stderr, "run %u: expected %u, got %u\n", x, want[x], got);
      ++failures;
    }
  }
  return failures ? 1 : 0;
}
