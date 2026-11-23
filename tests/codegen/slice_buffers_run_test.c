// Runs the functions in slice_buffers_run.pia, compiled by piac
// --emit=obj. A buffer of slices is two buffers, the elements' addresses
// and their lengths, which share one count (ADR 0048, step 3).

#include <stdint.h>
#include <stdio.h>

// The count follows the first buffer, as for a slice of records' fields.
uint16_t first(uint64_t *addr, int64_t n, uint64_t *len);
uint64_t width(uint64_t *addr, int64_t n, uint64_t *len, uint64_t i);
void copy_row(uint64_t *addr, int64_t n, uint64_t *len);

static int failures = 0;

#define EXPECT(cond, ...)             \
  do {                                \
    if (!(cond) && failures++ < 10) { \
      fprintf(stderr, __VA_ARGS__);   \
      fputc('\n', stderr);            \
    }                                 \
  } while (0)

int main(void) {
  uint16_t a[3] = {7, 8, 9}, b[2] = {40, 41}, c[1] = {500};
  uint64_t addr[3] = {(uint64_t)(uintptr_t)a, (uint64_t)(uintptr_t)b,
                      (uint64_t)(uintptr_t)c};
  uint64_t len[3] = {3, 2, 1};
  EXPECT(first(addr, 3, len) == 7, "first = %u", first(addr, 3, len));
  for (uint64_t i = 0; i < 3; ++i)
    EXPECT(width(addr, 3, len, i) == len[i], "width(%llu) = %llu",
           (unsigned long long)i, (unsigned long long)width(addr, 3, len, i));
  copy_row(addr, 3, len);
  EXPECT(addr[0] == (uint64_t)(uintptr_t)b && len[0] == 2,
         "copy_row: element 0 is not element 1");
  EXPECT(first(addr, 3, len) == 40, "first after copy_row = %u",
         first(addr, 3, len));
  if (failures) return 1;
  puts("slice_buffers_run: ok");
  return 0;
}
