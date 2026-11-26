// Runs rec_run.pia: a tree built in cells this test lends. A cell's size
// is Pia's layout, not C's, so the buffer is generous and the count of
// cells small.
#include <stdint.h>
#include <stdio.h>

uint64_t build(void *cells, size_t n);

int main(void) {
  static _Alignas(16) unsigned char cells[8 * 512];
  uint64_t got = build(cells, 6);
  if (got != 42) {
    printf("build with 6 cells: %llu, expected 42\n", (unsigned long long)got);
    return 1;
  }
  // Six allocations: with five cells the last fails, and build says 0.
  got = build(cells, 5);
  if (got != 0) {
    printf("build with 5 cells: %llu, expected 0\n", (unsigned long long)got);
    return 1;
  }
  return 0;
}
