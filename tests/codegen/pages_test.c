// Runs pages.pia, compiled by piac --emit=obj, over pages from mmap.

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/mman.h>

uint64_t fill_sum(size_t n, uint8_t v);

static int maps = 0, unmaps = 0;

uintptr_t pages_map(size_t n) {
  void *p = mmap(NULL, n ? n : 1, PROT_READ | PROT_WRITE,
                 MAP_PRIVATE | MAP_ANON, -1, 0);
  if (p == MAP_FAILED) return 0;
  ++maps;
  return (uintptr_t)p;
}

void pages_unmap(uintptr_t p, size_t n) {
  munmap((void *)p, n ? n : 1);
  ++unmaps;
}

int main(void) {
  int failures = 0;
  size_t sizes[] = {1, 7, 4096, 4097, 65536};
  for (size_t i = 0; i < sizeof sizes / sizeof *sizes; ++i)
    for (unsigned v = 0; v < 256; v += 51) {
      uint64_t got = fill_sum(sizes[i], (uint8_t)v);
      if (got != (uint64_t)sizes[i] * v && failures++ < 10)
        fprintf(stderr, "fill_sum(%zu, %u) = %llu\n", sizes[i], v,
                (unsigned long long)got);
    }
  if (maps != unmaps) {
    fprintf(stderr, "%d maps but %d unmaps\n", maps, unmaps);
    ++failures;
  }
  return failures != 0;
}
