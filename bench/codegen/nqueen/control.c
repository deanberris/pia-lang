// The control (ADR 0075, section 1): nqueen.pia's recursion transcribed into
// C, so that the gap between Pia and plb2's C splits into codegen (Pia
// against this) and algorithm (this against plb2's C).

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t place(unsigned n, uint32_t k, uint32_t l, uint32_t c,
                      uint32_t r) {
  uint64_t m = 0;
  uint32_t used = l | c | r;
  for (uint32_t i = 0; i < n; ++i) {
    uint32_t z = 1u << i;
    if ((used & z) != 0)
      continue;
    if (k + 1 == n)
      m += 1;
    else
      m += place(n, k + 1, ((l | z) & 0x7FFFFFFFu) << 1, c | z, (r | z) >> 1);
  }
  return m;
}

int main(int argc, char *argv[]) {
  int n = 15;
  if (argc > 1)
    n = atoi(argv[1]);
  if (n > 31 || n <= 0)
    abort();
  printf("%llu\n", (unsigned long long)place((unsigned)n, 0, 0, 0, 0));
  return 0;
}
