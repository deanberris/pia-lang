// The C entry point of the Pia port: runs hanabi1224's nsieve 1.c driver,
// three sieves of 10000 << (n - i) flags. C allocates each buffer, as 1.c
// does; nsieve.pia's ns_count fills it and counts the primes below its length.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint32_t ns_count(uint8_t *flags, int64_t len);

static void nsieve(int m) {
  uint8_t *flags = malloc(m);
  if (!flags)
    abort();
  unsigned int count = ns_count(flags, m);
  free(flags);
  printf("Primes up to %8u %8u\n", m, count);
}

int main(int argc, char **argv) {
  int m = argc > 1 ? atoi(argv[1]) : 4;
  if (m < 2 || m > 16)
    abort();
  for (int i = 0; i < 3; i++)
    nsieve(10000 << (m - i));
  return 0;
}
