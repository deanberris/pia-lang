// The C entry point of the Pia port: reads n as plb2's nqueen.c does and
// prints the number of solutions.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

// nqueen.pia's nq_solve; n : int{1..31} is a uint8_t in the C ABI.
uint64_t nq_solve(uint8_t n);

int main(int argc, char *argv[]) {
  int n = 15;
  if (argc > 1)
    n = atoi(argv[1]);
  if (n > 31 || n <= 0)
    abort();
  printf("%llu\n", (unsigned long long)nq_solve((uint8_t)n));
  return 0;
}
