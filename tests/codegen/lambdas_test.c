// Runs lambdas.pia, compiled by piac --emit=obj: a higher-order function
// specialised at a lambda and at a named function (ADR 0044).

#include <stdint.h>
#include <stdio.h>
#include <string.h>

uint64_t count_big(const uint8_t *xs, uint64_t n);
uint64_t count_digits(const uint8_t *xs, uint64_t n);

int main(void) {
  int failures = 0;
  uint8_t xs[300];
  uint64_t big = 0;
  for (int i = 0; i < 300; ++i) {
    xs[i] = (uint8_t)(i * 7 % 11);
    big += xs[i] > 3;
  }
  if (count_big(xs, 300) != big) {
    fprintf(stderr, "count_big = %llu, expected %llu\n",
            (unsigned long long)count_big(xs, 300), (unsigned long long)big);
    ++failures;
  }
  if (count_big(xs, 0) != 0) {
    fprintf(stderr, "count_big of nothing is not 0\n");
    ++failures;
  }
  const char *s = "a1b22c333-x";
  if (count_digits((const uint8_t *)s, strlen(s)) != 6) {
    fprintf(stderr, "count_digits = %llu\n",
            (unsigned long long)count_digits((const uint8_t *)s, strlen(s)));
    ++failures;
  }
  if (failures) return 1;
  printf("all lambda checks passed\n");
  return 0;
}
