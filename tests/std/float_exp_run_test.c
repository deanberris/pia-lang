// Runs Pia.Float.Exp's exp, built by its pia_library, against libm's
// double exp over x in [-110, 0]. The proof says the result is within
// 1e-7 of the real exp, relative, plus 2^-149: this checks the compiled
// code meets that bound too, and prints how close it comes, the worst
// relative error where exp x is a normal f32. exp is exported under its
// Pia name (docs/codegen.md#c-abi), so it is named here by an asm label,
// with the leading underscore of Mach-O.

#include <math.h>
#include <stdio.h>

#if defined(__APPLE__)
#define PIA_EXP "_pia$Pia$Float$Exp$exp"
#else
#define PIA_EXP "pia$Pia$Float$Exp$exp"
#endif

float pia_exp(float x) __asm__(PIA_EXP);

int main(void) {
  const double tiny2 = ldexp(1.0, -149);
  double worst = 0;
  float worst_x = 0;
  int fails = 0;
  for (float x = 0.0f; x >= -110.0f; x -= 0.0003f) {
    float got = pia_exp(x);
    double want = exp((double)x);
    if (!(got >= 0.0f && got <= 1.0f) ||
        fabs(got - want) > 1e-7 * want + tiny2) {
      printf("exp(%.9g) = %.9g, want %.9g\n", x, got, want);
      ++fails;
      continue;
    }
    double rel = fabs(got - want) / want;
    if (want >= ldexp(1.0, -126) && rel > worst) {
      worst = rel;
      worst_x = x;
    }
  }
  printf("worst relative error %.6g at x = %.9g\n", worst, worst_x);
  return fails != 0;
}
