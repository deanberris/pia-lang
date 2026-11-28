// Runs Pia.Float.Exp's exp, compiled by piac --emit=obj, against libm's
// double exp over x in [-90, 0]: the proof says the result is finite and
// in [0, 1], and this checks how close it is, which is not proved yet.
// exp is exported under its Pia name (docs/codegen.md#c-abi), so it is
// named here by an asm label, with the leading underscore of Mach-O.

#include <math.h>
#include <stdio.h>

#if defined(__APPLE__)
#define PIA_EXP "_pia$Pia$Float$Exp$exp"
#else
#define PIA_EXP "pia$Pia$Float$Exp$exp"
#endif

float pia_exp(float x) __asm__(PIA_EXP);

int main(void) {
  double worst = 0;
  float worst_x = 0;
  int fails = 0;
  for (float x = 0.0f; x >= -90.0f; x -= 0.0003f) {
    float got = pia_exp(x);
    double want = exp((double)x);
    if (!(got >= 0.0f && got <= 1.0f)) {
      printf("exp(%g) = %g is outside [0, 1]\n", x, got);
      ++fails;
      continue;
    }
    // Below f32's smallest normal, 2^-126, the result may be 0.
    if (want < 1.2e-38) {
      if (got > 1.2e-38f) {
        printf("exp(%g) = %g, want about %g\n", x, got, want);
        ++fails;
      }
      continue;
    }
    double rel = fabs(got - want) / want;
    if (rel > worst) {
      worst = rel;
      worst_x = x;
    }
  }
  if (pia_exp(0.0f) != 1.0f) {
    printf("exp(0) = %g, want 1\n", pia_exp(0.0f));
    ++fails;
  }
  printf("worst relative error %g at x = %g\n", worst, worst_x);
  if (worst > 3e-7) {
    printf("worse than 3e-7\n");
    ++fails;
  }
  return fails != 0;
}
