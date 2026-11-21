// Runs the passes in edges.pia, compiled by piac --emit=obj, over random
// images of several sizes and compares each with a C reference.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "examples/edges/pia_edges.h"

static void ref_gray(const uint8_t *rgb, long n, uint8_t *dst) {
  for (long i = 0; i < n; ++i)
    dst[i] = (77 * rgb[3 * i] + 150 * rgb[3 * i + 1] + 29 * rgb[3 * i + 2]) / 256;
}

static void ref_blur(const uint8_t *src, long w, long h, uint8_t *dst) {
  memcpy(dst, src, w * h);
  for (long y = 1; y + 1 < h; ++y)
    for (long x = 1; x + 1 < w; ++x) {
      int s = 0;
      for (int dy = -1; dy <= 1; ++dy)
        for (int dx = -1; dx <= 1; ++dx) s += src[(y + dy) * w + x + dx];
      dst[y * w + x] = s / 9;
    }
}

static void ref_sobel(const uint8_t *src, long w, long h, uint8_t *dst) {
  memset(dst, 0, w * h);
#define P(dx, dy) src[(y + (dy)) * w + x + (dx)]
  for (long y = 1; y + 1 < h; ++y)
    for (long x = 1; x + 1 < w; ++x) {
      int gx = (P(1, -1) + 2 * P(1, 0) + P(1, 1)) -
               (P(-1, -1) + 2 * P(-1, 0) + P(-1, 1));
      int gy = (P(-1, 1) + 2 * P(0, 1) + P(1, 1)) -
               (P(-1, -1) + 2 * P(0, -1) + P(1, -1));
      int g = abs(gx) + abs(gy);
      dst[y * w + x] = g > 255 ? 255 : g;
    }
#undef P
}

static int failures = 0;

static void compare(const char *what, long w, long h, const uint8_t *got,
                    const uint8_t *want) {
  for (long i = 0; i < w * h; ++i)
    if (got[i] != want[i]) {
      if (failures++ < 10)
        fprintf(stderr, "%s %ldx%ld: pixel (%ld, %ld) is %d, expected %d\n",
                what, w, h, i % w, i / w, got[i], want[i]);
      return;
    }
}

int main(void) {
  const long widths[] = {3, 4, 17, 64, 321};
  const long heights[] = {3, 5, 40};
  uint32_t seed = 1;
  for (unsigned wi = 0; wi < sizeof widths / sizeof *widths; ++wi)
    for (unsigned hi = 0; hi < sizeof heights / sizeof *heights; ++hi) {
      long w = widths[wi], h = heights[hi], n = w * h;
      uint8_t *rgb = malloc(3 * n), *a = malloc(n), *b = malloc(n),
              *c = malloc(n), *ra = malloc(n), *rb = malloc(n),
              *rc = malloc(n);
      for (long i = 0; i < 3 * n; ++i) {
        seed = seed * 1103515245 + 12345;
        // Mostly flat regions with sharp steps, plus extremes.
        rgb[i] = (i / 37) % 3 == 0 ? 255 : (uint8_t)(seed >> 16);
      }
      ref_gray(rgb, n, ra);
      ref_blur(ra, w, h, rb);
      ref_sobel(rb, w, h, rc);

      gray(rgb, 3 * n, a, n);
      compare("gray", w, h, a, ra);
      blur(ra, n, w, b, n);
      compare("blur", w, h, b, rb);
      sobel(rb, n, w, c, n);
      compare("sobel", w, h, c, rc);

      memset(c, 7, n);
      edges(rgb, 3 * n, w, a, n, b, n, c, n);
      compare("edges", w, h, c, rc);
      free(rgb), free(a), free(b), free(c), free(ra), free(rb), free(rc);
    }
  if (failures) {
    fprintf(stderr, "%d mismatches\n", failures);
    return 1;
  }
  printf("edges.pia matches the C reference\n");
  return 0;
}
