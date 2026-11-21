// Runs the stages of docs/streams.pia.md, compiled by piac --emit=obj, over
// random and hand-made terrains, and checks them against C references and
// against the properties the hydrology needs: filling never digs, settles
// to the reference surface, directions point downhill, every cell's flow is
// one plus its upstream neighbours', and watershed labels agree along flow.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "examples/streams/pia_streams.h"

static int failures = 0;

#define CHECK(cond, ...)                         \
  do {                                           \
    if (!(cond)) {                               \
      fprintf(stderr, "%s:%d: ", __FILE__, __LINE__); \
      fprintf(stderr, __VA_ARGS__);              \
      fputc('\n', stderr);                       \
      if (++failures > 20) exit(1);              \
    }                                            \
  } while (0)

static uint32_t seed = 2026;
static uint32_t rnd(void) {
  seed = seed * 1103515245u + 12345u;
  return seed >> 8;
}

static int border(long i, long w, long h) {
  long x = i % w, y = i / w;
  return x == 0 || y == 0 || x == w - 1 || y == h - 1;
}

// The filled surface, by relaxing W = max(Z, min_n W + 1) to its fixed
// point in plain index order. The fixed point is unique, so the sweep
// order does not matter.
static void ref_fill(const uint16_t *dem, long w, long h, uint16_t *out) {
  long n = w * h;
  for (long i = 0; i < n; ++i) out[i] = border(i, w, h) ? dem[i] : 65535;
  for (int changed = 1; changed;) {
    changed = 0;
    for (long i = 0; i < n; ++i) {
      if (border(i, w, h)) continue;
      uint32_t lo = 65535;
      for (int dy = -1; dy <= 1; ++dy)
        for (int dx = -1; dx <= 1; ++dx)
          if (dx || dy) {
            uint32_t v = out[i + dy * w + dx];
            if (v < lo) lo = v;
          }
      uint32_t up = lo + 1 > 65535 ? 65535 : lo + 1;
      uint32_t c = dem[i] > up ? dem[i] : up;
      if (c < out[i]) out[i] = (uint16_t)c, changed = 1;
    }
  }
}

// D8 with weights 10 and 7, neighbours in row order, first best wins.
static void ref_directions(const uint16_t *f, long w, long h, uint64_t *down) {
  for (long i = 0; i < w * h; ++i) {
    down[i] = i;
    if (border(i, w, h)) continue;
    uint32_t best = 0;
    for (int dy = -1; dy <= 1; ++dy)
      for (int dx = -1; dx <= 1; ++dx) {
        if (!dx && !dy) continue;
        long j = i + dy * w + dx;
        if (f[j] >= f[i]) continue;
        uint32_t d = (f[i] - f[j]) * (dx && dy ? 7u : 10u);
        if (d > best) best = d, down[i] = j;
      }
  }
}

static void check(const char *name, const uint16_t *dem, long w, long h) {
  long n = w * h;
  uint16_t *fill = malloc(n * 2), *want = malloc(n * 2);
  uint64_t *down = malloc(n * 8), *basin = malloc(n * 8), *want_down = malloc(n * 8);
  uint32_t *acc = malloc(n * 4), *sum = calloc(n, 4);
  uint8_t *rgb = malloc(3 * n);
  const uint32_t threshold = 4, limit = 100000;

  uint32_t passes = fill_sinks(dem, n, w, limit, fill, n);
  CHECK(passes < limit, "%s: filling did not settle", name);
  ref_fill(dem, w, h, want);
  for (long i = 0; i < n; ++i) {
    CHECK(fill[i] >= dem[i], "%s: cell %ld was dug", name, i);
    CHECK(fill[i] == want[i], "%s: cell %ld filled to %u, want %u", name, i,
          fill[i], want[i]);
  }

  directions(fill, n, w, down, n);
  ref_directions(fill, w, h, want_down);
  for (long i = 0; i < n; ++i) {
    CHECK(down[i] == want_down[i], "%s: cell %ld drains to %llu, want %llu",
          name, i, (unsigned long long)down[i], (unsigned long long)want_down[i]);
    CHECK(down[i] == (uint64_t)i || fill[down[i]] < fill[i],
          "%s: cell %ld drains uphill", name, i);
    // A settled surface below 65535 has no interior pits.
    CHECK(border(i, w, h) || down[i] != (uint64_t)i || fill[i] == 65535,
          "%s: interior cell %ld is a pit", name, i);
  }

  accumulate(fill, n, down, n, acc, n, basin, n);
  uint64_t drained = 0;
  for (long i = 0; i < n; ++i)
    if (down[i] != (uint64_t)i) sum[down[i]] += acc[i];
  for (long i = 0; i < n; ++i) {
    CHECK(acc[i] == sum[i] + 1, "%s: cell %ld has flow %u, want %u", name, i,
          acc[i], sum[i] + 1);
    CHECK(down[basin[i]] == basin[i], "%s: label of %ld is not an outlet", name, i);
    CHECK(basin[i] == basin[down[i]], "%s: %ld and its receiver disagree", name, i);
    if (down[i] == (uint64_t)i) drained += acc[i];
  }
  CHECK(drained == (uint64_t)n, "%s: outlets drain %llu of %ld cells", name,
        (unsigned long long)drained, n);

  uint64_t streams = render(dem, n, fill, n, acc, n, basin, n, threshold, rgb, 3 * n);
  uint64_t want_streams = 0;
  for (long i = 0; i < n; ++i) want_streams += acc[i] >= threshold;
  CHECK(streams == want_streams, "%s: %llu stream cells, want %llu", name,
        (unsigned long long)streams, (unsigned long long)want_streams);

  // The whole pipeline in one call gives the same picture.
  uint8_t *rgb2 = malloc(3 * n);
  uint64_t streams2 = delineate(dem, n, w, limit, threshold, fill, n, down, n,
                                acc, n, basin, n, rgb2, 3 * n);
  CHECK(streams2 == streams && memcmp(rgb, rgb2, 3 * n) == 0,
        "%s: delineate differs from the stages", name);

  free(fill), free(want), free(down), free(basin), free(want_down);
  free(acc), free(sum), free(rgb), free(rgb2);
}

int main(void) {
  static const long sizes[][2] = {{3, 3}, {4, 3}, {3, 7}, {17, 5}, {64, 48}, {100, 101}};
  for (size_t s = 0; s < sizeof sizes / sizeof *sizes; ++s) {
    long w = sizes[s][0], h = sizes[s][1];
    uint16_t *dem = malloc(w * h * 2);
    char name[64];
    // Rough random terrain, then a smoothed one with real valleys.
    for (long i = 0; i < w * h; ++i) dem[i] = rnd() % 60000;
    snprintf(name, sizeof name, "random %ldx%ld", w, h);
    check(name, dem, w, h);
    for (long i = 0; i < w * h; ++i) dem[i] = (uint16_t)(rnd() % 256 * 64);
    snprintf(name, sizeof name, "terraced %ldx%ld", w, h);
    check(name, dem, w, h);
    free(dem);
  }

  // A plane tilted to the south: every column drains straight down, so a
  // bottom-row cell collects its whole column, less the top row (a border
  // outlet of its own).
  {
    long w = 9, h = 7;
    uint16_t dem[63];
    for (long i = 0; i < w * h; ++i) dem[i] = (uint16_t)(1000 * (h - i / w));
    check("tilted plane", dem, w, h);
    uint16_t fill[63];
    uint64_t down[63], basin[63];
    uint32_t acc[63];
    fill_sinks(dem, 63, w, 100, fill, 63);
    directions(fill, 63, w, down, 63);
    accumulate(fill, 63, down, 63, acc, 63, basin, 63);
    for (long x = 1; x + 1 < w; ++x)
      CHECK(acc[(h - 1) * w + x] == h - 1, "tilted plane: column %ld drains %u",
            x, acc[(h - 1) * w + x]);
  }

  // A bowl, open only to the west edge: it fills into a lake that spills
  // west.
  {
    long w = 11, h = 11;
    uint16_t dem[121], fill[121];
    for (long i = 0; i < w * h; ++i) {
      long dx = i % w - 5, dy = i / w - 5;
      dem[i] = (uint16_t)(100 * (dx * dx + dy * dy) + (i % w == 0 ? 0 : 6000));
    }
    dem[5 * w + 5] = 0;  // the bottom of the pit
    check("bowl", dem, w, h);
    fill_sinks(dem, 121, w, 100, fill, 121);
    CHECK(fill[5 * w + 5] > dem[5 * w + 5], "bowl: the pit was not filled");
    CHECK(fill[5 * w + 5] >= 6000, "bowl: the lake is below the rim");
  }

  if (failures) return 1;
  printf("all stream delineation checks passed\n");
  return 0;
}
