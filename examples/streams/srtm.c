// The stream demo on a real SRTM tile: reads a .hgt file, turns it into
// heights with Pia's load_hgt, and runs the hydrology of
// docs/streams.pia.md, docs/sediment.pia.md and docs/basins.pia.md over the
// whole tile, timing every stage.
//
//   srtm tile.hgt [output.png [threshold]]
//
// It writes the map at full size, and the heights at a quarter of the size
// as a 16-bit PNG, `<output>-quarter.png`. The streams program turns that
// into the animated GIF of the evolving landscape:
//
//   streams out-quarter.png out-quarter-map.png
//
// See examples/streams/fetch_srtm.sh for a tile.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>

#include "examples/streams/demo_io.h"
#include "examples/streams/pia_streams.h"

enum { HEIGHTS = 65536 };

static double ms(double a, double b) { return (b - a) * 1e3; }

// The peak resident memory so far, in MiB (macOS reports it in bytes).
static double peak_mib(void) {
  struct rusage u;
  getrusage(RUSAGE_SELF, &u);
  return u.ru_maxrss / 1048576.0;
}

int main(int argc, char **argv) {
  char in_buf[4096], out_buf[4096], q_name[4096], q_buf[4096];
  if (argc < 2 || argc > 4 || argv[1][0] == '-') {
    fprintf(stderr, "usage: srtm tile.hgt [output.png [threshold]]\n");
    return 2;
  }
  const char *output = argc > 2 ? argv[2] : "srtm-output.png";
  size_t bytes;
  uint8_t *raw = read_file(resolve(argv[1], in_buf, sizeof in_buf), &bytes);
  if (!raw) return 1;
  if (bytes % 2) {
    fprintf(stderr, "%s: an odd number of bytes is not a tile\n", argv[1]);
    return 1;
  }
  uint64_t n = bytes / 2;
  uint16_t *dem = malloc(n * sizeof *dem);
  double t0 = seconds();
  uint64_t w = load_hgt(raw, bytes, dem, n);
  double t1 = seconds();
  free(raw);
  if (w == 0) {
    fprintf(stderr, "%s: %zu bytes is not an SRTM tile\n", argv[1], bytes);
    return 1;
  }
  uint64_t h = n / w;
  uint16_t top = 0;
  for (uint64_t i = 0; i < n; ++i) top = dem[i] > top ? dem[i] : top;
  printf("tile: %llux%llu cells, relief %u m, loaded in %.1f ms\n",
         (unsigned long long)w, (unsigned long long)h, top, ms(t0, t1));
  uint32_t threshold = argc > 3 ? (uint32_t)atol(argv[3])
                                : (uint32_t)(n / 1000 > 8 ? n / 1000 : 8);

  // 1. Priority-flood.
  uint16_t *fill = malloc(n * sizeof *fill);
  uint64_t *parent = malloc(n * 8), *rank = malloc(n * 8), *link = malloc(n * 8);
  uint64_t *head = malloc(HEIGHTS * 8);
  double f0 = seconds();
  uint64_t unreached =
      fill_sinks(dem, n, w, fill, n, parent, n, rank, n, link, n, head, HEIGHTS);
  double f1 = seconds();
  uint64_t lakes = 0;
  for (uint64_t i = 0; i < n; ++i) lakes += fill[i] > dem[i];
  printf("fill: %llu cells raised, %llu unreached (%.1f ms)\n",
         (unsigned long long)lakes, (unsigned long long)unreached, ms(f0, f1));
  free(parent), free(rank), free(link), free(head);

  // 2. D8 directions, then 3. flow counts and watersheds in linear time,
  // over the height order (docs/sediment.pia.md, section 7), with one unit
  // of rain on every cell.
  uint64_t *down = malloc(n * 8), *basin = malloc(n * 8);
  uint64_t *order = malloc(n * 8), *pos = malloc(n * 8);
  uint32_t *acc = malloc(n * 4), *rain = malloc(n * 4), *pend = malloc(n * 4);
  uint32_t *cnt = malloc(HEIGHTS * 4);
  uint64_t *first = malloc(HEIGHTS * 8), *next = malloc(HEIGHTS * 8),
           *last = malloc(HEIGHTS * 8);
  uint16_t *owner = malloc(n * 2);
  double d0 = seconds();
  directions(fill, n, w, down, n);
  double d1 = seconds();
  rain_uniform(1, rain, n);
  drainage(fill, n, down, n, acc, n, basin, n, rain, n, pend, n, order, n, pos,
           n, cnt, HEIGHTS, first, HEIGHTS, next, HEIGHTS, last, HEIGHTS, owner,
           n);
  double d2 = seconds();
  uint64_t outlets = 0, drained = 0;
  for (uint64_t i = 0; i < n; ++i)
    if (down[i] == i) ++outlets, drained += acc[i];
  printf("directions: %.1f ms; drainage: %llu outlets drain %llu cells "
         "(%.1f ms)\n",
         ms(d0, d1), (unsigned long long)outlets, (unsigned long long)drained,
         ms(d1, d2));

  uint8_t *rgb = malloc(3 * n);
  double r0 = seconds();
  uint64_t streams = render(dem, n, fill, n, acc, n, basin, n, threshold, rgb, 3 * n);
  double r1 = seconds();
  printf("render: %llu stream cells at threshold %u (%.1f ms)\n",
         (unsigned long long)streams, threshold, ms(r0, r1));
  if (!write_rgb(resolve(output, out_buf, sizeof out_buf), (long)w, (long)h, rgb))
    return 1;
  printf("map written to %s\n", output);

  // 5. Sediment, sequential and by basin in parallel, from the same start:
  // they must agree cell for cell, and conserve the total.
  const uint32_t seed = 100, steps = 4;
  uint32_t *bs = malloc(n * 4), *ls = malloc(n * 4), *is = malloc(n * 4),
           *fs = malloc(n * 4);
  for (uint64_t i = 0; i < n; ++i) bs[i] = seed;
  double s0 = seconds();
  uint64_t gone_s =
      sediment(fill, n, down, n, acc, n, steps, bs, n, ls, n, is, n, fs, n,
               order, n, pos, n, cnt, HEIGHTS, first, HEIGHTS, next, HEIGHTS,
               last, HEIGHTS, owner, n);
  double s1 = seconds();
  uint64_t total_s = gone_s;
  for (uint64_t i = 0; i < n; ++i) total_s += (uint64_t)bs[i] + ls[i] + is[i];
  printf("sediment: %u steps, sequential, %.1f ms; %llu out; %llu in all, "
         "%llu at the start\n",
         steps, ms(s0, s1), (unsigned long long)gone_s,
         (unsigned long long)total_s, (unsigned long long)(n * seed));
  free(owner);

  // The basins' labels and height order come from drainage again, so the
  // spread sees the same start as the sequential run.
  uint64_t *lab = malloc(n * 8), *ord = malloc(n * 8), *ps = malloc(n * 8);
  uint32_t *ac = malloc(n * 4);
  uint16_t *owner2 = malloc(n * 2);
  drainage(fill, n, down, n, ac, n, lab, n, rain, n, pend, n, ord, n, ps, n,
           cnt, HEIGHTS, first, HEIGHTS, next, HEIGHTS, last, HEIGHTS, owner2,
           n);
  free(owner2), free(ps), free(pend), free(rain);
  uint32_t *bp = malloc(n * 4), *lp = malloc(n * 4), *ip = malloc(n * 4),
           *fp = malloc(n * 4), *gb = malloc(n * 4);
  uint64_t *border = malloc(n * 8), *keys = malloc(n * 8),
           *place2 = malloc(n * 8), *pos2 = malloc(n * 8),
           *gfirst = malloc(n * 8), *gnext = malloc(n * 8),
           *glast = malloc(n * 8), *gowner = malloc(n * 8);
  uint32_t *gcnt = malloc(n * 4);
  for (uint64_t i = 0; i < n; ++i) bp[i] = seed;
  double p0 = seconds();
  uint64_t gone_p = sediment_basins(
      fill, n, down, n, ac, n, lab, n, ord, n, steps, bp, n, lp, n, ip, n, fp,
      n, gb, n, border, n, keys, n, place2, n, pos2, n, gcnt, n, gfirst, n,
      gnext, n, glast, n, gowner, n);
  double p1 = seconds();
  uint64_t differ = 0;
  for (uint64_t i = 0; i < n; ++i)
    differ += bs[i] != bp[i] || ls[i] != lp[i] || is[i] != ip[i];
  printf("basins: %u steps, by %llu basins in parallel, %.1f ms; %llu out; "
         "%llu cells differ\n",
         steps, (unsigned long long)outlets, ms(p0, p1),
         (unsigned long long)gone_p, (unsigned long long)differ);
  printf("memory: %.0f MiB at peak\n", peak_mib());
  if (total_s != n * seed || gone_s != gone_p || differ) {
    fprintf(stderr, "sediment: the runs disagree or the total changed\n");
    return 1;
  }

  // A quarter-size view of the heights, every fourth cell of every fourth
  // row, for the animation.
  uint64_t qw = (w + 3) / 4, qh = (h + 3) / 4;
  uint16_t *q = malloc(qw * qh * 2);
  for (uint64_t y = 0; y < qh; ++y)
    for (uint64_t x = 0; x < qw; ++x) q[y * qw + x] = dem[4 * y * w + 4 * x];
  const char *dot = strrchr(output, '.');
  size_t stem = dot ? (size_t)(dot - output) : strlen(output);
  snprintf(q_name, sizeof q_name, "%.*s-quarter.png", (int)stem, output);
  if (!write_heights(resolve(q_name, q_buf, sizeof q_buf), (long)qw, (long)qh, q))
    return 1;
  printf("quarter view (%llux%llu) written to %s\n", (unsigned long long)qw,
         (unsigned long long)qh, q_name);
  return 0;
}
