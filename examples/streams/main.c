// The stream delineation demo: reads a heightmap, runs the Pia pipeline in
// docs/streams.pia.md over it, and writes a map of its streams, lakes and
// watersheds (docs/streams.pia.md).
//
//   streams [input [output [threshold]]]
//
// Without an input it draws a synthetic terrain, saves it as
// streams-input.png, and writes streams-output.png. The input can be any
// image macOS can read (PNG, GIF, JPEG, TIFF, BMP, 8 or 16 bits); brighter
// means higher. The output is PNG, or GIF if its name ends in .gif. All the
// hydrology is Pia; this file and demo_io.c only read and write images,
// with ImageIO, because Pia has no I/O yet.

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "examples/streams/demo_io.h"
#include "examples/streams/pia_streams.h"

// A deterministic value noise in [0, 1), smoothly interpolated.
static double hash01(long x, long y, uint32_t seed) {
  uint32_t v = (uint32_t)x * 374761393u + (uint32_t)y * 668265263u + seed;
  v = (v ^ (v >> 13)) * 1274126177u;
  return (v ^ (v >> 16)) / 4294967296.0;
}

static double value_noise(double x, double y, uint32_t seed) {
  long x0 = (long)floor(x), y0 = (long)floor(y);
  double fx = x - x0, fy = y - y0;
  fx = fx * fx * (3 - 2 * fx);
  fy = fy * fy * (3 - 2 * fy);
  double a = hash01(x0, y0, seed), b = hash01(x0 + 1, y0, seed);
  double c = hash01(x0, y0 + 1, seed), d = hash01(x0 + 1, y0 + 1, seed);
  return (a + (b - a) * fx) + ((c + (d - c) * fx) - (a + (b - a) * fx)) * fy;
}

// A synthetic terrain: a ridge along the top, falling towards a valley that
// drains out of the bottom edge, rolling hills, a crater (a sink that
// filling must raise into a lake), and fractal noise for detail.
static uint16_t *draw_terrain(long w, long h) {
  uint16_t *dem = malloc((size_t)w * h * sizeof *dem);
  for (long y = 0; y < h; ++y) {
    for (long x = 0; x < w; ++x) {
      double u = (double)x / w, v = (double)y / h;
      double valley = 0.5 + 0.12 * sin(5 * v);        // a winding valley
      double z = 0.35 * (1 - v);                       // north is high
      z += 0.55 * fabs(u - valley);                    // sides fall to it
      double n = 0, amp = 0.5, freq = 3;
      for (int o = 0; o < 6; ++o, amp *= 0.55, freq *= 2)
        n += amp * value_noise(u * freq, v * freq, 7u + o);
      z += 0.35 * n;                                   // hills and gullies
      double cx = u - 0.78, cy = v - 0.4;              // the crater
      double r2 = (cx * cx + cy * cy) / (0.08 * 0.08);
      z += r2 < 1 ? -0.15 * (1 - r2) : 0.05 * exp(-(r2 - 1) * 2);
      if (z < 0) z = 0;
      if (z > 1.2) z = 1.2;
      dem[y * w + x] = (uint16_t)(z / 1.2 * 60000);
    }
  }
  return dem;
}

// Prints the map as text, about 72 characters wide: '#' for a major
// stream, '~' for a stream, 'o' for a lake, and the height otherwise.
static void print_text(long w, long h, const uint16_t *dem,
                       const uint16_t *fill, const uint32_t *acc,
                       uint32_t threshold) {
  static const char ramp[] = " .:-=+*";
  long cols = w < 72 ? w : 72;
  long rows = h * cols / w / 2;
  if (rows < 1) rows = 1;
  for (long r = 0; r < rows; ++r) {
    for (long c = 0; c < cols; ++c) {
      long y0 = r * h / rows, y1 = (r + 1) * h / rows;
      long x0 = c * w / cols, x1 = (c + 1) * w / cols;
      uint32_t peak = 0;
      long sum = 0, n = 0, lake = 0;
      for (long y = y0; y < y1; ++y)
        for (long x = x0; x < x1; ++x) {
          long i = y * w + x;
          if (acc[i] > peak) peak = acc[i];
          if (fill[i] > dem[i]) ++lake;
          sum += dem[i];
          ++n;
        }
      char ch;
      if (peak >= 16ull * threshold)
        ch = '#';
      else if (peak >= threshold)
        ch = '~';
      else if (2 * lake > n)
        ch = 'o';
      else
        ch = ramp[(n ? sum / n : 0) * 6 / 65535];
      putchar(ch);
    }
    putchar('\n');
  }
}

// The name of a sediment map: the output name with `tag`, and the epoch
// when it is not negative, before its extension.
static void sediment_name(const char *output, const char *tag, int epoch,
                          char *buf, size_t size) {
  const char *dot = strrchr(output, '.');
  size_t stem = dot ? (size_t)(dot - output) : strlen(output);
  char num[16] = "";
  if (epoch >= 0)
    snprintf(num, sizeof num, "%d", epoch);
  snprintf(buf, size, "%.*s%s%s%s", (int)stem, output, tag, num,
           dot ? dot : ".png");
}

int main(int argc, char **argv) {
  char in_buf[4096], out_buf[4096];
  const char *input = argc > 1 ? argv[1] : NULL;
  const char *output = argc > 2 ? argv[2] : "streams-output.png";
  long threshold_arg = argc > 3 ? atol(argv[3]) : 0;
  if (argc > 4 || (input && input[0] == '-') || (argc > 3 && threshold_arg < 1)) {
    fprintf(stderr, "usage: streams [input [output [threshold]]]\n");
    return 2;
  }
  long w, h;
  uint16_t *dem;
  if (input) {
    dem = read_heights(resolve(input, in_buf, sizeof in_buf), &w, &h);
    if (!dem) return 1;
  } else {
    w = 384, h = 256;
    dem = draw_terrain(w, h);
    input = "streams-input.png";
    if (!write_heights(resolve(input, in_buf, sizeof in_buf), w, h, dem))
      return 1;
    printf("drew a synthetic terrain: %s\n", input);
  }
  if (w < 3 || h < 3 || (unsigned long)w * h > 16777215ul) {
    fprintf(stderr,
            "the map must be at least 3x3 and at most 16777215 cells\n");
    return 1;
  }
  uint64_t n = (uint64_t)w * h;
  // A stream drains at least 1 in 100 of the map, unless told otherwise.
  uint32_t threshold = threshold_arg ? (uint32_t)threshold_arg
                                     : (uint32_t)(n / 100 > 8 ? n / 100 : 8);
  uint16_t *fill = malloc(n * sizeof *fill);
  uint64_t *down = malloc(n * sizeof *down), *basin = malloc(n * sizeof *basin);
  uint32_t *acc = malloc(n * sizeof *acc);
  uint8_t *rgb = malloc(3 * n);

  // The Pia pipeline, a stage at a time so each can be timed. The
  // preconditions are the caller's job here, and proved at every call
  // inside Pia: equal lengths, three bytes per pixel, and at least three
  // rows of at least three cells.
  // Priority-flood's scratch: each cell's parent and rank, and the bucket
  // queue's links, one list per height.
  uint64_t *fparent = malloc(n * sizeof *fparent),
           *frank = malloc(n * sizeof *frank), *fnext = malloc(n * sizeof *fnext);
  uint64_t *fhead = malloc(65536 * sizeof *fhead);
  double t0 = seconds();
  uint64_t unreached =
      fill_sinks(dem, n, w, fill, n, fparent, n, frank, n, fnext, n, fhead, 65536);
  double t1 = seconds();
  directions(fill, n, w, down, n);
  double t2 = seconds();
  accumulate(fill, n, down, n, acc, n, basin, n);
  double t3 = seconds();
  uint64_t streams = render(dem, n, fill, n, acc, n, basin, n, threshold, rgb, 3 * n);
  double t4 = seconds();

  if (!write_rgb(resolve(output, out_buf, sizeof out_buf), w, h, rgb)) return 1;
  // Every border cell is an outlet; the ones that drain a stream's worth
  // of the map are the watersheds worth counting.
  uint64_t lakes = 0, outlets = 0, rivers = 0, drained = 0;
  for (uint64_t i = 0; i < n; ++i) {
    lakes += fill[i] > dem[i];
    if (down[i] == i) {
      ++outlets;
      rivers += acc[i] >= threshold;
      drained += acc[i];
    }
  }
  print_text(w, h, dem, fill, acc, threshold);
  printf("%ldx%ld cells; sinks filled, %llu cells unreached (%.1f ms)\n", w, h,
         (unsigned long long)unreached, (t1 - t0) * 1e3);
  printf("D8 directions (%.1f ms); accumulation and watersheds (%.1f ms)\n",
         (t2 - t1) * 1e3, (t3 - t2) * 1e3);
  printf("%llu lake cells, %llu stream cells at threshold %u (%.1f ms)\n",
         (unsigned long long)lakes, (unsigned long long)streams, threshold,
         (t4 - t3) * 1e3);
  printf("%llu outlets drain %llu cells; %llu of them drain a stream\n",
         (unsigned long long)outlets, (unsigned long long)drained,
         (unsigned long long)rivers);
  printf("map written to %s\n", output);

  // Sediment transport (docs/streams.pia.md, section 5): 100 units of bed
  // on every cell, moved for a few steps in height order. Pia proves the
  // total is conserved; the check here is that the compiled code agrees.
  const uint32_t seed = 100, nsteps = 4;
  // Pia sorts the cells by height itself, in linear time; it needs scratch
  // buffers, since it cannot allocate yet.
  enum { HEIGHTS = 65536 };
  uint64_t *order = malloc(n * sizeof *order), *pos = malloc(n * sizeof *pos);
  uint32_t *bed = malloc(n * sizeof *bed), *load = malloc(n * sizeof *load);
  uint32_t *inflow = malloc(n * sizeof *inflow), *flux = malloc(n * sizeof *flux);
  uint32_t *cnt = malloc(HEIGHTS * sizeof *cnt);
  uint64_t *first = malloc(HEIGHTS * sizeof *first),
           *next = malloc(HEIGHTS * sizeof *next);
  uint64_t *last = malloc(HEIGHTS * sizeof *last);
  uint16_t *owner = malloc(n * sizeof *owner);
  for (uint64_t i = 0; i < n; ++i)
    bed[i] = seed;
  double t6 = seconds();
  uint64_t gone =
      sediment(fill, n, down, n, acc, n, nsteps, bed, n, load, n, inflow, n,
               flux, n, order, n, pos, n, cnt, HEIGHTS, first, HEIGHTS, next,
               HEIGHTS, last, HEIGHTS, owner, n);
  double t7 = seconds();
  uint64_t total = 0, carried = 0, moving = 0;
  for (uint64_t i = 0; i < n; ++i) {
    total += (uint64_t)bed[i] + load[i] + inflow[i];
    carried += flux[i] > 0;
    moving += flux[i] > 0 && acc[i] >= threshold;
  }
  render_load(dem, n, fill, n, acc, n, basin, n, flux, n, threshold, rgb, 3 * n);
  printf(
      "sediment: %u steps over %llu cells, sorted by height in Pia (%.1f ms)\n",
      nsteps, (unsigned long long)n, (t7 - t6) * 1e3);
  printf("sediment: %llu units in the beds and the water, %llu out, %llu in all;"
         " %llu at the start\n",
         (unsigned long long)total, (unsigned long long)gone,
         (unsigned long long)(total + gone), (unsigned long long)(n * seed));
  printf("sediment: %llu cells carry a load, %llu of them on a stream\n",
         (unsigned long long)carried, (unsigned long long)moving);
  // How the load leaving the stream cells spreads, by its number of bits:
  // the picture's colour ramp is over the same scale.
  uint64_t bits[33] = {0};
  for (uint64_t i = 0; i < n; ++i)
    if (acc[i] >= threshold) {
      int b = 0;
      for (uint32_t f = flux[i]; f; f >>= 1)
        ++b;
      ++bits[b];
    }
  printf("sediment: stream load by bits:");
  for (int b = 0; b <= 32; ++b)
    if (bits[b])
      printf(" %d:%llu", b, (unsigned long long)bits[b]);
  printf("\n");
  if (total + gone != n * seed) {
    fprintf(stderr, "sediment: the total changed\n");
    return 1;
  }
  char sed_name[4096], sed_buf[4096];
  sediment_name(output, "-sediment", -1, sed_name, sizeof sed_name);
  if (!write_rgb(resolve(sed_name, sed_buf, sizeof sed_buf), w, h, rgb)) return 1;
  printf("sediment map written to %s\n", sed_name);

  // The landscape evolves (docs/sediment.pia.md, section 6): epochs of
  // `steps` time steps, each under its own rainfall field, with the ground
  // raised by the sediment on it, and its sinks, directions and order
  // recomputed before each. A year is eight epochs: two of uniform rain,
  // four of a storm band moving down the map, then a wet season and a dry
  // one. Three years run; the first year's epochs are written as PNGs, and
  // every epoch is a frame of an animated GIF.
  enum { EPOCHS = 24, YEAR = 8, STEPS = 4 };
  uint8_t *pal = malloc(768), *frames = malloc((size_t)EPOCHS * n);
  palette(pal, 768);
  uint16_t *ground = malloc(n * sizeof *ground);
  uint32_t *rain = malloc(n * sizeof *rain), *flow = malloc(n * sizeof *flow);
  uint32_t *pend = malloc(n * sizeof *pend);
  for (uint64_t i = 0; i < n; ++i)
    bed[i] = seed, load[i] = 0, inflow[i] = 0;
  uint64_t moved = 0, changed = 0;
  uint16_t *fill0 = malloc(n * sizeof *fill0);
  memcpy(fill0, fill, n * sizeof *fill);
  double t8 = seconds(), pia_ms = 0, shed_ms = 0;
  for (int e = 0; e < EPOCHS; ++e) {
    // The rainfall fields are Pia's, each proved to keep the total rain
    // within a u32 (docs/sediment.pia.md, "Rainfall fields").
    const char *kind;
    int season = e % YEAR;
    if (season < 2)
      kind = "uniform", rain_uniform(4, rain, n);
    else if (season < 6)
      kind = "storm",
      rain_band(w, (season - 2) * h / 4, (season - 1) * h / 4, 16, 1, rain, n);
    else
      kind = season == 6 ? "wet" : "dry", rain_season(season == 6, 8, rain, n);
    double a = seconds();
    surface(dem, n, bed, n, ground, n);
    fill_sinks(ground, n, w, fill, n, fparent, n, frank, n, fnext, n, fhead,
               65536);
    directions(fill, n, w, down, n);
    uint64_t out =
        evolve(fill, n, down, n, rain, n, STEPS, bed, n, load, n, inflow, n,
               flux, n, flow, n, pend, n, order, n, pos, n, cnt, HEIGHTS, first,
               HEIGHTS, next, HEIGHTS, last, HEIGHTS, owner, n);
    double b = seconds();
    pia_ms += (b - a) * 1e3;
    if (out == UINT64_MAX) {
      fprintf(stderr,
              "evolve: the rain or the sediment does not fit in a u32\n");
      return 1;
    }
    moved += out;
    // The picture's flow counts and watersheds, in linear time over the
    // height order (docs/sediment.pia.md, section 7).
    double c0 = seconds();
    drainage(fill, n, down, n, acc, n, basin, n, rain, n, pend, n, order, n,
             pos, n, cnt, HEIGHTS, first, HEIGHTS, next, HEIGHTS, last, HEIGHTS,
             owner, n);
    shed_ms += (seconds() - c0) * 1e3;
    render_load_index(ground, n, fill, n, acc, n, basin, n, flux, n, threshold,
                      frames + (size_t)e * n, n);
    char frame[4096] = "", frame_buf[4096];
    if (e < YEAR) {
      render_load(ground, n, fill, n, acc, n, basin, n, flux, n, threshold, rgb,
                  3 * n);
      sediment_name(output, "-epoch-", e, frame, sizeof frame);
      if (!write_rgb(resolve(frame, frame_buf, sizeof frame_buf), w, h, rgb))
        return 1;
    }
    uint32_t peak = 0;
    for (uint64_t i = 0; i < n; ++i)
      peak = flow[i] > peak ? flow[i] : peak;
    printf("epoch %d (%s rain): %llu out, peak flow %u%s%s\n", e, kind,
           (unsigned long long)out, peak, *frame ? ", written to " : "", frame);
  }
  uint64_t left = 0;
  for (uint64_t i = 0; i < n; ++i) {
    left += (uint64_t)bed[i] + load[i] + inflow[i];
    changed += fill[i] != fill0[i];
  }
  printf("evolution: watersheds for the pictures in %.1f ms\n", shed_ms);
  printf("evolution: %d epochs of %d steps in %.1f ms (%.1f ms in Pia); "
         "%llu cells changed height\n",
         EPOCHS, STEPS, (seconds() - t8) * 1e3, pia_ms,
         (unsigned long long)changed);
  printf("evolution: %llu units left, %llu out, %llu in all; %llu at the "
         "start\n",
         (unsigned long long)left, (unsigned long long)moved,
         (unsigned long long)(left + moved), (unsigned long long)(n * seed));
  if (left + moved != n * seed) {
    fprintf(stderr, "evolution: the total changed\n");
    return 1;
  }

  // The animation: the encoder of Pia.Image.Gif.Encode, whose output is
  // proved to parse as a GIF with one frame per epoch.
  if (w <= 65535 && h <= 65535) {
    uint64_t bound = gif_bound(w, h, EPOCHS);
    uint8_t *gif = malloc(bound), *rect = malloc(n), *lz = malloc(3 * n + 5);
    uint8_t *hash = malloc(40960);
    double g0 = seconds();
    uint64_t size =
        gif_animation(w, h, pal, 768, frames, (uint64_t)EPOCHS * n, EPOCHS, 25,
                      0, gif, bound, rect, n, lz, 3 * n + 5, hash, 40960);
    double g1 = seconds();
    if (size == 0) {
      fprintf(stderr, "the animation could not be encoded\n");
      return 1;
    }
    char anim[4096], anim_buf[4096];
    sediment_name(output, "-evolution", -1, anim, sizeof anim);
    char *dot = strrchr(anim, '.');
    if (dot)
      strcpy(dot, ".gif");
    FILE *f = fopen(resolve(anim, anim_buf, sizeof anim_buf), "wb");
    if (!f || fwrite(gif, 1, size, f) != size || fclose(f) != 0) {
      fprintf(stderr, "%s: cannot write the animation\n", anim);
      return 1;
    }
    printf("animation: %d frames, %llu bytes, encoded in %.1f ms, written to "
           "%s\n",
           EPOCHS, (unsigned long long)size, (g1 - g0) * 1e3, anim);
    free(gif), free(rect), free(lz), free(hash);
  }
  free(pal), free(frames);

  // Sediment by basin (docs/basins.pia.md): every basin on its own core, a
  // spread over the basins, against the sequential sediment from the same
  // start. Basins never exchange sediment, so the two must agree cell for
  // cell.
  {
    uint64_t *lab = malloc(n * sizeof *lab), *ord = malloc(n * sizeof *ord);
    uint64_t *ps = malloc(n * sizeof *ps);
    uint32_t *ac = malloc(n * sizeof *ac);
    drainage(fill, n, down, n, ac, n, lab, n, rain, n, pend, n, ord, n, ps, n,
             cnt, HEIGHTS, first, HEIGHTS, next, HEIGHTS, last, HEIGHTS, owner,
             n);
    uint32_t *bs = malloc(n * 4), *ls = malloc(n * 4), *is = malloc(n * 4),
             *fs = malloc(n * 4);
    uint32_t *bp = malloc(n * 4), *lp = malloc(n * 4), *ip = malloc(n * 4),
             *fp = malloc(n * 4), *gb = malloc(n * 4);
    uint64_t *border = malloc(n * 8), *keys = malloc(n * 8),
             *place2 = malloc(n * 8), *pos2 = malloc(n * 8),
             *gfirst = malloc(n * 8), *gnext = malloc(n * 8),
             *glast = malloc(n * 8), *gowner = malloc(n * 8);
    uint32_t *gcnt = malloc(n * 4);
    const uint32_t bsteps = 16;
    for (uint64_t i = 0; i < n; ++i)
      bs[i] = bp[i] = seed;
    double s0 = seconds();
    uint64_t gone_s =
        sediment(fill, n, down, n, ac, n, bsteps, bs, n, ls, n, is, n, fs, n,
                 order, n, pos, n, cnt, HEIGHTS, first, HEIGHTS, next, HEIGHTS,
                 last, HEIGHTS, owner, n);
    double s1 = seconds();
    uint64_t gone_p = sediment_basins(
        fill, n, down, n, ac, n, lab, n, ord, n, bsteps, bp, n, lp, n, ip, n,
        fp, n, gb, n, border, n, keys, n, place2, n, pos2, n, gcnt, n, gfirst,
        n, gnext, n, glast, n, gowner, n);
    double s2 = seconds();
    uint64_t differ = 0, basins = 0;
    for (uint64_t i = 0; i < n; ++i) {
      differ += bs[i] != bp[i] || ls[i] != lp[i] || is[i] != ip[i];
      basins += down[i] == i;
    }
    printf("basins: %llu steps, sequential %.1f ms, by %llu basins in parallel "
           "%.1f ms; %llu out both ways; %llu cells differ\n",
           (unsigned long long)bsteps, (s1 - s0) * 1e3,
           (unsigned long long)basins, (s2 - s1) * 1e3,
           (unsigned long long)gone_p, (unsigned long long)differ);
    if (gone_s != gone_p || differ) {
      fprintf(stderr, "basins: the parallel run differs from the sequential\n");
      return 1;
    }
    free(lab), free(ord), free(ps), free(ac), free(bs), free(ls), free(is);
    free(fs), free(bp), free(lp), free(ip), free(fp), free(gb), free(border);
    free(keys), free(place2), free(pos2), free(gfirst), free(gnext);
    free(glast), free(gowner), free(gcnt);
  }
  free(ground), free(rain), free(flow), free(pend), free(fill0);
  free(order), free(pos), free(bed), free(load), free(inflow), free(flux);
  free(cnt), free(first), free(next), free(last), free(owner);
  free(dem), free(fill), free(down), free(basin), free(acc), free(rgb);
  free(fparent), free(frank), free(fnext), free(fhead);
  return 0;
}
