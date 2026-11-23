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
// hydrology is Pia; this file only reads and writes images, with ImageIO,
// because Pia has no I/O yet.

#include <ApplicationServices/ApplicationServices.h>
#include <ImageIO/ImageIO.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <time.h>

#include "examples/streams/pia_streams.h"

// Reads an image as 16-bit heights: a grayscale image's values, or a
// colour image's brightness, (r + 2g + b) / 4.
static uint16_t *read_heights(const char *path, long *w, long *h) {
  CFURLRef url = CFURLCreateFromFileSystemRepresentation(
      NULL, (const UInt8 *)path, (CFIndex)strlen(path), false);
  CGImageSourceRef src = CGImageSourceCreateWithURL(url, NULL);
  CFRelease(url);
  CGImageRef img = src ? CGImageSourceCreateImageAtIndex(src, 0, NULL) : NULL;
  if (src) CFRelease(src);
  if (!img) {
    fprintf(stderr, "%s: cannot read the image\n", path);
    return NULL;
  }
  *w = (long)CGImageGetWidth(img);
  *h = (long)CGImageGetHeight(img);
  long n = *w * *h;
  uint16_t *dem = malloc(n * sizeof *dem);
  CGColorSpaceRef own = CGImageGetColorSpace(img);
  if (own && CGColorSpaceGetModel(own) == kCGColorSpaceModelMonochrome) {
    // A grayscale heightmap is drawn in its own colour space, so its
    // values arrive unchanged.
    CGContextRef gray = CGBitmapContextCreate(
        dem, *w, *h, 16, *w * 2, own,
        kCGImageAlphaNone | kCGBitmapByteOrder16Little);
    if (gray) {
      CGContextDrawImage(gray, CGRectMake(0, 0, *w, *h), img);
      CGContextRelease(gray);
      CGImageRelease(img);
      return dem;
    }
  }
  uint16_t *rgba = calloc((size_t)*w * *h * 4, sizeof *rgba);
  CGColorSpaceRef cs = CGColorSpaceCreateWithName(kCGColorSpaceSRGB);
  CGContextRef ctx = CGBitmapContextCreate(
      rgba, *w, *h, 16, *w * 8, cs,
      kCGImageAlphaPremultipliedLast | kCGBitmapByteOrder16Little);
  CGColorSpaceRelease(cs);
  CGContextDrawImage(ctx, CGRectMake(0, 0, *w, *h), img);
  CGContextRelease(ctx);
  CGImageRelease(img);
  for (long i = 0; i < n; ++i) {
    const uint16_t *p = rgba + 4 * i;
    dem[i] = (uint16_t)(((uint32_t)p[0] + 2u * p[1] + p[2]) / 4);
  }
  free(rgba);
  return dem;
}

static int ends_with(const char *s, const char *suffix) {
  size_t n = strlen(s), k = strlen(suffix);
  return n >= k && strcasecmp(s + n - k, suffix) == 0;
}

// Writes packed RGB as a PNG, or a GIF when the name ends in .gif.
static int write_rgb(const char *path, long w, long h, const uint8_t *rgb) {
  uint8_t *rgba = malloc((size_t)w * h * 4);
  for (long i = 0; i < w * h; ++i) {
    memcpy(rgba + 4 * i, rgb + 3 * i, 3);
    rgba[4 * i + 3] = 255;
  }
  CFDataRef data = CFDataCreate(NULL, rgba, (CFIndex)(w * h * 4));
  CGDataProviderRef provider = CGDataProviderCreateWithCFData(data);
  CGColorSpaceRef cs = CGColorSpaceCreateWithName(kCGColorSpaceSRGB);
  CGImageRef img = CGImageCreate(w, h, 8, 32, w * 4, cs,
                                 kCGImageAlphaNoneSkipLast, provider, NULL,
                                 false, kCGRenderingIntentDefault);
  CFURLRef url = CFURLCreateFromFileSystemRepresentation(
      NULL, (const UInt8 *)path, (CFIndex)strlen(path), false);
  CFStringRef type = ends_with(path, ".gif") ? CFSTR("com.compuserve.gif")
                                             : CFSTR("public.png");
  CGImageDestinationRef dst = CGImageDestinationCreateWithURL(url, type, 1, NULL);
  int ok = dst != NULL;
  if (dst) {
    CGImageDestinationAddImage(dst, img, NULL);
    ok = CGImageDestinationFinalize(dst);
    CFRelease(dst);
  }
  if (!ok) fprintf(stderr, "%s: cannot write the image\n", path);
  CFRelease(url);
  CGImageRelease(img);
  CGColorSpaceRelease(cs);
  CGDataProviderRelease(provider);
  CFRelease(data);
  free(rgba);
  return ok;
}

// Writes 16-bit heights as a 16-bit grayscale PNG, so reading it back
// gives the same heights.
static int write_heights(const char *path, long w, long h, const uint16_t *dem) {
  CFDataRef data = CFDataCreate(NULL, (const UInt8 *)dem, (CFIndex)(w * h * 2));
  CGDataProviderRef provider = CGDataProviderCreateWithCFData(data);
  CGColorSpaceRef cs = CGColorSpaceCreateWithName(kCGColorSpaceLinearGray);
  CGImageRef img = CGImageCreate(w, h, 16, 16, w * 2, cs,
                                 kCGImageAlphaNone | kCGBitmapByteOrder16Little,
                                 provider, NULL, false, kCGRenderingIntentDefault);
  CFURLRef url = CFURLCreateFromFileSystemRepresentation(
      NULL, (const UInt8 *)path, (CFIndex)strlen(path), false);
  CGImageDestinationRef dst =
      CGImageDestinationCreateWithURL(url, CFSTR("public.png"), 1, NULL);
  int ok = dst != NULL && img != NULL;
  if (ok) {
    CGImageDestinationAddImage(dst, img, NULL);
    ok = CGImageDestinationFinalize(dst);
  }
  if (dst) CFRelease(dst);
  if (!ok) fprintf(stderr, "%s: cannot write the image\n", path);
  CFRelease(url);
  if (img) CGImageRelease(img);
  CGColorSpaceRelease(cs);
  CGDataProviderRelease(provider);
  CFRelease(data);
  return ok;
}

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

// Paths relative to where `bazel run` was started, not its runfiles.
static const char *resolve(const char *path, char *buf, size_t size) {
  const char *dir = getenv("BUILD_WORKING_DIRECTORY");
  if (!dir || path[0] == '/') return path;
  snprintf(buf, size, "%s/%s", dir, path);
  return buf;
}

static double seconds(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec + t.tv_nsec / 1e9;
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
  if (w < 3 || h < 3 || (unsigned long)w * h >= 4294967295ul) {
    fprintf(stderr, "the map must be at least 3x3 and under 2^32 cells\n");
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
  const uint32_t limit = 10000;
  double t0 = seconds();
  uint32_t passes = fill_sinks(dem, n, w, limit, fill, n);
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
  printf("%ldx%ld cells; sinks filled in %u sweep pairs%s (%.1f ms)\n", w, h,
         passes, passes == limit ? ", not settled" : "", (t1 - t0) * 1e3);
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
  // recomputed before each. Two epochs of uniform rain, four of a storm
  // band moving down the map, then a wet season and a dry one.
  enum { EPOCHS = 8, STEPS = 4 };
  uint16_t *ground = malloc(n * sizeof *ground);
  uint32_t *rain = malloc(n * sizeof *rain), *flow = malloc(n * sizeof *flow);
  uint32_t *pend = malloc(n * sizeof *pend);
  for (uint64_t i = 0; i < n; ++i)
    bed[i] = seed, load[i] = 0, inflow[i] = 0;
  uint64_t moved = 0, changed = 0;
  uint16_t *fill0 = malloc(n * sizeof *fill0);
  memcpy(fill0, fill, n * sizeof *fill);
  double t8 = seconds(), pia_ms = 0;
  for (int e = 0; e < EPOCHS; ++e) {
    const char *kind;
    for (long y = 0; y < h; ++y)
      for (long x = 0; x < w; ++x) {
        uint32_t r;
        if (e < 2)
          kind = "uniform", r = 4;
        else if (e < 6)
          kind = "storm",
          r = y >= (e - 2) * h / 4 && y < (e - 1) * h / 4 ? 16 : 1;
        else
          kind = e == 6 ? "wet" : "dry", r = e == 6 ? 8 : 0;
        rain[y * w + x] = r;
      }
    double a = seconds();
    surface(dem, n, bed, n, ground, n);
    fill_sinks(ground, n, w, limit, fill, n);
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
    accumulate(fill, n, down, n, acc, n, basin, n);
    render_load(ground, n, fill, n, acc, n, basin, n, flux, n, threshold, rgb,
                3 * n);
    char frame[4096], frame_buf[4096];
    sediment_name(output, "-epoch-", e, frame, sizeof frame);
    if (!write_rgb(resolve(frame, frame_buf, sizeof frame_buf), w, h, rgb))
      return 1;
    uint32_t peak = 0;
    for (uint64_t i = 0; i < n; ++i)
      peak = flow[i] > peak ? flow[i] : peak;
    printf("epoch %d (%s rain): %llu out, peak flow %u, written to %s\n", e,
           kind, (unsigned long long)out, peak, frame);
  }
  uint64_t left = 0;
  for (uint64_t i = 0; i < n; ++i) {
    left += (uint64_t)bed[i] + load[i] + inflow[i];
    changed += fill[i] != fill0[i];
  }
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
  free(ground), free(rain), free(flow), free(pend), free(fill0);
  free(order), free(pos), free(bed), free(load), free(inflow), free(flux);
  free(cnt), free(first), free(next), free(last), free(owner);
  free(dem), free(fill), free(down), free(basin), free(acc), free(rgb);
  return 0;
}
