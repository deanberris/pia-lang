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

// Reads an image as 16-bit brightness, (r + 2g + b) / 4.
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
  uint16_t *rgba = calloc((size_t)*w * *h * 4, sizeof *rgba);
  CGColorSpaceRef cs = CGColorSpaceCreateWithName(kCGColorSpaceSRGB);
  CGContextRef ctx = CGBitmapContextCreate(
      rgba, *w, *h, 16, *w * 8, cs,
      kCGImageAlphaPremultipliedLast | kCGBitmapByteOrder16Little);
  CGColorSpaceRelease(cs);
  CGContextDrawImage(ctx, CGRectMake(0, 0, *w, *h), img);
  CGContextRelease(ctx);
  CGImageRelease(img);
  long n = *w * *h;
  uint16_t *dem = malloc(n * sizeof *dem);
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
      double z = 0.75 * (1 - v);                       // north is high
      z += 0.18 * fabs(u - 0.5 - 0.1 * sin(6 * v));    // a winding valley
      double n = 0, amp = 0.5, freq = 4;
      for (int o = 0; o < 5; ++o, amp *= 0.5, freq *= 2)
        n += amp * value_noise(u * freq, v * freq, 7u + o);
      z += 0.22 * n;
      double cx = u - 0.72, cy = v - 0.55;               // the crater
      double r2 = (cx * cx + cy * cy) / (0.09 * 0.09);
      z += r2 < 1 ? -0.12 * (1 - r2) : 0.04 * exp(-(r2 - 1) * 2);
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
    uint8_t *gray = malloc((size_t)w * h * 3);
    for (long i = 0; i < w * h; ++i) memset(gray + 3 * i, dem[i] >> 8, 3);
    input = "streams-input.png";
    int ok = write_rgb(resolve(input, in_buf, sizeof in_buf), w, h, gray);
    free(gray);
    if (!ok) return 1;
    printf("drew a synthetic terrain: %s\n", input);
  }
  if (w < 3 || h < 3 || (unsigned long)w * h >= 4294967295ul) {
    fprintf(stderr, "the map must be at least 3x3 and under 2^32 cells\n");
    return 1;
  }
  uint64_t n = (uint64_t)w * h;
  // A stream drains at least 1 in 400 of the map, unless told otherwise.
  uint32_t threshold = threshold_arg ? (uint32_t)threshold_arg
                                     : (uint32_t)(n / 400 > 8 ? n / 400 : 8);
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
  uint64_t lakes = 0, outlets = 0, drained = 0;
  for (uint64_t i = 0; i < n; ++i) {
    lakes += fill[i] > dem[i];
    if (down[i] == i) {
      ++outlets;
      drained += acc[i];
    }
  }
  print_text(w, h, dem, fill, acc, threshold);
  printf("%ldx%ld cells; sinks filled in %u sweep pairs%s (%.1f ms)\n", w, h,
         passes, passes == limit ? ", not settled" : "", (t1 - t0) * 1e3);
  printf("D8 directions (%.1f ms); accumulation and watersheds (%.1f ms)\n",
         (t2 - t1) * 1e3, (t3 - t2) * 1e3);
  printf("%llu lake cells, %llu stream cells at threshold %u, %llu outlets "
         "draining %llu cells (%.1f ms)\n",
         (unsigned long long)lakes, (unsigned long long)streams, threshold,
         (unsigned long long)outlets, (unsigned long long)drained,
         (t4 - t3) * 1e3);
  printf("map written to %s\n", output);
  free(dem), free(fill), free(down), free(basin), free(acc), free(rgb);
  return 0;
}
