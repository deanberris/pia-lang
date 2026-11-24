// Image and file I/O for the stream demo's programs, main.c and srtm.c,
// with macOS's ImageIO, because Pia has no I/O yet.

#include <ApplicationServices/ApplicationServices.h>
#include <ImageIO/ImageIO.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <time.h>

#include "examples/streams/demo_io.h"

// Reads an image as 16-bit heights: a grayscale image's values, or a
// colour image's brightness, (r + 2g + b) / 4.
uint16_t *read_heights(const char *path, long *w, long *h) {
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
int write_rgb(const char *path, long w, long h, const uint8_t *rgb) {
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
int write_heights(const char *path, long w, long h, const uint16_t *dem) {
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

// Paths relative to where `bazel run` was started, not its runfiles.
const char *resolve(const char *path, char *buf, size_t size) {
  const char *dir = getenv("BUILD_WORKING_DIRECTORY");
  if (!dir || path[0] == '/') return path;
  snprintf(buf, size, "%s/%s", dir, path);
  return buf;
}

double seconds(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec + t.tv_nsec / 1e9;
}


// Reads a whole file, or returns NULL. `*size` is its length in bytes.
uint8_t *read_file(const char *path, size_t *size) {
  FILE *f = fopen(path, "rb");
  if (!f) {
    fprintf(stderr, "%s: cannot open the file\n", path);
    return NULL;
  }
  fseek(f, 0, SEEK_END);
  long n = ftell(f);
  fseek(f, 0, SEEK_SET);
  uint8_t *buf = n > 0 ? malloc((size_t)n) : NULL;
  if (!buf || fread(buf, 1, (size_t)n, f) != (size_t)n) {
    fprintf(stderr, "%s: cannot read the file\n", path);
    free(buf);
    fclose(f);
    return NULL;
  }
  fclose(f);
  *size = (size_t)n;
  return buf;
}
