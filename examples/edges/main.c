// The edge detection demo: reads a BMP image, runs the Pia pipeline in
// edges.pia over it, and writes the edge map as a BMP (docs/demo.md).
//
//   edges [input.bmp [output.bmp]]
//
// Without an input it draws a test scene, saves it as edges-input.bmp, and
// writes edges-output.bmp. It also prints both images as text, so the
// result is visible in the terminal. All the image processing is Pia; this
// file only reads and writes files, because Pia has no I/O yet.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "examples/edges/pia_edges.h"

typedef struct {
  long w, h;
  uint8_t *rgb;  // packed RGB, top row first
} image;

static uint32_t le32(const uint8_t *p) {
  return p[0] | p[1] << 8 | p[2] << 16 | (uint32_t)p[3] << 24;
}

static void put32(uint8_t *p, uint32_t v) {
  for (int i = 0; i < 4; ++i) p[i] = (uint8_t)(v >> (8 * i));
}

// Reads an uncompressed 24- or 32-bit BMP, as `sips -s format bmp` writes.
static int read_bmp(const char *path, image *img) {
  FILE *f = fopen(path, "rb");
  if (!f) {
    perror(path);
    return 0;
  }
  fseek(f, 0, SEEK_END);
  long size = ftell(f);
  fseek(f, 0, SEEK_SET);
  uint8_t *data = malloc(size > 0 ? size : 1);
  int ok = size > 54 && fread(data, 1, size, f) == (size_t)size;
  fclose(f);
  if (!ok || data[0] != 'B' || data[1] != 'M') {
    fprintf(stderr, "%s: not a BMP file\n", path);
    free(data);
    return 0;
  }
  uint32_t offset = le32(data + 10);
  int32_t w = (int32_t)le32(data + 18), h = (int32_t)le32(data + 22);
  int bpp = data[28] | data[29] << 8;
  uint32_t compression = le32(data + 30);
  int top_down = h < 0;
  if (top_down) h = -h;
  if ((bpp != 24 && bpp != 32) || (compression != 0 && compression != 3) ||
      w <= 0 || h <= 0) {
    fprintf(stderr, "%s: only uncompressed 24- and 32-bit BMPs are read\n",
            path);
    free(data);
    return 0;
  }
  long stride = ((long)w * (bpp / 8) + 3) / 4 * 4;
  if ((unsigned long)offset + (unsigned long)stride * (unsigned long)h >
      (unsigned long)size) {
    fprintf(stderr, "%s: truncated\n", path);
    free(data);
    return 0;
  }
  img->w = w;
  img->h = h;
  img->rgb = malloc((size_t)w * h * 3);
  for (long y = 0; y < h; ++y) {
    const uint8_t *row = data + offset + stride * (top_down ? y : h - 1 - y);
    for (long x = 0; x < w; ++x) {
      const uint8_t *px = row + x * (bpp / 8);  // blue, green, red
      uint8_t *out = img->rgb + 3 * (y * w + x);
      out[0] = px[2];
      out[1] = px[1];
      out[2] = px[0];
    }
  }
  free(data);
  return 1;
}

// Writes a 24-bit BMP of a grayscale image.
static int write_bmp(const char *path, long w, long h, const uint8_t *rgb,
                     int channels) {
  long stride = (w * 3 + 3) / 4 * 4;
  uint8_t header[54] = {'B', 'M'};
  put32(header + 2, 54 + stride * h);
  put32(header + 10, 54);
  put32(header + 14, 40);
  put32(header + 18, (uint32_t)w);
  put32(header + 22, (uint32_t)h);
  header[26] = 1;
  header[28] = 24;
  put32(header + 34, stride * h);
  FILE *f = fopen(path, "wb");
  if (!f) {
    perror(path);
    return 0;
  }
  fwrite(header, 1, sizeof header, f);
  uint8_t *row = calloc(stride, 1);
  for (long y = h - 1; y >= 0; --y) {
    for (long x = 0; x < w; ++x) {
      const uint8_t *px = rgb + channels * (y * w + x);
      row[3 * x + 0] = px[channels == 3 ? 2 : 0];
      row[3 * x + 1] = px[channels == 3 ? 1 : 0];
      row[3 * x + 2] = px[0];
    }
    fwrite(row, 1, stride, f);
  }
  free(row);
  return fclose(f) == 0;
}

// A test scene: a sky gradient, a sun, a house with a window, and noise
// that the blur removes.
static void draw_scene(image *img) {
  long w = img->w = 320, h = img->h = 200;
  img->rgb = malloc((size_t)w * h * 3);
  uint32_t seed = 12345;
  for (long y = 0; y < h; ++y) {
    for (long x = 0; x < w; ++x) {
      int r = 90 + (int)(y / 2), g = 140 + (int)(y / 3), b = 230;
      long dx = x - 250, dy = y - 50;
      if (dx * dx + dy * dy < 28 * 28) r = 255, g = 240, b = 120;
      if (y >= 150) r = 60, g = 150, b = 60;
      if (x >= 60 && x < 160 && y >= 95 && y < 160) r = 200, g = 80, b = 70;
      if (y >= 55 && y < 95 && x >= 60 + (95 - y) * 5 / 4 &&
          x < 160 - (95 - y) * 5 / 4)
        r = 120, g = 50, b = 40;
      if (x >= 85 && x < 115 && y >= 110 && y < 135) r = 240, g = 240, b = 200;
      seed = seed * 1103515245 + 12345;
      int noise = (int)(seed >> 16) % 17 - 8;
      uint8_t *px = img->rgb + 3 * (y * w + x);
      int c[3] = {r + noise, g + noise, b + noise};
      for (int i = 0; i < 3; ++i) px[i] = c[i] < 0 ? 0 : c[i] > 255 ? 255 : c[i];
    }
  }
}

// Prints a grayscale image as text, about 72 characters wide.
static void print_text(const char *title, long w, long h, const uint8_t *px,
                       int channels) {
  static const char ramp[] = " .:-=+*#%@";
  long cols = w < 72 ? w : 72;
  long rows = h * cols / w / 2;
  if (rows < 1) rows = 1;
  printf("%s\n", title);
  for (long r = 0; r < rows; ++r) {
    for (long c = 0; c < cols; ++c) {
      long y0 = r * h / rows, y1 = (r + 1) * h / rows;
      long x0 = c * w / cols, x1 = (c + 1) * w / cols;
      long sum = 0, n = 0, peak = 0;
      for (long y = y0; y < y1; ++y)
        for (long x = x0; x < x1; ++x) {
          const uint8_t *p = px + channels * (y * w + x);
          long v = channels == 3 ? (p[0] + 2 * p[1] + p[2]) / 4
                                 : p[0];
          sum += v;
          if (v > peak) peak = v;
          ++n;
        }
      // Edges are thin, so the edge map shows each cell's strongest pixel.
      long v = channels == 1 ? peak : (n ? sum / n : 0);
      putchar(ramp[v * 9 / 255]);
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

int main(int argc, char **argv) {
  char in_buf[4096], out_buf[4096];
  const char *input = argc > 1 ? argv[1] : NULL;
  const char *output = argc > 2 ? argv[2] : "edges-output.bmp";
  if (argc > 3 || (input && input[0] == '-')) {
    fprintf(stderr, "usage: edges [input.bmp [output.bmp]]\n");
    return 2;
  }
  image img;
  if (input) {
    if (!read_bmp(resolve(input, in_buf, sizeof in_buf), &img)) return 1;
  } else {
    draw_scene(&img);
    input = "edges-input.bmp";
    if (!write_bmp(resolve(input, in_buf, sizeof in_buf), img.w, img.h,
                   img.rgb, 3))
      return 1;
    printf("drew a test scene: %s\n", input);
  }
  if (img.w < 3 || img.h < 3) {
    fprintf(stderr, "the image must be at least 3x3 pixels\n");
    return 1;
  }
  uint64_t n = (uint64_t)img.w * img.h;
  uint8_t *luma = malloc(n), *smooth = malloc(n), *out = malloc(n);
  // The Pia pipeline. Its precondition, proved at every call inside Pia,
  // is the caller's job here: three bytes per pixel, equal buffers, and at
  // least three rows of at least three pixels.
  edges(img.rgb, 3 * n, (uint64_t)img.w, luma, n, smooth, n, out, n);
  if (!write_bmp(resolve(output, out_buf, sizeof out_buf), img.w, img.h, out,
                 1))
    return 1;
  print_text("input:", img.w, img.h, img.rgb, 3);
  print_text("edges:", img.w, img.h, out, 1);
  printf("%ldx%ld pixels, edges written to %s\n", img.w, img.h, output);
  return 0;
}
