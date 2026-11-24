// Image and file I/O shared by the stream demo's programs (demo_io.c).

#ifndef PIA_EXAMPLES_STREAMS_DEMO_IO_H
#define PIA_EXAMPLES_STREAMS_DEMO_IO_H

#include <stddef.h>
#include <stdint.h>

// Reads an image as 16-bit heights: a grayscale image's values, or a
// colour image's brightness. Returns NULL if it cannot.
uint16_t *read_heights(const char *path, long *w, long *h);
// Writes packed RGB as a PNG, or a GIF when the name ends in .gif.
int write_rgb(const char *path, long w, long h, const uint8_t *rgb);
// Writes 16-bit heights as a 16-bit grayscale PNG.
int write_heights(const char *path, long w, long h, const uint16_t *dem);
// Reads a whole file, or returns NULL.
uint8_t *read_file(const char *path, size_t *size);
// A path relative to where `bazel run` was started, not its runfiles.
const char *resolve(const char *path, char *buf, size_t size);
// Monotonic seconds.
double seconds(void);

#endif
