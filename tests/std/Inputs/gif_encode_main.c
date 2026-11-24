/* The C program around gif_encode_c.pia that tests/std/Inputs/gif_encode_gen.py
   runs: it encodes the frames in FRAMES with palette PAL and writes OUT. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
uint64_t gif_encode(uint16_t w, uint16_t h, const uint8_t *pal, uint64_t npal,
                    const uint8_t *frames, uint64_t nframes, uint16_t nf,
                    uint16_t delay, uint16_t loops, uint8_t *dst, uint64_t ndst,
                    uint8_t *rect, uint64_t nrect, uint8_t *lz, uint64_t nlz,
                    uint8_t *hash, uint64_t nhash);
/* main W H NF DELAY LOOPS pal.bin frames.bin out.gif */
int main(int argc, char **argv) {
  int w = atoi(argv[1]), h = atoi(argv[2]), nf = atoi(argv[3]);
  int delay = atoi(argv[4]), loops = atoi(argv[5]);
  static uint8_t pal[768], frames[1 << 22], dst[1 << 23], rect[1 << 20], lz[3 << 20 | 5], hash[40960];
  FILE *f = fopen(argv[6], "rb"); size_t np = fread(pal, 1, sizeof pal, f); fclose(f);
  f = fopen(argv[7], "rb"); size_t nfr = fread(frames, 1, sizeof frames, f); fclose(f);
  uint64_t fs = (uint64_t)w * h;
  uint64_t n = gif_encode(w, h, pal, np, frames, nfr, nf, delay, loops, dst, sizeof dst, rect, fs, lz, 3 * fs + 5, hash, sizeof hash);
  if (!n) { fprintf(stderr, "encode failed\n"); return 1; }
  f = fopen(argv[8], "wb"); fwrite(dst, 1, n, f); fclose(f);
  return 0;
}
