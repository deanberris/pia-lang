/* The C program around gif_quantise_c.pia that
   tests/std/Inputs/gif_quantise_gen.py runs: it encodes the RGB frames in
   RGB and writes OUT.  main W H NF DELAY LOOPS rgb.bin out.gif */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
uint64_t gif_encode_rgb(uint16_t w, uint16_t h, const uint8_t *rgb, uint64_t nrgb,
                        uint16_t nf, uint16_t delay, uint16_t loops, uint8_t *dst,
                        uint64_t ndst, uint8_t *idx, uint64_t nidx, uint8_t *pal,
                        uint64_t npal, uint8_t *bx, uint64_t nbx, uint8_t *hist,
                        uint64_t nhist, uint8_t *rect, uint64_t nrect, uint8_t *lz,
                        uint64_t nlz, uint8_t *hash, uint64_t nhash);
int main(int argc, char **argv) {
  int w = atoi(argv[1]), h = atoi(argv[2]), nf = atoi(argv[3]);
  int delay = atoi(argv[4]), loops = atoi(argv[5]);
  static uint8_t rgb[3 << 22], dst[1 << 24], idx[1 << 22], pal[768], bx[1536], hist[1024],
      rect[1 << 20], lz[3 << 20 | 5], hash[40960];
  FILE *f = fopen(argv[6], "rb");
  size_t n = fread(rgb, 1, sizeof rgb, f);
  fclose(f);
  uint64_t fs = (uint64_t)w * h;
  uint64_t out = gif_encode_rgb(w, h, rgb, n, nf, delay, loops, dst, sizeof dst, idx, n / 3,
                                pal, sizeof pal, bx, sizeof bx, hist, sizeof hist, rect, fs,
                                lz, 3 * fs + 5, hash, sizeof hash);
  if (!out) { fprintf(stderr, "encode failed\n"); return 1; }
  f = fopen(argv[7], "wb");
  fwrite(dst, 1, out, f);
  fclose(f);
  return 0;
}
