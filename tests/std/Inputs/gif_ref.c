/* enc W H BITS in.idx out.gif : giflib-encode raw indices.
   dec in.gif out.idx : giflib-decode the first frame's indices. */
#include <gif_lib.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
  int err;
  if (!strcmp(argv[1], "enc")) {
    int w = atoi(argv[2]), h = atoi(argv[3]), bits = atoi(argv[4]);
    FILE *f = fopen(argv[5], "rb");
    unsigned char *px = malloc(w * h);
    if (fread(px, 1, w * h, f) != (size_t)(w * h)) return 2;
    fclose(f);
    GifFileType *g = EGifOpenFileName(argv[6], 0, &err);
    ColorMapObject *cm = GifMakeMapObject(1 << bits, NULL);
    for (int i = 0; i < (1 << bits); ++i) cm->Colors[i].Red = cm->Colors[i].Green = cm->Colors[i].Blue = i;
    EGifPutScreenDesc(g, w, h, bits, 0, cm);
    EGifPutImageDesc(g, 0, 0, w, h, 0, NULL);
    for (int y = 0; y < h; ++y) EGifPutLine(g, px + y * w, w);
    EGifCloseFile(g, &err);
    return 0;
  }
  GifFileType *g = DGifOpenFileName(argv[2], &err);
  if (!g || DGifSlurp(g) != GIF_OK) { fprintf(stderr, "slurp failed\n"); return 3; }
  SavedImage *im = &g->SavedImages[0];
  FILE *o = fopen(argv[3], "wb");
  fwrite(im->RasterBits, 1, im->ImageDesc.Width * im->ImageDesc.Height, o);
  fclose(o);
  return 0;
}
