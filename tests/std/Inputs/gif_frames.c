/* The reference for Pia.Image.Gif.Decode's run test, over giflib.
     gif_frames make DIR    writes still.gif, interlaced.gif and anim.gif
     gif_frames comp F K    prints frame K of F composited, as RGBA hex
   Compositing follows ADR 0054's decode_frame: the canvas starts
   transparent; each frame is drawn with its local colour table or the
   global one, clipped to the screen, skipping its transparent index; and
   before the next frame, disposal 2 clears the frame's rectangle to
   transparent and disposal 3 restores the canvas from before the frame.
   giflib decodes the indices (and de-interlaces them) and reads each
   frame's Graphic Control Extension. */
#include <gif_lib.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static ColorMapObject *ramp(int bits, int r, int g, int b) {
  ColorMapObject *cm = GifMakeMapObject(1 << bits, NULL);
  for (int i = 0; i < (1 << bits); ++i) {
    cm->Colors[i].Red = (unsigned char)(i * r);
    cm->Colors[i].Green = (unsigned char)(i * g);
    cm->Colors[i].Blue = (unsigned char)(i * b);
  }
  return cm;
}

static void put_gce(GifFileType *g, int disposal, int delay, int tr) {
  GraphicsControlBlock gcb = {disposal, false, delay, tr};
  GifByteType ext[4];
  size_t n = EGifGCBToExtension(&gcb, ext);
  EGifPutExtension(g, GRAPHICS_EXT_FUNC_CODE, (int)n, ext);
}

static void put_frame(GifFileType *g, int x0, int y0, int w, int h, int il,
                      ColorMapObject *local, int seed, int mod) {
  EGifPutImageDesc(g, x0, y0, w, h, il, local);
  GifPixelType *row = malloc(w);
  /* giflib writes rows in the order given; for an interlaced frame the
     caller passes them in interlaced order. */
  static const int start[] = {0, 4, 2, 1}, step[] = {8, 8, 4, 2};
  for (int pass = 0; pass < (il ? 4 : 1); ++pass)
    for (int y = il ? start[pass] : 0; y < h; y += il ? step[pass] : 1) {
      for (int x = 0; x < w; ++x) row[x] = (GifPixelType)((x * 3 + y * 5 + seed) % mod);
      EGifPutLine(g, row, w);
    }
  free(row);
}

static void make(const char *dir) {
  char path[1024];
  int err;
  snprintf(path, sizeof path, "%s/still.gif", dir);
  GifFileType *g = EGifOpenFileName(path, false, &err);
  EGifPutScreenDesc(g, 20, 12, 4, 0, ramp(4, 16, 8, 4));
  put_frame(g, 0, 0, 20, 12, false, NULL, 0, 16);
  EGifCloseFile(g, &err);

  snprintf(path, sizeof path, "%s/interlaced.gif", dir);
  g = EGifOpenFileName(path, false, &err);
  EGifPutScreenDesc(g, 16, 19, 2, 0, ramp(2, 60, 60, 60));
  put_frame(g, 2, 1, 13, 17, true, ramp(3, 30, 0, 36), 1, 8);
  EGifCloseFile(g, &err);

  snprintf(path, sizeof path, "%s/anim.gif", dir);
  g = EGifOpenFileName(path, false, &err);
  EGifSetGifVersion(g, true);
  EGifPutScreenDesc(g, 24, 16, 5, 0, ramp(5, 8, 4, 2));
  EGifPutExtensionLeader(g, APPLICATION_EXT_FUNC_CODE);
  EGifPutExtensionBlock(g, 11, "NETSCAPE2.0");
  unsigned char loop[3] = {1, 3, 0};
  EGifPutExtensionBlock(g, 3, loop);
  EGifPutExtensionTrailer(g);
  put_gce(g, 1, 10, NO_TRANSPARENT_COLOR);
  put_frame(g, 0, 0, 24, 16, false, NULL, 0, 32);
  put_gce(g, 2, 20, 0);
  put_frame(g, 4, 2, 10, 8, false, NULL, 7, 5);
  put_gce(g, 3, 30, 3);
  put_frame(g, 10, 6, 14, 10, false, ramp(2, 80, 40, 20), 2, 4);
  put_gce(g, 0, 40, NO_TRANSPARENT_COLOR);
  put_frame(g, 18, 12, 10, 6, false, NULL, 5, 32);
  EGifCloseFile(g, &err);
}

static void comp(const char *file, int k) {
  int err;
  GifFileType *g = DGifOpenFileName(file, &err);
  if (!g || DGifSlurp(g) != GIF_OK) exit(3);
  int W = g->SWidth, H = g->SHeight;
  unsigned char *c = calloc(W * H, 4), *save = calloc(W * H, 4);
  int pd = 0, px = 0, py = 0, pw = 0, ph = 0;
  for (int j = 0; j <= k; ++j) {
    SavedImage *im = &g->SavedImages[j];
    GraphicsControlBlock gcb = {0, false, 0, NO_TRANSPARENT_COLOR};
    DGifSavedExtensionToGCB(g, j, &gcb);
    if (pd == 2)
      for (int y = py; y < py + ph && y < H; ++y)
        for (int x = px; x < px + pw && x < W; ++x) memset(c + (y * W + x) * 4, 0, 4);
    if (pd == 3) memcpy(c, save, W * H * 4);
    if (gcb.DisposalMode == 3) memcpy(save, c, W * H * 4);
    ColorMapObject *cm = im->ImageDesc.ColorMap ? im->ImageDesc.ColorMap : g->SColorMap;
    GifImageDesc *d = &im->ImageDesc;
    for (int y = 0; y < d->Height; ++y)
      for (int x = 0; x < d->Width; ++x) {
        int v = im->RasterBits[y * d->Width + x], X = d->Left + x, Y = d->Top + y;
        if (X >= W || Y >= H || v == gcb.TransparentColor) continue;
        unsigned char *o = c + (Y * W + X) * 4;
        if (v < cm->ColorCount) {
          o[0] = cm->Colors[v].Red; o[1] = cm->Colors[v].Green; o[2] = cm->Colors[v].Blue;
        } else o[0] = o[1] = o[2] = 0;
        o[3] = 255;
      }
    pd = gcb.DisposalMode; px = d->Left; py = d->Top; pw = d->Width; ph = d->Height;
  }
  for (int i = 0; i < W * H * 4; ++i) printf("%d%s", c[i], i + 1 < W * H * 4 ? " " : "\n");
}

int main(int argc, char **argv) {
  if (argc == 3 && !strcmp(argv[1], "make")) make(argv[2]);
  else if (argc == 4 && !strcmp(argv[1], "comp")) comp(argv[2], atoi(argv[3]));
  else return 2;
  return 0;
}
