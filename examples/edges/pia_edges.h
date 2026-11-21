// The C entry points of edges.pia, compiled by piac --emit=obj
// (docs/codegen.md, "C ABI"): a slice is a pointer and a length.

#ifndef PIA_EXAMPLES_EDGES_H
#define PIA_EXAMPLES_EDGES_H

#include <stdint.h>

void gray(const uint8_t *rgb, uint64_t nrgb, uint8_t *dst, uint64_t ndst);
void blur(const uint8_t *src, uint64_t nsrc, uint64_t w, uint8_t *dst,
          uint64_t ndst);
void sobel(const uint8_t *src, uint64_t nsrc, uint64_t w, uint8_t *dst,
           uint64_t ndst);
void edges(const uint8_t *rgb, uint64_t nrgb, uint64_t w, uint8_t *luma_buf,
           uint64_t nluma, uint8_t *smooth, uint64_t nsmooth, uint8_t *dst,
           uint64_t ndst);

#endif
