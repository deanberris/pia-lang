// The C entry points of docs/streams.pia.md, docs/sediment.pia.md and
// docs/basins.pia.md, compiled
// by piac --emit=obj (docs/codegen.md, "C ABI"): a slice is a pointer and a
// length, and `usize` is uint64_t.

#ifndef PIA_EXAMPLES_STREAMS_H
#define PIA_EXAMPLES_STREAMS_H

#include <stdbool.h>
#include <stdint.h>

uint64_t load_hgt(const uint8_t *raw, uint64_t nraw, uint16_t *dem,
                  uint64_t ndem);
uint64_t fill_sinks(const uint16_t *dem, uint64_t ndem, uint64_t w,
                    uint16_t *fill, uint64_t nfill, uint64_t *parent,
                    uint64_t nparent, uint64_t *rank, uint64_t nrank,
                    uint64_t *next, uint64_t nnext, uint64_t *head,
                    uint64_t nhead);
void directions(const uint16_t *fill, uint64_t nfill, uint64_t w,
                uint64_t *down, uint64_t ndown);
void accumulate(const uint16_t *fill, uint64_t nfill, const uint64_t *down,
                uint64_t ndown, uint32_t *acc, uint64_t nacc, uint64_t *basin,
                uint64_t nbasin);
uint64_t render(const uint16_t *dem, uint64_t ndem, const uint16_t *fill,
                uint64_t nfill, const uint32_t *acc, uint64_t nacc,
                const uint64_t *basin, uint64_t nbasin, uint32_t threshold,
                uint8_t *rgb, uint64_t nrgb);
uint64_t delineate(const uint16_t *dem, uint64_t ndem, uint64_t w,
                   uint32_t threshold, uint16_t *fill, uint64_t nfill,
                   uint64_t *parent, uint64_t nparent, uint64_t *rank,
                   uint64_t nrank, uint64_t *next, uint64_t nnext,
                   uint64_t *head, uint64_t nhead, uint64_t *down, uint64_t ndown,
                   uint32_t *acc, uint64_t nacc, uint64_t *basin,
                   uint64_t nbasin, uint8_t *rgb, uint64_t nrgb);

// docs/sediment.pia.md.
uint64_t sediment(const uint16_t *fill, uint64_t nfill, const uint64_t *down,
                  uint64_t ndown, const uint32_t *acc, uint64_t nacc,
                  uint32_t n, uint32_t *bed, uint64_t nbed, uint32_t *load,
                  uint64_t nload, uint32_t *inflow, uint64_t ninflow,
                  uint32_t *flux, uint64_t nflux, uint64_t *order,
                  uint64_t norder, uint64_t *pos, uint64_t npos, uint32_t *cnt,
                  uint64_t ncnt, uint64_t *first, uint64_t nfirst,
                  uint64_t *next, uint64_t nnext, uint64_t *last,
                  uint64_t nlast, uint16_t *owner, uint64_t nowner);
void surface(const uint16_t *rock, uint64_t nrock, const uint32_t *bed,
             uint64_t nbed, uint16_t *height, uint64_t nheight);
void rain_uniform(uint8_t r, uint32_t *rain, uint64_t nrain);
void rain_band(uint64_t w, uint64_t lo, uint64_t hi, uint8_t inside,
               uint8_t outside, uint32_t *rain, uint64_t nrain);
void rain_season(bool wet, uint8_t r, uint32_t *rain, uint64_t nrain);
void drainage(const uint16_t *fill, uint64_t nfill, const uint64_t *down,
              uint64_t ndown, uint32_t *acc, uint64_t nacc, uint64_t *basin,
              uint64_t nbasin, uint32_t *rain, uint64_t nrain, uint32_t *pend,
              uint64_t npend, uint64_t *order, uint64_t norder, uint64_t *pos,
              uint64_t npos, uint32_t *cnt, uint64_t ncnt, uint64_t *first,
              uint64_t nfirst, uint64_t *next, uint64_t nnext, uint64_t *last,
              uint64_t nlast, uint16_t *owner, uint64_t nowner);
uint64_t evolve(const uint16_t *fill, uint64_t nfill, const uint64_t *down,
                uint64_t ndown, const uint32_t *rain, uint64_t nrain,
                uint32_t k, uint32_t *bed, uint64_t nbed, uint32_t *load,
                uint64_t nload, uint32_t *inflow, uint64_t ninflow,
                uint32_t *flux, uint64_t nflux, uint32_t *flow, uint64_t nflow,
                uint32_t *pend, uint64_t npend, uint64_t *order,
                uint64_t norder, uint64_t *pos, uint64_t npos, uint32_t *cnt,
                uint64_t ncnt, uint64_t *first, uint64_t nfirst, uint64_t *next,
                uint64_t nnext, uint64_t *last, uint64_t nlast, uint16_t *owner,
                uint64_t nowner);
uint64_t render_load(const uint16_t *dem, uint64_t ndem, const uint16_t *fill,
                     uint64_t nfill, const uint32_t *acc, uint64_t nacc,
                     const uint64_t *basin, uint64_t nbasin,
                     const uint32_t *flux, uint64_t nflux, uint32_t threshold,
                     uint8_t *rgb, uint64_t nrgb);

// docs/basins.pia.md.
uint64_t sediment_basins(
    const uint16_t *fill, uint64_t nfill, const uint64_t *down, uint64_t ndown,
    const uint32_t *acc, uint64_t nacc, const uint64_t *label, uint64_t nlabel,
    const uint64_t *order, uint64_t norder, uint32_t steps, uint32_t *bed,
    uint64_t nbed, uint32_t *load, uint64_t nload, uint32_t *inflow,
    uint64_t ninflow, uint32_t *flux, uint64_t nflux, uint32_t *gone_by,
    uint64_t ngone_by, uint64_t *border, uint64_t nborder, uint64_t *keys,
    uint64_t nkeys, uint64_t *place2, uint64_t nplace2, uint64_t *pos2,
    uint64_t npos2, uint32_t *cnt, uint64_t ncnt, uint64_t *first,
    uint64_t nfirst, uint64_t *next, uint64_t nnext, uint64_t *last,
    uint64_t nlast, uint64_t *gowner, uint64_t ngowner);
// docs/pull.pia.md.
uint64_t pull_step(const uint16_t *fill, uint64_t nfill, const uint64_t *down,
                   uint64_t ndown, const uint32_t *acc, uint64_t nacc,
                   const uint64_t *order, uint64_t norder, const uint64_t *pos,
                   uint64_t npos, uint64_t w, const uint32_t *bed0,
                   uint64_t nbed0, uint32_t *bed, uint64_t nbed, uint32_t *flux,
                   uint64_t nflux, uint64_t *seen, uint64_t nseen,
                   uint64_t *gathered, uint64_t ngathered, uint32_t *newbed,
                   uint64_t nnewbed, uint32_t *newout, uint64_t nnewout,
                   uint64_t gone);
// examples/streams/gif.pia.
uint64_t gif_bound(uint16_t w, uint16_t h, uint16_t nf);
uint64_t gif_animation(uint16_t w, uint16_t h, const uint8_t *pal,
                       uint64_t npal, const uint8_t *frames, uint64_t nframes,
                       uint16_t nf, uint16_t delay, uint16_t loops,
                       uint8_t *dst, uint64_t ndst, uint8_t *rect,
                       uint64_t nrect, uint8_t *lz, uint64_t nlz, uint8_t *hash,
                       uint64_t nhash);
void palette(uint8_t *pal, uint64_t npal);
void render_load_index(const uint16_t *dem, uint64_t ndem, const uint16_t *fill,
                       uint64_t nfill, const uint32_t *acc, uint64_t nacc,
                       const uint64_t *basin, uint64_t nbasin,
                       const uint32_t *flux, uint64_t nflux, uint32_t threshold,
                       uint8_t *idx, uint64_t nidx);

#endif
