// The C entry points of docs/streams.pia.md, compiled by piac --emit=obj
// (docs/codegen.md, "C ABI"): a slice is a pointer and a length, and
// `usize` is uint64_t.

#ifndef PIA_EXAMPLES_STREAMS_H
#define PIA_EXAMPLES_STREAMS_H

#include <stdint.h>

uint32_t fill_sinks(const uint16_t *dem, uint64_t ndem, uint64_t w,
                    uint32_t limit, uint16_t *fill, uint64_t nfill);
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
                   uint32_t limit, uint32_t threshold, uint16_t *fill,
                   uint64_t nfill, uint64_t *down, uint64_t ndown,
                   uint32_t *acc, uint64_t nacc, uint64_t *basin,
                   uint64_t nbasin, uint8_t *rgb, uint64_t nrgb);

uint64_t sediment(const uint16_t *fill, uint64_t nfill, const uint64_t *down,
                  uint64_t ndown, const uint32_t *acc, uint64_t nacc,
                  const uint64_t *order, uint64_t norder, uint32_t n,
                  uint32_t *bed, uint64_t nbed, uint32_t *load, uint64_t nload,
                  uint32_t *inflow, uint64_t ninflow, uint32_t *flux,
                  uint64_t nflux);
uint64_t render_load(const uint16_t *dem, uint64_t ndem, const uint16_t *fill,
                     uint64_t nfill, const uint32_t *acc, uint64_t nacc,
                     const uint64_t *basin, uint64_t nbasin,
                     const uint32_t *flux, uint64_t nflux, uint32_t threshold,
                     uint8_t *rgb, uint64_t nrgb);

#endif
