// D8 directions and the picture on the GPU (docs/placed.pia.md), and the
// sediment pull step with each wave on the GPU (docs/pull_gpu.pia.md),
// checked against the CPU (docs/streams.pia.md, docs/pull.pia.md) on a real
// SRTM tile, cell for cell (ADR 0068, section 6). Each GPU stage runs at
// least twice: the first run also opens the device and loads the kernel.
// The buffers are allocated on page boundaries, so the shim wraps them in
// place, with no copy.
//
//   srtm_gpu tile.hgt [threshold]

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "examples/streams/demo_io.h"
#include "examples/streams/pia_streams.h"

enum { HEIGHTS = 65536 };

int32_t directions_gpu(const uint16_t *fill, uint64_t nfill, uint64_t w,
                       uint64_t *down, uint64_t ndown);
int32_t render_gpu(const uint16_t *dem, uint64_t ndem, const uint16_t *fill,
                   uint64_t nfill, const uint32_t *acc, uint64_t nacc,
                   const uint64_t *basin, uint64_t nbasin, uint32_t threshold,
                   uint32_t *rgba, uint64_t nrgba);

int32_t pull_step_gpu(const uint16_t *fill, uint64_t nfill,
                      const uint64_t *down, uint64_t ndown, const uint32_t *acc,
                      uint64_t nacc, const uint64_t *order, uint64_t norder,
                      const uint64_t *pos, uint64_t npos, uint64_t w,
                      const uint32_t *bed0, uint64_t nbed0, uint32_t *bed,
                      uint64_t nbed, uint32_t *flux, uint64_t nflux,
                      uint64_t *seen, uint64_t nseen, uint64_t *gathered,
                      uint64_t ngathered, uint32_t *newbed, uint64_t nnewbed,
                      uint32_t *newout, uint64_t nnewout, uint64_t gone,
                      uint64_t *sent, uint64_t nsent);

void pia_gpu_run_stats(uint64_t *wrapped, uint64_t *copied,
                       uint64_t *copied_bytes);

// A buffer on a page boundary, which the Metal shim wraps without a copy.
static void *page_alloc(size_t bytes) {
  void *p = NULL;
  return posix_memalign(&p, (size_t)getpagesize(), bytes ? bytes : 1) ? NULL
                                                                     : p;
}

// How many of the tile's buffer sizes malloc puts on a page boundary.
static int malloc_aligned(uint64_t n, int *of) {
  const size_t sizes[] = {n * 2, n * 2, n * 4, n * 8, n * 8, n * 4};
  int k = 0;
  *of = (int)(sizeof sizes / sizeof sizes[0]);
  void *p[sizeof sizes / sizeof sizes[0]];
  for (int i = 0; i < *of; ++i) {
    p[i] = malloc(sizes[i]);
    k += ((uintptr_t)p[i] % (uintptr_t)getpagesize()) == 0;
  }
  for (int i = 0; i < *of; ++i) free(p[i]);
  return k;
}

static double ms(double a, double b) { return (b - a) * 1e3; }

static const char *const kErrors[] = {"ok", "Gpu_unavailable",
                                      "Gpu_out_of_memory", "Gpu_fault",
                                      "Gpu_timeout"};

static const char *error_name(int32_t r) {
  return r >= 0 && r <= 4 ? kErrors[r] : "unknown";
}

int main(int argc, char **argv) {
  char in_buf[4096];
  if (argc < 2 || argc > 3 || argv[1][0] == '-') {
    fprintf(stderr, "usage: srtm_gpu tile.hgt [threshold]\n");
    return 2;
  }
  size_t bytes;
  uint8_t *raw = read_file(resolve(argv[1], in_buf, sizeof in_buf), &bytes);
  if (!raw) return 1;
  uint64_t n = bytes / 2;
  int of;
  int k = malloc_aligned(n, &of);
  uint16_t *dem = page_alloc(n * sizeof *dem);
  uint64_t w = bytes % 2 ? 0 : load_hgt(raw, bytes, dem, n);
  free(raw);
  if (w == 0) {
    fprintf(stderr, "%s: %zu bytes is not an SRTM tile\n", argv[1], bytes);
    return 1;
  }
  printf("tile: %llux%llu cells\n", (unsigned long long)w,
         (unsigned long long)(n / w));
  printf("malloc: %d of %d buffers of the tile's sizes start on a page\n", k,
         of);
  uint32_t threshold = argc > 2 ? (uint32_t)atol(argv[2])
                                : (uint32_t)(n / 1000 > 8 ? n / 1000 : 8);

  uint16_t *fill = page_alloc(n * sizeof *fill);
  uint64_t *parent = malloc(n * 8), *rank = malloc(n * 8), *link = malloc(n * 8);
  uint64_t *head = malloc(HEIGHTS * 8);
  fill_sinks(dem, n, w, fill, n, parent, n, rank, n, link, n, head, HEIGHTS);
  free(parent), free(rank), free(link), free(head);

  int bad = 0;
  uint64_t *down = malloc(n * 8), *down_gpu = page_alloc(n * 8);
  double c0 = seconds();
  directions(fill, n, w, down, n);
  double c1 = seconds();
  double times[2];
  for (int run = 0; run < 2; ++run) {
    for (uint64_t i = 0; i < n; ++i) down_gpu[i] = ~0ull;
    double g0 = seconds();
    int32_t r = directions_gpu(fill, n, w, down_gpu, n);
    times[run] = ms(g0, seconds());
    if (r != 0) {
      printf("directions: the GPU run failed: %s\n", error_name(r));
      return 1;
    }
  }
  uint64_t differ = 0;
  for (uint64_t i = 0; i < n; ++i) differ += down[i] != down_gpu[i];
  printf("directions: CPU %.1f ms, GPU %.1f ms (first run %.1f ms); "
         "%llu cells differ\n",
         ms(c0, c1), times[1], times[0], (unsigned long long)differ);
  bad |= differ != 0;

  uint32_t *acc = page_alloc(n * 4);
  uint64_t *basin = page_alloc(n * 8);
  accumulate(fill, n, down, n, acc, n, basin, n);
  uint8_t *rgb = malloc(3 * n);
  uint32_t *rgba = page_alloc(n * 4);
  double p0 = seconds();
  render(dem, n, fill, n, acc, n, basin, n, threshold, rgb, 3 * n);
  double p1 = seconds();
  for (int run = 0; run < 2; ++run) {
    for (uint64_t i = 0; i < n; ++i) rgba[i] = 0xffffffffu;
    double g0 = seconds();
    int32_t r = render_gpu(dem, n, fill, n, acc, n, basin, n, threshold, rgba, n);
    times[run] = ms(g0, seconds());
    if (r != 0) {
      printf("render: the GPU run failed: %s\n", error_name(r));
      return 1;
    }
  }
  differ = 0;
  for (uint64_t i = 0; i < n; ++i) {
    uint32_t c = rgb[3 * i] | (uint32_t)rgb[3 * i + 1] << 8 |
                 (uint32_t)rgb[3 * i + 2] << 16;
    differ += c != rgba[i];
  }
  printf("render: CPU %.1f ms, GPU %.1f ms (first run %.1f ms); "
         "%llu cells differ\n",
         ms(p0, p1), times[1], times[0], (unsigned long long)differ);
  bad |= differ != 0;

  // Sediment in pull form, the same steps from the same bed on the CPU and
  // on the GPU, over the height order drainage gives, with one unit of rain
  // on every cell. A GPU step is one dispatch for each wave, one wave for
  // each height, with the commit on the CPU between them.
  const uint32_t seed = 100, steps = 4;
  uint32_t *rain = malloc(n * 4), *pend = malloc(n * 4);
  uint64_t *order = page_alloc(n * 8), *pos = page_alloc(n * 8);
  uint32_t *cnt = malloc(HEIGHTS * 4);
  uint64_t *first = malloc(HEIGHTS * 8), *next = malloc(HEIGHTS * 8),
           *last = malloc(HEIGHTS * 8);
  uint16_t *owner = malloc(n * 2);
  rain_uniform(1, rain, n);
  drainage(fill, n, down, n, acc, n, basin, n, rain, n, pend, n, order, n, pos,
           n, cnt, HEIGHTS, first, HEIGHTS, next, HEIGHTS, last, HEIGHTS, owner,
           n);
  free(rain), free(pend), free(cnt), free(first), free(next), free(last);
  free(owner);
  uint64_t waves = n > 0;
  for (uint64_t q = 1; q < n; ++q) waves += fill[order[q]] != fill[order[q - 1]];
  uint32_t *b0 = page_alloc(n * 4), *bc = page_alloc(n * 4),
           *fc = page_alloc(n * 4), *bg = page_alloc(n * 4),
           *fg = page_alloc(n * 4), *nb = page_alloc(n * 4),
           *no = page_alloc(n * 4);
  uint64_t *seen = page_alloc(n * 8), *gath = page_alloc(n * 8);
  uint64_t sent[1] = {0};
  for (uint64_t i = 0; i < n; ++i) bc[i] = bg[i] = seed;
  uint64_t gone_c = 0, gone_g = 0;
  double q0 = seconds();
  for (uint32_t s = 0; s < steps; ++s) {
    memcpy(b0, bc, n * 4);
    gone_c = pull_step(fill, n, down, n, acc, n, order, n, pos, n, w, b0, n, bc,
                       n, fc, n, seen, n, gath, n, nb, n, no, n, gone_c);
  }
  double q1 = seconds();
  double first_step = 0;
  for (uint32_t s = 0; s < steps; ++s) {
    memcpy(b0, bg, n * 4);
    double g0 = seconds();
    int32_t r = pull_step_gpu(fill, n, down, n, acc, n, order, n, pos, n, w, b0,
                              n, bg, n, fg, n, seen, n, gath, n, nb, n, no, n,
                              gone_g, sent, 1);
    if (s == 0) first_step = ms(g0, seconds());
    if (r != 0) {
      printf("pull: the GPU run failed: %s\n", error_name(r));
      return 1;
    }
    gone_g = sent[0];
  }
  double q2 = seconds();
  differ = 0;
  for (uint64_t i = 0; i < n; ++i) differ += bc[i] != bg[i] || fc[i] != fg[i];
  printf("pull: %u steps of %llu waves; CPU %.1f ms a step, GPU %.1f ms a "
         "step (first step %.1f ms); %llu out on both: %s; %llu cells "
         "differ\n",
         steps, (unsigned long long)waves, ms(q0, q1) / steps,
         (ms(q1, q2) - first_step) / (steps - 1), first_step,
         (unsigned long long)gone_g, gone_c == gone_g ? "yes" : "no",
         (unsigned long long)differ);
  bad |= differ != 0 || gone_c != gone_g;

  uint64_t wrapped, copied, copied_bytes;
  pia_gpu_run_stats(&wrapped, &copied, &copied_bytes);
  printf("buffers: %llu wrapped in place, %llu copied (%llu bytes)\n",
         (unsigned long long)wrapped, (unsigned long long)copied,
         (unsigned long long)copied_bytes);
  return bad;
}
