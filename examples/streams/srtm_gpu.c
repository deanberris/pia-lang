// D8 directions and the picture on the GPU (docs/placed.pia.md), checked
// against the CPU stages of docs/streams.pia.md on a real SRTM tile, cell
// for cell (ADR 0068, section 6). Each GPU stage runs twice: the first run
// also opens the device and loads the kernel.
//
//   srtm_gpu tile.hgt [threshold]

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "examples/streams/demo_io.h"
#include "examples/streams/pia_streams.h"

enum { HEIGHTS = 65536 };

int32_t directions_gpu(const uint16_t *fill, uint64_t nfill, uint64_t w,
                       uint64_t *down, uint64_t ndown);
int32_t render_gpu(const uint16_t *dem, uint64_t ndem, const uint16_t *fill,
                   uint64_t nfill, const uint32_t *acc, uint64_t nacc,
                   const uint64_t *basin, uint64_t nbasin, uint32_t threshold,
                   uint32_t *rgba, uint64_t nrgba);

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
  uint16_t *dem = malloc(n * sizeof *dem);
  uint64_t w = bytes % 2 ? 0 : load_hgt(raw, bytes, dem, n);
  free(raw);
  if (w == 0) {
    fprintf(stderr, "%s: %zu bytes is not an SRTM tile\n", argv[1], bytes);
    return 1;
  }
  printf("tile: %llux%llu cells\n", (unsigned long long)w,
         (unsigned long long)(n / w));
  uint32_t threshold = argc > 2 ? (uint32_t)atol(argv[2])
                                : (uint32_t)(n / 1000 > 8 ? n / 1000 : 8);

  uint16_t *fill = malloc(n * sizeof *fill);
  uint64_t *parent = malloc(n * 8), *rank = malloc(n * 8), *link = malloc(n * 8);
  uint64_t *head = malloc(HEIGHTS * 8);
  fill_sinks(dem, n, w, fill, n, parent, n, rank, n, link, n, head, HEIGHTS);
  free(parent), free(rank), free(link), free(head);

  int bad = 0;
  uint64_t *down = malloc(n * 8), *down_gpu = malloc(n * 8);
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

  uint32_t *acc = malloc(n * 4);
  uint64_t *basin = malloc(n * 8);
  accumulate(fill, n, down, n, acc, n, basin, n);
  uint8_t *rgb = malloc(3 * n);
  uint32_t *rgba = malloc(n * 4);
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
  return bad;
}
