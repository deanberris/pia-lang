// Calls safetensors_run in tests/std/Inputs/safetensors_run.pia with two
// buffers of tensor records, of 8 and 3, and exits with its verdict. A
// buffer of records is one buffer per field (docs/codegen.md, "C ABI"):
// the eleven fields of Pia.Format.Safetensors.tensor, each given eight
// bytes per record, which is at least the width of every field.

#include <stdint.h>

int32_t safetensors_run(uint64_t *f0, uint64_t n, uint64_t *f1, uint64_t *f2,
                        uint64_t *f3, uint64_t *f4, uint64_t *f5, uint64_t *f6,
                        uint64_t *f7, uint64_t *f8, uint64_t *f9, uint64_t *f10,
                        uint64_t *g0, uint64_t m, uint64_t *g1, uint64_t *g2,
                        uint64_t *g3, uint64_t *g4, uint64_t *g5, uint64_t *g6,
                        uint64_t *g7, uint64_t *g8, uint64_t *g9,
                        uint64_t *g10);

enum { kFields = 11, kMany = 8, kFew = 3 };

static uint64_t many[kFields][kMany];
static uint64_t few[kFields][kFew];

int main(void) {
  return safetensors_run(many[0], kMany, many[1], many[2], many[3], many[4],
                         many[5], many[6], many[7], many[8], many[9],
                         many[10], few[0], kFew, few[1], few[2], few[3],
                         few[4], few[5], few[6], few[7], few[8], few[9],
                         few[10]);
}
