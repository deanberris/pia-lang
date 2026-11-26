// Calls tokenizer_load_checks and tokenizer_case in
// tests/std/Inputs/tokenizer_run.pia with the bytes of tok512.bin, the
// stories260K tokenizer, and a buffer of 600 piece records, then each text
// of tokenizer_cases.h with the ids llama2.c's run.c gives it, and exits 0
// when every check passes. A buffer of records is one buffer per field
// (docs/codegen.md, "C ABI"): the three fields of
// Pia.Llm.Tokenizer.piece, each given eight bytes per record, which is at
// least the width of every field.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "tokenizer_cases.h"

int32_t tokenizer_load_checks(const uint8_t *s, uint64_t s_len, uint64_t *f0,
                              uint64_t n, uint64_t *f1, uint64_t *f2,
                              uint8_t *dst, uint64_t dst_len);
int32_t tokenizer_case(const uint8_t *s, uint64_t s_len, uint64_t *f0,
                       uint64_t n, uint64_t *f1, uint64_t *f2,
                       const uint8_t *text, uint64_t text_len,
                       const uint32_t *want, uint64_t want_len,
                       uint32_t *toks, uint64_t toks_len, uint64_t *at,
                       uint64_t at_len, uint8_t *dst, uint64_t dst_len);

enum { kPieces = 600, kRoom = 1024 };

static uint64_t pieces[3][kPieces];
static uint32_t toks[kRoom];
static uint64_t at[kRoom];
static uint8_t dst[kRoom];

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: %s tok512.bin\n", argv[0]);
    return 2;
  }
  FILE *f = fopen(argv[1], "rb");
  if (!f) {
    perror(argv[1]);
    return 2;
  }
  static uint8_t s[1 << 16];
  size_t s_len = fread(s, 1, sizeof s, f);
  fclose(f);

  int32_t r = tokenizer_load_checks(s, s_len, pieces[0], kPieces, pieces[1],
                                    pieces[2], dst, kRoom);
  if (r != 0) {
    fprintf(stderr, "load check %d failed\n", r);
    return 1;
  }
  int failed = 0;
  for (size_t k = 0; k < sizeof kCases / sizeof kCases[0]; ++k) {
    const struct tokenizer_case *c = &kCases[k];
    r = tokenizer_case(s, s_len, pieces[0], kPieces, pieces[1], pieces[2],
                       c->text, c->text_len, c->ids, c->ids_len, toks, kRoom,
                       at, kRoom, dst, kRoom);
    if (r != 0) {
      fprintf(stderr, "case %zu (%s): check %d failed\n", k, c->what, r);
      failed = 1;
    }
  }
  return failed;
}
