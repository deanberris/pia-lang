// The C entry point of the Pia port: kostya's base64 test-nolib.c main,
// with encode and decode in base64.pia. It checks the same fixtures, then
// encodes 131,072 'a's and decodes the result `tries` times each (8192 by
// default), and prints the sums test-nolib.c prints, without its timings.

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

uint64_t b64_encode(uint8_t *dst, int64_t dst_len, const uint8_t *src,
                    int64_t src_len);
int64_t b64_decode(uint8_t *dst, int64_t dst_len, const uint8_t *src,
                   int64_t src_len);

static size_t encode_size(size_t size) { return (size_t)(size * 4 / 3.0) + 6; }

static size_t decode_size(size_t size) { return (size_t)(size * 3 / 4.0) + 6; }

static size_t encode(uint8_t *dst, size_t dst_len, const char *src,
                     size_t src_len) {
  return b64_encode(dst, (int64_t)dst_len, (const uint8_t *)src,
                    (int64_t)src_len);
}

static size_t decode(uint8_t *dst, size_t dst_len, const uint8_t *src,
                     size_t src_len) {
  int64_t n = b64_decode(dst, (int64_t)dst_len, src, (int64_t)src_len);
  if (n < 0) {
    fputs("error when decoding", stderr);
    exit(EXIT_FAILURE);
  }
  return (size_t)n;
}

int main(int argc, char *argv[]) {
  const char *fixtures[][2] = {{"hello", "aGVsbG8="}, {"world", "d29ybGQ="}};
  for (size_t i = 0; i < 2; ++i) {
    const char *src = fixtures[i][0], *dst = fixtures[i][1];
    size_t src_len = strlen(src), dst_len = strlen(dst);
    uint8_t encoded[32], decoded[32];
    size_t n = encode(encoded, encode_size(src_len), src, src_len);
    if (n != dst_len || memcmp(encoded, dst, n))
      abort();
    n = decode(decoded, decode_size(dst_len), (const uint8_t *)dst, dst_len);
    if (n != src_len || memcmp(decoded, src, n))
      abort();
  }

  int tries = argc > 1 ? atoi(argv[1]) : 8192;
  enum { STR_SIZE = 131072 };
  static char str[STR_SIZE];
  static uint8_t str2[STR_SIZE * 4 / 3 + 6], str3[STR_SIZE + 6],
      tmp[STR_SIZE * 4 / 3 + 6];
  memset(str, 'a', STR_SIZE);
  size_t str2_size = encode(str2, sizeof str2, str, STR_SIZE);
  decode(str3, sizeof str3, str2, str2_size);

  int s_encoded = 0;
  for (int i = 0; i < tries; i++)
    s_encoded += encode(tmp, sizeof tmp, str, STR_SIZE);
  int s_decoded = 0;
  for (int i = 0; i < tries; i++)
    s_decoded += decode(tmp, sizeof tmp, str2, str2_size);

  printf("encode %.4s... to %.4s...: %d\n", str, (const char *)str2, s_encoded);
  printf("decode %.4s... to %.4s...: %d\n", (const char *)str2,
         (const char *)str3, s_decoded);
  return 0;
}
