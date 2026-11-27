// The C control: main.c's driver with test-nolib.c's encode and decode in C,
// so that it differs from the Pia port only in who compiled the codec. It
// checks the same fixtures, then encodes 131,072 'a's and decodes the result
// `tries` times each (8192 by default), and prints the sums test-nolib.c
// prints, without its timings.

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// test-nolib.c's encode and decode, unchanged, called through the same
// entry points as the Pia port's. They are noinline because the Pia
// functions are in another object: test-nolib.c's own main lets clang see
// that the encoded output is never read and drop most of the encode loop.
static const char chars[] =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
static char decode_table[256];

static void init_decode_table(void) {
  uint8_t ch = 0;
  do {
    char code = -1;
    if (ch >= 'A' && ch <= 'Z') {
      code = ch - 0x41;
    }
    if (ch >= 'a' && ch <= 'z') {
      code = ch - 0x47;
    }
    if (ch >= '0' && ch <= '9') {
      code = ch + 0x04;
    }
    if (ch == '+' || ch == '-') {
      code = 0x3E;
    }
    if (ch == '/' || ch == '_') {
      code = 0x3F;
    }
    decode_table[ch] = code;
  } while (ch++ < 0xFF);
}

#define next_char(x)                                                           \
  char x = decode_table[(unsigned char)*str++];                                \
  if (x < 0)                                                                   \
    return false;

static int decode_c(size_t size, const char *str, size_t *out_size,
                    char *output) {
  char *out = output;
  while (size > 0 && (str[size - 1] == '\n' || str[size - 1] == '\r' ||
                      str[size - 1] == '=')) {
    size--;
  }
  const char *ends = str + size - 4;
  while (true) {
    if (str > ends) {
      break;
    }
    while (*str == '\n' || *str == '\r') {
      str++;
    }

    if (str > ends) {
      break;
    }
    next_char(a);
    next_char(b);
    next_char(c);
    next_char(d);

    *out++ = (char)(a << 2 | b >> 4);
    *out++ = (char)(b << 4 | c >> 2);
    *out++ = (char)(c << 6 | d >> 0);
  }

  uint8_t mod = (ends - str + 4) % 4;
  if (mod == 2) {
    next_char(a);
    next_char(b);
    *out++ = (char)(a << 2 | b >> 4);
  } else if (mod == 3) {
    next_char(a);
    next_char(b);
    next_char(c);
    *out++ = (char)(a << 2 | b >> 4);
    *out++ = (char)(b << 4 | c >> 2);
  }

  *out = '\0';
  *out_size = out - output;
  return true;
}

static inline uint32_t to_uint32_t(const char *str) {
  return ((uint32_t)(unsigned char)str[0] << 24) |
         ((uint32_t)(unsigned char)str[1] << 16) |
         ((uint32_t)(unsigned char)str[2] << 8);
}

static void encode_c(size_t size, const char *str, size_t *out_size,
                     char *output) {
  char *out = output;
  const char *ends = str + (size - size % 3);
  uint64_t n;
  while (str != ends) {
    uint32_t n = to_uint32_t(str);
    *out++ = chars[(n >> 26) & 63];
    *out++ = chars[(n >> 20) & 63];
    *out++ = chars[(n >> 14) & 63];
    *out++ = chars[(n >> 8) & 63];
    str += 3;
  }
  int pd = size % 3;
  if (pd == 1) {
    n = (uint64_t)(unsigned char)*str << 16;
    *out++ = chars[(n >> 18) & 63];
    *out++ = chars[(n >> 12) & 63];
    *out++ = '=';
    *out++ = '=';
  } else if (pd == 2) {
    n = (uint64_t)(unsigned char)*str++ << 16;
    n |= (uint64_t)(unsigned char)*str << 8;
    *out++ = chars[(n >> 18) & 63];
    *out++ = chars[(n >> 12) & 63];
    *out++ = chars[(n >> 6) & 63];
    *out++ = '=';
  }
  *out = '\0';
  *out_size = out - output;
}

__attribute__((noinline)) uint64_t b64_encode(uint8_t *dst, int64_t dst_len,
                                              const uint8_t *src,
                                              int64_t src_len) {
  size_t n;
  (void)dst_len;
  encode_c((size_t)src_len, (const char *)src, &n, (char *)dst);
  return n;
}

__attribute__((noinline)) int64_t b64_decode(uint8_t *dst, int64_t dst_len,
                                             const uint8_t *src,
                                             int64_t src_len) {
  size_t n;
  (void)dst_len;
  if (!decode_c((size_t)src_len, (const char *)src, &n, (char *)dst))
    return -1;
  return (int64_t)n;
}

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
  init_decode_table();
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
