#include <stdint.h>
#include <stdio.h>

extern const unsigned char pia_embed_c_magic[];
extern const uint64_t pia_embed_c_magic_len;
extern int32_t check_magic(void);

int main(void) {
  if (pia_embed_c_magic_len != 8) {
    fprintf(stderr, "expected len 8, got %llu\n",
            (unsigned long long)pia_embed_c_magic_len);
    return 1;
  }
  if (((uintptr_t)pia_embed_c_magic % 16) != 0) {
    fprintf(stderr, "expected 16-byte alignment, got %p\n",
            (const void *)pia_embed_c_magic);
    return 1;
  }
  const unsigned char expected[8] = {'M', 'T', 'L', 'B', 1, 2, 3, 4};
  for (uint64_t i = 0; i < 8; ++i) {
    if (pia_embed_c_magic[i] != expected[i]) {
      fprintf(stderr, "byte %llu: expected 0x%02x, got 0x%02x\n",
              (unsigned long long)i, expected[i], pia_embed_c_magic[i]);
      return 1;
    }
  }
  if (check_magic() != 0) {
    fprintf(stderr, "Pia check_magic() failed\n");
    return 1;
  }
  return 0;
}
