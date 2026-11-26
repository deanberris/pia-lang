// The .metallib that metal_library built and embedded starts with Metal's
// library magic, MTLB.
#include <stdio.h>
#include <string.h>

extern const unsigned char pia_test_add_metallib[];
extern const unsigned long pia_test_add_metallib_len;

int main(void) {
  if (pia_test_add_metallib_len < 4 ||
      memcmp(pia_test_add_metallib, "MTLB", 4)) {
    fprintf(stderr, "the embedded library is not a .metallib\n");
    return 1;
  }
  printf("embedded .metallib, %lu bytes\n", pia_test_add_metallib_len);
  return 0;
}
