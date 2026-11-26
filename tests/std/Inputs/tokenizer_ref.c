// The reference for tests/std/Inputs/tokenizer_gen.py: llama2.c's run.c
// tokenizer (MIT, https://github.com/karpathy/llama2.c), included whole
// with its main renamed. Reads one hex-encoded text per line on stdin and
// prints the ids run.c's encode gives it, with <s> and without </s>.
#define main llama2c_main
#include "run.c"
#undef main

static int hexval(int c) {
  return c <= '9' ? c - '0' : (c | 0x20) - 'a' + 10;
}

int main(int argc, char **argv) {
  if (argc != 3) {
    fprintf(stderr, "usage: %s tokenizer.bin vocab_size < texts.hex\n", argv[0]);
    return 2;
  }
  Tokenizer t;
  build_tokenizer(&t, argv[1], atoi(argv[2]));
  static char line[1 << 16];
  static char text[1 << 15];
  static int toks[1 << 15];
  while (fgets(line, sizeof line, stdin)) {
    size_t n = 0;
    for (char *p = line; p[0] && p[0] != '\n' && p[1]; p += 2)
      text[n++] = (char)(hexval(p[0]) * 16 + hexval(p[1]));
    text[n] = 0;
    int count = 0;
    encode(&t, text, 1, 0, toks, &count);
    for (int i = 0; i < count; i++) printf("%s%d", i ? " " : "", toks[i]);
    printf("\n");
  }
  free_tokenizer(&t);
  return 0;
}
