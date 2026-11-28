// Runs json_shape_variant_run.pia: @derive(json_dom) on a variant, its
// check and from_dom over parsed texts, and its to_dom read back. A
// buffer of members is passed as one buffer per field: the keys' starts
// and stops, and the values, with one length. A value cell's size is
// Pia's layout, so buffers are generous.
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

int64_t read_signal_dom(const uint8_t *s, size_t n, void *cells,
                        size_t ncells, uint64_t *key_start, size_t nmems,
                        uint64_t *key_stop, void *member_values);
int64_t round_trip_signal_dom(int64_t k, uint8_t *text, size_t ntext,
                              void *cells, size_t ncells, uint64_t *key_start,
                              size_t nmems, uint64_t *key_stop,
                              void *member_values);

static _Alignas(16) unsigned char cells[16 * 512];
static uint64_t key_start[16], key_stop[16];
static _Alignas(16) unsigned char member_values[16 * 512];
static uint8_t text[256];

// A signal's code: 0 off, 1 or 2 on, 10 + a level, a peak, or 2000 +
// a spot's code, x * 1000 + y * 10 + ok.
static int check_signal(const char *s, int64_t want) {
  int64_t got = read_signal_dom((const uint8_t *)s, strlen(s), cells, 16,
                                key_start, 16, key_stop, member_values);
  if (got == want)
    return 0;
  printf("read_signal_dom(%s): %lld, want %lld\n", s, (long long)got,
         (long long)want);
  return 1;
}

int main(void) {
  int bad = 0;
  // One constructor of each kind, told apart by its JSON.
  bad |= check_signal("null", 0);
  bad |= check_signal("false", 1);
  bad |= check_signal("true", 2);
  bad |= check_signal("7", 17);
  bad |= check_signal("512", 512);
  bad |= check_signal("{\"xx\": -5, \"y\": 6, \"ok\": true}", 2000 - 4939);
  bad |= check_signal("50", -2);           // in neither number's range
  bad |= check_signal("\"on\"", -2);       // a string is no signal
  bad |= check_signal("{\"xx\": 1}", -2);  // not a point
  bad |= check_signal("{", -1);            // not a document
  const int64_t want[5] = {0, 2, 17, 512, 2000 - 4939};
  for (int64_t k = 0; k < 5; ++k) {
    int64_t g = round_trip_signal_dom(k, text, sizeof text, cells, 16,
                                      key_start, 16, key_stop, member_values);
    if (g != want[k]) {
      printf("round_trip_signal_dom(%lld): %lld, want %lld\n", (long long)k,
             (long long)g, (long long)want[k]);
      bad = 1;
    }
  }
  return bad;
}
