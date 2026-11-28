// Runs json_shape_tagged_run.pia: @derive(json_dom) on a tagged variant,
// its check and from_dom over parsed texts, and its to_dom read back. A
// buffer of members is passed as one buffer per field: the keys' starts
// and stops, and the values, with one length. A value cell's size is
// Pia's layout, so buffers are generous.
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

int64_t read_event_dom(const uint8_t *s, size_t n, void *cells, size_t ncells,
                       uint64_t *key_start, size_t nmems, uint64_t *key_stop,
                       void *member_values);
int64_t round_trip_event_dom(int64_t k, uint8_t *text, size_t ntext,
                             void *cells, size_t ncells, uint64_t *key_start,
                             size_t nmems, uint64_t *key_stop,
                             void *member_values);

static _Alignas(16) unsigned char cells[16 * 512];
static uint64_t key_start[16], key_stop[16];
static _Alignas(16) unsigned char member_values[16 * 512];
static uint8_t text[256];

// An event's code: 0 to quit, 100000 + x * 100 + y for a click, and for a
// key 1000 + its code * 10, plus 1 if it repeats and 2 if it says not.
static int check_event(const char *s, int64_t want) {
  int64_t got = read_event_dom((const uint8_t *)s, strlen(s), cells, 16,
                               key_start, 16, key_stop, member_values);
  if (got == want)
    return 0;
  printf("read_event_dom(%s): %lld, want %lld\n", s, (long long)got,
         (long long)want);
  return 1;
}

int main(void) {
  int bad = 0;
  bad |= check_event("{\"kind\": \"Quit\"}", 0);
  bad |= check_event("{\"kind\": \"click\", \"x\": 3, \"y\": 4}", 100304);
  // The tag may come anywhere among the members.
  bad |= check_event("{\"y\": 4, \"x\": 3, \"kind\": \"click\"}", 100304);
  bad |= check_event("{\"kind\": \"Key\", \"code\": 9}", 1090);
  bad |=
      check_event("{\"code\": 9, \"repeat\": true, \"kind\": \"Key\"}", 1091);
  bad |=
      check_event("{\"kind\": \"Key\", \"code\": 9, \"repeat\": false}", 1092);
  bad |=
      check_event("{\"kind\": \"Key\", \"code\": 9, \"repeat\": null}", 1090);
  bad |=
      check_event("{\"kind\": \"Click\", \"x\": 3, \"y\": 4}", -2); // renamed
  bad |= check_event("{\"x\": 3, \"y\": 4}", -2);                   // no tag
  bad |= check_event("{\"kind\": 1, \"code\": 9}", -2); // not a string
  bad |= check_event("{\"kind\": \"Key\", \"kind\": \"Key\", \"code\": 9}",
                     -2);                                      // two tags
  bad |= check_event("{\"kind\": \"Quit\", \"code\": 9}", -2); // not Quit's
  bad |= check_event("{\"kind\": \"Key\", \"code\": 9, \"x\": 3}", -2);
  bad |= check_event("{\"kind\": \"click\", \"x\": 3}", -2); // y missing
  bad |= check_event("{", -1);
  const int64_t want[4] = {0, 100304, 1090, 1091};
  for (int64_t k = 0; k < 4; ++k) {
    int64_t g = round_trip_event_dom(k, text, sizeof text, cells, 16, key_start,
                                     16, key_stop, member_values);
    if (g != want[k]) {
      printf("round_trip_event_dom(%lld): %lld, want %lld\n", (long long)k,
             (long long)g, (long long)want[k]);
      bad = 1;
    }
  }
  return bad;
}
