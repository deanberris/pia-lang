// Runs json_shape_run.pia: @derive(json_dom)'s check and from_dom over
// parsed texts, and its to_dom read back. A buffer of members is passed as
// one buffer per field: the keys' starts and stops, and the values, with
// one length. A value cell's size is Pia's layout, so buffers are generous.
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

int64_t read_point(const uint8_t *s, size_t n, void *cells, size_t ncells,
                   uint64_t *key_start, size_t nmems, uint64_t *key_stop,
                   void *member_values);
int64_t round_trip(int32_t x, uint8_t y, bool ok, uint8_t *text, size_t ntext,
                   void *cells, size_t ncells, uint64_t *key_start,
                   size_t nmems, uint64_t *key_stop, void *member_values);

static _Alignas(16) unsigned char cells[16 * 512];
static uint64_t key_start[16], key_stop[16];
static _Alignas(16) unsigned char member_values[16 * 512];
static uint8_t text[128];

static int check(const char *s, int64_t want) {
  int64_t got = read_point((const uint8_t *)s, strlen(s), cells, 16, key_start,
                           16, key_stop, member_values);
  if (got != want) {
    printf("%s: %lld, expected %lld\n", s, (long long)got, (long long)want);
    return 1;
  }
  return 0;
}

int main(void) {
  int bad = 0;
  bad |= check("{\"xx\": -7, \"y\": 200, \"ok\": true}", -7000 + 2001);
  bad |= check("{\"ok\": false, \"y\": 0, \"xx\": 12}", 12000);
  bad |= check("{\"xx\": 1, \"y\": 256, \"ok\": true}", -2); // y out of range
  bad |= check("{\"xx\": 1, \"y\": 2}", -2);                 // ok missing
  bad |= check("{\"xx\": 1, \"y\": 2, \"ok\": true, \"z\": 0}", -2);
  bad |= check("{\"xx\": 1, \"xx\": 2, \"ok\": true}", -2);  // twice
  bad |= check("{\"xx\": 1.5, \"y\": 2, \"ok\": true}", -2); // a fraction
  bad |= check("{\"xx\": 1, \"y\": 2, \"ok\": 1}", -2);      // not a bool
  bad |= check("[1, 2]", -2);
  bad |= check("{\"xx\": 1,", -1);
  int64_t got = round_trip(-123, 45, true, text, sizeof text, cells, 16,
                           key_start, 16, key_stop, member_values);
  if (got != -123000 + 451) {
    printf("round_trip: %lld\n", (long long)got);
    bad = 1;
  }
  return bad;
}
