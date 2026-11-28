// Runs json_shape_route_run.pia: a route, two points and an option of
// one, read from its text and from a parsed document, and written both
// ways and read back. A point's code is x * 1000 + y * 10 + ok.
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

int64_t read_route(const uint8_t *s, size_t n);
int64_t round_trip_route(int32_t x, bool has_last, uint8_t *text, size_t ntext);
int64_t read_route_dom(const uint8_t *s, size_t n, void *cells, size_t ncells,
                       uint64_t *key_start, size_t nmems, uint64_t *key_stop,
                       void *member_values);
int64_t round_trip_route_dom(int32_t x, bool has_last, uint8_t *text,
                             size_t ntext, void *cells, size_t ncells,
                             uint64_t *key_start, size_t nmems,
                             uint64_t *key_stop, void *member_values);

static _Alignas(16) unsigned char cells[16 * 512];
static uint64_t key_start[16], key_stop[16];
static _Alignas(16) unsigned char member_values[16 * 512];
static uint8_t text[256];

static int check_route(const char *s, int64_t want) {
  int64_t got = read_route((const uint8_t *)s, strlen(s));
  if (got == want)
    return 0;
  printf("read_route(%s): %lld, want %lld\n", s, (long long)got,
         (long long)want);
  return 1;
}

int main(void) {
  int bad = 0;
  // A route: two points and an option of one, by
  // @derive(json) alone. Its code is its points' codes, once and twice,
  // and its last point's three times.
  const char *P1 = "{\"xx\": 1, \"y\": 2, \"ok\": true}";
  const char *P2 = "{\"xx\": -3, \"y\": 4, \"ok\": false}";
  char buf[256];
  snprintf(
      buf, sizeof buf,
      "{\"a\": %s, \"b\": %s, \"last\": {\"xx\": 5, \"y\": 6, \"ok\": true}}",
      P1, P2);
  bad |= check_route(buf, 1021 + 2 * -2960 + 3 * 5061);
  snprintf(buf, sizeof buf, "{\"a\": %s, \"b\": %s, \"last\": null}", P1, P2);
  bad |= check_route(buf, 1021 + 2 * -2960);
  snprintf(buf, sizeof buf, "{\"a\": %s, \"b\": %s}", P1, P2);
  bad |= check_route(buf, 1021 + 2 * -2960);
  snprintf(buf, sizeof buf,
           "{\"a\": {\"xx\": 1, \"y\": 256, \"ok\": true}, \"b\": %s}", P2);
  bad |= check_route(buf, -3); // a's y out of range
  snprintf(buf, sizeof buf, "{\"a\": %s, \"b\": %s, \"last\": 5}", P1, P2);
  bad |= check_route(buf, -4); // the last is not a point
  snprintf(buf, sizeof buf, "{\"a\": %s}", P1);
  bad |= check_route(buf, -1); // b missing
  int64_t r1 = round_trip_route(-7, true, text, sizeof text);
  if (r1 != -6989 + 2 * 7020 + 3 * 31) {
    printf("round_trip_route: %lld\n", (long long)r1);
    bad = 1;
  }
  int64_t d1 = round_trip_route_dom(-7, true, text, sizeof text, cells, 16,
                                    key_start, 16, key_stop, member_values);
  if (d1 != -6989 + 2 * 7020 + 3 * 31) {
    printf("round_trip_route_dom: %lld\n", (long long)d1);
    bad = 1;
  }
  int64_t d0 = round_trip_route_dom(-7, false, text, sizeof text, cells, 16,
                                    key_start, 16, key_stop, member_values);
  if (d0 != -6989 + 2 * 7020) {
    printf("round_trip_route_dom (no last): %lld\n", (long long)d0);
    bad = 1;
  }
  int64_t r0 = round_trip_route(-7, false, text, sizeof text);
  if (r0 != -6989 + 2 * 7020) {
    printf("round_trip_route (no last): %lld\n", (long long)r0);
    bad = 1;
  }
  return bad;
}
