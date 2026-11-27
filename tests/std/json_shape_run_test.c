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
int64_t read_reading(const uint8_t *s, size_t n, void *cells, size_t ncells,
                     uint64_t *key_start, size_t nmems, uint64_t *key_stop,
                     void *member_values);
int64_t round_trip_reading(uint16_t id, bool has_temp, int8_t temp, int64_t ok,
                           uint8_t *text, size_t ntext, void *cells,
                           size_t ncells, uint64_t *key_start, size_t nmems,
                           uint64_t *key_stop, void *member_values);

int64_t read_sample(const uint8_t *s, size_t n, void *cells, size_t ncells,
                    uint64_t *key_start, size_t nmems, uint64_t *key_stop,
                    void *member_values);
int64_t round_trip_sample(uint8_t id, int8_t x0, int8_t x1, int8_t x2, bool f0,
                          bool f1, uint8_t *text, size_t ntext, void *cells,
                          size_t ncells, uint64_t *key_start, size_t nmems,
                          uint64_t *key_stop, void *member_values);

int64_t read_segment(const uint8_t *s, size_t n, void *cells, size_t ncells,
                     uint64_t *key_start, size_t nmems, uint64_t *key_stop,
                     void *member_values);
int64_t round_trip_segment(int32_t x, uint8_t y, uint8_t n, uint8_t *text,
                           size_t ntext, void *cells, size_t ncells,
                           uint64_t *key_start, size_t nmems,
                           uint64_t *key_stop, void *member_values);

int64_t read_route(const uint8_t *s, size_t n);
int64_t round_trip_route(int32_t x, bool has_last, uint8_t *text, size_t ntext);

static _Alignas(16) unsigned char cells[16 * 512];
static uint64_t key_start[16], key_stop[16];
static _Alignas(16) unsigned char member_values[16 * 512];
static uint8_t text[256];

static int check(const char *s, int64_t want) {
  int64_t got = read_point((const uint8_t *)s, strlen(s), cells, 16, key_start,
                           16, key_stop, member_values);
  if (got != want) {
    printf("%s: %lld, expected %lld\n", s, (long long)got, (long long)want);
    return 1;
  }
  return 0;
}

// A reading's code: id * 100000 + temp's * 10 + ok's, where temp's is
// 500 for None and temp + 128 for a value, and ok's is 0 for None, 1 for
// false and 2 for true.
static int check_reading(const char *s, int64_t want) {
  int64_t got = read_reading((const uint8_t *)s, strlen(s), cells, 16,
                             key_start, 16, key_stop, member_values);
  if (got != want) {
    printf("%s: %lld, expected %lld\n", s, (long long)got, (long long)want);
    return 1;
  }
  return 0;
}

static int check_round_trip_reading(uint16_t id, bool has_temp, int8_t temp,
                                    int64_t ok, int64_t want) {
  int64_t got =
      round_trip_reading(id, has_temp, temp, ok, text, sizeof text, cells, 16,
                         key_start, 16, key_stop, member_values);
  if (got != want) {
    printf("round_trip_reading: %lld, expected %lld\n", (long long)got,
           (long long)want);
    return 1;
  }
  return 0;
}

// A sample's code: id, then each x + 128 in three decimal digits, then
// the flags as two bits.
static int check_sample(const char *s, int64_t want) {
  int64_t got = read_sample((const uint8_t *)s, strlen(s), cells, 16,
                            key_start, 16, key_stop, member_values);
  if (got != want) {
    printf("%s: %lld, expected %lld\n", s, (long long)got, (long long)want);
    return 1;
  }
  return 0;
}

// A segment's code: its first point's code twice, its second's three
// times, and n; a point's code is x * 1000 + y * 10 + ok.
static int check_route(const char *s, int64_t want) {
  int64_t got = read_route((const uint8_t *)s, strlen(s));
  if (got == want)
    return 0;
  printf("read_route(%s): %lld, want %lld\n", s, (long long)got,
         (long long)want);
  return 1;
}

static int check_segment(const char *s, int64_t want) {
  int64_t got = read_segment((const uint8_t *)s, strlen(s), cells, 16,
                             key_start, 16, key_stop, member_values);
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
  bad |= check_reading("{\"id\": 7, \"temp\": -5, \"ok\": true}", 701232);
  bad |= check_reading("{\"id\": 7}", 705000); // both missing
  bad |= check_reading("{\"ok\": null, \"id\": 7, \"temp\": null}", 705000);
  bad |= check_reading("{\"temp\": 1}", -2);         // id missing
  bad |= check_reading("{\"id\": 7, \"x\": 1}", -2); // another member
  bad |= check_reading("{\"id\": 7, \"temp\": 1, \"temp\": 2}", -2);
  bad |= check_reading("{\"id\": 7, \"temp\": 200}", -2); // out of range
  bad |= check_reading("{\"id\": 7, \"ok\": 1}", -2);     // not a bool
  bad |= check_round_trip_reading(7, false, 0, 1, 705001);
  bad |= check_round_trip_reading(7, true, -128, 2, 700002);
  bad |= check_sample(
      "{\"id\": 9, \"xs\": [-128, 0, 127], \"flags\": [true, false]}",
      90001282552);
  bad |= check_sample("{\"id\": 9, \"xs\": [1, 2], \"flags\": [true, false]}",
                      -2); // too few
  bad |= check_sample(
      "{\"id\": 9, \"xs\": [1, 2, 3, 4], \"flags\": [true, false]}", -2);
  bad |= check_sample(
      "{\"id\": 9, \"xs\": [1, 2, 300], \"flags\": [true, false]}", -2);
  bad |= check_sample("{\"id\": 9, \"xs\": 1, \"flags\": [true, false]}", -2);
  bad |= check_sample("{\"id\": 9, \"xs\": [1, 2, 3], \"flags\": [1, 0]}",
                      -2); // not bools
  int64_t sample = round_trip_sample(5, -1, 0, 1, false, true, text, sizeof text,
                                     cells, 16, key_start, 16, key_stop,
                                     member_values);
  if (sample != 51271281291) {
    printf("round_trip_sample: %lld\n", (long long)sample);
    bad = 1;
  }
  bad |=
      check_segment("{\"a\": {\"xx\": 1, \"y\": 2, \"ok\": true}, "
                    "\"b\": {\"ok\": false, \"xx\": -3, \"y\": 4}, \"n\": 5}",
                    2 * 1021 + 3 * -2960 + 5);
  bad |= check_segment("{\"a\": {\"xx\": 1, \"y\": 2, \"ok\": true}, \"n\": 5}",
                       -2); // b missing
  bad |=
      check_segment("{\"a\": {\"xx\": 1, \"y\": 2, \"ok\": true}, "
                    "\"b\": {\"xx\": 1, \"y\": 256, \"ok\": true}, \"n\": 5}",
                    -2); // b's y out of range
  bad |= check_segment("{\"a\": 1, \"b\": 2, \"n\": 5}", -2);
  int64_t seg = round_trip_segment(-7, 9, 3, text, sizeof text, cells, 16,
                                   key_start, 16, key_stop, member_values);
  if (seg != 2 * (-7000 + 91) + 3 * 7090 + 3) {
    printf("round_trip_segment: %lld\n", (long long)seg);
    bad = 1;
  }
  // A route: an array of two points and an option of one, by
  // @derive(json) alone. Its code is its stops' codes, once and twice,
  // and its last point's three times.
  const char *P1 = "{\"xx\": 1, \"y\": 2, \"ok\": true}";
  const char *P2 = "{\"xx\": -3, \"y\": 4, \"ok\": false}";
  char buf[256];
  snprintf(
      buf, sizeof buf,
      "{\"stops\": [%s, %s], \"last\": {\"xx\": 5, \"y\": 6, \"ok\": true}}",
      P1, P2);
  bad |= check_route(buf, 1021 + 2 * -2960 + 3 * 5061);
  snprintf(buf, sizeof buf, "{\"stops\": [%s, %s], \"last\": null}", P1, P2);
  bad |= check_route(buf, 1021 + 2 * -2960);
  snprintf(buf, sizeof buf, "{\"stops\": [%s, %s]}", P1, P2);
  bad |= check_route(buf, 1021 + 2 * -2960);
  snprintf(buf, sizeof buf,
           "{\"stops\": [{\"xx\": 1, \"y\": 256, \"ok\": true}, %s]}", P2);
  bad |= check_route(buf, -3); // a stop's y out of range
  snprintf(buf, sizeof buf, "{\"stops\": [%s, %s], \"last\": 5}", P1, P2);
  bad |= check_route(buf, -4); // the last is not a point
  snprintf(buf, sizeof buf, "{\"stops\": [%s]}", P1);
  bad |= check_route(buf, -1); // too few stops
  int64_t r1 = round_trip_route(-7, true, text, sizeof text);
  if (r1 != -6989 + 2 * 7020 + 3 * 31) {
    printf("round_trip_route: %lld\n", (long long)r1);
    bad = 1;
  }
  int64_t r0 = round_trip_route(-7, false, text, sizeof text);
  if (r0 != -6989 + 2 * 7020) {
    printf("round_trip_route (no last): %lld\n", (long long)r0);
    bad = 1;
  }
  return bad;
}
