// Runs json_dom_run.pia: Pia.Text.Json.Dom.parse over texts, into cells
// this test lends. A value cell's size is Pia's layout, not C's, so the
// buffers are generous and the counts of cells small. A buffer of members
// is passed as one buffer per field, as for every buffer of records: the
// keys' starts and stops, and the values, with one length.
#include <stdint.h>
#include <stdio.h>
#include <string.h>

int64_t run(const uint8_t *s, size_t n, void *cells, size_t ncells,
            uint64_t *key_start, size_t nmems, uint64_t *key_stop,
            void *member_values, uint8_t max_depth);

static _Alignas(16) unsigned char cells[64 * 512];
static uint64_t key_start[16], key_stop[16];
static _Alignas(16) unsigned char member_values[16 * 512];

static int check(const char *text, size_t ncells, uint8_t depth,
                 int64_t want) {
  int64_t got = run((const uint8_t *)text, strlen(text), cells, ncells,
                    key_start, 16, key_stop, member_values, depth);
  if (got != want) {
    printf("%s: %lld, expected %lld\n", text, (long long)got, (long long)want);
    return 1;
  }
  return 0;
}

int main(void) {
  int bad = 0;
  bad |= check("true", 16, 16, 1);
  bad |= check(" -12.5e3 ", 16, 16, 1);
  bad |= check("\"a\\u00e9\"", 16, 16, 1);
  // 1, [true, null] and {"a": "x", "b": []}: 8 values.
  bad |= check("[1, [true, null], {\"a\": \"x\", \"b\": []}]", 16, 16, 8);
  bad |= check("{}", 16, 16, 1);
  bad |= check("[]", 16, 16, 1);
  bad |= check("[1,]", 16, 16, -2);           // a value expected
  bad |= check("{\"a\" 1}", 16, 16, -2);      // no colon
  bad |= check("[[[1]]]", 16, 2, -3);         // three deep, two allowed
  bad |= check("[[[1]]]", 16, 3, 4);
  bad |= check("1 2", 16, 16, -4);            // trailing
  bad |= check("[1, 2, 3]", 2, 16, -5);       // three cells needed
  bad |= check("[1, @]", 16, 16, -1);         // not a token
  return bad;
}
