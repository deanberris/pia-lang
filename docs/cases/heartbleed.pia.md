# Heartbleed

In April 2014, OpenSSL disclosed a bug that let anyone who could open a TLS
connection read up to 64 KB of a server's memory per request, over and over:
private keys, session cookies, passwords, whatever happened to sit next to
the request in the heap. It was [CVE-2014-0160][advisory], and it became
known as Heartbleed. The cause was one missing comparison.

This page recreates the bug in Pia, shows `piac` refusing to compile it,
and then proves the fix. It is a literate Pia file,
[`docs/cases/heartbleed.pia.md`](https://github.com/deanberris/pia-lang/blob/main/docs/cases/heartbleed.pia.md):
the `pia` blocks are the fixed program, which the test suite proves, and the
other code blocks are the broken versions, each checked to fail exactly as
shown.

## The bug

TLS has a *heartbeat* extension ([RFC 6520][rfc]): one side sends a
request carrying some bytes, and the other side echoes the same bytes back,
to show the connection is alive. A heartbeat message is a type byte, a
16-bit `payload_length`, the payload, and at least 16 bytes of random
padding:

```text
+------+----------------+----------------------+------------------+
| type | payload_length | payload              | padding (>= 16)  |
| 1 B  | 2 B, big-endian| payload_length bytes |                  |
+------+----------------+----------------------+------------------+
```

The sender writes `payload_length` itself, so the receiver must check it
against the size of the record that actually arrived. OpenSSL 1.0.1 to
1.0.1f did not. Here is the start of `tls1_process_heartbeat` in
`ssl/t1_lib.c`, as it was before the fix ([source][before]):

```c
unsigned char *p = &s->s3->rrec.data[0], *pl;
unsigned short hbtype;
unsigned int payload;
unsigned int padding = 16; /* Use minimum padding */

/* Read type and payload length first */
hbtype = *p++;
n2s(p, payload);
pl = p;
```

and the response it built:

```c
buffer = OPENSSL_malloc(1 + 2 + payload + padding);
bp = buffer;

/* Enter response type, length and copy payload */
*bp++ = TLS1_HB_RESPONSE;
s2n(payload, bp);
memcpy(bp, pl, payload);
```

`n2s` reads the two length bytes. `memcpy` then copies `payload` bytes
starting at the payload, whatever the record's real length was. A request
that says "65535 bytes" but carries one byte gets back that byte and the
65534 bytes of heap after it. Nothing in C connects `pl` to the length of
the buffer it points into, so no compiler could object.

## The same code in Pia

A Pia slice carries its length, and every index and every subslice is a
goal the compiler must prove in bounds. Here is the heartbeat handler
written the way OpenSSL wrote it. `req` is the received record and `resp`
the response buffer, which the caller makes big enough for any payload.
`copy` copies one slice into another of the same length:

<!-- example: heartbleed.pia -->
<!-- expect: fail -->
```ocaml
let copy (dst : out mutable [u8]) (src : [u8]) : unit
  requires len src = len dst
  ensures forall (k in 0..len dst). dst.[k] = src.[k]
=
  for i in 0..len dst
    invariant forall (k in 0..i). dst.[k] = src.[k]
  do dst.[i] <- src.[i] done

let heartbeat (req : [u8]) (resp : out mutable [u8]) : usize
  requires len resp >= 3 + 65535
=
  let payload : usize = ((req.[1] << 8) | req.[2]) in
  resp.[0] <- 2;
  resp.[1] <- req.[1];
  resp.[2] <- req.[2];
  copy (resp.[3 .. 3 + payload]) (req.[3 .. 3 + payload]);
  3 + payload
```

`piac` will not compile it:

```console
$ piac --verify heartbleed.pia
...
heartbleed.pia:12:27: failed: the index is within bounds
  counterexample: len req = 0, len resp = 98304, index = 1, length = 0
...
heartbleed.pia:12:43: failed: the index is within bounds
  counterexample: len req = 2, len resp = 98304, index = 2, length = 2
...
heartbleed.pia:16:35: failed: the slice is within bounds
  counterexample: len req = 4, len resp = 131039, start = 3, end = 5, length = 4
...
18 proved, 3 failed, 0 skipped
```

The third failure is Heartbleed. The counterexample is an attack: a
4-byte record, one byte of payload, whose length field says 2, so the
slice `req.[3 .. 5]` would run past the end of `req`. Make the length
field say 65535 and it is the real exploit. The first two failures are a
second bug the C code shares: a record shorter than three bytes has no
length field to read, and `n2s` reads past it too.

## Half a fix

The obvious patch checks the length field against the record:

<!-- example: half_fixed.pia -->
<!-- expect: fail -->
```ocaml
let copy (dst : out mutable [u8]) (src : [u8]) : unit
  requires len src = len dst
  ensures forall (k in 0..len dst). dst.[k] = src.[k]
=
  for i in 0..len dst
    invariant forall (k in 0..i). dst.[k] = src.[k]
  do dst.[i] <- src.[i] done

let heartbeat (req : [u8]) (resp : out mutable [u8]) : usize
  requires len resp >= 3 + 65535
=
  let payload : usize = ((req.[1] << 8) | req.[2]) in
  if 3 + payload + 16 > len req then 0
  else (
    resp.[0] <- 2;
    resp.[1] <- req.[1];
    resp.[2] <- req.[2];
    copy (resp.[3 .. 3 + payload]) (req.[3 .. 3 + payload]);
    3 + payload)
```

The copy is proved now, but reading the length still is not:

```console
$ piac --verify half_fixed.pia
...
half_fixed.pia:12:27: failed: the index is within bounds
  counterexample: len req = 0, len resp = 98304, index = 1, length = 0
...
half_fixed.pia:12:43: failed: the index is within bounds
  counterexample: len req = 2, len resp = 98304, index = 2, length = 2
...
half_fixed.pia:18:37: proved: the slice is within bounds [smt]
...
21 proved, 2 failed, 0 skipped
```

OpenSSL's real fix ([commit 96db902][fix], by Adam Langley and Bodo
Möller) has both checks, the first one before the length is read:

```c
/* Read type and payload length first */
if (1 + 2 + 16 > s->s3->rrec.length)
	return 0; /* silently discard */
hbtype = *p++;
n2s(p, payload);
if (1 + 2 + payload + 16 > s->s3->rrec.length)
	return 0; /* silently discard per RFC 6520 sec. 4 */
pl = p;
```

In C, nothing told the authors the first check was needed; they had to see
it. In Pia, leaving it out is a compile error with a counterexample.

## The fix, proved

The rest of this page is the fixed program: the handler, with both of
OpenSSL's checks, and the request type checked as `tls1_process_heartbeat`
does. It returns the length of the response it wrote, before padding, or 0
when RFC 6520 says to discard the message: "If the payload_length of a received HeartbeatMessage is too
large, the received HeartbeatMessage MUST be discarded silently." The
postcondition is the property Heartbleed broke, stated and proved: a
response is never longer than the request it answers, and every payload
byte in it came from that request. The copy is written out as a loop, so
its invariant carries that second fact straight to the postcondition.

```pia
let heartbeat (req : [u8]) (resp : out mutable [u8]) : usize
  requires len resp >= 3 + 65535
  ensures result = 0 || result + 16 <= len req
  ensures forall (k in 3..result). resp.[k] = req.[k]
=
  if 3 + 16 > len req then 0
  else (
    let payload : usize = ((req.[1] << 8) | req.[2]) in
    if 3 + payload + 16 > len req then 0
    else if req.[0] <> 1 then 0
    else (
      resp.[0] <- 2;
      resp.[1] <- req.[1];
      resp.[2] <- req.[2];
      for i in 3..3 + payload
        invariant forall (k in 3..i). resp.[k] = req.[k]
      do resp.[i] <- req.[i] done;
      3 + payload))
```

Every goal on this page is proved:

```console
$ piac --verify heartbleed.pia.md
...
```

Because the bounds are proved, the compiled code has no bounds checks in
it: the safety costs nothing at run time. And the proof is in the
interface. A caller of `heartbeat` knows from its postcondition, without
reading its body, that it cannot leak memory beyond the request.

## What Pia needs for the rest

The real handler allocates its response buffer, writes 16 random bytes of
padding and hands the message to the record layer. Pia has no allocator or
I/O yet, so the caller passes `resp` and adds the padding. With the memory
module ([ADR 0026](../adr/0026-memory-manager.md)), the allocation would be
one more call whose failure the caller must handle.

## Sources

- OpenSSL Security Advisory, 7 April 2014, "TLS heartbeat read overrun
  (CVE-2014-0160)": [advisory]. It credits Neel Mehta of Google Security
  with the discovery, and says "A missing bounds check in the handling of
  the TLS heartbeat extension can be used to reveal up to 64k of memory to
  a connected client or server." Affected: 1.0.1 to 1.0.1f and
  1.0.2-beta1; fixed in 1.0.1g.
- The fix: OpenSSL commit
  [96db9023b881d7cd9f379b0c154650d6c108e9a3][fix], "Add heartbeat
  extension bounds check."
- The code before the fix: [`ssl/t1_lib.c` at its parent commit][before].
- [RFC 6520, section 4][rfc]: "The padding_length MUST be at least 16."

[advisory]: https://openssl-library.org/news/secadv/20140407.txt
[fix]: https://github.com/openssl/openssl/commit/96db9023b881d7cd9f379b0c154650d6c108e9a3
[before]: https://github.com/openssl/openssl/blob/0d7717fc9c83dafab8153cbd5e2180e6e04cc802/ssl/t1_lib.c#L2584
[rfc]: https://www.rfc-editor.org/rfc/rfc6520#section-4
