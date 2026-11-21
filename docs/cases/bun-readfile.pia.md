# Bun's `readFile` on Windows

Zig is a safe language in some build modes and not in others. Its
[language reference][modes] lists four: Debug and ReleaseSafe have
"Safety checks enabled", and ReleaseFast and ReleaseSmall have "Safety
checks disabled". One of the checks is on `@intCast`, which "Converts an
integer to another integer while keeping the same numerical value". A
value that does not fit is, in the reference's words, "safety-protected
Undefined Behavior": a panic where safety is on, and nothing at all where
it is off.

[Bun](https://bun.sh), the JavaScript runtime, is written in Zig. Its
issue [#23849][issue] is titled "Incorrect integer type used in readFile
on Windows". Reading a file bigger than 2 GB in one call crashed Bun with
the panic "integer does not fit in destination type", in `preadv` in
`src/sys_uv.zig`. The safety check caught it. In a build mode without
the check, the same cast would have handed a garbage byte count to the
code that reads the buffer.

This page is a literate Pia file,
[`docs/cases/bun-readfile.pia.md`](https://github.com/deanberris/pia-lang/blob/main/docs/cases/bun-readfile.pia.md).
The `pia` blocks are the fixed program, which the test suite proves, and
the other code blocks are the broken versions, each checked to fail
exactly as shown.

## The bug

On Windows, Bun reads files through libuv. `uv_fs_read` returns a C
`int`, and as the [fix][pr]'s description explains, for a synchronous
call that `int` is `(int)req->result`, where `req->result` is the full
`ssize_t` byte count. Past `INT_MAX` bytes the conversion wraps, and the
count comes back negative. Bun then converted it to a `usize`:

```zig
const bytes_read: usize = @intCast(rc.int());
```

Two narrowings sit in that line's history. The first is C's, from
`ssize_t` to `int`, which no build mode checks. The second is Zig's,
from a negative `int` to an unsigned `usize`, which Bun's build did check,
so the program stopped instead of carrying on with a wrong count. The
[fix][pr], "windows: fix readFile panic on files >2GB", by Dylan Conway,
merged on 15 April 2026, stops using the truncated return value and reads
the untruncated one instead:

```zig
const bytes_read: usize = @intCast(req.result.int());
```

## The same code in Pia

Here is the libuv call, written as C wrote it: an `@overflow(wrap)`
function, so its narrowing wraps exactly as C's cast does. Its
postcondition is what Bun's code took for granted: a successful read,
with a count that is not negative, gives a return value that is not
negative either.

<!-- example: uv.pia -->
<!-- expect: fail -->
```ocaml
let uv_fs_read (req_result : isize) : i32 @overflow(wrap)
  ensures req_result >= 0 ==> result >= 0
= req_result

let bytes_read (req_result : isize) : usize
  requires req_result >= 0
=
  let rc : i32 = uv_fs_read req_result in
  rc
```

```console
$ piac --verify uv.pia
...
```

The verifier refutes the assumption with a count just past 2 GB, the size
of file in the bug report. Given the postcondition, `bytes_read`'s own
narrowing would prove. But the postcondition is false, so the program
does not compile, in any build mode.

Without the postcondition, the assumption is not written anywhere, and
the narrowing in `bytes_read` is the goal that fails:

<!-- example: uv_unstated.pia -->
<!-- expect: fail -->
```ocaml
let uv_fs_read (req_result : isize) : i32 @overflow(wrap) = req_result

let bytes_read (req_result : isize) : usize
  requires req_result >= 0
=
  let rc : i32 = uv_fs_read req_result in
  rc
```

```console
$ piac --verify uv_unstated.pia
...
```

This is Zig's `@intCast` check, done once, at compile time, for every
input. There is no build mode in Pia that turns it off
([ADR 0004](../adr/0004-strongest-guarantee-by-default.md)): a narrowing
either proves or the program does not compile.

## The fix, proved

The rest of this page is the fixed program. Like Bun's fix, it reads the
untruncated count. An error is a negative count, and a successful read
returns the count as a `usize`:

```pia
let read_result = type { failed : bool; bytes : usize }

let preadv (req_result : isize) : read_result
  ensures result.failed = (req_result < 0)
=
  if req_result < 0 then { failed = true; bytes = 0 }
  else { failed = false; bytes = req_result }
```

Every goal on this page is proved:

```console
$ piac --verify bun-readfile.pia.md
...
```

## What this says about safe build modes

Zig gives the programmer a choice, per build and even per block with
`@setRuntimeSafety`, between checking a cast and trusting it. Bun's check
turned a wrong count into a crash, which is the best a run-time check can
do. It still shipped, and it still crashed for users with large files. A
proof moves the same check to the compiler, where it runs for every
input before the program exists, and there is nothing to turn off.

## Sources

- The Zig 0.13.0 language reference: [Build Mode][modes],
  [`@intCast`][intcast] and [Cast Truncates Data][truncates].
- Bun issue [#23849][issue], "Incorrect integer type used in readFile on
  Windows".
- Bun PR [#29327][pr], "windows: fix readFile panic on files >2GB", by
  Dylan Conway, merged 15 April 2026: the explanation of the `int`
  return, the crash report and its panic message, and the
  [diff][diff].

[modes]: https://ziglang.org/documentation/0.13.0/#Build-Mode
[intcast]: https://ziglang.org/documentation/0.13.0/#intCast
[truncates]: https://ziglang.org/documentation/0.13.0/#Cast-Truncates-Data
[issue]: https://github.com/oven-sh/bun/issues/23849
[pr]: https://github.com/oven-sh/bun/pull/29327
[diff]: https://github.com/oven-sh/bun/pull/29327/files
