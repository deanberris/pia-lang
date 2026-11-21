# CrowdStrike Channel File 291

At 04:09 UTC on Friday 19 July 2024, CrowdStrike pushed a routine content
update to its Falcon sensor, the endpoint security agent that runs inside
the Windows kernel. Windows hosts that received it crashed, and crashed
again on reboot. CrowdStrike reverted the update at 05:27 UTC, but the
machines that had it stayed down until someone fixed each one, often by
hand. Microsoft estimated that the update "affected 8.5 million Windows
devices". Airlines, hospitals, banks and broadcasters went offline.

CrowdStrike's [root cause analysis][rca] traces it to a count: a template
that defined 21 input fields, fed by code that supplied 20.

This page is a literate Pia file,
[`docs/cases/crowdstrike.pia.md`](https://github.com/deanberris/pia-lang/blob/main/docs/cases/crowdstrike.pia.md).
The `pia` blocks are the fixed program, which the test suite proves, and
the other code blocks are the broken versions, each checked to fail
exactly as shown.

## The bug

The sensor's detection logic is partly data. *Rapid Response Content*,
delivered in channel files, holds *Template Instances*: lists of matching
criteria, one per input field, that the sensor's *Content Interpreter*
checks against live system activity. Each instance belongs to a *Template
Type* compiled into the sensor, which says how many fields there are.

In February 2024, sensor 7.11 added a Template Type for Windows
interprocess communication (IPC), whose instances arrive in Channel File
291. From the RCA:

> The new IPC Template Type defined 21 input parameter fields, but the
> integration code that invoked the Content Interpreter with Channel File
> 291's Template Instances supplied only 20 input values to match against.

For five months nothing went wrong, because every instance used a
wildcard for the 21st field, and a wildcard matches without reading its
input. The tests did too: "a regex wildcard matching criterion in the
21st field for all Template Instances". The Content Validator, which
checks new content before it ships, "based its assessment on the
expectation that the IPC Template Type would be provided with 21 inputs."
Then, on 19 July, one new instance "introduced a non-wildcard matching
criterion for the 21st input parameter", and:

> The Content Interpreter expected only 20 values. Therefore, the attempt
> to access the 21st value produced an out-of-bounds memory read beyond
> the end of the input data array and resulted in a system crash.

In a kernel driver, an out-of-bounds read is a blue screen.

## The same code in Pia

Here is the interpreter's core, reduced to integers. An instance is two
slices of the same length, one entry per field: `wild.[i]` says whether
field `i` is a wildcard, and `want.[i]` is the value it must equal
otherwise. `inputs` holds the values the sensor supplies. The loop checks
every field, and reads an input only for a field that is not a wildcard,
just as the real interpreter did:

<!-- example: interpreter.pia -->
<!-- expect: fail -->
```ocaml
let matches (wild : [bool]) (want : [u32]) (inputs : [u32]) : bool
  requires len want = len wild
=
  let ok : mutable bool = true in
  for i in 0..len wild do
    if wild.[i] then () else if inputs.[i] <> want.[i] then ok <- false else ()
  done;
  ok
```

`piac` will not compile it:

```console
$ piac --verify interpreter.pia
...
```

The counterexample has fewer inputs than fields. This is the point testing
could not reach: the read happens only when the criterion is not a
wildcard, and every test used a wildcard there. The verifier does not
sample criteria; it proves the read is safe for all of them, or shows one
where it is not.

## The count belongs in the contract

The RCA's first finding is that "the number of fields in the IPC Template
Type was not validated at sensor compile time". In Pia, the place to say
how many inputs the interpreter needs is its precondition. Now the
interpreter proves, and the obligation moves to every caller. Here is the
integration code for the IPC template, with the template's 21 fields and
the sensor's 20 inputs written into the types:

<!-- example: integration.pia -->
<!-- expect: fail -->
```ocaml
let matches (wild : [bool]) (want : [u32]) (inputs : [u32]) : bool
  requires len want = len wild && len inputs = len wild
=
  let ok : mutable bool = true in
  for i in 0..len wild do
    if wild.[i] then () else if inputs.[i] <> want.[i] then ok <- false else ()
  done;
  ok

let check_ipc (wild : [bool; 21]) (want : [u32; 21]) (inputs : [u32; 20]) : bool =
  matches wild want inputs
```

```console
$ piac --verify integration.pia
...
```

That is the bug, as a compile error in the sensor's own build, before any
content was ever written for it. No channel file, wildcard or not, could
then have reached the read.

## The fix, proved

The rest of this page is the fixed program. The interpreter states its
requirement, and its postcondition says what a match means: every field
that is not a wildcard equals its input.

```pia
let matches (wild : [bool]) (want : [u32]) (inputs : [u32]) : bool
  requires len want = len wild && len inputs = len wild
  ensures result ==> forall (k in 0..len wild). wild.[k] || inputs.[k] = want.[k]
=
  let ok : mutable bool = true in
  for i in 0..len wild
    invariant ok ==> forall (k in 0..i). wild.[k] || inputs.[k] = want.[k]
  do
    if wild.[i] then () else if inputs.[i] <> want.[i] then ok <- false else ()
  done;
  ok
```

The integration code supplies all 21 inputs, which is CrowdStrike's own
fix: "The sensor code defining the IPC Template Type was updated to
provide the correct number of inputs (21)."

```pia
let check_ipc (wild : [bool; 21]) (want : [u32; 21]) (inputs : [u32; 21]) : bool =
  matches wild want inputs
```

Every goal on this page is proved:

```console
$ piac --verify crowdstrike.pia.md
...
```

CrowdStrike's other fix was a runtime bounds check in the interpreter,
added on 25 July. In Pia that check is unnecessary, so the compiled code
has none: the proof that every read is in bounds is the check, and it ran
once, at compile time.

## What Pia needs for the rest

The real interpreter matches strings against regular expressions, and the
template's field count comes from a definitions file rather than the type
of an array. Pia's verifier handles neither yet. The count can still be
checked at compile time once modules export interfaces with contracts
([M8](https://github.com/deanberris/pia-lang/issues/9)): the Template Type
would be an exported symbol whose field count is a constant, and the
sensor would be proved against it.

## Sources

- CrowdStrike, ["External Technical Root Cause Analysis — Channel File
  291"][rca], 6 August 2024. The quotations, the findings and the fixes
  above are from it.
- CrowdStrike, ["Preliminary Post Incident Review"][pir], 24 July 2024,
  for the update and revert times: "On Friday, July 19, 2024 at 04:09
  UTC" and "reverted on Friday, July 19, 2024 at 05:27 UTC."
- Microsoft, ["Helping our customers through the CrowdStrike
  outage"][msft], 20 July 2024: "We currently estimate that CrowdStrike's
  update affected 8.5 million Windows devices, or less than one percent of
  all Windows machines."

[rca]: https://www.crowdstrike.com/wp-content/uploads/2024/08/Channel-File-291-Incident-Root-Cause-Analysis-08.06.2024.pdf
[pir]: https://www.crowdstrike.com/blog/falcon-content-update-preliminary-post-incident-report/
[msft]: https://blogs.microsoft.com/blog/2024/07/20/helping-our-customers-through-the-crowdstrike-outage/
