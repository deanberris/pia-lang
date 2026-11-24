nl-dump: SMT-LIB dumps of Pia's hardest proof goals, for benchmarking other solvers.

piac: built from origin/main 436306d1c0dd1e2c4d00e2ebfea2625e10737f8e
  (bazel build //tools/piac:piac, macOS arm64, iMac). piac has no --version flag.
Z3: 4.15.2 (BCR module "z3", MODULE.bazel) with the repo's patch
  third_party/z3/qfbv_memory_independent.patch.
Solver settings: piac defaults (--solver-timeout 600000 ms, --solver-rlimit 1200000000), --jobs=4.

Files per case:
  <case>.smt.txt         stderr of: piac --dump-smt --solver-cost --goal-times --jobs=4 [args] <file>
                         (each query begins "; <file>:<line>:<col>: <goal>"; bazelq's queue
                         messages, lines starting "bazelq:", are mixed in at the top and end)
  <case>.smt.stdout.txt  stdout of that run: the goal report (with --dump-smt the report goes to stdout)
  <case>.report.txt      stdout+stderr of: piac --verify --solver-cost --goal-times --jobs=4 [args] <file>
Interfaces for imports were made with piac --emit=interface from main's lib/ (Fn, Core/Order,
Core/Algo/Permutation, Text/Json/Spec, Image/Bits, Image/Gif/Spec) and, for lzw, from the
branch's wip/lzw-whole-stream/Ref.pia; every run passes --iface-path=<that dir>.

Cases (file: where it came from):
  int         lib/Pia/Core/Int.pia                      main 436306d
  remove      lib/Pia/Core/Algo/Remove.pia              main 436306d
  sort        lib/Pia/Core/Algo/Sort.pia                main 436306d
  edges       examples/edges/edges.pia                  main 436306d
  json_write  lib/Pia/Text/Json/Write.pia               main 436306d
  streams     docs/streams.pia.md (literate)            main 436306d
  rand        scratch cells.pia (Pia.Core.Rand / minstd_rand prototype, C++ std work):
              /private/tmp/claude-501/-Users-deanmichaelberris-pia-lang/c84cf46d-bf6a-4244-b838-7d50c9630f4b/scratchpad/rand/cells.pia
              run as a copy without its last line, `minstd_next 1` (a REPL expression cell,
              which piac rejects: "'ExprItem' items are not supported yet").
              Hard goal: minstd_next's call to `undo` (u64 / and % vs int), "state never 0".
  lzw         wip/lzw-whole-stream/Lzw.pia, branch claude/lzw-whole-stream at fccc2df
              (identical to 097e253 apart from README notes), with
              --verify-only=decode_ref --verify-only=sym_is_x --verify-only=emit_code
              --verify-only=emit_kwk --verify-only=link_new (the README's command).
              Hard goals: Lzw.pia:289, :296 (emit_kwk), :313 (link_new), :361, :369 (loop invariants).
  to_chars    missing: see to_chars.missing.txt

Wall-clock times ("wall_incl_queue" includes waiting in the iMac's bazelq build queue;
"piac_run" is piac's own run time; int was measured before piac_run was recorded):
  int smt rc=0 wall_incl_queue=1516s
  int report rc=0 wall_incl_queue=278s
  remove smt rc=0 wall_incl_queue=1174s piac_run=5s
  remove report rc=0 wall_incl_queue=3558s piac_run=5s
From sort on, each case's two runs share one bazelq slot ("both runs" is the total including queue):
  (the first rand attempt failed at once on the REPL expression cell, so rand was run again)
  rand smt rc=1 piac_run=0s
  rand report rc=1 piac_run=0s
  rand both runs, wall_incl_queue=1653s
  lzw smt rc=124 piac_run=1200s
  lzw smt KILLED after 20 min

lzw: the --dump-smt run was killed at the 20-minute limit. Its dump is partial but holds 224 queries
(all written in the first minute; the rest was solving), and its stdout report is empty as a result.
