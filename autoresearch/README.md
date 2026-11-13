# autoresearch/phases: timing tools for bolt's lint (never merged)

Build each from the repo root, inside `nix develop`, onto a tree that holds
the commit under test (merge main into this branch first):

    bend autoresearch/bench/stages.bend -o bin/stages.bin   # one file: each phase, each rule
    bend autoresearch/bench/plan.bend -o bin/plan.bin       # a whole tree: each planner stage

Run with the stderr lines timed:

    autoresearch/stage.sh bin/stages.bin <file.bend>
    cd <repo> && <bolt>/autoresearch/stage.sh <bolt>/bin/plan.bin ""

`corpus.sh <scratch dir>` runs two binaries (`NEW`, `OLD` in the environment)
over every repo of the lint corpus (`~/.local/share/bolt-corpus`) and writes
`corpus/cmp.tsv` (same or DIFF per repo) and `corpus/times.tsv`.

What they found, 2026-11-12: bolt #294, #296, #298, #302 and issue #301.
In stages.bend the same rule pass over a 5.7 MB file took 8.3 s first and
19 s on its fifth run in one process. A stand-alone program (2M cells, one
pure pass eight times) did not reproduce it (0.74 s every pass), so the cause
is not known: compare stages in the same order across builds and do not read
a later stage's time as that stage's cost.

`sweep.py <repo> <scratch> [workers] [per_def]` is the mutation sweep (issue
#310); `sweep-2026-11-12.json` its results on main at #308.

`sweep2.py` is the second sweep, with wider operators (negate a `Bool.pick`'s
condition, swap a `List.append`'s sides, compare a value with itself, shift a
comparison's boundary, empty a string literal, drop a `+ 1`);
`sweep2-2026-11-13.json` its results on main at #322 (225 of 922 survive).
`recheck.py <sweep.json> <repo> <scratch>` re-runs a sweep's survivors against
a branch and says which now fail a proof.
