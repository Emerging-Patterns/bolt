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
The same pure work takes longer the more the process has allocated (one
rule pass over a 5.7 MB file: 8.3 s on a fresh heap, 19 s after four
passes), so compare stages in the same order across builds.
