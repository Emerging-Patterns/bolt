# autoresearch: bolt lint performance

    Goal:       make `bolt` (the lint) faster over a real tree, bolt's own
    Scope:      bolt/**/*.bend, syntax/*.bend (implementation; LAWS.bend untouched)
    Metric:     seconds for `bolt --gpu off` over this repo's tree, native binary
    Direction:  lower_is_better
    Verify:     autoresearch/verify.sh   (build from HEAD, time the lint)
    Guard:      autoresearch/guard.sh    (every PROOF.bend checks; findings == baseline)
    Iterations: 25
    Profiler:   autoresearch/bench/rules.bend -- per-stage/per-rule timing of one file

Tracking lives only on this branch (autoresearch/bolt-lint-perf). Kept code
changes are carried to main through claude/bolt-lint-performance-3jytgy.

Machine: 4 cores, bend 2.0.27, clang 18.
