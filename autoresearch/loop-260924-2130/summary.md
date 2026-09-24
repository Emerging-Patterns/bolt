# bolt lint performance: autoresearch summary

Metric: `bolt --gpu off` over bolt's own tree (95 files, 2.6 MB of Bend),
native binary, 4-core container. Lower is better.

    baseline  208.24 s
    final      20.38 s   (10.2x faster, 7 kept of 11 tried)

Every kept change leaves the findings identical (guard: every PROOF.bend
checks, findings equal the baseline's but for line numbers) and keeps every
law proven; no LAWS.bend was edited.

| # | change | metric | where the time was |
|---|--------|--------|--------------------|
| 1 | unused: trie of use targets as a sound fast path, linear scan only on a miss, lazily gated on reportable binders | 208.2 -> 64.7 | rules/PROOF.bend: 22k binders x 94k uses = 135 s |
| 2 | binder notes: a cursor over the lines in source order instead of `List.get` from line 0 per binder | 64.7 -> 45.5 | binder 35 s -> 15.6 s |
| 3 | binder item search: char-by-char `same` (proven = `String.eq`) with early exit | 45.5 -> 43.3 | binder 15.6 -> 12.6 s |
| 4 | coverage/unsafe closure: a proven twin of the walk with early-exit lookups, asking `seen` before every file | 43.3 -> 35.0 | coverage 10.2 -> 2.75 s |
| 5 | `Src.of` lexes once | 35.0 -> 31.3 | the tree re-lexed every file |
| 6 | lexer `step`: `Lazy.either`, so a token is flushed once, not on every char of it | 31.3 -> 26.6 | lex 2.44 -> 0.89 s on the big file |
| 7 | binder item list drops adjacent duplicates (`law x` + `def x`) | 26.6 -> 20.4 | binder 13 -> 7.5 s |

## Where the rest goes (final)

Over the whole tree: parsing and binding ~12 s (binder item scans ~7 s of it,
on bolt/rules/PROOF.bend), coverage ~2.9 s, per-file rules ~4 s, noqa 0.4 s,
reading 0.7 s.

## What blocks more

- The binder's item lookup. `syntax/LAWS.bend` `resolves` and `uses` state
  resolution over `Bind.Names{its, als}` with `its` a `List<String>`, so a
  use no binder holds must be looked up by a scan of the list (every
  alias-qualified name, `Unused.x`, `Bool.pick`, misses and scans all of
  it). An index (length buckets are provable from `String.cmp`'s structure
  alone) needs `Names` to carry it, which changes the law: a human's call.
- The coverage closure. `coverage_reach`, `reach_shut` and `reach_least`
  pin the walk's list, so the twin walk has to reproduce it step for step;
  an indexed `seen` would need the least/shut proofs redone for a new walk.

## Shapes worth a rule (filed as issues)

- An eager `Bool.pick` whose not-taken branch does real work in a per-step
  loop (the lexer flushed every char). `strict` catches `Bool.and/or` only.
- A per-item membership scan over a list that is the same for every item
  (`unused`: `used(uses, ..)` per binder; coverage: `has(read, ..)` per edge).
- `List.get` / `List.append` onto an accumulator reached through a
  non-recursive helper or a continuation: `index` (U007) and `concat` (U004)
  miss both (the binder's `line_text`, the reader's `slurp.cut`).
- A strict `+more = f(rest)` with `Bool.pick(eq, hit, more)`: a first-match
  search that never exits early (`deps_of`, `find`).

## Reproduce

    export BEND_LIB=<shake, ezjson, snap at the pinned revs>  CC=clang
    autoresearch/verify.sh     # prints seconds
    autoresearch/guard.sh      # pass / FAIL
    bend autoresearch/bench/rules.bend -o bench.bin; bench.bin --gpu off <file>    # per stage/rule
    bend autoresearch/bench/project.bend -o proj.bin; proj.bin --gpu off <files>   # project rules
