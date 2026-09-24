# lazy

Three branches that run one side only.

`Bool.pick`, `Bool.and` and `Bool.or` are defs, and a def's arguments are
evaluated before it is called, so both sides of a `Bool.pick` always run.
A search written with one is linear in the whole list however early it
hits, and a `Bool.or` of two walks pays for both.

    stop(A, c, a, rest)      a when c, else rest(Unit{})
    or_else(a, rest)          True when a, else rest(Unit{})
    and_then(a, rest)         rest(Unit{}) when a, else False

The last argument is a thunk, `Unit -> T`, which is a value: it is applied
only on the branch that needs it.

    # walks to the end whatever it finds
    Bool.pick(Json, String.eq(k, key), v, find(r, key))
    # stops at the first hit
    Lazy.stop(Json, String.eq(k, key), v, _u => find(r, key))

Measured native, 100 searches over 100,000 cells: `Bool.pick` costs 0.10 s
for a hit at the head and 0.11 s for one at the end; `stop` costs 0.00 s
and 0.13 s. bolt's `pick` and `strict` rules point here.
