# syntax/word: the name under a (line, col), both 0-based. A name is letters,
# digits, `_` and `.` (dots are just characters in a Bend name, and a module
# alias rides in front: `Frame.decode`). A position right after a name counts
# as on it, as editors put the cursor there.
import Base
import ../lazy/lazy.bend as Lazy

# i: the column of the next char; start: where the current run began; run: the
# current name, reversed; hit: the name found
type W is Data:
  W{i: U32, start: U32, run: List<&2, Char>, hit: Maybe<&2, String>}

# a char a name may hold: letters, digits, `_` and `.`
def is_name(+cc: Char) -> Bool:
  Bool.or(Bool.or(Char.is_alpha(cc), Char.is_digit(cc)), Bool.or(Char.is_eq(cc, '_'), Char.is_eq(cc, '.')))

# the run's chars (reversed) as a string
def text(run: List<&2, Char>) -> String:
  String.from_list(List.reverse(&2, Char, run))

# the run holds the column: keep it; otherwise the hit so far
def close.yes(ok: Bool, run: List<&2, Char>, hit: Maybe<&2, String>) -> Maybe<&2, String>:
  match ok:
    case True{}:
      Some{text(run)}
    case False{}:
      hit

# an empty run leaves the hit; otherwise the run if start <= col <= i
def close.run(run: List<&2, Char>, +start: U32, +ii: U32, +col: U32, hit: Maybe<&2, String>) -> Maybe<&2, String>:
  match run:
    case Nil{}:
      hit
    case h <> t:
      close.yes(Bool.and(U32.is_le(start, col), U32.is_le(col, ii)), h <> t, hit)

# a run that ends at column i holds col when start <= col <= i, unless one already did
def close(+ii: U32, +start: U32, run: List<&2, Char>, hit: Maybe<&2, String>, +col: U32) -> Maybe<&2, String>:
  match hit:
    case Some{s}:
      Some{s}
    case None{}:
      close.run(run, start, ii, col, None{})

# a name char joins the run; any other char ends it
def step.on(name: Bool, cc: Char, +ii: U32, +start: U32, run: List<&2, Char>, hit: Maybe<&2, String>, +col: U32) -> W:
  match name:
    case True{}:
      W{(ii + 1 : U32), start, cc <> run, hit}
    case False{}:
      W{(ii + 1 : U32), (ii + 1 : U32), [], close(ii, start, run, hit, col)}

# one char: it extends the run of name chars, or ends it (a run holding the
# column is the answer)
def step(+cc: Char, st: W, +col: U32) -> W:
  W{i, start, run, hit} = st
  step.on(is_name(cc), cc, i, start, run, hit, col)

# the run that held the column, else ""
def finish(st: W, col: U32) -> String:
  W{i, start, run, hit} = st
  Maybe.default(&2, String, close(i, start, run, hit, col), "")

# lines still to skip after this char; a newline counts as one
def at.skip.n(nl: Bool, nn: U32) -> U32:
  match nl:
    case True{}:
      (nn - 1 : U32)
    case False{}:
      nn

# the next char starts the wanted line when this one was its preceding newline
def at.skip.done(nl: Bool, nn: U32) -> Bool:
  match nl:
    case True{}:
      U32.is_eq(nn, 1)
    case False{}:
      False{}

# the source with `n` lines skipped. `done` means this string is the line
def at.skip(ss: String, +nn: U32, done: Bool) -> String:
  match ss done:
    case SNil{} _:
      SNil{}
    case SCon{h, t} True{}:
      SCon{h, t}
    case SCon{+h, t} False{}:
      at.skip(t, at.skip.n(Char.is_eq(h, '\n'), nn), at.skip.done(Char.is_eq(h, '\n'), nn))

# a newline ends the line; any other char is part of it
def at.advance(nl: Bool, hh: Char, st: W, +col: U32) -> W:
  match nl:
    case True{}:
      st
    case False{}:
      step(hh, st, col)

# the name at col, from here up to the next newline
def at.read(ss: String, stop: Bool, st: W, +col: U32) -> String:
  match ss stop:
    case SNil{} _:
      finish(st, col)
    case SCon{h, t} True{}:
      finish(st, col)
    case SCon{+h, t} False{}:
      at.read(t, Char.is_eq(h, '\n'), at.advance(Char.is_eq(h, '\n'), h, st, col), col)

# the name under a (line, col) of a source, "" when none
def at(source: String, +line: U32, col: U32) -> String:
  at.read(at.skip(source, line, U32.is_eq(line, 0)), False{}, W{0, 0, [], None{}}, col)

# `Alias.rest` cut at its first dot: ("Alias", "rest"); no dot: (name, "")
def cut.go(cs: List<&2, Char>, acc: List<&2, Char>) -> String & String:
  match cs:
    case Nil{}:
      (text(acc), "")
    case Con{'.', t}:
      (text(acc), String.from_list(t))
    case Con{c, t}:
      cut.go(t, c <> acc)

# `Alias.rest` cut at its first dot: ("Alias", "rest"); no dot: (name, "")
def cut(name: String) -> String & String:
  cut.go(String.to_list(name), [])

# a pair's first
def fst(pp: String & String) -> String:
  (h, r) = pp
  h

# a pair's second
def snd(pp: String & String) -> String:
  (h, r) = pp
  r

# the part before the first dot
def head(name: String) -> String:
  fst(cut(name))

# the part after the first dot, "" when there is none
def rest(name: String) -> String:
  snd(cut(name))

# the leading run of name chars
def run_of(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      Lazy.stop(List<&2, Char>, Bool.not(is_name(c)), Nil{}, _u => c <> run_of(t))

# the name that ends at (line, col): what is being typed, for completion
def before(source: String, line: U32, col: U32) -> String:
  text(run_of(List.reverse(&2, Char, String.to_list(String.take(
    Maybe.default(&2, String, List.get(&2, String, String.lines(source), U32.to_nat(line)), ""),
    U32.to_nat(col))))))
