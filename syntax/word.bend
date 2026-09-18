# syntax/word: the name under a (line, col), both 0-based. A name is letters,
# digits, `_` and `.` (dots are just characters in a Bend name, and a module
# alias rides in front: `Frame.decode`). A position right after a name counts
# as on it, as editors put the cursor there.
import Base

# i: the column of the next char; start: where the current run began; run: the
# current name, reversed; hit: the name found
type W is Data:
  W{i: U32, start: U32, run: List<&2, Char>, hit: Maybe<&2, String>}

# a char a name may hold: letters, digits, `_` and `.`
def is_name(+c: Char) -> Bool:
  Bool.or(Bool.or(Char.is_alpha(c), Char.is_digit(c)), Bool.or(Char.is_eq(c, '_'), Char.is_eq(c, '.')))

# the run's chars (reversed) as a string
def text(run: List<&2, Char>) -> String:
  String.from_list(List.reverse(&2, Char, run))

# a run that ends at column i holds col when start <= col <= i
def close(+i: U32, +start: U32, +run: List<&2, Char>, +hit: Maybe<&2, String>, +col: U32) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>,
    Bool.and(Bool.and(Maybe.is_none(&2, String, hit), Bool.not(List.is_empty(&2, Char, run))),
      Bool.and(U32.is_le(start, col), U32.is_le(col, i))),
    Some{text(run)}, hit)

# one char: it extends the run of name chars, or ends it (a run holding the
# column is the answer)
def step(+c: Char, st: W, +col: U32) -> W:
  W{+i, +start, +run, +hit} = st
  Bool.pick(W, is_name(c),
    W{(i + 1 : U32), start, c <> run, hit},
    W{(i + 1 : U32), (i + 1 : U32), [], close(i, start, run, hit, col)})

# every char, in order
def scan(cs: List<&2, Char>, st: W, +col: U32) -> W:
  match cs:
    case Nil{}:
      st
    case Con{c, t}:
      scan(t, step(c, st, col), col)

# the run that held the column, else ""
def finish(st: W, col: U32) -> String:
  W{i, start, run, hit} = st
  Maybe.default(&2, String, close(i, start, run, hit, col), "")

# the name at a column of a line
def in_line(line: String, +col: U32) -> String:
  finish(scan(String.to_list(line), W{0, 0, [], None{}}, col), col)

# the name under a (line, col) of a source, "" when none
def at(source: String, line: U32, col: U32) -> String:
  in_line(Maybe.default(&2, String, List.get(&2, String, String.lines(source), U32.to_nat(line)), ""), col)

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
def fst(p: String & String) -> String:
  (h, r) = p
  h

# a pair's second
def snd(p: String & String) -> String:
  (h, r) = p
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
      Bool.pick(List<&2, Char>, is_name(c), c <> run_of(t), Nil{})

# the name that ends at (line, col): what is being typed, for completion
def before(source: String, line: U32, col: U32) -> String:
  text(run_of(List.reverse(&2, Char, String.to_list(String.take(
    Maybe.default(&2, String, List.get(&2, String, String.lines(source), U32.to_nat(line)), ""),
    U32.to_nat(col))))))
