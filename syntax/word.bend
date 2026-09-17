# syntax/word: the name under a (line, col), both 0-based. A name is letters,
# digits, `_` and `.` (dots are just characters in a Bend name, and a module
# alias rides in front: `Frame.decode`). A position right after a name counts
# as on it, as editors put the cursor there.
import Base

# i: the column of the next char; start: where the current run began; run: the
# current name, reversed; hit: the name found
type W is Data:
  W{i: U32, start: U32, run: List<&2, Char>, hit: Maybe<&2, String>}

def is_name(+c: Char) -> Bool:
  Bool.or(Bool.or(Char.is_alpha(c), Char.is_digit(c)), Bool.or(Char.is_eq(c, '_'), Char.is_eq(c, '.')))

def text(run: List<&2, Char>) -> String:
  String.from_list(List.reverse(&2, Char, run))

# a run that ends at column i holds col when start <= col <= i
def close(+i: U32, +start: U32, +run: List<&2, Char>, +hit: Maybe<&2, String>, +col: U32) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>,
    Bool.and(Bool.and(Maybe.is_none(&2, String, hit), Bool.not(List.is_empty(&2, Char, run))),
      Bool.and(U32.is_le(start, col), U32.is_le(col, i))),
    Some{text(run)}, hit)

def step(+c: Char, st: W, +col: U32) -> W:
  W{+i, +start, +run, +hit} = st
  Bool.pick(W, is_name(c),
    W{(i + 1 : U32), start, c <> run, hit},
    W{(i + 1 : U32), (i + 1 : U32), [], close(i, start, run, hit, col)})

def scan(cs: List<&2, Char>, st: W, +col: U32) -> W:
  match cs:
    case Nil{}:
      st
    case Con{c, t}:
      scan(t, step(c, st, col), col)

def finish(st: W, col: U32) -> String:
  W{i, start, run, hit} = st
  Maybe.default(&2, String, close(i, start, run, hit, col), "")

def in_line(line: String, +col: U32) -> String:
  finish(scan(String.to_list(line), W{0, 0, [], None{}}, col), col)

def at(source: String, line: U32, col: U32) -> String:
  in_line(Maybe.default(&2, String, List.get(&2, String, String.lines(source), U32.to_nat(line)), ""), col)
