# lsp/report: the checker's text, as diagnostics. bend prints an error as
#   Error:            (or `Error: a one-line message`)
#   - expected : ..   the message lines, then `Context:` and its lines
#   Location: name    bend's key for the def: `name` in this file, the
#                     import's namespace first in another (`m.g`, `../m.g`)
#   4>|   x           the source excerpt; `>|` marks the line, 1-based
# There are no columns, so a diagnostic covers its whole line. An error in an
# import cannot be placed in this file: it lands on line 0, naming its home.
# Which errors are this file's is read against the file's own keys (mine).
import Base
import ../lazy/lazy.bend as Lazy

# line is 0-based, as LSP counts
type Diag is Data:
  Diag{line: U32, msg: String}

# a line of the checker's report, by what it starts with
type Line is Data:
  KError{rest: String}
  KLocation{place: String}
  KOther{text: String}

# an error bend reported, before it is placed: where it is (the Location's
# name, bend's key for its def), the line it marks (1-based, 0 for none), and
# its message
type Raw is Data:
  Raw{place: String, line: U32, body: String}

# msg and out are reversed
type St is Data:
  St{seen: Bool, located: Bool, msg: List<&2, String>, line: U32, place: String, out: List<&2, Raw>}

# a report line's kind
def classify(+ss: String) -> Line:
  Bool.pick(Line, String.starts_with(ss, "Error:"), KError{String.drop(ss, 6n)},
    Bool.pick(Line, String.starts_with(ss, "Location:"), KLocation{String.drop(ss, 9n)}, KOther{ss}))

# reading a marker past its padding: `count` digits of `whole` so far, and at
# the first other character, the number they make when `>|` follows them
def marker.go(ss: String, +whole: String, +count: Nat) -> Maybe<&2, U32>:
  match ss:
    case SNil{}:
      None{}
    case SCon{+hh, +tt}:
      Lazy.stop(Maybe<&2, U32>, Bool.not(Char.is_digit(hh)),
        Bool.pick(Maybe<&2, U32>, String.starts_with(SCon{hh, tt}, ">|"), U32.read(String.take(whole, count)), None{}),
        _u => marker.go(tt, whole, 1n+count))

# the line number a source line of the report carries, when it does: `12>|
# code` marks line 12, padding before the digits aside; a line of context
# (`11 | code`) marks none, whatever its code holds
def marker(ss: String) -> Maybe<&2, U32>:
  +tt = String.trim_start(ss)
  marker.go(tt, tt, 0n)

# a message line, without its `- `
def clean(+ss: String) -> String:
  Bool.pick(String, String.starts_with(ss, "- "), String.drop(ss, 2n), ss)

# bend's "N is available: run bend update" is not part of a diagnostic
def is_nag(+ss: String) -> Bool:
  String.contains(ss, "is available: run bend update")

# a non-empty, non-nag line onto the message
def push(+ss: String, +msg: List<&2, String>) -> List<&2, String>:
  Bool.pick(List<&2, String>, Bool.or(String.is_empty(ss), is_nag(ss)), msg, ss <> msg)

# the error so far, its message lines reversed, onto the ones before it; "no
# main to run" is a library, not an error
def flush(seen: Bool, msg: List<&2, String>, +line: U32, +place: String, +out: List<&2, Raw>) -> List<&2, Raw>:
  +body = String.join(List.reverse(&2, String, msg), "\n")
  Bool.pick(List<&2, Raw>, Bool.and(seen, Bool.not(String.eq(body, "no main to run"))),
    Raw{place, line, body} <> out, out)

def step.go(
  kk: Line,
  located: Bool,
  seen: Bool,
  msg: List<&2, String>,
  +line: U32,
  place: String,
  out: List<&2, Raw>
) -> St:
  match kk located seen:
    case KError{rest} l s:
      St{True{}, False{}, push(String.trim_start(rest), []), 0, "", flush(s, msg, line, place, out)}
    case KLocation{p} l s:
      St{s, True{}, msg, line, String.trim_start(p), out}
    case KOther{text} False{} True{}:
      St{True{}, False{}, push(clean(text), msg), line, place, out}
    case KOther{text} True{} True{}:
      St{True{}, True{}, msg, Maybe.default(&2, U32, marker(text), line), place, out}
    case KOther{text} l False{}:
      St{False{}, l, msg, line, place, out}

# one report line
def step(ss: String, st: St) -> St:
  St{seen, located, msg, line, place, out} = st
  step.go(classify(ss), located, seen, msg, line, place, out)

# every report line, in order
def run(lines: List<&2, String>, st: St) -> St:
  match lines:
    case Nil{}:
      st
    case Con{l, t}:
      run(t, step(l, st))

# the errors once the lines are over, a pending one flushed
def finish(st: St) -> List<&2, Raw>:
  St{seen, located, msg, line, place, out} = st
  List.reverse(&2, Raw, flush(seen, msg, line, place, out))

# the text before the first `~`: an instance of a template (`f~1`) is the
# template's
def stem(ss: String) -> String:
  match ss:
    case SNil{}:
      SNil{}
    case SCon{+hh, tt}:
      Lazy.stop(String, Char.is_eq(hh, '~'), SNil{}, _u => SCon{hh, stem(tt)})

# is the name among these?
def owns(names: List<&2, String>, +name: String) -> Bool:
  match names:
    case Nil{}:
      False{}
    case Con{hh, tt}:
      Lazy.or_else(String.eq(hh, name), _u => owns(tt, name))

# is an error at this place in the checked file? With the file's names
# (bend's keys for its items, checker/names.bend): when the place is one of
# them or names nothing. Without them: when the place holds no path. bend
# names a def of an import beside the file with no path (`m.g`), so only
# the names tell it from a def `m.g` of the file
def mine(names: Maybe<&2, List<&2, String>>, +place: String) -> Bool:
  match names:
    case None{}:
      Bool.not(String.contains(place, "/"))
    case Some{ks}:
      Bool.or(String.is_empty(place), owns(ks, stem(place)))

# an error placed: on its marked line, 0-based, in the checked file; on line
# 0, its message headed by where it is, in another file
def diag.at(+own: Bool, +place: String, +line: U32, +body: String) -> Diag:
  Diag{Bool.pick(U32, Bool.or(Bool.not(own), U32.is_eq(line, 0)), 0, (line - 1 : U32)),
    Bool.pick(String, own, body, "in " ++ place ++ ":\n" ++ body)}

# an error placed, by the checked file's names
def diag(names: Maybe<&2, List<&2, String>>, rr: Raw) -> Diag:
  Raw{+place, line, body} = rr
  diag.at(mine(names, place), place, line, body)

# every error placed
def diags(rs: List<&2, Raw>, +names: Maybe<&2, List<&2, String>>) -> List<&2, Diag>:
  match rs:
    case Nil{}:
      []
    case Con{rr, rest}:
      diag(names, rr) <> diags(rest, names)

# the checker's text as diagnostics, placed by the checked file's names when
# they are known
def parse_in(+names: Maybe<&2, List<&2, String>>, text: String) -> List<&2, Diag>:
  diags(finish(run(String.lines(text), St{False{}, False{}, [], 0, "", []})), names)
