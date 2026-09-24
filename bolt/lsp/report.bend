# lsp/report: the checker's text, as diagnostics. bend prints an error as
#   Error:            (or `Error: a one-line message`)
#   - expected : ..   the message lines, then `Context:` and its lines
#   Location: name    the def; `../mod.name` when it sits in an import
#   4>|   x           the source excerpt; `>|` marks the line, 1-based
# There are no columns, so a diagnostic covers its whole line. An error in an
# import cannot be placed in this file: it lands on line 0, naming its home.
# bend names a def of an import beside this file without a path (`m.g`), as
# it names a def `m.g` of this file, so such an error reads as this file's.
import Base
import ../../lazy/lazy.bend as Lazy

# line is 0-based, as LSP counts
type Diag is Data:
  Diag{line: U32, msg: String}

# a line of the checker's report, by what it starts with
type Line is Data:
  KError{rest: String}
  KLocation{place: String}
  KOther{text: String}

# msg and out are reversed
type St is Data:
  St{seen: Bool, located: Bool, msg: List<&2, String>, line: U32, place: String, out: List<&2, Diag>}

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

# the message lines (reversed) as text, headed by where it is when that is
# another file
def message(+place: String, msg: List<&2, String>) -> String:
  +body = String.join(List.reverse(&2, String, msg), "\n")
  Bool.pick(String, String.contains(place, "/"), "in " ++ place ++ ":\n" ++ body, body)

# the 0-based line for a diagnostic: line 0 for an error in an import
def line_of(place: String, +line: U32) -> U32:
  Bool.pick(U32, Bool.or(String.contains(place, "/"), U32.is_eq(line, 0)), 0, (line - 1 : U32))

# the error so far becomes a diagnostic; "no main to run" is a library, not an error
def flush(seen: Bool, msg: List<&2, String>, +line: U32, +place: String, +out: List<&2, Diag>) -> List<&2, Diag>:
  +text = message(place, msg)
  Bool.pick(List<&2, Diag>, Bool.and(seen, Bool.not(String.eq(text, "no main to run"))),
    Diag{line_of(place, line), text} <> out, out)

def step.go(
  kk: Line,
  located: Bool,
  seen: Bool,
  msg: List<&2, String>,
  +line: U32,
  place: String,
  out: List<&2, Diag>
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

# the diagnostics once the lines are over, a pending one flushed
def finish(st: St) -> List<&2, Diag>:
  St{seen, located, msg, line, place, out} = st
  List.reverse(&2, Diag, flush(seen, msg, line, place, out))

# the checker's text as diagnostics
def parse(text: String) -> List<&2, Diag>:
  finish(run(String.lines(text), St{False{}, False{}, [], 0, "", []}))
