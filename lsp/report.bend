# lsp/report: the checker's text, as diagnostics. bend prints an error as
#   Error:            (or `Error: a one-line message`)
#   - expected : ..   the message lines, then `Context:` and its lines
#   Location: name    the def; `../mod.name` when it sits in an import
#   4>|   x           the source excerpt; `>|` marks the line, 1-based
# There are no columns, so a diagnostic covers its whole line. An error in an
# import cannot be placed in this file: it lands on line 0, naming its home.
import Base

# line is 0-based, as LSP counts
type Diag is Data:
  Diag{line: U32, msg: String}

type Line is Data:
  KError{rest: String}
  KLocation{place: String}
  KOther{text: String}

# msg and out are reversed
type St is Data:
  St{seen: Bool, located: Bool, msg: List<&2, String>, line: U32, place: String, out: List<&2, Diag>}

def classify(+s: String) -> Line:
  Bool.pick(Line, String.starts_with(s, "Error:"), KError{String.drop(s, 6n)},
    Bool.pick(Line, String.starts_with(s, "Location:"), KLocation{String.drop(s, 9n)}, KOther{s}))

def not_space(c: Char) -> Bool:
  Bool.not(Char.is_space(c))

def strip(s: String) -> String:
  String.from_list(List.filter(~Char, ~not_space, String.to_list(s)))

# drops leading spaces
def lstrip.go(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Con{' ', t}:
      lstrip.go(t)
    case other:
      other

def lstrip(s: String) -> String:
  String.from_list(lstrip.go(String.to_list(s)))

# `12>|  code` marks line 12: the text before the first '>' is the number, and
# the text after it starts with '|' (a '>' later in the code changes nothing)
def marker.of(parts: List<&2, String>) -> Maybe<&2, U32>:
  match parts:
    case Con{a, Con{b, rest}}:
      Bool.pick(Maybe<&2, U32>, String.starts_with(b, "|"), U32.read(strip(a)), None{})
    case other:
      None{}

def marker(s: String) -> Maybe<&2, U32>:
  marker.of(String.split(s, '>'))

# a message line, without its `- `
def clean(+s: String) -> String:
  Bool.pick(String, String.starts_with(s, "- "), String.drop(s, 2n), s)

def push(+s: String, +msg: List<&2, String>) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.is_empty(s), msg, s <> msg)

def message(+place: String, msg: List<&2, String>) -> String:
  +body = String.join(List.reverse(&2, String, msg), "\n")
  Bool.pick(String, String.contains(place, "/"), "in " ++ place ++ ":\n" ++ body, body)

def line_of(place: String, +line: U32) -> U32:
  Bool.pick(U32, Bool.or(String.contains(place, "/"), U32.is_eq(line, 0)), 0, (line - 1 : U32))

# the error so far becomes a diagnostic; "no main to run" is a library, not an error
def flush(seen: Bool, msg: List<&2, String>, +line: U32, +place: String, +out: List<&2, Diag>) -> List<&2, Diag>:
  +text = message(place, msg)
  Bool.pick(List<&2, Diag>, Bool.and(seen, Bool.not(String.eq(text, "no main to run"))),
    Diag{line_of(place, line), text} <> out, out)

def step.go(k: Line, located: Bool, seen: Bool, msg: List<&2, String>, +line: U32, place: String, out: List<&2, Diag>) -> St:
  match k located seen:
    case KError{rest} l s:
      St{True{}, False{}, push(lstrip(rest), []), 0, "", flush(s, msg, line, place, out)}
    case KLocation{p} l s:
      St{s, True{}, msg, line, lstrip(p), out}
    case KOther{text} False{} True{}:
      St{True{}, False{}, push(clean(text), msg), line, place, out}
    case KOther{text} True{} True{}:
      St{True{}, True{}, msg, Maybe.default(&2, U32, marker(text), line), place, out}
    case KOther{text} l False{}:
      St{False{}, l, msg, line, place, out}

def step(s: String, st: St) -> St:
  St{seen, located, msg, line, place, out} = st
  step.go(classify(s), located, seen, msg, line, place, out)

def run(lines: List<&2, String>, st: St) -> St:
  match lines:
    case Nil{}:
      st
    case Con{l, t}:
      run(t, step(l, st))

def finish(st: St) -> List<&2, Diag>:
  St{seen, located, msg, line, place, out} = st
  List.reverse(&2, Diag, flush(seen, msg, line, place, out))

def parse(text: String) -> List<&2, Diag>:
  finish(run(String.lines(text), St{False{}, False{}, [], 0, "", []}))
