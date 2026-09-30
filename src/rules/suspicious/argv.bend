# rule argv: a call to `IO.args(`: among the significant tokens, an `IO.args`
# token with a `(` token right after it, and nothing else. Since bend 2.0.32
# IO.args gives the program as invoked first, as C's argv does, so a program
# that parses it as it comes takes its own path for its first argument (the
# move to bend 2.0.34 broke every such reader silently). Read the arguments
# through shake's `Shake.argv()`, or drop the first word before parsing. The
# rule does not try to tell a reader that drops it from one that does not:
# the one reader a program has carries `# noqa: U014`, and the rule is
# opt-in, off unless a bolt.bend names it (BOLT-CFG-6). No path is exempt: a
# law file, a proof or a test reads IO.args as wrongly as any other file.
import Base
import ../../src.bend as Src
import ../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../tokens.bend as T

# a dotted name?
def calls.dotted(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TDotted{}:
      True{}
    case other:
      False{}

# a dotted name then an open bracket: a finding when they are `IO.args` and
# `(`, before what the rest reports
def calls.one(
  +tt: String,
  +oo: String,
  +ll: U32,
  +cc: U32,
  +path: String,
  +more: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  Bool.pick(List<&2, F.Finding>, Bool.and(String.eq(tt, "IO.args"), String.eq(oo, "(")),
    F.Finding{path, ll, cc, 7, "argv", "IO.args() starts with the program as invoked (bend 2.0.32); use Shake.argv(), or drop the first word before parsing."}
      <> more,
    more)

# every `IO.args(` among the significant tokens
def calls(toks: List<&2, Lex.Tok>, +path: String) -> List<&2, F.Finding>:
  match toks:
    case Con{Lex.Tok{k, +t, +l, +c}, +rest}:
      match rest:
        case Con{Lex.Tok{k2, +o, l2, c2}, r2}:
          Lazy.either(List<&2, F.Finding>, Bool.and(calls.dotted(k), Lex.is_open(k2)), _u => calls.one(t, o, l, c, path,
            calls(r2, path)), _v => calls(rest, path))
        case Nil{}:
          Nil{}
    case Nil{}:
      Nil{}

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  calls(T.sig(toks), path)
