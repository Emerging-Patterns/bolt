# rule fromrev: a String read off a reversed list: among the significant
# tokens (spaces, newlines and comments dropped), four tokens right after one
# another whose texts are `String.from_list`, `(`, `List.reverse` and `(`;
# one finding, on the `String.from_list` token, for each such run, and
# nothing else. Anything between them, another `(` included
# (`String.from_list((List.reverse(..)))`), is not the shape, and neither is
# `List.reverse.go`. A buffer of chars consed on the front, then reversed
# and read into a String, walks the buffer twice and builds a list only to
# throw it away (and String.from_list, not a tail call, runs the JS lane out
# of stack on a long buffer): fold the buffer onto a String with SCon in one
# pass, `go(t, SCon{h, acc})` from `SNil{}` (src/rchars.bend). A LAWS.bend
# or a PROOF.bend, which never runs, is exempt.
import Base
import ../../src.bend as Src
import ../../paths.bend as Paths
import ../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../tokens.bend as T

# are the four texts `String.from_list`, `(`, `List.reverse` and `(`?
def shape(+tt: String, +aa: String, +bb: String, +dd: String) -> Bool:
  Bool.and(String.eq(tt, "String.from_list"),
    Bool.and(String.eq(aa, "("), Bool.and(String.eq(bb, "List.reverse"), String.eq(dd, "("))))

# a token of text tt, then these: do the four open the shape?
def at(+tt: String, toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Con{Lex.Tok{k1, +aa, l1, c1}, Con{Lex.Tok{k2, +bb, l2, c2}, Con{Lex.Tok{k3, +dd, l3, c3}, rest}}}:
      shape(tt, aa, bb, dd)
    case other:
      False{}

# every run of the shape among the tokens, in order
def walk(toks: List<&2, Lex.Tok>, +path: String) -> List<&2, F.Finding>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{k, +t, +l, +c}, +rest}:
      +more = walk(rest, path)
      Bool.pick(List<&2, F.Finding>, at(t, rest),
        F.Finding{path, l, c, 16, "fromrev", "String.from_list(List.reverse(..)) walks the list twice and builds one it throws away; fold it onto a String with SCon in one pass."}
          <> more,
        more)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = ss
  Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path), [], _u => walk(T.sig(toks), path))
