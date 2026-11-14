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
import ../../role.bend as Role
import ../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../tokens.bend as T

# are the four texts `String.from_list`, `(`, `List.reverse` and `(`?
def shape(+t: String, +a: String, +b: String, +d: String) -> Bool:
  Bool.and(String.eq(t, "String.from_list"),
    Bool.and(String.eq(a, "("), Bool.and(String.eq(b, "List.reverse"), String.eq(d, "("))))

# a token of text t, then these: do the four open the shape?
def at(+t: String, toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Con{Lex.Tok{k1, +a, l1, c1}, Con{Lex.Tok{k2, +b, l2, c2}, Con{Lex.Tok{k3, +d, l3, c3}, rest}}}:
      shape(t, a, b, d)
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
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = s
  Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path), [], _u => walk(T.sig(toks), path))

# the rule, told the file's role (src/role.bend): a law or proof file is
# skipped
def check.role(r: Role.Role, s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = s
  Lazy.stop(List<&2, F.Finding>, Role.is_law_file(r), [], _u => walk(T.sig(toks), path))
