# bolt/src: the readings a rule is handed are the ones it used to take for
# itself. Every rule now reads Src.of's fields instead of calling Tree.parse,
# Lex.tokens or Bind.bound on the text, so each field must equal the call it
# replaced, and the whole rule set must answer the same either way.
import Base
import ../src.bend as Src
import ../rules.bend as Rules
import ../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree
import ../../syntax/bind.bend as Bind
import ../../core/check/kit.bend as Check
import ../../core/check/print.bend as Report

# a source with a def, a law-less type, a hole and a long line
def sample() -> String:
  String.join([
    "import Base",
    "",
    "# adds one",
    "def inc(n: U32) -> U32:",
    "  a = 1",
    "  (n + a : U32)",
    "",
    "def go(xs: List<&2, U32>) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      Bool.pick(U32, U32.is_eq(h, 0), go(t), (h + go(t) : U32))"], "\n")

# how many leaves a tree has
def leaves(n: Tree.Node) -> Nat:
  List.length(&2, Lex.Tok, Tree.leaves(n))

# the counts the binder found, as one string
def bound_counts(b: Bind.Bound) -> String:
  Bind.Bound{binds, uses, scopes} = b
  Nat.show(List.length(&2, Bind.Bind, binds)) ++ "/" ++ Nat.show(List.length(&2, Bind.Use, uses))
    ++ "/" ++ Nat.show(List.length(&2, Bind.Scope, scopes))

# the fields of a source read once
def fields(s: Src.Src) -> String:
  Src.Src{path, text, toks, tree, bound, items} = s
  path ++ " " ++ Nat.show(List.length(&2, Lex.Tok, toks)) ++ " " ++ Nat.show(leaves(tree))
    ++ " " ++ bound_counts(bound)

# the same fields, each computed the way a rule used to
def direct(+path: String, +text: String) -> String:
  path ++ " " ++ Nat.show(List.length(&2, Lex.Tok, Lex.tokens(text))) ++ " "
    ++ Nat.show(leaves(Tree.parse(text))) ++ " " ++ bound_counts(Bind.bound(text))

# findings as lines
def lines(fs: List<&2, F.Finding>) -> String:
  String.join(F.show_all(fs), "; ")

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str(~Report.new(), "src: the fields equal Lex.tokens, Tree.parse and Bind.bound of the text",
      fields(Src.of("a.bend", sample())), direct("a.bend", sample()))
    Check.eq_str(~Report.new(), "src: the text and path are carried unchanged",
      fields(Src.of("b/c.bend", "def f() -> U32:\n  1\n")), direct("b/c.bend", "def f() -> U32:\n  1\n"))
    Check.eq_str(~Report.new(), "rules: all(path, text) is on(Src.of(path, text))",
      lines(Rules.all("a.bend", sample())), lines(Rules.on(Src.of("a.bend", sample()))))
    Check.eq_str(~Report.new(), "rules: the sample's findings, read once",
      lines(Rules.on(Src.of("a.bend", sample()))),
      "a.bend:8:1: doc: def go has no comment above it; a.bend:13:7: pick: go recurses in both branches; Bool.pick runs both")

#|ok src: the fields equal Lex.tokens, Tree.parse and Bind.bound of the text
#|ok src: the text and path are carried unchanged
#|ok rules: all(path, text) is on(Src.of(path, text))
#|ok rules: the sample's findings, read once
