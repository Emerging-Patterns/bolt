# lanes: native
# syntax/tree on real files of this repo (run from its root): the tree's
# leaves are the significant tokens, every bracket closes, and no bracket
# becomes a stray leaf
import Base
import ../lex.bend as Lex
import ../tree.bend as Tree
import ../../bolt/lsp/files/service.bend as F
import ../../bolt/lsp/files/disk.bend as Disk
import ../../core/check/kit.bend as Check
import ../../core/check/print.bend as Report

def significant(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{+k, t, l, c}, rest}:
      +more = significant(rest)
      Bool.pick(List<&2, Lex.Tok>, Lex.significant(k), Lex.Tok{k, t, l, c} <> more, more)

# an unclosed group or a stray close bracket
def flaws(n: Tree.Node) -> U32:
  match n:
    case Tree.Leaf{Lex.Tok{k, t, l, c}}:
      Bool.pick(U32, Lex.is_close(k), 1, 0)
    case Tree.Group{open, kids, close}:
      +a = flaws(kids)
      (a + Bool.pick(U32, Maybe.is_some(&2, Lex.Tok, close), 0, 1) : U32)
    case Tree.Stmt{kind, kids, body}:
      +a = flaws(kids)
      +b = flaws(body)
      (a + b : U32)
    case Tree.NNil{}:
      0
    case Tree.NCons{h, t}:
      +a = flaws(h)
      +b = flaws(t)
      (a + b : U32)

def faithful.on(path: String, +text: String) -> IO(Unit):
  +tree = Tree.parse(text)
  Check.eq_str(~Report.new(), path,
    Lex.text(Tree.leaves(tree)) ++ Bool.pick(String, String.is_empty(text), "<unread>", "") ++ " flaws:" ++ U32.show(flaws(tree)),
    Lex.text(significant(Lex.tokens(text))) ++ " flaws:0")

def faithful(~fs: F.Files, +path: String) -> IO(Unit):
  do IO<Unit>:
    r : Maybe<&2, String> <- F.read(fs, path)
    faithful.on(path, Maybe.default(&2, String, r, ""))

def main() -> IO(Unit):
  do IO<Unit>:
    faithful(~Disk.new(), "bolt/lsp/server.bend")
    faithful(~Disk.new(), "syntax/tree.bend")
    faithful(~Disk.new(), "core/PROOF.bend")
    faithful(~Disk.new(), "core/LAWS.bend")
    faithful(~Disk.new(), "bolt/args.bend")
    faithful(~Disk.new(), "bolt/lsp/tests/checker.bend")

#|ok bolt/lsp/server.bend
#|ok syntax/tree.bend
#|ok core/PROOF.bend
#|ok core/LAWS.bend
#|ok bolt/args.bend
#|ok bolt/lsp/tests/checker.bend
