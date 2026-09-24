# bench: per-rule timing (not part of bolt). bench/rules.bend <path>
import Base
import ../../bolt/args.bend as Args
import ../../bolt/src.bend as Src
import ../../bolt/finding.bend as F
import ../../bolt/lsp/files/disk.bend as Disk
import ../../bolt/rules.bend as Rules
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree
import ../../syntax/bind.bend as Bind
import ../../syntax/outline.bend as Outline
import ../../bolt/rules/style/doc.bend as Doc
import ../../bolt/rules/suspicious/unused.bend as Unused
import ../../bolt/rules/correctness/hole.bend as Hole
import ../../bolt/rules/style/space.bend as Space
import ../../bolt/rules/style/wrap.bend as Wrap
import ../../bolt/rules/style/param.bend as Param
import ../../bolt/rules/correctness/pick.bend as Pick
import ../../bolt/rules/laws/law.bend as Law
import ../../bolt/rules/suspicious/strict.bend as Strict
import ../../bolt/rules/suspicious/eager.bend as Eager
import ../../bolt/rules/pedantic/tail.bend as Tail
import ../../bolt/rules/suspicious/concat.bend as Concat
import ../../bolt/rules/suspicious/index.bend as Index
import ../../bolt/rules/suspicious/table.bend as Table
import ../../bolt/rules/suspicious/hoist.bend as Hoist
import ../../bolt/rules/suspicious/ring.bend as Ring
import ../../bolt/rules/suspicious/rewalk.bend as Rewalk
import ../../bolt/rules/suspicious/unit.bend as Unit
import ../../bolt/rules/correctness/put.bend as Put
import ../../bolt/rules/correctness/escape.bend as Escape
import ../../bolt/rules/correctness/strings.bend as Strings
import ../../bolt/rules/correctness/chars.bend as Chars
import ../../bolt/rules/correctness/twice.bend as Twice
import ../../bolt/rules/correctness/arms.bend as Arms
import ../../bolt/rules/correctness/foreign.bend as Foreign
import ../../bolt/rules/suspicious/fuel.bend as Fuel
import ../../bolt/rules/laws/closed.bend as Closed
import ../../bolt/rules/laws/trace.bend as Trace
import ../../bolt/rules/laws/unsafe.bend as Unsafe

def toks(ss: Src.Src) -> List<&2, Lex.Tok>:
  Src.Src{_path, _text, toks, tree, bound, items} = ss
  toks

def say(+name: String, +n: U32) -> IO(Unit):
  IO.print_err(name ++ " " ++ U32.show(n))

def go(+ss: Src.Src) -> IO(Unit):
  do IO<Unit>:
    say("parse", U32.from_nat(List.length(&2, Lex.Tok, toks(ss))))
    say("Doc", U32.from_nat(List.length(&2, F.Finding, Doc.check(ss))))
    say("Unused", U32.from_nat(List.length(&2, F.Finding, Unused.check(ss))))
    say("Hole", U32.from_nat(List.length(&2, F.Finding, Hole.check(ss))))
    say("Space", U32.from_nat(List.length(&2, F.Finding, Space.check(ss))))
    say("Wrap", U32.from_nat(List.length(&2, F.Finding, Wrap.check(ss))))
    say("Param", U32.from_nat(List.length(&2, F.Finding, Param.check(ss))))
    say("Pick", U32.from_nat(List.length(&2, F.Finding, Pick.check(ss))))
    say("Strict", U32.from_nat(List.length(&2, F.Finding, Strict.check(ss))))
    say("Eager", U32.from_nat(List.length(&2, F.Finding, Eager.check(ss))))
    say("Tail", U32.from_nat(List.length(&2, F.Finding, Tail.check(ss))))
    say("Concat", U32.from_nat(List.length(&2, F.Finding, Concat.check(ss))))
    say("Index", U32.from_nat(List.length(&2, F.Finding, Index.check(ss))))
    say("Table", U32.from_nat(List.length(&2, F.Finding, Table.check(ss))))
    say("Hoist", U32.from_nat(List.length(&2, F.Finding, Hoist.check(ss))))
    say("Ring", U32.from_nat(List.length(&2, F.Finding, Ring.check(ss))))
    say("Rewalk", U32.from_nat(List.length(&2, F.Finding, Rewalk.check(ss))))
    say("Unit", U32.from_nat(List.length(&2, F.Finding, Unit.check(ss))))
    say("Put", U32.from_nat(List.length(&2, F.Finding, Put.check(ss))))
    say("Escape", U32.from_nat(List.length(&2, F.Finding, Escape.check(ss))))
    say("Strings", U32.from_nat(List.length(&2, F.Finding, Strings.check(ss))))
    say("Chars", U32.from_nat(List.length(&2, F.Finding, Chars.check(ss))))
    say("Twice", U32.from_nat(List.length(&2, F.Finding, Twice.check(ss))))
    say("Arms", U32.from_nat(List.length(&2, F.Finding, Arms.check(ss))))
    say("Foreign", U32.from_nat(List.length(&2, F.Finding, Foreign.check(ss))))
    say("Fuel", U32.from_nat(List.length(&2, F.Finding, Fuel.check(ss))))
    say("Closed", U32.from_nat(List.length(&2, F.Finding, Closed.check(ss))))
    say("project", U32.from_nat(List.length(&2, F.Finding, Rules.project([ss], True{}, None{}))))

def nodes(nn: Tree.Node) -> U32:
  match nn:
    case Tree.NCons{_h, rest}:
      U32.inc(nodes(rest))
    case _other:
      0

def binds_n(bb: Bind.Bound) -> U32:
  Bind.Bound{binds, uses, scopes} = bb
  U32.from_nat(List.length(&2, Bind.Bind, binds))

def uses_n(bb: Bind.Bound) -> U32:
  Bind.Bound{binds, uses, scopes} = bb
  U32.from_nat(List.length(&2, Bind.Use, uses))

def stage4(+path: String, +text: String, +toks: List<&2, Lex.Tok>, +tree: Tree.Node, +bound: Bind.Bound) -> IO(Unit):
  +items = Outline.of_tokens(text, toks)
  do IO<Unit>:
    say("outline", U32.from_nat(List.length(&2, Outline.Item, items)))
    go(Src.Src{path, text, toks, tree, bound, items})

def stage3(+path: String, +text: String, +toks: List<&2, Lex.Tok>, +tree: Tree.Node, +lines: List<&2, String>) -> IO(Unit):
  +bound = Bind.of_tree(tree, lines)
  do IO<Unit>:
    say("bind.binds", binds_n(bound))
    say("bind.uses", uses_n(bound))
    stage4(path, text, toks, tree, bound)

def stage2(+path: String, +text: String, +toks: List<&2, Lex.Tok>, +tree: Tree.Node) -> IO(Unit):
  +lines = String.lines(text)
  do IO<Unit>:
    say("lines", U32.from_nat(List.length(&2, String, lines)))
    stage3(path, text, toks, tree, lines)

def stage1(+path: String, +text: String, +toks: List<&2, Lex.Tok>) -> IO(Unit):
  +tree = Tree.of_tokens(toks)
  do IO<Unit>:
    say("lex", U32.from_nat(List.length(&2, Lex.Tok, toks)))
    say("tree", nodes(tree))
    stage2(path, text, toks, tree)

def got(mm: Maybe<&2, String>, +path: String) -> IO(Unit):
  match mm:
    case None{}:
      IO.print_err("unread")
    case Some{+text}:
      do IO<Unit>:
        IO.print_err("read " ++ U32.show(U32.from_nat(String.length(text))))
        stage1(path, text, Lex.tokens(text))

def pick(av: List<&2, String>) -> IO(Unit):
  match av:
    case Nil{}:
      IO.print_err("usage")
    case Con{+p, _rest}:
      do IO<Unit>:
        mm : Maybe<&2, String> <- Disk.read(p)
        got(mm, p)

def main() -> IO(Unit):
  do IO<Unit>:
    av : List<&2, String> <- Args.argv()
    pick(av)
