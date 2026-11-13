# bench: per-stage and per-rule timing of one file (not part of bolt).
#   stages.bin +RTS --gpu off -RTS <path> 2>&1 | while read -r l; do echo "$(date +%s.%N) $l"; done
# Each stage's strict let sits in its own def, and each prints a number read
# off its result, so no stage can be skipped or run early.
import Base
import ../../src/args.bend as Args
import ../../src/src.bend as Src
import ../../src/finding.bend as F
import ../../src/role.bend as Role
import ../../src/noqa.bend as Noqa
import ../../src/config.bend as Config
import ../../src/rules.bend as Rules
import ../../src/rules/digest.bend as Digest
import ../../src/rules/laws/law.bend as Law
import ../../src/lsp/files/disk.bend as Disk
import ../../src/syntax/lex.bend as Lex
import ../../src/syntax/tree.bend as Tree
import ../../src/syntax/bind.bend as Bind
import ../../src/syntax/outline.bend as Outline

def say(+name: String, +n: Nat) -> IO(Unit):
  IO.print_err(name ++ " " ++ U32.show(U32.from_nat(n)))

def uses(bb: Bind.Bound) -> Nat:
  Bind.Bound{binds, uses, _scopes} = bb
  Nat.add(List.length(&2, Bind.Bind, binds), List.length(&2, Bind.Use, uses))

def st.lex(+text: String) -> IO(List<&2, Lex.Tok>):
  +toks = Lex.tokens(text)
  do IO<List<&2, Lex.Tok>>:
    say("lex", List.length(&2, Lex.Tok, toks))
    return toks

def st.tree(+toks: List<&2, Lex.Tok>) -> IO(Tree.Node):
  +tree = Tree.of_tokens(toks)
  do IO<Tree.Node>:
    say("tree", List.length(&2, Digest.Span, Digest.spans(tree)))
    return tree

def st.lines(+text: String) -> IO(List<&2, String>):
  +ls = String.lines(text)
  do IO<List<&2, String>>:
    say("lines", List.length(&2, String, ls))
    return ls

def st.bind(+tree: Tree.Node, +ls: List<&2, String>) -> IO(Bind.Bound):
  +bb = Bind.of_tree(tree, ls)
  do IO<Bind.Bound>:
    say("bind", uses(bb))
    return bb

def st.outline(+text: String, +toks: List<&2, Lex.Tok>) -> IO(List<&2, Outline.Item>):
  +items = Outline.of_tokens(text, toks)
  do IO<List<&2, Outline.Item>>:
    say("outline", List.length(&2, Outline.Item, items))
    return items

def st.rule(+slug: String, ww: Rules.Which, +rr: Role.Role, +ss: Src.Src) -> IO(Unit):
  +fs = Rules.on.run(ww, rr, ss)
  say("rule " ++ slug, List.length(&2, F.Finding, fs))

def st.rules(rs: List<&2, Rules.Run>, +rr: Role.Role, +ss: Src.Src) -> IO(Unit):
  match rs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{Rules.Run{+slug, ww}, rest}:
      do IO<Unit>:
        st.rule(slug, ww, rr, ss)
        st.rules(rest, rr, ss)

def st.marks(+ss: Src.Src) -> IO(List<&2, Role.Mark>):
  +ms = Role.marks([ss])
  do IO<List<&2, Role.Mark>>:
    say("marks", List.length(&2, Role.Mark, ms))
    return ms

def st.digest(+ms: List<&2, Role.Mark>, +ss: Src.Src) -> IO(List<&2, Digest.Digest>):
  +ds = Digest.all.role(ms, [ss])
  do IO<List<&2, Digest.Digest>>:
    say("digest", List.length(&2, Digest.Digest, ds))
    return ds

def st.law(+ds: List<&2, Digest.Digest>) -> IO(Unit):
  +fs = Law.check(ds)
  say("law", List.length(&2, F.Finding, fs))

def st.found(+cfg: Config.Config, +rr: Role.Role, +ss: Src.Src) -> IO(List<&2, F.Finding>):
  +fs = Rules.on.role.live(cfg, rr, ss)
  do IO<List<&2, F.Finding>>:
    say("found(default config)", List.length(&2, F.Finding, fs))
    return fs

def st.all(+rr: Role.Role, +ss: Src.Src) -> IO(Unit):
  +fs = Rules.on.rules.role(rr, ss)
  say("on.rules.role (every rule, one call)", List.length(&2, F.Finding, fs))

def st.live(+cfg: Config.Config, +rr: Role.Role, +ss: Src.Src) -> IO(Unit):
  +fs = Rules.on.live(Rules.on.table(), cfg, rr, ss)
  say("on.live (default config, no on.at)", List.length(&2, F.Finding, fs))

def st.grade(+cfg: Config.Config, +fs: List<&2, F.Finding>) -> IO(List<&2, F.Graded>):
  +gs = Rules.graded(cfg, fs)
  do IO<List<&2, F.Graded>>:
    say("grade", List.length(&2, F.Graded, gs))
    return gs

def st.noqa(+ss: Src.Src) -> IO(List<&2, Noqa.Marks>):
  +ms = Noqa.of_srcs([ss])
  do IO<List<&2, Noqa.Marks>>:
    say("noqa marks", List.length(&2, Noqa.Marks, ms))
    return ms

def st.keep(+ms: List<&2, Noqa.Marks>, +gs: List<&2, F.Graded>) -> IO(Unit):
  +ks = Noqa.keep(ms, gs)
  say("noqa keep", List.length(&2, F.Graded, ks))

def go(+path: String, +text: String) -> IO(Unit):
  do IO<Unit>:
    say("read", String.length(text))
    +toks : List<&2, Lex.Tok> <- st.lex(text)
    +tree : Tree.Node <- st.tree(toks)
    +ls : List<&2, String> <- st.lines(text)
    +bb : Bind.Bound <- st.bind(tree, ls)
    +items : List<&2, Outline.Item> <- st.outline(text, toks)
    +ss : Src.Src = Src.Src{path, text, toks, tree, bb, items}
    +ms : List<&2, Role.Mark> <- st.marks(ss)
    +rr : Role.Role = Role.of(ms, path)
    st.all(rr, ss)
    st.rules(Rules.on.table(), rr, ss)
    st.all(rr, ss)
    st.rules(Rules.on.table(), rr, ss)
    +ds : List<&2, Digest.Digest> <- st.digest(ms, ss)
    st.law(ds)
    +cfg : Config.Config = Config.nearest([])
    st.all(rr, ss)
    st.live(cfg, rr, ss)
    +fs : List<&2, F.Finding> <- st.found(cfg, rr, ss)
    st.live(cfg, rr, ss)
    +gs : List<&2, F.Graded> <- st.grade(cfg, fs)
    +nm : List<&2, Noqa.Marks> <- st.noqa(ss)
    st.keep(nm, gs)
    say("done", 0n)

def pick(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{p, _rest}:
      p

def have(+path: String, mm: Maybe<&2, String>) -> IO(Unit):
  match mm:
    case None{}:
      IO.print_err("cannot read " ++ path)
    case Some{text}:
      go(path, text)

def main() -> IO(Unit):
  do IO<Unit>:
    +av : List<&2, String> <- Args.argv()
    +path : String = pick(av)
    mm : Maybe<&2, String> <- Disk.read(path)
    have(path, mm)
