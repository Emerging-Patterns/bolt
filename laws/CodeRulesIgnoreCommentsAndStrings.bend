# For every rule whose pattern is code (all but `escape`, `strings`, `chars`,
# `space`, `twice`, `foreign`, `noqa`, `rewalk` and `prefix`, which reads a
# string literal's length: laws/InertPrefix.bend says what it ignores),
# changing the contents of a comment or string literal does not change the
# findings.
#
# also rests on: laws/InertFromrev.bend, laws/InertTranscong.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/correctness/put.bend as Put
import ../src/rules/correctness/hole.bend as Hole
import ../src/rules/style/param.bend as Param
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/style/doc.bend as Doc
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/pedantic/tail.bend as Tail
import ../src/rules/suspicious/concat.bend as Concat
import ../src/rules/suspicious/eager.bend as Eager
import ../src/rules/suspicious/strict.bend as Strict
import ../src/rules/suspicious/hoist.bend as Hoist
import ../src/rules/suspicious/index.bend as Index
import ../src/rules/suspicious/ring.bend as Ring
import ../src/rules/suspicious/table.bend as Table
import ../src/rules/suspicious/unit.bend as UnitRule
import ../src/rules/suspicious/thunk.bend as Thunk
import ../src/rules/suspicious/scan.bend as Scan
import ../src/rules/tokens.bend as T
import ../src/rules/correctness/arms.bend as Arms
import ../src/rules/suspicious/unused.bend as Unused
import ../src/rules/suspicious/fuel.bend as FuelRule
import ../src/rules/style/wrap.bend as Wrap
import ./defs/InertText.bend as D1

# LAW: hole reads what no comment or string says: two sources whose tokens
# read the same with comments and strings cut have the same findings
law inert_hole:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for toks2: List<&2, Lex.Tok>
  for tree2: Tree.Node
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for e: {D1.inert.toks(toks) == D1.inert.toks(toks2) : List<&2, Lex.Tok>}
  {Hole.check(Src.Src{path, text, toks, tree, bound, items})
    == Hole.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: put reads what no comment or string says: two sources as the lexer
# makes them whose tokens read the same with comments and strings cut have
# the same findings
law inert_put:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for toks2: List<&2, Lex.Tok>
  for tree2: Tree.Node
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for ok: {D1.inert.oks(toks) == True{} : Bool}
  for ok2: {D1.inert.oks(toks2) == True{} : Bool}
  for e: {D1.inert.toks(toks) == D1.inert.toks(toks2) : List<&2, Lex.Tok>}
  {Put.check(Src.Src{path, text, toks, tree, bound, items})
    == Put.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: tail reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings (a
# string's text is only ever compared with the def's name or `Bool.pick`)
law inert_tail:
  for +path: String
  for text: String
  for +tree: Tree.Node
  for toks: List<&2, Lex.Tok>
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for +tree2: Tree.Node
  for toks2: List<&2, Lex.Tok>
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for +ok: {D1.inert.ok(tree) == True{} : Bool}
  for +ok2: {D1.inert.ok(tree2) == True{} : Bool}
  for e: {D1.inert.node(tree) == D1.inert.node(tree2) : Tree.Node}
  {Tail.check(Src.Src{path, text, toks, tree, bound, items})
    == Tail.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: pick reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings
law inert_pick:
  for +path: String
  for text: String
  for +tree: Tree.Node
  for toks: List<&2, Lex.Tok>
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for +tree2: Tree.Node
  for toks2: List<&2, Lex.Tok>
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for +ok: {D1.inert.ok(tree) == True{} : Bool}
  for +ok2: {D1.inert.ok(tree2) == True{} : Bool}
  for e: {D1.inert.node(tree) == D1.inert.node(tree2) : Tree.Node}
  {Pick.check(Src.Src{path, text, toks, tree, bound, items})
    == Pick.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: strict reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings
law inert_strict:
  for +path: String
  for text: String
  for +tree: Tree.Node
  for toks: List<&2, Lex.Tok>
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for +tree2: Tree.Node
  for toks2: List<&2, Lex.Tok>
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for +ok: {D1.inert.ok(tree) == True{} : Bool}
  for +ok2: {D1.inert.ok(tree2) == True{} : Bool}
  for e: {D1.inert.node(tree) == D1.inert.node(tree2) : Tree.Node}
  {Strict.check(Src.Src{path, text, toks, tree, bound, items})
    == Strict.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# an item as doc reads it: its kind, name and line, and nothing it says
def inert.item(it: Outline.Item) -> Outline.Item:
  match it:
    case Outline.Item{k, n, l, _s, _d, _p}:
      Outline.Item{k, n, l, "", "", ""}

# the items, each as doc reads it
def inert.items(its: List<&2, Outline.Item>) -> List<&2, Outline.Item>:
  match its:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      inert.item(h) <> inert.items(t)

# how a line starts, as doc reads it: with `#`, with `@`, or with neither
type inert.Lead is Data:
  LHash{}
  LAt{}
  LPlain{}

# how a line starts, from whether it starts with `#` and whether with `@`
def inert.lead(hash: Bool, at: Bool) -> inert.Lead:
  match hash:
    case True{}:
      LHash{}
    case False{}:
      match at:
        case True{}:
          LAt{}
        case False{}:
          LPlain{}

# how each line starts
def inert.leads(ls: List<&2, String>) -> List<&2, inert.Lead>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      inert.lead(String.starts_with(h, "#"), String.starts_with(h, "@")) <> inert.leads(t)

# LAW: doc reads no comment or string: two sources whose items have the same
# kinds, names and lines, and whose lines (one that starts inside a string
# literal read as empty) start with `#` alike and with `@` alike, have the
# same findings, what their comments and strings say aside
law inert_doc:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +text2: String
  for +toks2: List<&2, Lex.Tok>
  for tree2: Tree.Node
  for bound2: Bind.Bound
  for +items2: List<&2, Outline.Item>
  for ei: {inert.items(items) == inert.items(items2) : List<&2, Outline.Item>}
  for el: {inert.leads(Doc.lines(text, toks)) == inert.leads(Doc.lines(text2, toks2)) : List<&2, inert.Lead>}
  {Doc.check(Src.Src{path, text, toks, tree, bound, items})
    == Doc.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# a binder as param reads it: its note with each string literal cut
def inert.bind(bb: Bind.Bind) -> Bind.Bind:
  match bb:
    case Bind.Bind{n, l, c, k, +note}:
      Bind.Bind{n, l, c, k, T.code(note)}

# the binders, each as param reads it
def inert.binds(bs: List<&2, Bind.Bind>) -> List<&2, Bind.Bind>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      inert.bind(h) <> inert.binds(t)

# LAW: param reads a note with its string literals cut to their quote: two
# binder lists alike in each binder's name, position, kind and note so read
# have the same findings, what their strings say aside
law inert_param:
  for +b1: List<&2, Bind.Bind>
  for +b2: List<&2, Bind.Bind>
  for +path: String
  for e: {inert.binds(b1) == inert.binds(b2) : List<&2, Bind.Bind>}
  {Param.check.on(b1, path) == Param.check.on(b2, path) : List<&2, F.Finding>}

# LAW: table reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings (a
# string's text is only ever compared with a call's or a table's name)
law inert_table:
  for +path: String
  for text: String
  for +tree: Tree.Node
  for toks: List<&2, Lex.Tok>
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for +tree2: Tree.Node
  for toks2: List<&2, Lex.Tok>
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for +ok: {D1.inert.ok(tree) == True{} : Bool}
  for +ok2: {D1.inert.ok(tree2) == True{} : Bool}
  for e: {D1.inert.node(tree) == D1.inert.node(tree2) : Tree.Node}
  {Table.check(Src.Src{path, text, toks, tree, bound, items})
    == Table.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: index reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings
law inert_index:
  for +path: String
  for text: String
  for +tree: Tree.Node
  for toks: List<&2, Lex.Tok>
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for +tree2: Tree.Node
  for toks2: List<&2, Lex.Tok>
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for +ok: {D1.inert.ok(tree) == True{} : Bool}
  for +ok2: {D1.inert.ok(tree2) == True{} : Bool}
  for e: {D1.inert.node(tree) == D1.inert.node(tree2) : Tree.Node}
  {Index.check(Src.Src{path, text, toks, tree, bound, items})
    == Index.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: concat reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings
law inert_concat:
  for +path: String
  for text: String
  for +tree: Tree.Node
  for toks: List<&2, Lex.Tok>
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for +tree2: Tree.Node
  for toks2: List<&2, Lex.Tok>
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for +ok: {D1.inert.ok(tree) == True{} : Bool}
  for +ok2: {D1.inert.ok(tree2) == True{} : Bool}
  for e: {D1.inert.node(tree) == D1.inert.node(tree2) : Tree.Node}
  {Concat.check(Src.Src{path, text, toks, tree, bound, items})
    == Concat.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: unit reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings
law inert_unit:
  for +path: String
  for text: String
  for +tree: Tree.Node
  for toks: List<&2, Lex.Tok>
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for +tree2: Tree.Node
  for toks2: List<&2, Lex.Tok>
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for +ok: {D1.inert.ok(tree) == True{} : Bool}
  for +ok2: {D1.inert.ok(tree2) == True{} : Bool}
  for e: {D1.inert.node(tree) == D1.inert.node(tree2) : Tree.Node}
  {UnitRule.check(Src.Src{path, text, toks, tree, bound, items})
    == UnitRule.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: thunk reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings
law inert_thunk:
  for +path: String
  for text: String
  for +tree: Tree.Node
  for toks: List<&2, Lex.Tok>
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for +tree2: Tree.Node
  for toks2: List<&2, Lex.Tok>
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for +ok: {D1.inert.ok(tree) == True{} : Bool}
  for +ok2: {D1.inert.ok(tree2) == True{} : Bool}
  for e: {D1.inert.node(tree) == D1.inert.node(tree2) : Tree.Node}
  {Thunk.check(Src.Src{path, text, toks, tree, bound, items})
    == Thunk.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: eager reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings
law inert_eager:
  for +path: String
  for text: String
  for +tree: Tree.Node
  for toks: List<&2, Lex.Tok>
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for +tree2: Tree.Node
  for toks2: List<&2, Lex.Tok>
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for +ok: {D1.inert.ok(tree) == True{} : Bool}
  for +ok2: {D1.inert.ok(tree2) == True{} : Bool}
  for e: {D1.inert.node(tree) == D1.inert.node(tree2) : Tree.Node}
  {Eager.check(Src.Src{path, text, toks, tree, bound, items})
    == Eager.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: fuel reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings
law inert_fuel:
  for +path: String
  for text: String
  for +tree: Tree.Node
  for toks: List<&2, Lex.Tok>
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for +tree2: Tree.Node
  for toks2: List<&2, Lex.Tok>
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for +ok: {D1.inert.ok(tree) == True{} : Bool}
  for +ok2: {D1.inert.ok(tree2) == True{} : Bool}
  for e: {D1.inert.node(tree) == D1.inert.node(tree2) : Tree.Node}
  {FuelRule.check(Src.Src{path, text, toks, tree, bound, items})
    == FuelRule.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: ring reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings
law inert_ring:
  for +path: String
  for text: String
  for +tree: Tree.Node
  for toks: List<&2, Lex.Tok>
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for +tree2: Tree.Node
  for toks2: List<&2, Lex.Tok>
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for +ok: {D1.inert.ok(tree) == True{} : Bool}
  for +ok2: {D1.inert.ok(tree2) == True{} : Bool}
  for e: {D1.inert.node(tree) == D1.inert.node(tree2) : Tree.Node}
  {Ring.check(Src.Src{path, text, toks, tree, bound, items})
    == Ring.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: arms reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings
law inert_arms:
  for +path: String
  for text: String
  for +tree: Tree.Node
  for toks: List<&2, Lex.Tok>
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for +tree2: Tree.Node
  for toks2: List<&2, Lex.Tok>
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for +ok: {D1.inert.ok(tree) == True{} : Bool}
  for +ok2: {D1.inert.ok(tree2) == True{} : Bool}
  for e: {D1.inert.node(tree) == D1.inert.node(tree2) : Tree.Node}
  {Arms.check(Src.Src{path, text, toks, tree, bound, items})
    == Arms.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# a binder as unused reads it: its name, position and kind, and whether its
# note opens with `-`, and nothing else the note says
def inert.ubind(bb: Bind.Bind) -> Bind.Bind:
  match bb:
    case Bind.Bind{n, l, c, k, +note}:
      Bind.Bind{n, l, c, k, Bool.pick(String, String.starts_with(note, "-"), "-", "")}

# the binders, each as unused reads it
def inert.ubinds(bs: List<&2, Bind.Bind>) -> List<&2, Bind.Bind>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      inert.ubind(h) <> inert.ubinds(t)

# LAW: unused reads no comment or string: two sources whose trees read the
# same with strings cut, with the same uses, and whose binders are alike in
# name, position, kind and a leading `-` of their notes have the same findings
law inert_unused:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +binds: List<&2, Bind.Bind>
  for +uses: List<&2, Bind.Use>
  for scopes: List<&2, Bind.Scope>
  for items: List<&2, Outline.Item>
  for text2: String
  for toks2: List<&2, Lex.Tok>
  for +tree2: Tree.Node
  for +binds2: List<&2, Bind.Bind>
  for scopes2: List<&2, Bind.Scope>
  for items2: List<&2, Outline.Item>
  for et: {D1.inert.node(tree) == D1.inert.node(tree2) : Tree.Node}
  for eb: {inert.ubinds(binds) == inert.ubinds(binds2) : List<&2, Bind.Bind>}
  {Unused.check(Src.Src{path, text, toks, tree, Bind.Bound{binds, uses, scopes}, items})
    == Unused.check(Src.Src{path, text2, toks2, tree2, Bind.Bound{binds2, uses, scopes2}, items2})
    : List<&2, F.Finding>}

# LAW: hoist reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings (a
# string's text is only ever compared with a name, a keyword or a mark)
law inert_hoist:
  for +path: String
  for text: String
  for +tree: Tree.Node
  for toks: List<&2, Lex.Tok>
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for +tree2: Tree.Node
  for toks2: List<&2, Lex.Tok>
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for +ok: {D1.inert.ok(tree) == True{} : Bool}
  for +ok2: {D1.inert.ok(tree2) == True{} : Bool}
  for e: {D1.inert.node(tree) == D1.inert.node(tree2) : Tree.Node}
  {Hoist.check(Src.Src{path, text, toks, tree, bound, items})
    == Hoist.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: scan reads what no comment or string says: two sources as the lexer
# makes them whose trees read the same with comments and strings cut have
# the same findings
law inert_scan:
  for +path: String
  for text: String
  for +tree: Tree.Node
  for toks: List<&2, Lex.Tok>
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for +tree2: Tree.Node
  for toks2: List<&2, Lex.Tok>
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for +ok: {D1.inert.ok(tree) == True{} : Bool}
  for +ok2: {D1.inert.ok(tree2) == True{} : Bool}
  for e: {D1.inert.node(tree) == D1.inert.node(tree2) : Tree.Node}
  {Scan.check(Src.Src{path, text, toks, tree, bound, items})
    == Scan.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# the tokens of each item's header, with comments and strings cut
def inert.sigs(its: List<&2, Outline.Item>) -> List<&2, List<&2, Lex.Tok>>:
  match its:
    case Nil{}:
      Nil{}
    case Con{Outline.Item{_k, _n, _l, s, _d, _p}, t}:
      D1.inert.toks(Lex.tokens(s)) <> inert.sigs(t)

# LAW: wrap reads no comment or string: two sources whose items have the same
# kinds, names and lines, and whose headers' tokens read the same with
# comments and strings cut, have the same findings
law inert_wrap:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  for text2: String
  for toks2: List<&2, Lex.Tok>
  for tree2: Tree.Node
  for bound2: Bind.Bound
  for +items2: List<&2, Outline.Item>
  for ei: {inert.items(items) == inert.items(items2) : List<&2, Outline.Item>}
  for es: {inert.sigs(items) == inert.sigs(items2) : List<&2, List<&2, Lex.Tok>>}
  {Wrap.check(Src.Src{path, text, toks, tree, bound, items})
    == Wrap.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}
