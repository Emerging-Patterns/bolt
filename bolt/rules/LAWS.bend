# bolt/rules: the laws. Each rule is a pure function of the source it is
# handed, so its laws quantify over that source, never over one fixture.
import Base
import ../../syntax/lex.bend as Lex
import ../finding.bend as F
import ./suspicious/nat.bend as NatRule
import ./correctness/escape.bend as Esc
import ./correctness/put.bend as Put
import ./correctness/hole.bend as Hole
import ./style/param.bend as Param
import ../../syntax/bind.bend as Bind
import ../paths.bend as Paths
import ./laws/trace.bend as Trace
import ./digest.bend as Digest
import ./style/space.bend as Space
import ../src.bend as Src
import ../../syntax/tree.bend as Tree
import ../../syntax/outline.bend as Outline
import ./style/doc.bend as Doc
import ./correctness/pick.bend as Pick
import ./pedantic/tail.bend as Tail
import ./suspicious/concat.bend as Concat
import ./suspicious/eager.bend as Eager
import ./suspicious/rewalk.bend as Rewalk
import ./suspicious/strict.bend as Strict
import ./suspicious/hoist.bend as Hoist
import ./suspicious/index.bend as Index
import ./suspicious/ring.bend as Ring
import ./suspicious/table.bend as Table
import ./suspicious/unit.bend as UnitRule
import ./correctness/chars.bend as Chars
import ./correctness/strings.bend as Strings
import ./calls.bend as Calls
import ./correctness/foreign.bend as Foreign
import ./tokens.bend as T
import ./correctness/arms.bend as Arms
import ./correctness/twice.bend as Twice

# how many tokens are Nat literals of 1000 or more
def big_count(toks: List<&2, Lex.Tok>) -> Nat:
  match toks:
    case Nil{}:
      0n
    case Con{Lex.Tok{Lex.TNum{}, +t, l, c}, rest}:
      +m = big_count(rest)
      Bool.pick(Nat, NatRule.big(t), 1n+m, m)
    case Con{h, rest}:
      big_count(rest)

# LAW: nat reports one finding for each Nat literal of 1000 or more, and none
# for any other token: a comment, a string, a U32 or a small Nat
# BOLT-RULE-U005
law nat_counts:
  for toks: List<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, NatRule.check.go(toks, path)) == big_count(toks) : Nat}

# 1 when the Syms open with a digit (`0` included), else 0
def nul_lead(ss: List<&2, Esc.Sym>) -> Nat:
  match ss:
    case Con{Esc.SZero{}, t}:
      1n
    case Con{Esc.SDigit{d}, t}:
      1n
    case other:
      0n

# how many `\0`s a literal holds with a digit right after, its escapes read
# as Bend reads them: a backslash and the one char after it
def nul_count(ss: List<&2, Esc.Sym>) -> Nat:
  match ss:
    case Con{Esc.SSlash{}, Con{Esc.SZero{}, +rest}}:
      Nat.add(nul_lead(rest), nul_count(rest))
    case Con{Esc.SSlash{}, Con{e, rest}}:
      nul_count(rest)
    case Con{s, rest}:
      nul_count(rest)
    case Nil{}:
      0n

# how many such escapes the string and char literals among the tokens hold
def esc_count(toks: List<&2, Lex.Tok>) -> Nat:
  match toks:
    case Con{Lex.Tok{Lex.TStr{}, t, l, c}, rest}:
      Nat.add(nul_count(Esc.syms(String.to_list(t))), esc_count(rest))
    case Con{Lex.Tok{Lex.TChar{}, t, l, c}, rest}:
      Nat.add(nul_count(Esc.syms(String.to_list(t))), esc_count(rest))
    case Con{h, rest}:
      esc_count(rest)
    case Nil{}:
      0n

# LAW: escape reports one finding for each `\0` then a digit in a literal,
# its escapes read a backslash and one char at a time, and none elsewhere in it
# BOLT-RULE-C006
law escape_scan_counts:
  for ss: List<&2, Esc.Sym>
  for +path: String
  for +line: U32
  for +col: U32
  {List.length(&2, F.Finding, Esc.scan(ss, path, line, col)) == nul_count(ss) : Nat}

# LAW: escape reports exactly those escapes of the string and char literals,
# and nothing for any other token: a comment or code never has one
# BOLT-RULE-C006
law escape_counts:
  for toks: List<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Esc.check.go(toks, path)) == esc_count(toks) : Nat}

# one char, and a capital
def one_upper(cs: List<&2, Char>) -> Bool:
  match cs:
    case Con{ch, Nil{}}:
      Char.is_upper(ch)
    case Con{ch, Con{d2, r}}:
      False{}
    case Nil{}:
      False{}

# a parameter binder shorter than 2 chars that is neither one capital (a type
# parameter) nor bare or typed `: Quant` (a quantity)
def too_short(kk: Bind.BindKind, +nm: String, +note: String) -> Bool:
  match kk:
    case Bind.KParam{}:
      Bool.and(Nat.is_lt(String.length(nm), 2n),
        Bool.not(Bool.or(one_upper(String.to_list(nm)),
          Bool.or(Bool.not(String.contains(note, ":")), String.ends_with(note, ": Quant")))))
    case other:
      False{}

# how many binders are parameters too short
def short_count(binds: List<&2, Bind.Bind>) -> Nat:
  match binds:
    case Nil{}:
      0n
    case Con{Bind.Bind{+nm, line, col, kk, +note}, rest}:
      +m = short_count(rest)
      Bool.pick(Nat, too_short(kk, nm, note), 1n+m, m)

# LAW: over the binder list, param reports one finding for each parameter
# binder shorter than 2 chars that is neither one capital nor bare or typed
# `: Quant`, none for any other binder, and none at all in a PROOF.bend
# BOLT-RULE-S004
law param_counts:
  for binds: List<&2, Bind.Bind>
  for +path: String
  {List.length(&2, F.Finding, Param.check.on(binds, path))
    == Bool.pick(Nat, Paths.is_proof(path), 0n, short_count(binds)) : Nat}

# True when tt is `Map.put` and the tokens open with a `(` token
def put_open(+tt: String, toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Con{Lex.Tok{Lex.TOpen{}, +o, l, c}, rest}:
      Bool.and(String.eq(tt, "Map.put"), String.eq(o, "("))
    case Con{h, rest}:
      False{}
    case Nil{}:
      False{}

# how many `Map.put` tokens have a `(` token right after them
def put_count(toks: List<&2, Lex.Tok>) -> Nat:
  match toks:
    case Nil{}:
      0n
    case Con{Lex.Tok{Lex.TDotted{}, +t, l, c}, +rest}:
      +m = put_count(rest)
      Bool.pick(Nat, put_open(t, rest), 1n+m, m)
    case Con{h, rest}:
      put_count(rest)

# True when the first token's text is `Map.put`
def put_named(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Con{Lex.Tok{k, +t, l, c}, rest}:
      String.eq(t, "Map.put")
    case Nil{}:
      False{}

# True when some `def` keyword has a `Map.put` token right after it
def put_defined(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Nil{}:
      False{}
    case Con{Lex.Tok{Lex.TKey{}, +t, l, c}, +rest}:
      +m = put_defined(rest)
      Bool.or(Bool.and(String.eq(t, "def"), put_named(rest)), m)
    case Con{h, rest}:
      put_defined(rest)

# LAW: over the significant tokens, put reports one finding for each
# `Map.put` token with a `(` token right after it, and none at all when a
# `def` keyword has a `Map.put` token right after it
# BOLT-RULE-C004
law put_counts:
  for +toks: List<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Put.check.on(toks, path))
    == Bool.pick(Nat, put_defined(toks), 0n, put_count(toks)) : Nat}

# True when the first token past spaces, newlines and comments is `TODO`
def todo_next(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Con{Lex.Tok{Lex.TSpace{}, t, l, c}, rest}:
      todo_next(rest)
    case Con{Lex.Tok{Lex.TNewline{}, t, l, c}, rest}:
      todo_next(rest)
    case Con{Lex.Tok{Lex.TComment{}, t, l, c}, rest}:
      todo_next(rest)
    case Con{Lex.Tok{Lex.TUpper{}, +t, l, c}, rest}:
      String.eq(t, "TODO")
    case other:
      False{}

# how many `?` tokens have `TODO` next past spaces, newlines and comments
def hole_count(toks: List<&2, Lex.Tok>) -> Nat:
  match toks:
    case Nil{}:
      0n
    case Con{Lex.Tok{Lex.TOp{}, +q, l, c}, +rest}:
      +m = hole_count(rest)
      Bool.pick(Nat, Bool.and(String.eq(q, "?"), todo_next(rest)), 1n+m, m)
    case Con{h, rest}:
      hole_count(rest)

# LAW: hole reports one finding for each `?` token with `TODO` next past
# spaces, newlines and comments, none for any other token, and none at all in
# a LAWS.bend
# BOLT-RULE-C002
law hole_counts:
  for toks: List<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Hole.check.on(toks, path))
    == Bool.pick(Nat, Paths.is_laws(path), 0n, hole_count(toks)) : Nat}
# LAW: trace takes a pending row that names laws as it takes a proved row
# that names the same laws: each entry is checked (the law exists, has a
# binder, carries the row's tag), and the Law cell adds no finding of its own
# BOLT-LAW-5
law trace_pending_judged:
  for +id: String
  for +e: String
  for +es: List<&2, String>
  for +nn: U32
  for +sp: Trace.Spec
  for +ds: List<&2, Digest.Digest>
  {Trace.judge_row(Trace.Row{id, "Proved", "pending", e <> es, nn}, sp, ds)
    == Trace.judge_row(Trace.Row{id, "Proved", "proved", e <> es, nn}, sp, ds) : List<&2, F.Finding>}

# LAW: a pending row's level, status and Law cell are well formed whatever
# laws it names, none included
# BOLT-LAW-5
law trace_pending_shape:
  for +ls: List<&2, String>
  {Trace.shape("Proved", "pending", ls) == "" : String}

# LAW: a proved row is well formed exactly when its Law cell names a law
# BOLT-LAW-5
law trace_proved_shape:
  for +ls: List<&2, String>
  {Trace.shape("Proved", "proved", ls)
    == Bool.pick(String, List.is_empty(&2, String, ls), "a proved row names its law", "") : String}

# LAW: a Trusted row is well formed exactly when its Law cell is empty
# BOLT-LAW-5
law trace_trusted_shape:
  for +ls: List<&2, String>
  {Trace.shape("Trusted", "", ls)
    == Bool.pick(String, List.is_empty(&2, String, ls), "", "a Trusted row names no law") : String}

# LAW: a tag naming a pending row is claimed exactly as one naming a proved
# row is, so neither is a stray
# BOLT-LAW-5
law trace_pending_claimed:
  for +i: String
  for +ls: List<&2, String>
  for +n: U32
  for +rs: List<&2, Trace.Row>
  for +id: String
  {Trace.claimed(Trace.Row{i, "Proved", "pending", ls, n} <> rs, id)
    == Trace.claimed(Trace.Row{i, "Proved", "proved", ls, n} <> rs, id) : Bool}

# LAW: a Trusted row claims no tag, whatever its status: a tag naming it is
# judged by the rows after it alone
# BOLT-LAW-5
law trace_trusted_unclaimed:
  for +i: String
  for +st: String
  for +ls: List<&2, String>
  for +n: U32
  for +rs: List<&2, Trace.Row>
  for +id: String
  {Trace.claimed(Trace.Row{i, "Trusted", st, ls, n} <> rs, id) == Trace.claimed(rs, id) : Bool}

# LAW: with no rows, no ID is claimed: a tag naming an ID SPEC.md does not
# list is a stray
# BOLT-LAW-5
law trace_unlisted_unclaimed:
  for +id: String
  {Trace.claimed([], id) == False{} : Bool}

# True when the line's last char is whitespace
def ends_space(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{c, Nil{}}:
      Char.is_space(c)
    case Con{c, t}:
      ends_space(t)

# True when a tab is among the chars
def tabbed(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{c, t}:
      Bool.or(Char.is_eq(c, '\t'), tabbed(t))

# how many lines end in whitespace or hold a tab, one each
def space_count(lines: List<&2, String>) -> Nat:
  match lines:
    case Nil{}:
      0n
    case Con{+line, rest}:
      +m = space_count(rest)
      Bool.pick(Nat, Bool.or(ends_space(String.to_list(line)), tabbed(String.to_list(line))), 1n+m, m)

# LAW: over the text's lines, space reports one finding for each line that
# ends in whitespace or holds a tab, anywhere in it (a string literal or a
# `#|` line included), and none for any other line
# BOLT-RULE-S002
law space_line_counts:
  for lines: List<&2, String>
  for +path: String
  for +nn: U32
  {List.length(&2, F.Finding, Space.check.go(lines, path, nn)) == space_count(lines) : Nat}

# a token's columns: a string literal two, a `#|` comment none, a comment
# otherwise at its full width, and any other token its length
def share(kk: Lex.TokKind, +tt: String) -> U32:
  match kk:
    case Lex.TStr{}:
      2
    case Lex.TComment{}:
      Bool.pick(U32, String.starts_with(tt, "#|"), 0, U32.from_nat(String.length(tt)))
    case other:
      U32.from_nat(String.length(tt))

# the count more, one higher when a line is over 120 columns wide
def over(+width: U32, +more: Nat) -> Nat:
  Bool.pick(Nat, U32.is_gt(width, 120), 1n+more, more)

# how many lines are over 120 columns, the first already acc wide; a newline
# token closes a line
def wide_count(toks: List<&2, Lex.Tok>, +acc: U32) -> Nat:
  match toks:
    case Nil{}:
      over(acc, 0n)
    case Con{Lex.Tok{Lex.TNewline{}, t, l, c}, rest}:
      over(acc, wide_count(rest, 0))
    case Con{Lex.Tok{k, +t, l, c}, rest}:
      wide_count(rest, (acc + share(k, t) : U32))

# LAW: over the tokens, space reports one finding for each line over 120
# columns, a string literal counted as two, a comment at its full width and a
# `#|` comment as nothing, and none for any other line
# BOLT-RULE-S002
law space_width_counts:
  for toks: List<&2, Lex.Tok>
  for +path: String
  for +nn: U32
  for +acc: U32
  {List.length(&2, F.Finding, Space.widths(toks, path, nn, acc)) == wide_count(toks, acc) : Nat}

# LAW: space reports exactly those two: the lines of the text with trailing
# whitespace or a tab, then the lines of the tokens over 120 columns
# BOLT-RULE-S002
law space_counts:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Space.check(Src.Src{path, text, toks, tree, bound, items}))
    == Nat.add(space_count(String.lines(text)), wide_count(toks, 0)) : Nat}

# The header exemptions. A per-file rule whose header exempts a path (a law
# file, a proof, a test) returns no findings on it, for every source: any
# text, token list, tree, binding structure and outline. bolt/paths.bend
# decides the path by its segments.

# LAW: hole reports nothing in a LAWS.bend, whose laws are open claims, whatever the source holds
# BOLT-RULE-EXEMPT
law hole_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_laws(path) == True{} : Bool}
  {Hole.check(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: doc reports nothing in a PROOF.bend or in a file under a `tests` directory, whatever the source holds
# BOLT-RULE-EXEMPT
law doc_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Bool.or(Paths.is_proof(path), Paths.is_test(path)) == True{} : Bool}
  {Doc.check(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: param reports nothing in a PROOF.bend, whose parameters are the law's, whatever the source holds
# BOLT-RULE-EXEMPT
law param_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_proof(path) == True{} : Bool}
  {Param.check(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: pick reports nothing in a LAWS.bend or a PROOF.bend, which never run, whatever the source holds
# BOLT-RULE-EXEMPT
law pick_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_law_file(path) == True{} : Bool}
  {Pick.check(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: tail reports nothing in a LAWS.bend or a PROOF.bend, which never run, whatever the source holds
# BOLT-RULE-EXEMPT
law tail_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_law_file(path) == True{} : Bool}
  {Tail.check(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: concat reports nothing in a LAWS.bend or a PROOF.bend, which never run, whatever the source holds
# BOLT-RULE-EXEMPT
law concat_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_law_file(path) == True{} : Bool}
  {Concat.check(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: eager reports nothing in a LAWS.bend or a PROOF.bend, which never run, whatever the source holds
# BOLT-RULE-EXEMPT
law eager_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_law_file(path) == True{} : Bool}
  {Eager.check(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: rewalk reports nothing in a LAWS.bend or a PROOF.bend, which never run, whatever the source holds
# BOLT-RULE-EXEMPT
law rewalk_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_law_file(path) == True{} : Bool}
  {Rewalk.check(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: strict reports nothing in a LAWS.bend or a PROOF.bend, which never run, whatever the source holds
# BOLT-RULE-EXEMPT
law strict_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_law_file(path) == True{} : Bool}
  {Strict.check(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: hoist reports nothing in a LAWS.bend or a PROOF.bend, which never run, whatever the source holds
# BOLT-RULE-EXEMPT
law hoist_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_law_file(path) == True{} : Bool}
  {Hoist.check(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: index reports nothing in a LAWS.bend or a PROOF.bend, which never run, whatever the source holds
# BOLT-RULE-EXEMPT
law index_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_law_file(path) == True{} : Bool}
  {Index.check(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: ring reports nothing in a LAWS.bend or a PROOF.bend, which never run, whatever the source holds
# BOLT-RULE-EXEMPT
law ring_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_law_file(path) == True{} : Bool}
  {Ring.check(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: table reports nothing in a LAWS.bend or a PROOF.bend, which never run, whatever the source holds
# BOLT-RULE-EXEMPT
law table_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_law_file(path) == True{} : Bool}
  {Table.check(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: unit reports nothing in a LAWS.bend or a PROOF.bend, which never run, whatever the source holds
# BOLT-RULE-EXEMPT
law unit_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_law_file(path) == True{} : Bool}
  {UnitRule.check(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# The match rules, chars and strings. Each walks every statement of the tree
# at any depth; a match is read by the case statements of its body, and a
# case by the first node of its pattern, the node after `case` (the first
# match column). Nothing else in the tree counts.

# does a statement's kids open with the `match` keyword?
def chars.is_match(kids: Tree.Node) -> Bool:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TKey{}, +t, l, c}}, rest}:
      String.eq(t, "match")
    case other:
      False{}

# one when a case statement's first match column opens with a char literal,
# else zero
def chars.opens(kids: Tree.Node) -> U32:
  match kids:
    case Tree.NCons{k, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TChar{}, t, l, c}}, rest}}:
      1
    case other:
      0

# acc and the case statements among a match body's statements that open
# with a char literal
def chars.arms(body: Tree.Node, +acc: U32) -> U32:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, b}, rest}:
      chars.arms(rest, (acc + chars.opens(kids) : U32))
    case Tree.NCons{h, rest}:
      chars.arms(rest, acc)
    case other:
      acc

# how many statements, at any depth, are a match with more than eight arms
# opening with a char literal
def chars.count(nn: Tree.Node) -> Nat:
  match nn:
    case Tree.NCons{Tree.Stmt{kind, +kids, +body}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(chars.is_match(kids), U32.is_gt(chars.arms(body, 0), 8)), 1n, 0n),
        Nat.add(chars.count(body), chars.count(rest)))
    case Tree.NCons{h, rest}:
      chars.count(rest)
    case other:
      0n

# LAW: chars reports one finding for each match, at any depth, with more than
# eight case arms whose first match column opens with a char literal, and
# none for anything else: a literal later in a pattern or in a later column
# does not count
# BOLT-RULE-C009
law chars_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Chars.check(Src.Src{path, text, toks, tree, bound, items})) == chars.count(tree)
    : Nat}

# the chars between the quotes of the string a case statement's first match
# column opens with, when it does and the string is closed, else zero
def strings.size(kids: Tree.Node) -> U32:
  match kids:
    case Tree.NCons{k, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TStr{}, +t, l, c}}, rest}}:
      Bool.pick(U32, Strings.terminated(t), (U32.from_nat(String.length(t)) - 2 : U32), 0)
    case other:
      0

# acc and the chars of the closed string arms among a match body's statements
def strings.total(body: Tree.Node, +acc: U32) -> U32:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, b}, rest}:
      strings.total(rest, (acc + strings.size(kids) : U32))
    case Tree.NCons{h, rest}:
      strings.total(rest, acc)
    case other:
      acc

# how many statements, at any depth, are a match whose closed string arms
# total over 64 chars
def strings.count(nn: Tree.Node) -> Nat:
  match nn:
    case Tree.NCons{Tree.Stmt{kind, +kids, +body}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(chars.is_match(kids), U32.is_gt(strings.total(body, 0), 64)), 1n, 0n),
        Nat.add(strings.count(body), strings.count(rest)))
    case Tree.NCons{h, rest}:
      strings.count(rest)
    case other:
      0n

# LAW: strings reports one finding for each match, at any depth, whose case
# arms opening their first match column with a closed string literal total
# over 64 chars between their quotes, and none for anything else: an
# unclosed string or one in a later column does not count
# BOLT-RULE-C008
law strings_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Strings.check(Src.Src{path, text, toks, tree, bound, items})) == strings.count(tree)
    : Nat}

# tail (BOLT-RULE-P001). Over a def's statements the rule reports each call
# `name(..)` of the def itself, except inside a `Bool.pick(..)` and except
# when the call is a statement's whole chain (a tail call); over the file it
# does that for each def whose first live parameter is a List or a String
# (Calls.seq) and that is not exempt (a law file, or a def returning a
# proof), the call shrinking that parameter or not.

# a statement's chain is exactly a call of the name, `name(..)`, and nothing more
def tail.whole(kids: Tree.Node, +name: String) -> Bool:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{j, +o, m, n}, g, e}, Tree.NNil{}}}:
      Bool.and(String.eq(t, name), String.eq(o, "("))
    case other:
      False{}

# how many self-calls of the name sit under the node: outside any
# `Bool.pick(..)`, and not counting the chain's head call when whole says the
# chain is a statement's whole chain
def tail.count(nn: Tree.Node, +name: String, whole: Bool) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_k, +o, _l, _c}, kids, _e}, rest}}:
      +call = String.eq(o, "(")
      +m = Nat.add(Bool.pick(Nat, Bool.and(call, String.eq(t, "Bool.pick")), 0n, tail.count(kids, name, False{})),
        tail.count(rest, name, False{}))
      Bool.pick(Nat, Bool.and(Bool.and(call, String.eq(t, name)), Bool.not(whole)), 1n+m, m)
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      Nat.add(tail.count(kids, name, False{}), tail.count(rest, name, False{}))
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      Nat.add(tail.count(kids, name, tail.whole(kids, name)),
        Nat.add(tail.count(body, name, False{}), tail.count(rest, name, False{})))
    case Tree.NCons{h, rest}:
      tail.count(rest, name, False{})
    case other:
      0n

# how many non-tail self-calls the defs hold, over the defs that walk a List
# or a String and are not exempt
def tail.total(ds: List<&2, Calls.Def>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, body}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(Calls.seq(sig), Bool.not(Calls.exempt(path, sig))),
        tail.count(body, name, False{}), 0n), tail.total(rest, path))

# LAW: over a def's statements, tail reports one finding for each self-call
# outside any `Bool.pick(..)` that is not a statement's whole chain, and
# none for anything else
# BOLT-RULE-P001
law tail_walk_counts:
  for nn: Tree.Node
  for +name: String
  for +path: String
  for skip: Bool
  {List.length(&2, F.Finding, Tail.walk(nn, name, path, skip)) == tail.count(nn, name, skip) : Nat}

# LAW: tail reports exactly those self-calls of each of the file's defs whose
# first live parameter is a List or a String and that is not exempt, and
# none in any other def
# BOLT-RULE-P001
law tail_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Tail.check(Src.Src{path, text, toks, tree, bound, items}))
    == tail.total(Calls.defs(tree), path) : Nat}

# foreign (BOLT-RULE-C010). Over the file's top-level statements the rule
# reports each def whose body is one import or more and nothing else (a
# foreign def) and whose imports name a `.c` body and no `.js` one, unless the
# file is headed `# lanes: native`, or a `.js` body and no `.c` one. Headed
# means the exact line is among the file's leading comment lines, those before
# its first line that does not start with `#`. An import's path is its first
# string literal (Foreign.target).

# every statement of the body is an import, none at all included
def foreign.imports(body: Tree.Node) -> Bool:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SImport{}, kids, ib}, rest}:
      foreign.imports(rest)
    case Tree.NCons{h, rest}:
      False{}
    case other:
      True{}

# a foreign def's body: one import or more, and nothing else
def foreign.only(body: Tree.Node) -> Bool:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SImport{}, kids, ib}, rest}:
      foreign.imports(rest)
    case other:
      False{}

# some import of the body names a path ending in the suffix (quoted: `.c"`)
def foreign.has(body: Tree.Node, +ext: String) -> Bool:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SImport{}, kids, ib}, rest}:
      Bool.or(String.ends_with(Foreign.target(kids), ext), foreign.has(rest, ext))
    case Tree.NCons{h, rest}:
      foreign.has(rest, ext)
    case other:
      False{}

# a foreign def with a `.c` body and no `.js` one (in a file not native only),
# or with a `.js` body and no `.c` one
def foreign.bad(+body: Tree.Node, +native: Bool) -> Bool:
  +cc = foreign.has(body, ".c\"")
  +js = foreign.has(body, ".js\"")
  Bool.and(foreign.only(body),
    Bool.or(Bool.and(cc, Bool.and(Bool.not(js), Bool.not(native))), Bool.and(js, Bool.not(cc))))

# how many of the file's top-level defs are foreign defs missing a lane
def foreign.count(root: Tree.Node, +native: Bool) -> Nat:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest}:
      +m = foreign.count(rest, native)
      Bool.pick(Nat, foreign.bad(body, native), 1n+m, m)
    case Tree.NCons{h, rest}:
      foreign.count(rest, native)
    case other:
      0n

# the exact line `# lanes: native` is among the leading lines that start with `#`
def foreign.headed(lines: List<&2, String>) -> Bool:
  match lines:
    case Nil{}:
      False{}
    case Con{+line, rest}:
      Bool.and(String.starts_with(line, "#"), Bool.or(String.eq(line, "# lanes: native"), foreign.headed(rest)))

# LAW: a file is native only exactly when the line `# lanes: native` is one
# of its leading comment lines; the line anywhere later does not count
# BOLT-RULE-C010
law foreign_native:
  for lines: List<&2, String>
  {Foreign.native_only.go(lines) == foreign.headed(lines) : Bool}

# LAW: over the file's top-level statements, foreign reports one finding for
# each foreign def with a `.c` body and no `.js` one (none needed in a native
# only file) or a `.js` body and no `.c` one, and none for anything else
# BOLT-RULE-C010
law foreign_walk_counts:
  for root: Tree.Node
  for +native: Bool
  for +path: String
  {List.length(&2, F.Finding, Foreign.check.go(root, native, path)) == foreign.count(root, native) : Nat}

# LAW: foreign reports exactly those defs of the file, native only when its
# leading comment lines say so
# BOLT-RULE-C010
law foreign_counts:
  for +path: String
  for +text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Foreign.check(Src.Src{path, text, toks, tree, bound, items}))
    == foreign.count(tree, foreign.headed(String.lines(text))) : Nat}

# The match rules arms and twice read a case statement's pattern: its tokens
# after `case` in the tree (T.pattern), the first match column first.

# after a Nat literal, `+ p :`: the arm matches every Nat from the literal up
def arms.plus(rest: Tree.Node) -> Bool:
  match rest:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, +o, l, c}},
        Tree.NCons{Tree.Leaf{Lex.Tok{b, p, l2, c2}}, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, s, l3, c3}}, more}}}:
      String.eq(o, "+")
    case other:
      False{}

# after a Nat literal, `:`: the arm matches the literal alone
def arms.exact(rest: Tree.Node) -> Bool:
  match rest:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, s, l, c}}, more}:
      True{}
    case other:
      False{}

# a name or `_`: what `Succ{..}` binds when it matches every Nat from 1 up
def arms.binder(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TName{}:
      True{}
    case Lex.TWild{}:
      True{}
    case other:
      False{}

# `Succ{x}` with x one name or `_`: every Nat from 1 up
def arms.succ(+tt: String, kk: Lex.TokKind) -> Bool:
  Bool.and(String.eq(tt, "Succ"), arms.binder(kk))

# a Nat literal's value k, when what follows it makes the arm one that counts
def arms.num(mm: Maybe<&2, U32>, +when: Bool) -> Maybe<&2, U32>:
  match mm:
    case None{}:
      None{}
    case Some{k}:
      Bool.pick(Maybe<&2, U32>, when, Some{k}, None{})

# k when the pattern matches every Nat from k up: `kn+p:`, or `Succ{p}` and
# `Succ{_}` (k is 1); none for any other pattern
def arms.from(pat: Tree.Node) -> Maybe<&2, U32>:
  match pat:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, +t, l, c}}, rest}:
      arms.num(T.nat_value(t), arms.plus(rest))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, +t, l, c}},
        Tree.NCons{Tree.Group{open, Tree.NCons{Tree.Leaf{Lex.Tok{k, p, l2, c2}}, Tree.NNil{}}, close}, more}}:
      Bool.pick(Maybe<&2, U32>, arms.succ(t, k), Some{1}, None{})
    case other:
      None{}

# the least Nat a Nat arm matches: k for `kn:` and `kn+p:`, 1 for `Succ{p}`
# and `Succ{_}`; none for any other pattern
def arms.least(pat: Tree.Node) -> Maybe<&2, U32>:
  match pat:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, +t, l, c}}, +rest}:
      arms.num(T.nat_value(t), Bool.or(arms.plus(rest), arms.exact(rest)))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, +t, l, c}},
        Tree.NCons{Tree.Group{open, Tree.NCons{Tree.Leaf{Lex.Tok{k, p, l2, c2}}, Tree.NNil{}}, close}, more}}:
      Bool.pick(Maybe<&2, U32>, arms.succ(t, k), Some{1}, None{})
    case other:
      None{}

# an arm is covered when its least Nat is at or above low, the least k of the
# from-k-up arms above it
def arms.hit(low: Maybe<&2, U32>, least: Maybe<&2, U32>) -> Bool:
  match low least:
    case None{} m:
      False{}
    case Some{k} None{}:
      False{}
    case Some{k} Some{j}:
      U32.is_ge(j, k)

# the least k of the from-k-up arms so far, once one more arm is read
def arms.lower(low: Maybe<&2, U32>, from: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match low from:
    case None{} f:
      f
    case Some{k} None{}:
      Some{k}
    case Some{+k} Some{+j}:
      Bool.pick(Maybe<&2, U32>, U32.is_lt(j, k), Some{j}, Some{k})

# how many of a match's case arms an earlier from-k-up arm already covers,
# low the least k of those above them
def arms.covered(body: Tree.Node, +low: Maybe<&2, U32>) -> Nat:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, b}, rest}:
      +pat = T.pattern(kids)
      +m = arms.covered(rest, arms.lower(low, arms.from(pat)))
      Bool.pick(Nat, arms.hit(low, arms.least(pat)), 1n+m, m)
    case Tree.NCons{h, rest}:
      arms.covered(rest, low)
    case other:
      0n

# a statement's own tokens are `match x:`: one scrutinee
def arms.single(kids: Tree.Node) -> Bool:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TKey{}, +t, l, c}},
        Tree.NCons{x, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, s, l2, c2}}, Tree.NNil{}}}}:
      String.eq(t, "match")
    case other:
      False{}

# how many covered arms the single-scrutinee matches under the node hold, at
# any depth
def arms_count(nn: Tree.Node) -> Nat:
  match nn:
    case Tree.NCons{Tree.Stmt{kind, kids, +body}, rest}:
      Nat.add(Bool.pick(Nat, arms.single(kids), arms.covered(body, None{}), 0n),
        Nat.add(arms_count(body), arms_count(rest)))
    case Tree.NCons{h, rest}:
      arms_count(rest)
    case other:
      0n

# LAW: arms reports one finding for each case arm of a single-scrutinee
# match, at any depth, whose least Nat an earlier `kn+p`, `Succ{p}` or
# `Succ{_}` arm of the same match already matches, and none for any other arm
# BOLT-RULE-C005
law arms_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Arms.check(Src.Src{path, text, toks, tree, bound, items})) == arms_count(tree) : Nat}

# the text of the literal a list pattern opens with: `x <> ..` or `Con{x, ..}`
def twice.first(pat: Tree.Node) -> Maybe<&2, String>:
  match pat:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.Leaf{Lex.Tok{k2, +o, l2, c2}}, rest}}:
      Bool.pick(Maybe<&2, String>, Bool.and(T.is_lit(k), String.eq(o, "<>")), Some{t}, None{})
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, +t, l, c}},
        Tree.NCons{Tree.Group{open, Tree.NCons{Tree.Leaf{Lex.Tok{k, x, l2, c2}}, kids}, close}, rest}}:
      Bool.pick(Maybe<&2, String>, Bool.and(String.eq(t, "Con"), T.is_lit(k)), Some{x}, None{})
    case other:
      None{}

# a list pattern past its first element: past `x <>`, or past `Con{x,`
def twice.after(pat: Tree.Node) -> Tree.Node:
  match pat:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}},
        Tree.NCons{Tree.Group{open, Tree.NCons{x, Tree.NCons{comma, kids}}, close}, rest}}:
      kids
    case Tree.NCons{x, Tree.NCons{op, rest}}:
      rest
    case other:
      Tree.NNil{}

# two literals, both there and the same text
def twice.same(aa: Maybe<&2, String>, bb: Maybe<&2, String>) -> Bool:
  match aa bb:
    case Some{x} Some{y}:
      String.eq(x, y)
    case a2 b2:
      False{}

# a list pattern that opens with the same literal twice
def twice.dup(+pat: Tree.Node) -> Bool:
  twice.same(twice.first(pat), twice.first(twice.after(pat)))

# how many case statements under the node, at any depth, hold a pattern that
# opens with the same literal twice
def twice.cases(nn: Tree.Node) -> Nat:
  match nn:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, body}, rest}:
      Nat.add(Bool.pick(Nat, twice.dup(T.pattern(kids)), 1n, 0n), Nat.add(twice.cases(body), twice.cases(rest)))
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      Nat.add(twice.cases(body), twice.cases(rest))
    case Tree.NCons{h, rest}:
      twice.cases(rest)
    case other:
      0n

# a def's such case statements, when its body calls it, `name(..)`
def twice.def(mm: Maybe<&2, String>, +body: Tree.Node) -> Nat:
  match mm:
    case None{}:
      0n
    case Some{+name}:
      Bool.pick(Nat, Calls.calls(body, name), twice.cases(body), 0n)

# how many such case statements the top-level defs that call themselves hold
def twice_count(root: Tree.Node) -> Nat:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest}:
      Nat.add(twice.def(Bind.declared(kids), body), twice_count(rest))
    case Tree.NCons{h, rest}:
      twice_count(rest)
    case other:
      0n

# LAW: twice reports one finding for each case statement, at any depth under
# a top-level def whose body calls the def, whose pattern (read from its first
# column) opens with the same literal twice, and none for any other
# BOLT-RULE-C007
law twice_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Twice.check(Src.Src{path, text, toks, tree, bound, items})) == twice_count(tree) : Nat}

# The eager Bool combinators: pick (BOLT-RULE-C003) and strict
# (BOLT-RULE-U002). Both walk each def's body in the tree and look for a
# self-call, the def's own name followed by a `(` group (Calls.calls),
# counted here over every chain the walk can meet.

# does a branch of a pick, its third or fourth argument, call the def?
def pick.branch(+as: List<&2, Tree.Node>, +name: String) -> Bool:
  Bool.or(Calls.calls(Calls.arg(as, 2n), name), Calls.calls(Calls.arg(as, 3n), name))

# is argument nth of `Bool.pick(T, c, a, b)` a branch: a or b?
def pick.branch_arg(nth: Nat) -> Bool:
  match nth:
    case 2n:
      True{}
    case 3n:
      True{}
    case other:
      False{}

# is the token a top-level comma, which starts the next argument?
def pick.comma(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TComma{}:
      True{}
    case other:
      False{}

# the argument after a token: one further past a comma
def pick.step(kk: Lex.TokKind, +nth: Nat) -> Nat:
  Bool.pick(Nat, pick.comma(kk), 1n+nth, nth)

# argument nth of a group is quiet when the group is (quiet), or when it is
# a branch of a pick counted (hush)
def pick.hushed(+quiet: Bool, +hush: Bool, nth: Nat) -> Bool:
  Bool.or(quiet, Bool.and(hush, pick.branch_arg(nth)))

# how many `Bool.pick` calls in the chain, at any depth, call the def in a
# branch and are not quiet: a pick in a branch of a pick counted is not
# counted again, one in its condition is. The chain is argument nth of a
# group with quiet and hush
def pick.count(nn: Tree.Node, +name: String, +quiet: Bool, +hush: Bool, +nth: Nat) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.Group{open, +kids, close}, rest}}:
      +at = pick.step(k, nth)
      +q = pick.hushed(quiet, hush, at)
      +hit = Bool.and(String.eq(t, "Bool.pick"), Bool.and(Bool.not(q), pick.branch(Calls.args(kids), name)))
      +m = Nat.add(pick.count(kids, name, q, hit, 0n), pick.count(rest, name, quiet, hush, at))
      Bool.pick(Nat, hit, 1n+m, m)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, rest}:
      pick.count(rest, name, quiet, hush, pick.step(k, nth))
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      Nat.add(pick.count(kids, name, pick.hushed(quiet, hush, nth), False{}, 0n), pick.count(rest, name, quiet, hush,
        nth))
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      Nat.add(pick.count(kids, name, pick.hushed(quiet, hush, nth), False{}, 0n),
        Nat.add(pick.count(body, name, pick.hushed(quiet, hush, nth), False{}, 0n), pick.count(rest, name, quiet, hush,
          nth)))
    case Tree.NCons{h, rest}:
      pick.count(rest, name, quiet, hush, nth)
    case other:
      0n

# LAW: the rule's quiet for argument nth of a group is the law's: the
# group's quiet, hushed too in a branch (the third or fourth argument)
# BOLT-RULE-C003
law pick_mute:
  for +quiet: Bool
  for +hush: Bool
  for nth: Nat
  {Pick.mute(quiet, hush, nth) == pick.hushed(quiet, hush, nth) : Bool}

# LAW: the rule moves to the next argument exactly past a comma
# BOLT-RULE-C003
law pick_next:
  for kk: Lex.TokKind
  for +nth: Nat
  {Pick.next(kk, nth) == pick.step(kk, nth) : Nat}

# LAW: over any chain, pick reports one finding for each `Bool.pick(..)` whose
# third or fourth argument calls the def, in both or in one, none for a pick
# inside a branch of one it reported, and one for a pick in its condition
# BOLT-RULE-C003
law pick_walk_counts:
  for nn: Tree.Node
  for +name: String
  for +path: String
  for +quiet: Bool
  for +hush: Bool
  for +nth: Nat
  {List.length(&2, F.Finding, Pick.walk(nn, name, path, quiet, hush, nth))
    == pick.count(nn, name, quiet, hush, nth) : Nat}

# LAW: a def's body is walked outside any pick's arguments
# BOLT-RULE-C003
law pick_picks_counts:
  for nn: Tree.Node
  for +name: String
  for +path: String
  for +quiet: Bool
  {List.length(&2, F.Finding, Pick.picks(nn, name, path, quiet)) == pick.count(nn, name, quiet, False{}, 0n) : Nat}

# the picks of each def of the list, none in an exempt one (a law file, a
# proof file, a def that returns a proof)
def pick.defs(ds: List<&2, Calls.Def>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, body}, rest}:
      Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n, pick.count(body, name, False{}, False{}, 0n)),
        pick.defs(rest, path))

# LAW: pick reports exactly those picks, def by def, over the defs of the tree
# BOLT-RULE-C003
law pick_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Pick.check(Src.Src{path, text, toks, tree, bound, items}))
    == pick.defs(Calls.defs(tree), path) : Nat}

# does the chain, up to its first top-level comma or `=>`, hold a `&&` or
# `||` operator (a stretch that is an operand of one)? A `=>` ends the
# stretch on its left, so a lambda body's operators never reach back past it
def strict.ops(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, rest}:
      False{}
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}}, rest}:
      False{}
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, +t, l, c}}, rest}:
      Bool.or(Bool.or(String.eq(t, "&&"), String.eq(t, "||")), strict.ops(rest))
    case Tree.NCons{h, rest}:
      strict.ops(rest)
    case other:
      False{}

# how many self-calls in the chain, at any depth, sit in an eager operand:
# inside the `(..)` of `Bool.and` or `Bool.or`, or in a stretch (ended by a
# comma or a `=>`) holding `&&` or `||`. outer: the enclosing group is an
# operand; hot: the current stretch is. A `=>` starts a lambda body, an
# operand only by its own `&&` or `||`; a statement's own tokens start cold,
# its body colder.
def strict.count(nn: Tree.Node, +name: String, +outer: Bool, +hot: Bool) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, +rest}:
      strict.count(rest, name, outer, Bool.or(outer, strict.ops(rest)))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}}, +rest}:
      strict.count(rest, name, outer, strict.ops(rest))
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +call = String.eq(o, "(")
      +inner = Bool.or(hot, Bool.and(call, Bool.or(String.eq(t, "Bool.and"), String.eq(t, "Bool.or"))))
      +m = Nat.add(strict.count(kids, name, inner, Bool.or(inner, strict.ops(kids))),
        strict.count(rest, name, outer, hot))
      Bool.pick(Nat, Bool.and(Bool.and(call, String.eq(t, name)), hot), 1n+m, m)
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      Nat.add(strict.count(kids, name, hot, Bool.or(hot, strict.ops(kids))), strict.count(rest, name, outer, hot))
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      Nat.add(strict.count(kids, name, False{}, strict.ops(kids)),
        Nat.add(strict.count(body, name, False{}, False{}), strict.count(rest, name, outer, hot)))
    case Tree.NCons{h, rest}:
      strict.count(rest, name, outer, hot)
    case other:
      0n

# LAW: over any chain, strict reports one finding for each self-call in an
# eager operand, matched by its exact text, and none for any other call
# BOLT-RULE-U002
law strict_walk_counts:
  for nn: Tree.Node
  for +name: String
  for +path: String
  for +outer: Bool
  for +hot: Bool
  {List.length(&2, F.Finding, Strict.walk(nn, name, path, outer, hot)) == strict.count(nn, name, outer, hot) : Nat}

# the self-calls in operands of each def of the list, none in an exempt one
def strict.defs(ds: List<&2, Calls.Def>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, body}, rest}:
      Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n, strict.count(body, name, False{}, False{})),
        strict.defs(rest, path))

# LAW: strict reports exactly those self-calls, def by def, over the defs of
# the tree, each body starting cold
# BOLT-RULE-U002
law strict_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Strict.check(Src.Src{path, text, toks, tree, bound, items}))
    == strict.defs(Calls.defs(tree), path) : Nat}

# The table rules: table (BOLT-RULE-U008) and ring (BOLT-RULE-U010). Each
# reads each def of the file whose body calls it, `name(..)` (Calls.calls),
# and is not exempt, and walks that body at any depth: a call site is a name
# token then a group.

# table: is the call `List.get(..)` or `List.set(..)` whose index (argument
# 3, counting `&2` and the type) is not one number token (Table.literal) and
# whose list (argument 2) is a fixed table (Table.owns): a list literal with
# a top-level comma, a `[v : T*n]` or `[v : T^n]` array sized by a number, or
# `List.replicate` / `Array.new` / `List.range` with a number count, written
# inline, as `name()` or `name` for a def of the file whose body is one such
# table (Table.modules), or as a use of a name whose let in scope binds one
# (Table.scope). A let reaches the statements after it and their blocks, not
# an enclosing block or a sibling case arm, and a later let of the name to
# anything else ends it; a case pattern, a lambda or a parameter binding the
# same name does not end it.
def table.site(+tt: String, +op: String, kids: Tree.Node, +fixed: List<&2, String>) -> Bool:
  +as = Calls.args(kids)
  Bool.and(Bool.and(String.eq(op, "("), Bool.or(String.eq(tt, "List.get"), String.eq(tt, "List.set"))),
    Bool.and(Bool.not(Table.literal(Calls.arg(as, 3n))), Table.owns(Calls.arg(as, 2n), fixed)))

# how many call sites under the node, at any depth, are a fixed-table get or
# set at a computed index
def table.count(nn: Tree.Node, +fixed: List<&2, String>) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_k, +o, _l, _c}, +kids, _e}, rest}}:
      Nat.add(Bool.pick(Nat, table.site(t, o, kids, fixed), 1n, 0n),
        Nat.add(table.count(kids, fixed), table.count(rest, fixed)))
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      Nat.add(table.count(kids, fixed), table.count(rest, fixed))
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      Nat.add(table.count(kids, fixed), Nat.add(table.count(body, fixed), table.count(rest, fixed)))
    case Tree.NCons{h, rest}:
      table.count(rest, fixed)
    case other:
      0n

# LAW: over any chain, table reports one finding for each fixed-table
# `List.get(..)` or `List.set(..)` at an index that is not one number token,
# and none for any other call: a literal index (0 and 1 included), a list
# that is not a fixed table, `List.head` and `List.tail` stay quiet
# BOLT-RULE-U008
law table_walk_counts:
  for nn: Tree.Node
  for +path: String
  for +fixed: List<&2, String>
  {List.length(&2, F.Finding, Table.walk(nn, path, fixed)) == table.count(nn, fixed) : Nat}

# the fixed-table gets and sets of each def of the list that calls itself
# and is not exempt, the tables in scope of its body
def table.defs(ds: List<&2, Calls.Def>, +mods: List<&2, String>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig))),
        table.count(body, Table.scope(body, mods)), 0n), table.defs(rest, mods, path))

# LAW: table reports exactly those gets and sets, def by def, over the defs
# of the tree that call themselves, and none in a def that does not
# BOLT-RULE-U008
law table_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Table.check(Src.Src{path, text, toks, tree, bound, items}))
    == table.defs(Calls.defs(tree), Table.modules(Calls.defs(tree), []), path) : Nat}

# ring: one when the scan found a drop, else zero
def ring.hit(mm: Maybe<&2, Lex.Tok>) -> Nat:
  match mm:
    case None{}:
      0n
    case Some{t}:
      1n

# how many self-call arguments slide the window of their own slot: argument
# i is read against parameter i only (Ring.slot_wins: that parameter, when
# it is a window), and slides when Ring.plus_scan finds, over it, a
# `List.drop` / `String.drop` of the window by a number literal or a
# `List.tail` / `String.tail` of it, that is then `++`-appended onto or is
# the receiver of `List.append` / `String.append`. What is appended is not
# measured: the drop is the fixed part.
def ring.args(as: List<&2, Tree.Node>, +params: List<&2, String>, +wins: List<&2, String>) -> Nat:
  match as:
    case Nil{}:
      0n
    case Con{h, rest}:
      +slot = Maybe.default(&2, String, List.head(&2, String, params), "")
      Nat.add(ring.hit(Ring.plus_scan(h, None{}, Ring.slot_wins(slot, wins))),
        ring.args(rest, List.tail(&2, String, params), wins))

# how many sliding arguments the self-calls `self(..)` under the node hold,
# at any depth
def ring.count(nn: Tree.Node, +self: String, +params: List<&2, String>, +wins: List<&2, String>) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_k, +o, _l, _c}, +kids, _e}, rest}}:
      Nat.add(Bool.pick(Nat, Bool.and(String.eq(o, "("), String.eq(t, self)), ring.args(Calls.args(kids), params, wins),
        0n), Nat.add(ring.count(kids, self, params, wins), ring.count(rest, self, params, wins)))
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      Nat.add(ring.count(kids, self, params, wins), ring.count(rest, self, params, wins))
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      Nat.add(ring.count(kids, self, params, wins),
        Nat.add(ring.count(body, self, params, wins), ring.count(rest, self, params, wins)))
    case Tree.NCons{h, rest}:
      ring.count(rest, self, params, wins)
    case other:
      0n

# LAW: over any chain, ring reports one finding for each argument of a
# self-call that drops and appends the window in its own parameter slot, and
# none for a window moved to another parameter's slot or any other call
# BOLT-RULE-U010
law ring_walk_counts:
  for nn: Tree.Node
  for +self: String
  for +params: List<&2, String>
  for +path: String
  for +wins: List<&2, String>
  {List.length(&2, F.Finding, Ring.walk(nn, self, params, path, wins)) == ring.count(nn, self, params, wins) : Nat}

# the sliding arguments of each def of the list that calls itself and is not
# exempt; its windows are its parameters not named as any scrutinee of a
# `match` in its body (Ring.windows)
def ring.defs(ds: List<&2, Calls.Def>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig))),
        ring.count(body, name, Calls.names(sig), Ring.windows(sig, body)), 0n), ring.defs(rest, path))

# LAW: ring reports exactly those arguments, def by def, over the defs of the
# tree that call themselves, and none in a def that does not
# BOLT-RULE-U010
law ring_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Ring.check(Src.Src{path, text, toks, tree, bound, items}))
    == ring.defs(Calls.defs(tree), path) : Nat}
