# bolt/rules: the laws. Each rule is a pure function of the source it is
# handed, so its laws quantify over that source, never over one fixture.
import Base
import ../../syntax/lex.bend as Lex
import ../finding.bend as F
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
import ./laws/closed.bend as Closed
import ./suspicious/unused.bend as Unused
import ./suspicious/fuel.bend as FuelRule
import ./style/wrap.bend as Wrap
import ../../lazy/lazy.bend as Lazy
import ./laws/law.bend as Coverage
import ./laws/unsafe.bend as Unsafe
import ./imports.bend as Imports

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
# parameter) nor bare or typed `: Quant` (a quantity), its note read with
# each string literal cut to its quote
def too_short(kk: Bind.BindKind, +nm: String, +note: String) -> Bool:
  match kk:
    case Bind.KParam{}:
      Bool.and(Nat.is_lt(String.length(nm), 2n),
        Bool.not(Bool.or(one_upper(String.to_list(nm)),
          Bool.or(Bool.not(String.contains(T.code(note), ":")), String.ends_with(T.code(note), ": Quant")))))
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
    == Bool.pick(String, List.is_empty(&2, String, ls), "a proved row must name its law", "") : String}

# LAW: a Trusted row is well formed exactly when its Law cell is empty
# BOLT-LAW-5
law trace_trusted_shape:
  for +ls: List<&2, String>
  {Trace.shape("Trusted", "", ls)
    == Bool.pick(String, List.is_empty(&2, String, ls), "", "a Trusted row must not name a law") : String}

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
# decides the path by its segments. The cost rules also skip a def that is a
# proof wherever it is: one that returns a proof, or one with no type at all.

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

# LAW: a def written with no type (no `:` among its parameters, no `->`) fills the law of its name, so it is a
# proof: every cost rule that reads Calls.exempt skips it wherever it is, as it skips one that returns a proof
# BOLT-RULE-EXEMPT
law untyped_exempt:
  for +path: String
  for +sig: Tree.Node
  for e: {Calls.typed(sig) == False{} : Bool}
  {Calls.exempt(path, sig) == True{} : Bool}

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

# closed (BOLT-LAW-2). Over the file's top-level statements the rule reports
# each law whose body holds no `for` or `exs` line (the tree's SFor
# statement), and it reads only a LAWS.bend.

# some statement of a law's body is a `for` or `exs` binder
def closed.bound(body: Tree.Node) -> Bool:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SFor{}, kids, b}, rest}:
      True{}
    case Tree.NCons{h, rest}:
      closed.bound(rest)
    case other:
      False{}

# how many of the top-level laws bind nothing
def closed.count(root: Tree.Node) -> Nat:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SLaw{}, kids, +body}, rest}:
      +m = closed.count(rest)
      Bool.pick(Nat, closed.bound(body), m, 1n+m)
    case Tree.NCons{h, rest}:
      closed.count(rest)
    case other:
      0n

# LAW: over the file's top-level statements, closed reports one finding for
# each law with no `for` or `exs` binder, equality or not, and none for any
# other statement
# BOLT-LAW-2
law closed_walk_counts:
  for root: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Closed.check.go(root, path)) == closed.count(root) : Nat}

# LAW: closed reports exactly those laws of a LAWS.bend, and nothing in any
# other file, whatever the source holds
# BOLT-LAW-2
law closed_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Closed.check(Src.Src{path, text, toks, tree, bound, items}))
    == Bool.pick(Nat, Paths.is_laws(path), closed.count(tree), 0n) : Nat}

# doc (BOLT-RULE-S001). Over the outline's items the rule reports each def,
# type and law with no comment block right above it: its outline doc text is
# empty and the line right above it does not start with `#` (a block of bare
# `#` lines has an empty text). The header's exemptions: a name that is
# `main` or holds a dot (a helper), and a PROOF.bend or a file under a
# `tests` directory.

# a def, a type or a law: the kinds that need a comment
def doc.kind(kk: Outline.ItemKind) -> Bool:
  match kk:
    case Outline.IDef{}:
      True{}
    case Outline.IType{}:
      True{}
    case Outline.ILaw{}:
      True{}
    case other:
      False{}

# `main`, or a helper: a name holding a dot
def doc.free(+name: String) -> Bool:
  Bool.or(String.eq(name, "main"), String.contains(name, "."))

# line nn of the lines (0-based) starts with `#`
def doc.hash(lines: List<&2, String>, +nn: U32) -> Bool:
  match lines:
    case Nil{}:
      False{}
    case Con{hh, tt}:
      Bool.pick(Bool, U32.is_eq(nn, 0), String.starts_with(hh, "#"), doc.hash(tt, U32.sub(nn, 1)))

# an item that needs a comment and has none: an unexempt def, type or law
# whose line has no `#` line right above it (its doc text is never read)
def doc.bare(kk: Outline.ItemKind, +name: String, +line: U32, _doc: String, +lines: List<&2, String>) -> Bool:
  Bool.and(Bool.and(doc.kind(kk), Bool.not(doc.free(name))),
    Bool.not(Bool.and(Bool.not(U32.is_eq(line, 0)), doc.hash(lines, U32.sub(line, 1)))))

# how many items need a comment and have none
def doc.count(items: List<&2, Outline.Item>, +lines: List<&2, String>) -> Nat:
  match items:
    case Nil{}:
      0n
    case Con{Outline.Item{kk, +name, +line, sig, +doc, pp}, rest}:
      +m = doc.count(rest, lines)
      Bool.pick(Nat, doc.bare(kk, name, line, doc, lines), 1n+m, m)

# LAW: over the outline's items, doc reports one finding for each def, type
# or law not named `main` and holding no dot whose line has no `#` line
# right above it, and none for any other item
# BOLT-RULE-S001
law doc_walk_counts:
  for items: List<&2, Outline.Item>
  for +path: String
  for +lines: List<&2, String>
  {List.length(&2, F.Finding, Doc.check.go(items, path, lines)) == doc.count(items, lines) : Nat}

# LAW: doc reports exactly those items of the file, read against its lines
# (a line that starts inside a string literal read as empty), and nothing in
# a PROOF.bend or a file under a `tests` directory
# BOLT-RULE-S001
law doc_counts:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Doc.check(Src.Src{path, text, toks, tree, bound, items}))
    == Bool.pick(Nat, Bool.or(Paths.is_proof(path), Paths.is_test(path)), 0n, doc.count(items, Doc.lines(text, toks)))
    : Nat}

# The binding rule, unused. It reads the binder's lists: every binder, and
# every use with what it resolves to. A binder counts when it is a let, a
# do-bind or a lambda binder (KLocal), or a parameter (KParam) that is not
# erased (its declaration opens with `-`) and does not sit on a header line
# of a foreign def; its name does not start with `_`; and no use resolves to
# its position. Pattern binders (KPat), a law's `for` names (KFor) and every
# other kind never count.

# does a def's body open with an import statement? then the def is foreign
def unused.imported(body: Tree.Node) -> Bool:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SImport{}, kids, b}, rest}:
      True{}
    case other:
      False{}

# the line of each token
def unused.token_lines(ts: List<&2, Lex.Tok>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{k, t, +l, c}, rest}:
      l <> unused.token_lines(rest)

# every line a foreign def's header covers, however it is wrapped: the lines
# of its own tokens, def by def
def unused.headers(root: Tree.Node) -> List<&2, U32>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest}:
      +more = unused.headers(rest)
      Bool.pick(List<&2, U32>, unused.imported(body),
        List.append(&2, U32, unused.token_lines(Tree.leaves(kids)), more), more)
    case Tree.NCons{h, rest}:
      unused.headers(rest)
    case other:
      Nil{}

# does a use's target name the binder at (line, col)?
def unused.names(tg: Bind.Target, +line: U32, +col: U32) -> Bool:
  match tg:
    case Bind.TLocal{tl, tc}:
      Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col))
    case Bind.TItem{n}:
      False{}
    case Bind.TQual{a, n}:
      False{}
    case Bind.TFree{}:
      False{}

# does any use resolve to the binder at (line, col)?
def unused.seen(uses: List<&2, Bind.Use>, +line: U32, +col: U32) -> Bool:
  match uses:
    case Nil{}:
      False{}
    case Con{Bind.Use{n, l, c, tg}, rest}:
      Bool.or(unused.names(tg, line, col), unused.seen(rest, line, col))

# is a binder of this kind one the rule speaks for? A let, do-bind or lambda
# binder is; a parameter is unless erased or on a foreign header line;
# nothing else is
def unused.kept(kk: Bind.BindKind, +note: String, +line: U32, +fl: List<&2, U32>) -> Bool:
  match kk:
    case Bind.KItem{}:
      False{}
    case Bind.KCtor{}:
      False{}
    case Bind.KParam{}:
      Bool.and(Bool.not(String.starts_with(note, "-")), Bool.not(List.contains(~U32, ~U32.is_eq, fl, line)))
    case Bind.KTypeParam{}:
      False{}
    case Bind.KField{}:
      False{}
    case Bind.KLocal{}:
      True{}
    case Bind.KPat{}:
      False{}
    case Bind.KFor{}:
      False{}
    case Bind.KTypeVar{}:
      False{}

# how many binders count, are not named `_..`, and have no use
def unused.count(binds: List<&2, Bind.Bind>, +uses: List<&2, Bind.Use>, +fl: List<&2, U32>) -> Nat:
  match binds:
    case Nil{}:
      0n
    case Con{Bind.Bind{+name, +line, +col, kk, +note}, rest}:
      +m = unused.count(rest, uses, fl)
      Bool.pick(Nat, Bool.and(Bool.and(unused.kept(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
        Bool.not(unused.seen(uses, line, col))), 1n+m, m)

# LAW: unused reports one finding for each let, do-bind, lambda binder or
# parameter no use resolves to, and none for any other binder: not a pattern
# binder, a name starting with `_`, an erased parameter, a law's `for` name,
# or a parameter of a foreign def (one whose body opens with `import`),
# however its header is wrapped
# BOLT-RULE-U001
law unused_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for binds: List<&2, Bind.Bind>
  for +uses: List<&2, Bind.Use>
  for scopes: List<&2, Bind.Scope>
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Unused.check(Src.Src{path, text, toks, tree, Bind.Bound{binds, uses, scopes}, items}))
    == unused.count(binds, uses, unused.headers(tree)) : Nat}

# The recursion rule, index. It reads each def of the file whose body calls
# its own name and that is not a law or a proof, and every call in that body
# at any depth: a name token, then a group. A `String.get(..)` whose index
# (argument 1) is not one number token is a finding. So is a `List.get(..)`
# whose index (argument 3) is not one number token, unless `table` reports
# that same call: its fixed-table test, over the tables it finds in that def.

# is the chain exactly one number token?
def index.lit(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}}, Tree.NNil{}}:
      True{}
    case other:
      False{}

# does a call report, given whether its name is List.get (list) or
# String.get (sget), whether its group opens with `(` (ob), its arguments,
# and what `table` reports for it?
def index.fires(list: Bool, +ob: Bool, +sget: Bool, +as: List<&2, Tree.Node>, table: List<&2, F.Finding>) -> Bool:
  match list:
    case True{}:
      Bool.and(ob, Bool.and(Bool.not(index.lit(Calls.arg(as, 3n))), List.is_empty(&2, F.Finding, table)))
    case False{}:
      Bool.and(ob, Bool.and(sget, Bool.not(index.lit(Calls.arg(as, 1n)))))

# one when the name token tt at (ll, cc), then the rest, is a call index reports
def index.site(+tt: String, +ll: U32, +cc: U32, rest: Tree.Node, +path: String, +fixed: List<&2, String>) -> Nat:
  match rest:
    case Tree.NCons{Tree.Group{Lex.Tok{k, +o, ol, oc}, +kids, cl}, r}:
      Bool.pick(Nat, index.fires(String.eq(tt, "List.get"), String.eq(o, "("), String.eq(tt, "String.get"),
        Calls.args(kids), Table.hit(String.eq(o, "("), "List.get", kids, fixed, path, ll, cc)), 1n, 0n)
    case other:
      0n

# how many calls at any depth of the node index reports, fixed the tables
# `table` sees
def index.count(nn: Tree.Node, +path: String, +fixed: List<&2, String>) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, +l, +c}}, +rest}:
      Nat.add(index.site(t, l, c, rest, path, fixed), index.count(rest, path, fixed))
    case Tree.NCons{Tree.Group{o, kids, cl}, rest}:
      Nat.add(index.count(kids, path, fixed), index.count(rest, path, fixed))
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      Nat.add(index.count(kids, path, fixed), Nat.add(index.count(body, path, fixed), index.count(rest, path, fixed)))
    case Tree.NCons{h, rest}:
      index.count(rest, path, fixed)
    case other:
      0n

# how many calls index reports over the defs: those in each def that calls
# itself and is not a law or a proof, with the fixed tables `table` sees in it
def index.total(ds: List<&2, Calls.Def>, +mods: List<&2, String>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig))),
        index.count(body, path, Table.scope(body, mods)), 0n), index.total(rest, mods, path))

# LAW: index reports one finding for each `List.get(..)` or `String.get(..)`
# at an index that is not one number token, anywhere in a def that calls
# itself (a base arm included) and is not a law or a proof, except a
# `List.get` that `table` reports as a get on a fixed table; none for
# anything else
# BOLT-RULE-U007
law index_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Index.check(Src.Src{path, text, toks, tree, bound, items}))
    == index.total(Calls.defs(tree), Table.modules(Calls.defs(tree), []), path) : Nat}

# concat (BOLT-RULE-U004). concat walks each def's body tree: a self-call is
# a leaf whose text is the def's name followed by a `(` group, its arguments
# are the group's kids split at top-level commas (Calls.args), and the
# parameter in an argument's position is the def's parameter at the same
# index ("" past the last, the same as an unnamed type parameter). The name
# an argument appends onto is Concat.seen's: Concat.onto's `p ++ ..`,
# `List.append(.., p, ..)` or `String.append(p, ..)` written as the argument,
# inside any number of parentheses, else a lone name's nearest let in scope
# (Concat.find). A let statement of one plain name (Concat.bound) is in scope
# for the statements after it in its chain, and for everything under them.

# True when the argument appends onto a name and that name is the slot's
def concat.is(mm: Maybe<&2, Lex.Tok>, +slot: String) -> Bool:
  match mm:
    case None{}:
      False{}
    case Some{Lex.Tok{k, +t, l, c}}:
      String.eq(t, slot)

# how many arguments append onto the parameter in their own position
def concat.slots(as: List<&2, Tree.Node>, +params: List<&2, String>, +lets: List<&2, Concat.Let>) -> Nat:
  match as params:
    case Nil{} ps:
      0n
    case Con{+a, rest} Nil{}:
      +m = concat.slots(rest, Nil{}, lets)
      Bool.pick(Nat, concat.is(Concat.seen(a, lets), ""), 1n+m, m)
    case Con{+a, rest} Con{p, ps}:
      +m = concat.slots(rest, ps, lets)
      Bool.pick(Nat, concat.is(Concat.seen(a, lets), p), 1n+m, m)

# how many arguments of self-calls under the node append onto the parameter
# in their own position: a self-call's own arguments, then what its group and
# what follows it hold; a statement's let is in scope for what follows it
def concat.count(nn: Tree.Node, +name: String, +params: List<&2, String>, +lets: List<&2, Concat.Let>) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +here = Bool.pick(Nat, Bool.and(String.eq(o, "("), String.eq(t, name)),
        concat.slots(Calls.args(kids), params, lets), 0n)
      Nat.add(here, Nat.add(concat.count(kids, name, params, lets), concat.count(rest, name, params, lets)))
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      Nat.add(concat.count(kids, name, params, lets), concat.count(rest, name, params, lets))
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      Nat.add(concat.count(kids, name, params, lets),
        Nat.add(concat.count(body, name, params, lets),
          concat.count(rest, name, params, Concat.after(kind, kids, lets))))
    case Tree.NCons{h, rest}:
      concat.count(rest, name, params, lets)
    case other:
      0n

# the count over a file's defs, none in a def that is exempt (a law file, a
# proof file, a def that returns a proof), each def starting with no lets
def concat.file(ds: List<&2, Calls.Def>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, body}, rest}:
      Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n, concat.count(body, name, Calls.names(sig), [])),
        concat.file(rest, path))

# LAW: an argument in parentheses appends onto what its inside does
# BOLT-RULE-U004
law concat_paren:
  for k: Lex.TokKind
  for l: U32
  for c: U32
  for kids: Tree.Node
  for cl: Maybe<&2, Lex.Tok>
  {Concat.onto(Tree.NCons{Tree.Group{Lex.Tok{k, "(", l, c}, kids, cl}, Tree.NNil{}}) == Concat.onto(kids)
    : Maybe<&2, Lex.Tok>}

# LAW: a lone name appends onto what its nearest let's right side does, and
# a let of the name shadows every one after it
# BOLT-RULE-U004
law concat_nearest:
  for +name: String
  for mm: Maybe<&2, Lex.Tok>
  for lets: List<&2, Concat.Let>
  {Concat.find(Concat.Let{name, mm} <> lets, name) == mm : Maybe<&2, Lex.Tok>}

# LAW: a let of another name is passed over
# BOLT-RULE-U004
law concat_other:
  for +nm: String
  for +name: String
  for mm: Maybe<&2, Lex.Tok>
  for lets: List<&2, Concat.Let>
  for e: {String.eq(nm, name) == False{} : Bool}
  {Concat.find(Concat.Let{nm, mm} <> lets, name) == Concat.find(lets, name) : Maybe<&2, Lex.Tok>}

# LAW: a lone name is read through the lets
# BOLT-RULE-U004
law concat_via:
  for +t: String
  for l: U32
  for c: U32
  for +lets: List<&2, Concat.Let>
  {Concat.seen(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, Tree.NNil{}}, lets) == Concat.find(lets, t)
    : Maybe<&2, Lex.Tok>}

# LAW: an append written in place is read in place, whatever the lets say
# BOLT-RULE-U004
law concat_in_place:
  for +aa: Tree.Node
  for tok: Lex.Tok
  for lets: List<&2, Concat.Let>
  for e: {Concat.onto(aa) == Some{tok} : Maybe<&2, Lex.Tok>}
  {Concat.seen(aa, lets) == Some{tok} : Maybe<&2, Lex.Tok>}

# LAW: a let statement that binds one plain name puts it in scope, nearest
# first, for the statements after it
# BOLT-RULE-U004
law concat_scope:
  for +kids: Tree.Node
  for lt: Concat.Let
  for lets: List<&2, Concat.Let>
  for e: {Concat.bound(kids) == Some{lt} : Maybe<&2, Concat.Let>}
  {Concat.after(Tree.SLet{}, kids, lets) == lt <> lets : List<&2, Concat.Let>}

# LAW: `+q = rhs` and `q = rhs` bind q to what rhs appends onto
# BOLT-RULE-U004
law concat_bound:
  for +t: String
  for tl: U32
  for tc: U32
  for e: String
  for el: U32
  for ec: U32
  for +rhs: Tree.Node
  {Concat.bound(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, tl, tc}},
    Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, e, el, ec}}, rhs}}) == Some{Concat.Let{t, Concat.onto(rhs)}}
    : Maybe<&2, Concat.Let>}

# LAW: the `+` form binds the same way
# BOLT-RULE-U004
law concat_bound_plus:
  for pl: U32
  for pc: U32
  for +t: String
  for tl: U32
  for tc: U32
  for e: String
  for el: U32
  for ec: U32
  for +rhs: Tree.Node
  {Concat.bound(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, "+", pl, pc}},
    Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, tl, tc}}, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, e, el, ec}}, rhs}}})
    == Some{Concat.Let{t, Concat.onto(rhs)}} : Maybe<&2, Concat.Let>}

# LAW: a lone name is looked up in the lets, whatever they hold
law concat_via_name:
  for +t: String
  for l: U32
  for c: U32
  for +lets: List<&2, Concat.Let>
  {Concat.via(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, Tree.NNil{}}, lets) == Concat.find(lets, t)
    : Maybe<&2, Lex.Tok>}

# LAW: with nothing in place, the second maybe is the answer
law concat_either:
  for bb: Maybe<&2, Lex.Tok>
  {Concat.either(None{}, bb) == bb : Maybe<&2, Lex.Tok>}

# LAW: a statement that binds nothing leaves the lets as they were
law concat_push:
  for lets: List<&2, Concat.Let>
  {Concat.push(None{}, lets) == lets : List<&2, Concat.Let>}

# LAW: concat reports one finding for each self-call argument that appends
# onto the parameter in its own position, in every def its header does not
# exempt, and none for anything else
# BOLT-RULE-U004
law concat_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Concat.check(Src.Src{path, text, toks, tree, bound, items}))
    == concat.file(Calls.defs(tree), path) : Nat}

# eager (BOLT-RULE-U003). eager walks each def's body tree carrying three
# things: hot (the node runs whatever a pick's condition says: it sits in a
# branch argument of a `Bool.pick`, the third argument on, and not in a
# lambda's body after a `=>`), seg (which argument of a pick's own group the
# walk is in, 9 in a group that is not a pick's) and keep (what hot returns to
# at a comma of a group that is not a pick's). A leaf moves them by its kind,
# Eager.work.hot and Eager.work.seg; a statement starts cold. A looping def of
# the file is one Eager.loops lists: it calls itself, or a looping def above
# it.

# how many calls under the node, `f(..)` with f a looping def of the file
# (in ns) other than the def itself, sit where hot holds
def eager.count(
  nn: Tree.Node,
  +ns: List<&2, String>,
  +self: String,
  +hot: Bool,
  +seg: U32,
  +keep: Bool
) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +now = Eager.work.hot(k, hot, seg, keep)
      +call = Bool.and(Eager.work.name(k), String.eq(o, "("))
      +is_pick = Bool.and(call, String.eq(t, "Bool.pick"))
      +mine = Bool.and(Bool.not(String.eq(t, self)), List.contains(~String, ~String.eq, ns, t))
      +inner = Bool.and(now, Bool.not(is_pick))
      +m = Nat.add(eager.count(kids, ns, self, inner, Bool.pick(U32, is_pick, 0, 9), inner),
        eager.count(rest, ns, self, now, Eager.work.seg(k, seg), keep))
      Bool.pick(Nat, Bool.and(now, Bool.and(call, mine)), 1n+m, m)
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, t, l, c}}, rest}:
      eager.count(rest, ns, self, Eager.work.hot(k, hot, seg, keep), Eager.work.seg(k, seg), keep)
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      Nat.add(eager.count(kids, ns, self, hot, 9, hot), eager.count(rest, ns, self, hot, seg, keep))
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      Nat.add(eager.count(kids, ns, self, False{}, 9, False{}),
        Nat.add(eager.count(body, ns, self, False{}, 9, False{}), eager.count(rest, ns, self, hot, seg, keep)))
    case Tree.NCons{h, rest}:
      eager.count(rest, ns, self, hot, seg, keep)
    case other:
      0n

# the count over a file's defs, each body walked cold, none in a def that is
# exempt (a law file, a proof file, a def that returns a proof)
def eager.file(ds: List<&2, Calls.Def>, +ns: List<&2, String>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, body}, rest}:
      Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n, eager.count(body, ns, name, False{}, 9, False{})),
        eager.file(rest, ns, path))

# LAW: eager reports one finding for each call to a looping def of the file,
# not the def itself, in a branch of a `Bool.pick` (and not in a lambda's
# body there), in every def its header does not exempt, and none for
# anything else
# BOLT-RULE-U003
law eager_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Eager.check(Src.Src{path, text, toks, tree, bound, items}))
    == eager.file(Calls.defs(tree), Eager.loops(Calls.defs(tree)), path) : Nat}

# True for a leaf that is neither a `=>` nor a comma
def eager.plain(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TLam{}:
      False{}
    case Lex.TComma{}:
      False{}
    case other:
      True{}

# LAW: a `=>` leaves the rest of its argument cold, keeps the argument count
# and names no call
# BOLT-RULE-U003
law eager_lambda:
  for hot: Bool
  for +seg: U32
  for keep: Bool
  {(Eager.work.hot(Lex.TLam{}, hot, seg, keep), Eager.work.seg(Lex.TLam{}, seg), Eager.work.name(Lex.TLam{}))
    == (False{}, seg, False{}) : Bool & U32 & Bool}

# LAW: a comma of a pick's own group (seg 0 to 8) moves to its next
# argument, cold after the type and hot from the first branch on, and past
# the ninth it is a group like any other; a comma of any other group (seg 9)
# returns hot to keep; neither the hot it had nor the comma names a call
# BOLT-RULE-U003
law eager_comma:
  for +hot: Bool
  for +keep: Bool
  {([Eager.work.hot(Lex.TComma{}, hot, 0, keep), Eager.work.hot(Lex.TComma{}, hot, 1, keep),
      Eager.work.hot(Lex.TComma{}, hot, 2, keep), Eager.work.hot(Lex.TComma{}, hot, 8, keep),
      Eager.work.hot(Lex.TComma{}, hot, 9, keep), Eager.work.name(Lex.TComma{})],
    [Eager.work.seg(Lex.TComma{}, 0), Eager.work.seg(Lex.TComma{}, 1), Eager.work.seg(Lex.TComma{}, 2),
      Eager.work.seg(Lex.TComma{}, 8), Eager.work.seg(Lex.TComma{}, 9)])
    == ([False{}, True{}, True{}, True{}, keep, False{}], [1, 2, 3, 9, 9]) : List<&2, Bool> & List<&2, U32>}

# LAW: any other leaf leaves the state as it was and may name a call
# BOLT-RULE-U003
law eager_plain:
  for kk: Lex.TokKind
  for +hot: Bool
  for +seg: U32
  for keep: Bool
  for e: {eager.plain(kk) == True{} : Bool}
  {(Eager.work.hot(kk, hot, seg, keep), Eager.work.seg(kk, seg), Eager.work.name(kk))
    == (hot, seg, True{}) : Bool & U32 & Bool}

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

# fuel (BOLT-RULE-U006). The rule lists the file's fuel parameters: for each
# def of the file (Calls.defs), each parameter (Calls.params) whose name, its
# first lowercase name before the colon (Calls.param_name), is `fuel`, `gas`,
# `steps` or `budget` or starts with `fuel`, with its position. Over each
# top-level statement it then reads every call at any depth, a name token
# then a `(` group, that is not a call of the statement's own name (a
# self-call): for each fuel parameter of a def of that name, one finding when
# the argument in its position (Calls.args, split at top-level commas) is one
# Nat literal token alone, digits then `n`.

# is the name a fuel parameter's: `fuel`, `gas`, `steps` or `budget`, or one
# starting with `fuel`?
def fuel.named(+nn: String) -> Bool:
  Bool.or(String.starts_with(nn, "fuel"), List.contains(~String, ~String.eq, ["gas", "steps",
    "budget"], nn))

# the parameters with a fuel name among ps, the first at position i, each
# with the def's name
def fuel.slots.of(ps: List<&2, Tree.Node>, +name: String, +ii: Nat) -> List<&2, FuelRule.Fuel>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, rest}:
      +more = fuel.slots.of(rest, name, 1n+ii)
      Bool.pick(List<&2, FuelRule.Fuel>, fuel.named(Calls.param_name(p)), FuelRule.Fuel{name, ii} <> more, more)

# every fuel parameter of every def, in order
def fuel.slots(ds: List<&2, Calls.Def>) -> List<&2, FuelRule.Fuel>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Calls.Def{name, sig, body}, rest}:
      List.append(&2, FuelRule.Fuel, fuel.slots.of(Calls.params(sig), name, 0n), fuel.slots(rest))

# is the argument one Nat literal token alone, digits then `n`?
def fuel.lone(aa: Tree.Node) -> Bool:
  match aa:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, +t, l, c}}, Tree.NNil{}}:
      T.nat_ok(String.to_list(t))
    case other:
      False{}

# how many fuel parameters of defs named name a call with these arguments
# fills with a lone Nat literal
def fuel.hits(fs: List<&2, FuelRule.Fuel>, +name: String, +as: List<&2, Tree.Node>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case Con{FuelRule.Fuel{+fn, at}, rest}:
      +m = fuel.hits(rest, name, as)
      Bool.pick(Nat, Bool.and(String.eq(fn, name), fuel.lone(Calls.arg(as, at))), 1n+m, m)

# how many lone Nat literals the calls under the node pass for fuel, at any
# depth: a call is a name token then a `(` group, and a call of self is not
# counted
def fuel.count(nn: Tree.Node, +fs: List<&2, FuelRule.Fuel>, +self: String) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{ok, +o, ol, oc}, +kids, close},
      rest}}:
      +m = Nat.add(fuel.count(kids, fs, self), fuel.count(rest, fs, self))
      Bool.pick(Nat, Bool.and(Bool.and(Lex.is_name(k), String.eq(o, "(")), Bool.not(String.eq(t, self))),
        Nat.add(fuel.hits(fs, t, Calls.args(kids)), m), m)
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      Nat.add(fuel.count(kids, fs, self), fuel.count(rest, fs, self))
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      Nat.add(fuel.count(kids, fs, self), Nat.add(fuel.count(body, fs, self), fuel.count(rest, fs, self)))
    case Tree.NCons{h, rest}:
      fuel.count(rest, fs, self)
    case other:
      0n

# a statement's own name, "" when it has none
def fuel.own(mm: Maybe<&2, String>) -> String:
  match mm:
    case None{}:
      ""
    case Some{nm}:
      nm

# the fuel literals of the file: each top-level statement's calls, its own
# name the self it does not count
def fuel.total(root: Tree.Node, +fs: List<&2, FuelRule.Fuel>) -> Nat:
  match root:
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      +self = fuel.own(Bind.declared(kids))
      Nat.add(fuel.count(kids, fs, self), Nat.add(fuel.count(body, fs, self), fuel.total(rest, fs)))
    case Tree.NCons{h, rest}:
      fuel.total(rest, fs)
    case other:
      0n

# LAW: the rule's fuel parameters are the file's defs' parameters with a fuel
# name, each at its position
# BOLT-RULE-U006
law fuel_slots:
  for ds: List<&2, Calls.Def>
  {FuelRule.fuels(ds) == fuel.slots(ds) : List<&2, FuelRule.Fuel>}

# LAW: over any chain, fuel reports one finding for each fuel parameter a
# call (not of self) fills with a lone Nat literal, and none for anything else
# BOLT-RULE-U006
law fuel_walk_counts:
  for nn: Tree.Node
  for +fs: List<&2, FuelRule.Fuel>
  for +self: String
  for +path: String
  {List.length(&2, F.Finding, FuelRule.calls(nn, fs, self, path)) == fuel.count(nn, fs, self) : Nat}

# LAW: fuel reports exactly those literals over the file's top-level
# statements, against the fuel parameters of the file's defs
# BOLT-RULE-U006
law fuel_counts:
  for path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, FuelRule.check(Src.Src{path, text, toks, tree, bound, items}))
    == fuel.total(tree, fuel.slots(Calls.defs(tree))) : Nat}

# unit (BOLT-RULE-U012). The rule walks each def of the file that calls
# itself (Calls.calls) and is not exempt (a law file, a proof file, a def
# returning a proof), its body hot: the recursive step. A case arm's body is
# hot only when it calls the def too (a base case is not), a case's own
# pattern tokens never; anything else, lambda bodies included, is as hot as
# what holds it. In a hot region it reports one finding for each operator
# `*` with the literal one (a number token `1`, `1n` or `1.0`) right after or
# right before it, or `/` with it right after (the divisor); and one for each
# call, a leaf then a `(` group, of `Nat.mul`, `U32.mul` or `F32.mul` with
# the literal one alone as some argument, or of `Nat.div`, `U32.div` or
# `F32.div` with it alone as the last. Right before an operator is the leaf
# just before it in its chain, none past a group, a statement or another
# operator; right after is the node just after it, when a leaf.

# does the maybe hold the literal one: a number token `1`, `1n` or `1.0`?
def unit.one(mm: Maybe<&2, Lex.Tok>) -> Bool:
  match mm:
    case Some{Lex.Tok{Lex.TNum{}, +t, l, c}}:
      Bool.or(String.eq(t, "1"), Bool.or(String.eq(t, "1n"), String.eq(t, "1.0")))
    case other:
      False{}

# is the operator's text `*` with the literal one after or before it, or `/`
# with it after?
def unit.by_one(+op: String, prev: Maybe<&2, Lex.Tok>, +nxt: Maybe<&2, Lex.Tok>) -> Bool:
  Bool.pick(Bool, String.eq(op, "*"), Bool.or(unit.one(nxt), unit.one(prev)),
    Bool.and(String.eq(op, "/"), unit.one(nxt)))

# is the token an operator by one, between prev and nxt?
def unit.hit(tok: Lex.Tok, prev: Maybe<&2, Lex.Tok>, nxt: Maybe<&2, Lex.Tok>) -> Bool:
  match tok:
    case Lex.Tok{Lex.TOp{}, t, l, c}:
      unit.by_one(t, prev, nxt)
    case other:
      False{}

# what an operator after this leaf sees before it: the leaf, none when it is
# an operator
def unit.next(tok: Lex.Tok) -> Maybe<&2, Lex.Tok>:
  match tok:
    case Lex.Tok{Lex.TOp{}, t, l, c}:
      None{}
    case other:
      Some{other}

# the node right after, when it is a leaf
def unit.first(nn: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match nn:
    case Tree.NCons{Tree.Leaf{tok}, rest}:
      Some{tok}
    case other:
      None{}

# the name a group right after the leaf calls, "" after no leaf
def unit.name(mm: Maybe<&2, Lex.Tok>) -> String:
  match mm:
    case None{}:
      ""
    case Some{Lex.Tok{k, t, l, c}}:
      t

# is the argument the literal one alone?
def unit.lone(aa: Tree.Node) -> Bool:
  match aa:
    case Tree.NCons{Tree.Leaf{tok}, Tree.NNil{}}:
      unit.one(Some{tok})
    case other:
      False{}

# is some argument the literal one alone?
def unit.any(as: List<&2, Tree.Node>) -> Bool:
  match as:
    case Nil{}:
      False{}
    case Con{h, rest}:
      Bool.or(unit.lone(h), unit.any(rest))

# is the last argument the literal one alone?
def unit.last(as: List<&2, Tree.Node>) -> Bool:
  match as:
    case Nil{}:
      False{}
    case Con{h, Nil{}}:
      unit.lone(h)
    case Con{h, rest}:
      unit.last(rest)

# is the call a multiply with some argument one, else a divide by one?
def unit.call(+tt: String, +as: List<&2, Tree.Node>) -> Bool:
  Bool.pick(Bool, List.contains(~String, ~String.eq, ["Nat.mul", "U32.mul", "F32.mul"], tt),
    unit.any(as),
    Bool.and(List.contains(~String, ~String.eq, ["Nat.div", "U32.div", "F32.div"], tt),
      unit.last(as)))

# how many multiplies and divides by one the chain holds, at any depth, from
# a region as hot as hot, the leaf before it prev
def unit.count(nn: Tree.Node, +prev: Maybe<&2, Lex.Tok>, +self: String, +hot: Bool) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{+tok}, +rest}:
      +m = unit.count(rest, unit.next(tok), self, hot)
      Bool.pick(Nat, Bool.and(hot, unit.hit(tok, prev, unit.first(rest))), 1n+m, m)
    case Tree.NCons{Tree.Group{Lex.Tok{ok, +o, ol, oc}, +kids, close}, rest}:
      +own = Bool.and(String.eq(o, "("), Bool.and(hot, unit.call(unit.name(prev), Calls.args(kids))))
      Nat.add(unit.count(kids, None{}, self, hot),
        Nat.add(Bool.pick(Nat, own, 1n, 0n), unit.count(rest, None{}, self, hot)))
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, +body}, rest}:
      Nat.add(unit.count(kids, None{}, self, False{}),
        Nat.add(unit.count(body, None{}, self, Bool.and(hot, Calls.calls(body, self))), unit.count(rest, None{}, self,
          hot)))
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      Nat.add(unit.count(kids, None{}, self, hot),
        Nat.add(unit.count(body, None{}, self, hot), unit.count(rest, None{}, self, hot)))
    case Tree.NCons{h, rest}:
      unit.count(rest, prev, self, hot)
    case other:
      0n

# LAW: over any chain, unit reports one finding for each multiply or divide
# by one in a hot region, and none for anything else
# BOLT-RULE-U012
law unit_walk_counts:
  for nn: Tree.Node
  for +prev: Maybe<&2, Lex.Tok>
  for +self: String
  for +path: String
  for +hot: Bool
  {List.length(&2, F.Finding, UnitRule.walk(nn, prev, self, path, hot)) == unit.count(nn, prev, self, hot) : Nat}

# the multiplies and divides by one of each def of the list that calls itself
# and is not exempt, its body hot
def unit.defs(ds: List<&2, Calls.Def>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig))),
        unit.count(body, None{}, name, True{}), 0n), unit.defs(rest, path))

# LAW: unit reports exactly those, def by def, over the defs of the tree
# BOLT-RULE-U012
law unit_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, UnitRule.check(Src.Src{path, text, toks, tree, bound, items}))
    == unit.defs(Calls.defs(tree), path) : Nat}

# The header rule wrap (BOLT-RULE-S003) judges each def header of the
# outline by its sig's tokens (Lex.tokens), once: a finding or none. A
# header on one line is too wide past 120 columns, measured through its last
# `:` (the whole header when it has none), each token counted the way space
# counts it (Space.width_of: a string literal two, a `#|` comment none, any
# other token its length). A header across lines is judged by its parameter
# list. The list opens at the first `(` read while no bracket is open. Inside
# it, with only that `(` open, a `)` ends the list and a `,` ends a
# parameter; every other significant token is part of a parameter. A
# parameter is misplaced when it spans lines, starts on the `(` line, or
# starts on the line a later parameter starts on; the list is empty when it
# opened and holds no parameter; it is cramped when it closed and its `)` is
# not on a line below the last parameter's last line; it is loose when it
# closed and the next significant token is not a `->` (or the `:` of a
# header with no return type) on the `)` line. The spec reads single tokens
# with the rule's own readings and no more: Wrap.check.is_colon (a `:`),
# Wrap.check.is_arrow (a `->`), Wrap.check.is_oparen and Wrap.check.is_cparen
# (the text `(`, `)`), Lex.is_comma, Lex.significant, Lex.is_name (a name
# glues a `<` right after it), Wrap.check.brackets (the bracket a token opens
# or closes: `(` `[` `{` and `)` `]` `}`, a `<` or `<&` glued to a name
# opening an angle, a run of `>` closing) and Wrap.check.ticks_of (how many
# angles that run closes).

# some token of the list is a `:`
def wrap.colons(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Nil{}:
      False{}
    case Con{Lex.Tok{kk, tx, ln, cl}, rest}:
      Bool.or(Wrap.check.is_colon(kk), wrap.colons(rest))

# the width, acc so far, through the last `:` of the tokens
def wrap.upto(toks: List<&2, Lex.Tok>, +acc: U32) -> U32:
  match toks:
    case Nil{}:
      acc
    case Con{Lex.Tok{+kk, +tx, ln, cl}, +rest}:
      +next = (acc + Space.width_of(kk, tx) : U32)
      Bool.pick(U32, wrap.colons(rest), wrap.upto(rest, next), next)

# the width of all the tokens, acc so far
def wrap.total(toks: List<&2, Lex.Tok>, +acc: U32) -> U32:
  match toks:
    case Nil{}:
      acc
    case Con{Lex.Tok{+kk, +tx, ln, cl}, rest}:
      wrap.total(rest, (acc + Space.width_of(kk, tx) : U32))

# a one-line header's width: through its last `:`, else all of it
def wrap.width(+toks: List<&2, Lex.Tok>) -> U32:
  Bool.pick(U32, wrap.colons(toks), wrap.upto(toks, 0), wrap.total(toks, 0))

# LAW: wrap measures a header through its last `:`, the whole header when it
# has none, a string literal two columns and a comment after the `:` none
# BOLT-RULE-S003
law wrap_width:
  for +toks: List<&2, Lex.Tok>
  {Wrap.check.width.go(toks, 0, 0, False{}) == wrap.width(toks) : U32}

# a broken header read so far: where it stands (before its parameter list,
# inside it, just past its `)`, past a `->` on the `)` line, past anything
# else), the paren, bracket, brace and angle depths, the
# `(` line, the `)` line, the parameter being read, and those read, last first
type wrap.Read is Data:
  wrap.Read{at: Wrap.Phase, paren: U32, bracket: U32, brace: U32, angle: U32, open: U32, shut: U32,
    cur: Maybe<&2, Wrap.Span>, done: List<&2, Wrap.Span>}

# nothing read yet
def wrap.start() -> wrap.Read:
  wrap.Read{Wrap.Seek{}, 0, 0, 0, 0, 0, 0, None{}, []}

# no depth open
def wrap.shut_all(+paren: U32, +bracket: U32, +brace: U32, +angle: U32) -> Bool:
  Bool.and(U32.is_eq(paren, 0), Bool.and(U32.is_eq(angle, 0), Bool.and(U32.is_eq(brace, 0), U32.is_eq(bracket, 0))))

# only the list's own `(` open
def wrap.flat(+paren: U32, +bracket: U32, +brace: U32, +angle: U32) -> Bool:
  Bool.and(U32.is_eq(paren, 1), Bool.and(U32.is_eq(angle, 0), Bool.and(U32.is_eq(brace, 0), U32.is_eq(bracket, 0))))

# at the list's own depth: a `)` ends the list, a `,` a parameter, and any
# other token moves as it would anywhere
def wrap.edge(+kk: Lex.TokKind, +tx: String, move: Wrap.Act) -> Wrap.Act:
  Bool.pick(Wrap.Act, Wrap.check.is_cparen(kk, tx), Wrap.AEnd{},
    Bool.pick(Wrap.Act, Lex.is_comma(kk), Wrap.AComma{}, move))

# what a significant token does. Before the list a `(` with no depth open
# opens it; inside it, with only its `(` open, a `)` or a `,` is an edge;
# right after its `)` a token is a `->` (or a `:`) or a stray; later nothing
# moves; any other token moves the depths as Wrap.check.brackets reads it
def wrap.motion(
  at: Wrap.Phase,
  +kk: Lex.TokKind,
  +tx: String,
  +glued: Bool,
  +paren: U32,
  +bracket: U32,
  +brace: U32,
  +angle: U32
) -> Wrap.Act:
  match at:
    case Wrap.Seek{}:
      Bool.pick(Wrap.Act, Bool.and(Wrap.check.is_oparen(kk, tx), wrap.shut_all(paren, bracket, brace, angle)),
        Wrap.AOpen{}, Wrap.check.brackets(kk, tx, glued))
    case Wrap.Args{}:
      Bool.pick(Wrap.Act, wrap.flat(paren, bracket, brace, angle),
        wrap.edge(kk, tx, Wrap.check.brackets(kk, tx, glued)), Wrap.check.brackets(kk, tx, glued))
    case Wrap.Past{}:
      Wrap.ANone{}
    case Wrap.Shut{}:
      Bool.pick(Wrap.Act, Bool.or(Wrap.check.is_arrow(kk), Wrap.check.is_colon(kk)), Wrap.AArrow{}, Wrap.AStray{})
    case Wrap.Loose{}:
      Wrap.ANone{}

# one less, not below zero
def wrap.less(+nn: U32) -> U32:
  Lazy.stop(U32, U32.is_eq(nn, 0), 0, _u => (nn - 1 : U32))

# left angles closed, the depth staying at zero once there
def wrap.lower(left: Nat, +angle: U32) -> U32:
  match left:
    case Zero{}:
      angle
    case Succ{p}:
      Bool.pick(U32, U32.is_eq(angle, 0), angle, wrap.lower(p, (angle - 1 : U32)))

# the parameter being read, taken on to this token
def wrap.extend(cur: Maybe<&2, Wrap.Span>, +ln: U32, +cl: U32) -> Maybe<&2, Wrap.Span>:
  match cur:
    case None{}:
      Some{Wrap.Span{ln, ln, cl}}
    case Some{Wrap.Span{line, _end, col}}:
      Some{Wrap.Span{line, ln, col}}

# the parameter being read, onto those read
def wrap.close(cur: Maybe<&2, Wrap.Span>, done: List<&2, Wrap.Span>) -> List<&2, Wrap.Span>:
  match cur:
    case None{}:
      done
    case Some{sp}:
      sp <> done

# new depths; inside the list the token joins the parameter being read
def wrap.join(
  at: Wrap.Phase,
  paren: U32,
  bracket: U32,
  brace: U32,
  angle: U32,
  open: U32,
  shut: U32,
  cur: Maybe<&2, Wrap.Span>,
  done: List<&2, Wrap.Span>,
  +ln: U32,
  +cl: U32
) -> wrap.Read:
  match at:
    case Wrap.Args{}:
      wrap.Read{Wrap.Args{}, paren, bracket, brace, angle, open, shut, wrap.extend(cur, ln, cl), done}
    case Wrap.Seek{}:
      wrap.Read{Wrap.Seek{}, paren, bracket, brace, angle, open, shut, cur, done}
    case Wrap.Past{}:
      wrap.Read{Wrap.Past{}, paren, bracket, brace, angle, open, shut, cur, done}
    case Wrap.Shut{}:
      wrap.Read{Wrap.Shut{}, paren, bracket, brace, angle, open, shut, cur, done}
    case Wrap.Loose{}:
      wrap.Read{Wrap.Loose{}, paren, bracket, brace, angle, open, shut, cur, done}

# past the `)`, a `->` on its line puts the return type there; on a later
# line it does not
def wrap.turn(+ln: U32, +shut: U32) -> Wrap.Phase:
  Bool.pick(Wrap.Phase, U32.is_eq(ln, shut), Wrap.Past{}, Wrap.Loose{})

# a significant token's motion applied to the read, the token on line ln at
# column cl, closing ticks angles if it closes any
def wrap.move(
  act: Wrap.Act,
  at: Wrap.Phase,
  +paren: U32,
  +bracket: U32,
  +brace: U32,
  +angle: U32,
  open: U32,
  +shut: U32,
  cur: Maybe<&2, Wrap.Span>,
  done: List<&2, Wrap.Span>,
  +ln: U32,
  +cl: U32,
  ticks: Nat
) -> wrap.Read:
  match act:
    case Wrap.AOpen{}:
      wrap.Read{Wrap.Args{}, 1, bracket, brace, angle, ln, 0, None{}, done}
    case Wrap.AEnd{}:
      wrap.Read{Wrap.Shut{}, wrap.less(paren), bracket, brace, angle, open, ln, None{}, wrap.close(cur, done)}
    case Wrap.AComma{}:
      wrap.Read{at, paren, bracket, brace, angle, open, shut, None{}, wrap.close(cur, done)}
    case Wrap.AArrow{}:
      wrap.Read{wrap.turn(ln, shut), paren, bracket, brace, angle, open, shut, cur, done}
    case Wrap.AStray{}:
      wrap.Read{Wrap.Loose{}, paren, bracket, brace, angle, open, shut, cur, done}
    case Wrap.AParen{}:
      wrap.join(at, (paren + 1 : U32), bracket, brace, angle, open, shut, cur, done, ln, cl)
    case Wrap.AUnparen{}:
      wrap.join(at, wrap.less(paren), bracket, brace, angle, open, shut, cur, done, ln, cl)
    case Wrap.ABrack{}:
      wrap.join(at, paren, (bracket + 1 : U32), brace, angle, open, shut, cur, done, ln, cl)
    case Wrap.AUnbrack{}:
      wrap.join(at, paren, wrap.less(bracket), brace, angle, open, shut, cur, done, ln, cl)
    case Wrap.ABrace{}:
      wrap.join(at, paren, bracket, (brace + 1 : U32), angle, open, shut, cur, done, ln, cl)
    case Wrap.AUnbrace{}:
      wrap.join(at, paren, bracket, wrap.less(brace), angle, open, shut, cur, done, ln, cl)
    case Wrap.AAngle{}:
      wrap.join(at, paren, bracket, brace, (angle + 1 : U32), open, shut, cur, done, ln, cl)
    case Wrap.AUnangle{}:
      wrap.join(at, paren, bracket, brace, wrap.lower(ticks, angle), open, shut, cur, done, ln, cl)
    case Wrap.ANone{}:
      wrap.join(at, paren, bracket, brace, angle, open, shut, cur, done, ln, cl)

# one token onto the read; a space, a newline or a comment changes nothing
def wrap.step(+tok: Lex.Tok, +rd: wrap.Read, glued: Bool) -> wrap.Read:
  Lex.Tok{+kk, +tx, +ln, +cl} = tok
  wrap.Read{+at, +paren, +bracket, +brace, +angle, +open, +shut, +cur, +done} = rd
  Bool.pick(wrap.Read, Lex.significant(kk),
    wrap.move(wrap.motion(at, kk, tx, glued, paren, bracket, brace, angle), at, paren, bracket, brace, angle, open,
      shut, cur, done, ln, cl, Wrap.check.ticks_of(tx)),
    wrap.Read{at, paren, bracket, brace, angle, open, shut, cur, done})

# the tokens read in order, each glued when the token before it is a name;
# at the end the parameter being read is done
def wrap.run(toks: List<&2, Lex.Tok>, rd: wrap.Read, glued: Bool) -> wrap.Read:
  match toks:
    case Nil{}:
      wrap.Read{at, paren, bracket, brace, angle, open, shut, cur, done} = rd
      wrap.Read{at, paren, bracket, brace, angle, open, shut, None{}, wrap.close(cur, done)}
    case Con{+tok, rest}:
      Lex.Tok{+kk, _tx, _ln, _cl} = tok
      wrap.run(rest, wrap.step(tok, rd, glued), Lex.is_name(kk))

# some parameter of the list starts on the line
def wrap.starts_on(ps: List<&2, Wrap.Span>, +ln: U32) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{Wrap.Span{+line, _end, _col}, rest}:
      Bool.or(U32.is_eq(line, ln), wrap.starts_on(rest, ln))

# some parameter, in source order, spans lines, starts on the `(` line, or
# starts on the line a later one starts on
def wrap.misplaced(ps: List<&2, Wrap.Span>, +open: U32) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{Wrap.Span{+line, +end, _col}, +rest}:
      Bool.or(Bool.or(Bool.not(U32.is_eq(line, end)), Bool.or(U32.is_eq(line, open), wrap.starts_on(rest, line))),
        wrap.misplaced(rest, open))

# the last parameter (the first of those read, last first) does not end on a
# line above the `)` line
def wrap.tight(ps: List<&2, Wrap.Span>, +shut: U32) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{Wrap.Span{_line, +end, _col}, _rest}:
      Bool.not(U32.is_lt(end, shut))

# the list closed, and its `)` is not on a line below the last parameter's
def wrap.cramped(at: Wrap.Phase, +shut: U32, done: List<&2, Wrap.Span>) -> Bool:
  match at:
    case Wrap.Past{}:
      wrap.tight(done, shut)
    case Wrap.Shut{}:
      wrap.tight(done, shut)
    case Wrap.Loose{}:
      wrap.tight(done, shut)
    case Wrap.Seek{}:
      False{}
    case Wrap.Args{}:
      False{}

# no parameter read
def wrap.none(done: List<&2, Wrap.Span>) -> Bool:
  match done:
    case Nil{}:
      True{}
    case Con{_sp, _rest}:
      False{}

# the list opened and holds no parameter
def wrap.empty(at: Wrap.Phase, done: List<&2, Wrap.Span>) -> Bool:
  match at:
    case Wrap.Seek{}:
      False{}
    case Wrap.Args{}:
      wrap.none(done)
    case Wrap.Past{}:
      wrap.none(done)
    case Wrap.Shut{}:
      wrap.none(done)
    case Wrap.Loose{}:
      wrap.none(done)

# the list closed, and no `->` follows its `)` on the `)` line
def wrap.loose(at: Wrap.Phase) -> Bool:
  match at:
    case Wrap.Shut{}:
      True{}
    case Wrap.Loose{}:
      True{}
    case Wrap.Seek{}:
      False{}
    case Wrap.Args{}:
      False{}
    case Wrap.Past{}:
      False{}

# a header read to its end is misshapen: a parameter misplaced, or the list
# empty, cramped or loose
def wrap.bad_shape(rd: wrap.Read) -> Bool:
  wrap.Read{+at, _paren, _bracket, _brace, _angle, +open, +shut, _cur, +done} = rd
  Bool.or(wrap.misplaced(List.reverse(&2, Wrap.Span, done), open),
    Bool.or(wrap.empty(at, done), Bool.or(wrap.cramped(at, shut, done), wrap.loose(at))))

# a broken header's tokens are misshapen
def wrap.shape(toks: List<&2, Lex.Tok>) -> Bool:
  wrap.bad_shape(wrap.run(toks, wrap.start(), False{}))

# LAW: over the tokens of a broken header, wrap reports one finding when a
# parameter spans lines, starts on the `(` line or on another parameter's
# line, the list holds no parameter, or the list's `)` is not on a line below
# the last parameter or has no `->` (or `:`) right after it on its line, and
# none otherwise
# BOLT-RULE-S003
law wrap_shape_counts:
  for toks: List<&2, Lex.Tok>
  for +line: U32
  for +path: String
  {List.length(&2, F.Finding, Wrap.check.jam(line, toks, path, [])) == Bool.pick(Nat, wrap.shape(toks), 1n, 0n) : Nat}

# a header is misshapen: across lines by its parameter list, on one line by
# a width over 120
def wrap.bad(+sig: String) -> Bool:
  Bool.pick(Bool, String.contains(sig, "\n"), wrap.shape(Lex.tokens(sig)), U32.is_gt(wrap.width(Lex.tokens(sig)), 120))

# how many items of the outline are def headers that are misshapen
def wrap.count(items: List<&2, Outline.Item>) -> Nat:
  match items:
    case Nil{}:
      0n
    case Con{Outline.Item{kk, _name, _line, +sig, _doc, _pp}, rest}:
      +m = wrap.count(rest)
      Bool.pick(Nat, Bool.and(Outline.is_def(kk), wrap.bad(sig)), 1n+m, m)

# LAW: wrap reports exactly one finding for each def header of the outline
# that is misshapen, and none for anything else
# BOLT-RULE-S003
law wrap_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Wrap.check(Src.Src{path, text, toks, tree, bound, items})) == wrap.count(items) : Nat}

# coverage (BOLT-LAW-1). The rule reads the digests of the files in the run
# (bolt/rules/digest.bend), and so do these laws: they hold for every list of
# digests. A digest records, for a LAWS.bend, each use its quantified laws
# make, as the path and name the use resolves to (`Digest.Mention`); which
# uses those are is the binder's (BOLT-SYN-5) and Digest.of's, not the
# rule's. Under law is every file of the run when one of them is a LAWS.bend
# (BOLT-SCOPE-3), else none.

# the uses name the item: its path and its name
def coverage.names(ms: List<&2, Digest.Mention>, +pp: String, +name: String) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{Digest.Mention{mp, mn}, rest}:
      Bool.or(Bool.and(String.eq(mp, pp), String.eq(mn, name)), coverage.names(rest, pp, name))

# some LAWS.bend among the digests uses the item
def coverage.used(ds: List<&2, Digest.Digest>, +pp: String, +name: String) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      Bool.or(Bool.and(is_laws, coverage.names(says, pp, name)), coverage.used(rest, pp, name))

# some LAWS.bend uses one of the names (a type's constructors) in the file
def coverage.any(ns: List<&2, String>, +ds: List<&2, Digest.Digest>, +pp: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{name, rest}:
      Bool.or(coverage.used(ds, pp, name), coverage.any(rest, ds, pp))

# the items no LAWS.bend uses, in order: a def whose name has no dot (a
# helper's has), and a type when neither it nor any of its constructors is
# used (a use of another def of its file does not count)
def coverage.gaps(
  ts: List<&2, Digest.Top>,
  +ds: List<&2, Digest.Digest>,
  +pp: String,
  +path: String
) -> List<&2, F.Finding>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{Digest.Top{Outline.IDef{}, +name, +line, cs}, rest}:
      +more = coverage.gaps(rest, ds, pp, path)
      Bool.pick(List<&2, F.Finding>, Bool.or(String.contains(name, "."), coverage.used(ds, pp, name)), more,
        F.Finding{path, line, 0, 0, "coverage", "No quantified law names def " ++ name ++ "."} <> more)
    case Con{Digest.Top{Outline.IType{}, +name, +line, cs}, rest}:
      +more = coverage.gaps(rest, ds, pp, path)
      Bool.pick(List<&2, F.Finding>, Bool.or(coverage.used(ds, pp, name), coverage.any(cs, ds, pp)), more,
        F.Finding{path, line, 0, 0, "coverage", "No quantified law names type " ++ name ++ " or any of its constructors."}
          <> more)
    case Con{other, rest}:
      coverage.gaps(rest, ds, pp, path)

# the gaps of every file of fs not exempt (a law file or a test), against
# the uses the laws of all record
def coverage.files(fs: List<&2, Digest.Digest>, +all: List<&2, Digest.Digest>) -> List<&2, F.Finding>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      match exempt:
        case True{}:
          coverage.files(rest, all)
        case False{}:
          List.append(&2, F.Finding, coverage.gaps(tops, all, norm, path), coverage.files(rest, all))

# some digest is a LAWS.bend
def coverage.lawful(ds: List<&2, Digest.Digest>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      Bool.or(is_laws, coverage.lawful(rest))

# LAW: over every list of digests, coverage reports exactly this: when one
# is a LAWS.bend, in every file that is not a law file or a test, each def
# with no dot in its name that no LAWS.bend's quantified laws use, and each
# type they use neither by name nor by a constructor; else nothing
# BOLT-LAW-1
law coverage_reports:
  for +ds: List<&2, Digest.Digest>
  {Coverage.check(ds) == Bool.pick(List<&2, F.Finding>, coverage.lawful(ds), coverage.files(ds, ds), [])
    : List<&2, F.Finding>}

# unsafe (BOLT-LAW-3). Over every list of digests, as coverage's laws are.
# A digest records a file's relative imports (normalized, `deps`) and its
# `@unsafe def`s; the import graph is theirs, and the closure a law file
# reaches over it is Imports.closure.go's, the walk every project rule
# shares.

# every file of the digests the file at from reaches by relative imports,
# itself first, as the closure walk takes it
def unsafe.closure(+all: List<&2, Digest.Digest>, from: String) -> List<&2, String>:
  Imports.closure.go(Digest.edges(all), Imports.paths(Digest.edges(all)), List.length(&2, Digest.Digest, all), from)

# the path of the first law file among ls (a LAWS.bend or a PROOF.bend)
# whose closure over all holds the path pp
def unsafe.origin(ls: List<&2, Digest.Digest>, +all: List<&2, Digest.Digest>, +pp: String) -> Maybe<&2, String>:
  match ls:
    case Nil{}:
      None{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      +more = unsafe.origin(rest, all, pp)
      Bool.pick(Maybe<&2, String>, Bool.and(is_law_file, Imports.has(unsafe.closure(all, norm), pp)), Some{path}, more)

# one finding for each `@unsafe def`, at its `@`, naming the law file
def unsafe.each(us: List<&2, Digest.Unsafe>, +origin: String, +path: String) -> List<&2, F.Finding>:
  match us:
    case Nil{}:
      Nil{}
    case Con{Digest.Unsafe{n, l, c}, rest}:
      F.Finding{path, l, c, 7, "unsafe", "@unsafe def " ++ n ++ " is reachable from " ++ origin
        ++ ", where the checker skips its termination check and still exits 0; recurse on a shrinking argument or on fuel, and drop @unsafe."}
        <> unsafe.each(rest, origin, path)

# a file's unsafe defs when a law file reaches it, else nothing
def unsafe.at(mm: Maybe<&2, String>, us: List<&2, Digest.Unsafe>, path: String) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      Nil{}
    case Some{origin}:
      unsafe.each(us, origin, path)

# the findings of every file of fs, in order, against the law files of all
def unsafe.files(fs: List<&2, Digest.Digest>, +all: List<&2, Digest.Digest>) -> List<&2, F.Finding>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      List.append(&2, F.Finding, unsafe.at(unsafe.origin(all, all, norm), unsafes, path), unsafe.files(rest, all))

# LAW: over every list of digests, unsafe reports exactly each `@unsafe def`
# of each file that the closure of some law file holds, in file order, and
# names the first such law file
# BOLT-LAW-3
law unsafe_reports:
  for +ds: List<&2, Digest.Digest>
  {Unsafe.check(ds) == unsafe.files(ds, ds) : List<&2, F.Finding>}

# The recursion rule, hoist. It reads each def of the file whose body calls
# its own name and that is not a law or a proof, and walks that body as
# chains: a `=>` token makes the rest of its chain cold, a case's pattern is
# cold, and a case arm's body stays hot only when it calls the def; the rest
# keeps the heat it came in with, and the def's body starts hot. On a hot
# path it reports each call, a name token then a `(` group, that is a
# `List.get` / `List.set` (collection argument 2), `String.get` (0) or
# `Array.get` / `Array.set` (1) whose collection is a table, and each
# statement that is not a case, whose tokens before its first `=` hold exactly
# one lowercase name and no constructor or group, whose right side is a
# table, and whose name is indexed (`name[..]`, or a get or set's collection,
# bare or in parentheses) anywhere in its own block or the statements after
# it. A table is the rule's own recognizer (`is_table`): a list literal with
# eight or more top-level commas, an array literal `[v : T*n]` or `[v : T^d]`
# whose size is not a literal 0 to 8 after `*` or 0 to 3 after `^` (2^d
# slots), a `List.replicate` / `Array.new` / `List.range` whose count is not
# such a literal, a `List.map` / `Array.map`, or a call to a def of the file
# (not an undotted self-call) whose body is one constant-size table of that
# width (`wide_defs`); in every case
# with each value name under it (callees, `~` templates, dotted names and
# types aside) a parameter that every self-call passes back as that same lone
# name in its own position.

# does a get or set's collection argument, at its slot, hold a table?
def hoist.slot(
  ss: Hoist.Slot,
  +as: List<&2, Tree.Node>,
  +self: String,
  +wides: List<&2, String>,
  +carried: List<&2, String>
) -> Bool:
  match ss:
    case Hoist.Slot{on, at}:
      Bool.and(on, Hoist.is_table(Calls.arg(as, at), self, wides, carried))

# does a call site report: hot, a `(` group, and a get or set on a table
def hoist.call(
  +hot: Bool,
  +open: Bool,
  +tt: String,
  kids: Tree.Node,
  +self: String,
  +wides: List<&2, String>,
  +carried: List<&2, String>
) -> Bool:
  Bool.and(hot, Bool.and(open, hoist.slot(Hoist.slot_of(tt), Calls.args(kids), self, wides, carried)))

# a plain let's name and right side: a table, and the name indexed afterwards
def hoist.got(
  mm: Maybe<&2, Hoist.Got>,
  +body: Tree.Node,
  +rest: Tree.Node,
  +self: String,
  +wides: List<&2, String>,
  +carried: List<&2, String>
) -> Bool:
  match mm:
    case None{}:
      False{}
    case Some{Hoist.Got{+nm, +expr}}:
      Bool.and(Hoist.is_table(expr, self, wides, carried), Hoist.uses_or(body, rest, nm))

# does a statement report: hot, and a plain let of a table indexed afterwards
def hoist.let(
  +hot: Bool,
  kids: Tree.Node,
  +body: Tree.Node,
  +rest: Tree.Node,
  +self: String,
  +wides: List<&2, String>,
  +carried: List<&2, String>
) -> Bool:
  Bool.and(hot, hoist.got(Hoist.eat(kids, False{}, False{}, ""), body, rest, self, wides, carried))

# how many calls and lets hoist reports under the node, entered hot or cold
def hoist.count(
  nn: Tree.Node,
  +self: String,
  +wides: List<&2, String>,
  +carried: List<&2, String>,
  +hot: Bool
) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +heat = Hoist.warm(hot, k)
      Nat.add(Bool.pick(Nat, hoist.call(heat, String.eq(o, "("), t, kids, self, wides, carried), 1n, 0n),
        Nat.add(hoist.count(kids, self, wides, carried, heat), hoist.count(rest, self, wides, carried, heat)))
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, rest}:
      hoist.count(rest, self, wides, carried, Hoist.warm(hot, k))
    case Tree.NCons{Tree.Group{o, kids, cl}, rest}:
      Nat.add(hoist.count(kids, self, wides, carried, hot), hoist.count(rest, self, wides, carried, hot))
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, +body}, rest}:
      Nat.add(hoist.count(kids, self, wides, carried, False{}),
        Nat.add(hoist.count(body, self, wides, carried, Bool.and(hot, Calls.calls(body, self))),
          hoist.count(rest, self, wides, carried, hot)))
    case Tree.NCons{Tree.Stmt{kind, +kids, +body}, +rest}:
      Nat.add(Bool.pick(Nat, hoist.let(hot, kids, body, rest, self, wides, carried), 1n, 0n),
        Nat.add(hoist.count(kids, self, wides, carried, hot),
          Nat.add(hoist.count(body, self, wides, carried, hot), hoist.count(rest, self, wides, carried, hot))))
    case Tree.NCons{h, rest}:
      hoist.count(rest, self, wides, carried, hot)
    case other:
      0n

# how many hoist reports over the defs: those in each def that calls itself
# and is not a law or a proof, walked hot, with its carried parameters
def hoist.total(ds: List<&2, Calls.Def>, +wides: List<&2, String>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig))),
        hoist.count(body, name, wides, Hoist.carried(sig, body, name), True{}), 0n), hoist.total(rest, wides, path))

# LAW: hoist reports one finding for each call and each let the walk above
# counts, in each def that calls itself and is not a law or a proof, with
# the file's defs whose body is one wide constant-size table as builders;
# none for anything else
# BOLT-RULE-U009
law hoist_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Hoist.check(Src.Src{path, text, toks, tree, bound, items}))
    == hoist.total(Calls.defs(tree), Hoist.wide_defs(Calls.defs(tree), []), path) : Nat}

# The recursion rule, rewalk (BOLT-RULE-U011). It reads each def of the file
# that is not a law or a proof, and in it each straight piece: the def's body
# outside its case arms, and each case arm's body outside the arms nested in
# it. A walk is a callee token right before a `(` group, other than the def
# itself, that is a looping def of the file (one that calls itself, or calls
# a looping def above it) or a listed Base walk (`Rewalk.expensive`). Two
# calls of one walk read the same argument when the argument text is the same
# and so is, for each name in it, the number of lets of that name (`=` or
# `<-`, at the let's last token) before the call. A call's result is read for
# a single value when the call is indexed on the spot (`f(x)[i]`), is the
# collection argument of an accessor (`List.get`, `List.head`, `List.last`,
# `List.length`, `String.get`, `String.length`, `Array.get`), or is alone the
# right of an `=` let whose left holds one name: in a record pattern (a
# field), or a name read over the piece at least once and each time indexed
# or as an accessor's collection argument. The rule reports each call read
# for a single value, and not after a twin so read, that a twin keeps whole:
# another call, at another position, of the same walk on the same argument.
# The single-token and single-node recognizers are the rule's: slot_of and
# mark_slot (an accessor and its collection argument's call), open_site (one
# call as a site, by expensive), indexed, note_st (one statement's own tokens
# as a let of one call: a field or one name), has_eq, bind_at, last_pos,
# before, name_hit, here_hit, hit_keep, step_hot, step_left, pick_hot,
# pick_left, pick_live, either, none_hit, narrow_let, retag_one, note_line,
# note_col, note_how_of and pin_how. Every walk below, over the tree, the
# sites and the defs, is written here.

# the name tokens under the node, pushed onto acc in order
def rewalk.names(nn: Tree.Node, +acc: List<&2, String>) -> List<&2, String>:
  match nn:
    case Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}:
      t <> acc
    case Tree.Group{open, kids, close}:
      rewalk.names(kids, acc)
    case Tree.Stmt{kind, kids, body}:
      rewalk.names(body, rewalk.names(kids, acc))
    case Tree.NCons{h, rest}:
      rewalk.names(rest, rewalk.names(h, acc))
    case other:
      acc

# the names a let binds, pushed onto acc: every name before its first
# top-level `=` or `<-`, at any depth
def rewalk.lhs(nn: Tree.Node, +acc: List<&2, String>) -> List<&2, String>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest}:
      acc
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}}, rest}:
      acc
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}, rest}:
      rewalk.lhs(rest, t <> acc)
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      rewalk.lhs(rest, rewalk.names(kids, acc))
    case Tree.NCons{h, rest}:
      rewalk.lhs(rest, acc)
    case other:
      acc

# the lets of the piece, pushed onto acc in order: each let statement at any
# statement depth outside a case arm, one binding per name it binds, at its
# last token
def rewalk.binds(nn: Tree.Node, +acc: List<&2, Rewalk.Bind>) -> List<&2, Rewalk.Bind>:
  match nn:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, body}, rest}:
      rewalk.binds(rest, acc)
    case Tree.NCons{Tree.Stmt{Tree.SLet{}, +kids, +body}, rest}:
      rewalk.binds(rest, rewalk.binds(body,
        Rewalk.bind_at(rewalk.lhs(kids, []), Rewalk.last_pos(Tree.leaves.go(body, Tree.leaves.go(kids, []))), acc)))
    case Tree.NCons{Tree.Stmt{kind, kids, +body}, rest}:
      rewalk.binds(rest, rewalk.binds(body, acc))
    case Tree.NCons{h, rest}:
      rewalk.binds(rest, acc)
    case other:
      acc

# how many lets of the name take effect before (line, col)
def rewalk.lets(bs: List<&2, Rewalk.Bind>, +name: String, +line: U32, +col: U32) -> U32:
  match bs:
    case Nil{}:
      0
    case Con{Rewalk.Bind{+nm, +l, +c}, rest}:
      +more = rewalk.lets(rest, name, line, col)
      Bool.pick(U32, Bool.and(String.eq(nm, name), Rewalk.before(l, c, line, col)), (more + 1 : U32), more)

# which let of each name an argument at (line, col) reads
def rewalk.stamp(ns: List<&2, String>, +bs: List<&2, Rewalk.Bind>, +line: U32, +col: U32) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{+nm, rest}:
      "|" ++ nm ++ "=" ++ U32.show(rewalk.lets(bs, nm, line, col)) ++ rewalk.stamp(rest, bs, line, col)

# every call of a walk in the piece, in order, at any depth outside a case
# arm: its callee, its argument (text and stamp), its position, and a slot
# when it is indexed on the spot, else wide
def rewalk.gather(
  nn: Tree.Node,
  +self: String,
  +lp: List<&2, String>,
  +bs: List<&2, Rewalk.Bind>
) -> List<&2, Rewalk.Site>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, +l, +c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, +rest}}:
      +args = Tree.show(kids) ++ rewalk.stamp(rewalk.names(kids, []), bs, l, c)
      List.concat(&2, Rewalk.Site, [Rewalk.open_site(String.eq(o, "("), Rewalk.indexed(rest), t, args, l, c,
        U32.from_nat(String.length(t)), self, lp), rewalk.gather(kids, self, lp, bs),
        rewalk.gather(rest, self, lp, bs)])
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      List.concat(&2, Rewalk.Site, [rewalk.gather(kids, self, lp, bs), rewalk.gather(rest, self, lp, bs)])
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, +kids, body}, rest}:
      List.concat(&2, Rewalk.Site, [rewalk.gather(kids, self, lp, bs), rewalk.gather(rest, self, lp, bs)])
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      List.concat(&2, Rewalk.Site, [rewalk.gather(kids, self, lp, bs), rewalk.gather(body, self, lp, bs),
        rewalk.gather(rest, self, lp, bs)])
    case Tree.NCons{h, rest}:
      rewalk.gather(rest, self, lp, bs)
    case other:
      Nil{}

# each site at the note's position takes the note's reading
def rewalk.retag(sites: List<&2, Rewalk.Site>, +note: Rewalk.Note) -> List<&2, Rewalk.Site>:
  match sites:
    case Nil{}:
      Nil{}
    case Con{Rewalk.Site{+name, +args, +line, +col, +len, how}, rest}:
      Rewalk.retag_one(Bool.and(U32.is_eq(line, Rewalk.note_line(note)), U32.is_eq(col, Rewalk.note_col(note))), how,
        Rewalk.note_how_of(note), name, args, line, col, len) <> rewalk.retag(rest, note)

# a let of one call retags that call
def rewalk.relet(mm: Maybe<&2, Rewalk.Note>, sites: List<&2, Rewalk.Site>) -> List<&2, Rewalk.Site>:
  match mm:
    case None{}:
      sites
    case Some{note}:
      rewalk.retag(sites, note)

# each statement of the piece, in order, at any depth outside a case arm,
# retags the call it binds (a field, or a let of that name)
def rewalk.apply(nn: Tree.Node, sites: List<&2, Rewalk.Site>) -> List<&2, Rewalk.Site>:
  match nn:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, body}, rest}:
      rewalk.apply(rest, sites)
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      rewalk.apply(rest, rewalk.apply(body, rewalk.relet(Rewalk.note_st(kids), sites)))
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      rewalk.apply(rest, rewalk.apply(kids, sites))
    case Tree.NCons{h, rest}:
      rewalk.apply(rest, sites)
    case other:
      sites

# the callees of accessors' collection arguments, at any depth
def rewalk.marks(nn: Tree.Node) -> List<&2, Rewalk.Pos>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      List.concat(&2, Rewalk.Pos, [Bool.pick(List<&2, Rewalk.Pos>, String.eq(o, "("),
        Rewalk.mark_slot(Rewalk.slot_of(t), Calls.args(kids)), []), rewalk.marks(kids), rewalk.marks(rest)])
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      List.concat(&2, Rewalk.Pos, [rewalk.marks(kids), rewalk.marks(rest)])
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, +kids, body}, rest}:
      List.concat(&2, Rewalk.Pos, [rewalk.marks(kids), rewalk.marks(rest)])
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      List.concat(&2, Rewalk.Pos, [rewalk.marks(kids), rewalk.marks(body), rewalk.marks(rest)])
    case Tree.NCons{h, rest}:
      rewalk.marks(rest)
    case other:
      Nil{}

# is (line, col) among the positions?
def rewalk.pinned(+line: U32, +col: U32, ps: List<&2, Rewalk.Pos>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{Rewalk.Pos{l, c}, rest}:
      Bool.or(Bool.and(U32.is_eq(l, line), U32.is_eq(c, col)), rewalk.pinned(line, col, rest))

# a wide site at a marked position becomes a slot
def rewalk.pin(+ps: List<&2, Rewalk.Pos>, sites: List<&2, Rewalk.Site>) -> List<&2, Rewalk.Site>:
  match sites:
    case Nil{}:
      Nil{}
    case Con{Rewalk.Site{+name, +args, +line, +col, +len, how}, rest}:
      Rewalk.pin_how(rewalk.pinned(line, col, ps), how, name, args, line, col, len) <> rewalk.pin(ps, rest)

# the reads of a name in a chain: wide or at a slot. hot: the chain is a
# collection argument; left, live: the arguments to skip to it; skip: still
# the left of a let
def rewalk.reads(nn: Tree.Node, +name: String, +hot: Bool, +left: Nat, +live: Bool, +skip: Bool) -> Rewalk.Hit:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest}:
      rewalk.reads(rest, name, hot, left, live, False{})
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, rest}:
      rewalk.reads(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left, live), live, skip)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      Rewalk.either(Rewalk.hit_keep(skip, Rewalk.here_hit(String.eq(o, "["), String.eq(o, "("), t, name, hot)),
        Rewalk.either(rewalk.reads(kids, name, Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot),
          Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t),
          Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t), skip),
          rewalk.reads(rest, name, hot, left, live, skip)))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}, rest}:
      Rewalk.either(Rewalk.hit_keep(skip, Rewalk.name_hit(String.eq(t, name), hot)),
        rewalk.reads(rest, name, hot, left, live, skip))
    case Tree.NCons{Tree.Leaf{tok}, rest}:
      rewalk.reads(rest, name, hot, left, live, skip)
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      Rewalk.either(rewalk.reads(kids, name, hot, 0n, False{}, skip), rewalk.reads(rest, name, hot, left, live, skip))
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      Rewalk.either(rewalk.reads(kids, name, False{}, 0n, False{}, Rewalk.has_eq(kids)),
        Rewalk.either(rewalk.reads(body, name, False{}, 0n, False{}, False{}),
          rewalk.reads(rest, name, hot, left, live, skip)))
    case Tree.NCons{h, rest}:
      rewalk.reads(rest, name, hot, left, live, skip)
    case other:
      Rewalk.none_hit()

# is a result, so read, used for a single value over the piece?
def rewalk.single(hh: Rewalk.How, +piece: Tree.Node) -> Bool:
  match hh:
    case Rewalk.HWide{}:
      False{}
    case Rewalk.HSlot{}:
      True{}
    case Rewalk.HField{}:
      True{}
    case Rewalk.HLet{+binder}:
      Rewalk.narrow_let(rewalk.reads(piece, binder, False{}, 0n, False{}, False{}))

# the same walk on the same argument, at another position
def rewalk.twin(
  +nm: String,
  +as: String,
  +ll: U32,
  +cc: U32,
  +name: String,
  +args: String,
  +line: U32,
  +col: U32
) -> Bool:
  Bool.and(Bool.and(String.eq(nm, name), String.eq(as, args)),
    Bool.not(Bool.and(U32.is_eq(ll, line), U32.is_eq(cc, col))))

# does a twin among the sites keep its whole result?
def rewalk.whole(
  sites: List<&2, Rewalk.Site>,
  +name: String,
  +args: String,
  +line: U32,
  +col: U32,
  +piece: Tree.Node
) -> Bool:
  match sites:
    case Nil{}:
      False{}
    case Con{Rewalk.Site{+nm, +as, +l, +c, len, how}, rest}:
      Bool.or(Bool.and(rewalk.twin(nm, as, l, c, name, args, line, col), Bool.not(rewalk.single(how, piece))),
        rewalk.whole(rest, name, args, line, col, piece))

# is a twin among the sites read for a single value?
def rewalk.prior(
  sites: List<&2, Rewalk.Site>,
  +name: String,
  +args: String,
  +line: U32,
  +col: U32,
  +piece: Tree.Node
) -> Bool:
  match sites:
    case Nil{}:
      False{}
    case Con{Rewalk.Site{+nm, +as, +l, +c, len, how}, rest}:
      Bool.or(Bool.and(rewalk.twin(nm, as, l, c, name, args, line, col), rewalk.single(how, piece)),
        rewalk.prior(rest, name, args, line, col, piece))

# a site is reported when it is read for a single value, a twin among all
# the sites keeps its whole result, and no twin before it (seen) is read for
# a single value
def rewalk.flag(
  ss: Rewalk.Site,
  +all: List<&2, Rewalk.Site>,
  +piece: Tree.Node,
  +seen: List<&2, Rewalk.Site>
) -> Bool:
  Rewalk.Site{+name, +args, +line, +col, len, how} = ss
  Bool.and(rewalk.whole(all, name, args, line, col, piece),
    Bool.and(rewalk.single(how, piece), Bool.not(rewalk.prior(seen, name, args, line, col, piece))))

# how many of the sites are reported, each after the ones before it
def rewalk.count(
  sites: List<&2, Rewalk.Site>,
  +all: List<&2, Rewalk.Site>,
  +piece: Tree.Node,
  +seen: List<&2, Rewalk.Site>
) -> Nat:
  match sites:
    case Nil{}:
      0n
    case Con{+s, rest}:
      +m = rewalk.count(rest, all, piece, s <> seen)
      Bool.pick(Nat, rewalk.flag(s, all, piece, seen), 1n+m, m)

# the sites of a piece: every call of a walk, read as its let, field, index
# or accessor makes it
def rewalk.sites(+nn: Tree.Node, +self: String, +lp: List<&2, String>) -> List<&2, Rewalk.Site>:
  rewalk.pin(rewalk.marks(nn), rewalk.apply(nn, rewalk.gather(nn, self, lp, rewalk.binds(nn, []))))

# the findings of one piece
def rewalk.piece(+nn: Tree.Node, +self: String, +lp: List<&2, String>) -> Nat:
  +ss = rewalk.sites(nn, self, lp)
  rewalk.count(ss, ss, nn, [])

# the findings of every case arm's piece under the node, at any depth
def rewalk.arms(nn: Tree.Node, +self: String, +lp: List<&2, String>) -> Nat:
  match nn:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, +body}, rest}:
      Nat.add(rewalk.piece(body, self, lp), Nat.add(rewalk.arms(body, self, lp), rewalk.arms(rest, self, lp)))
    case Tree.NCons{Tree.Stmt{kind, +kids, +body}, rest}:
      Nat.add(rewalk.arms(kids, self, lp), Nat.add(rewalk.arms(body, self, lp), rewalk.arms(rest, self, lp)))
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      Nat.add(rewalk.arms(kids, self, lp), rewalk.arms(rest, self, lp))
    case Tree.NCons{h, rest}:
      rewalk.arms(rest, self, lp)
    case other:
      0n

# every name the node calls, in order: a token right before a `(` group
def rewalk.called(nn: Tree.Node) -> List<&2, String>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +more = List.concat(&2, String, [rewalk.called(kids), rewalk.called(rest)])
      Bool.pick(List<&2, String>, String.eq(o, "("), t <> more, more)
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      List.concat(&2, String, [rewalk.called(kids), rewalk.called(rest)])
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      List.concat(&2, String, [rewalk.called(kids), rewalk.called(body), rewalk.called(rest)])
    case Tree.NCons{h, rest}:
      rewalk.called(rest)
    case other:
      Nil{}

# does the list hold a name the set has?
def rewalk.any(cs: List<&2, String>, +set: List<&2, String>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{c, t}:
      Bool.or(List.contains(~String, ~String.eq, set, c), rewalk.any(t, set))

# the looping defs pushed onto acc: each def, in order, that calls itself or
# a looping def before it
def rewalk.loops(ds: List<&2, Calls.Def>, +acc: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      acc
    case Con{Calls.Def{+name, sig, body}, rest}:
      +cs = rewalk.called(body)
      rewalk.loops(rest, Bool.pick(List<&2, String>,
        Bool.or(List.contains(~String, ~String.eq, cs, name), rewalk.any(cs, acc)), name <> acc, acc))

# the findings of each def, none in a law or a proof: its body's piece and
# its case arms' pieces
def rewalk.total(ds: List<&2, Calls.Def>, +lp: List<&2, String>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n,
        Nat.add(rewalk.piece(body, name, lp), rewalk.arms(body, name, lp))), rewalk.total(rest, lp, path))

# LAW: over any piece, rewalk reports one finding for each site the law flags
# BOLT-RULE-U011
law rewalk_local_counts:
  for +nn: Tree.Node
  for +self: String
  for +lp: List<&2, String>
  for +path: String
  {List.length(&2, F.Finding, Rewalk.local(nn, self, lp, path)) == rewalk.piece(nn, self, lp) : Nat}

# LAW: under any node, rewalk reports each case arm's piece on its own
# BOLT-RULE-U011
law rewalk_visit_counts:
  for nn: Tree.Node
  for +self: String
  for +lp: List<&2, String>
  for +path: String
  {List.length(&2, F.Finding, Rewalk.visit(nn, self, lp, path)) == rewalk.arms(nn, self, lp) : Nat}

# LAW: rewalk reports exactly those findings, def by def, over the defs of
# the tree, with the looping defs the law finds
# BOLT-RULE-U011
law rewalk_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Rewalk.check(Src.Src{path, text, toks, tree, bound, items}))
    == rewalk.total(Calls.defs(tree), rewalk.loops(Calls.defs(tree), []), path) : Nat}

# Scope: a path exemption is decided by the path alone. The `law` rule lets
# off a file by its digest's `exempt` flag, and a per-file rule's header
# exempts a LAWS.bend, a PROOF.bend or a file under `tests` by bolt/paths.bend.
# Neither reads the text: two files at one path, whatever each holds, are
# exempt alike, and an exempt file's findings from the rule that exempts it
# are the same for both. What a rule reads from content to skip a def, a line
# or a file (a def returning a proof, a file defining `Map.put`, `#|` lines,
# `# lanes: native`, `main` and dotted names) is that rule's own behavior,
# not a path exemption.

# whether the coverage rule lets a digest's file off
def scope.exempt(dd: Digest.Digest) -> Bool:
  match dd:
    case Digest.Digest{_path, _norm, _dir, _is_laws, _is_law_file, exempt, _tops, _says, _deps, _unsafes, _laws}:
      exempt

# LAW: two files at the same path are exempt from `law` alike, whatever the
# text, tokens, tree, binding structure and outline of each
# BOLT-SCOPE-4
law scope_digest_exempt:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +text2: String
  for +toks2: List<&2, Lex.Tok>
  for +tree2: Tree.Node
  for +bound2: Bind.Bound
  for +items2: List<&2, Outline.Item>
  {scope.exempt(Digest.of(Src.Src{path, text, toks, tree, bound, items}))
    == scope.exempt(Digest.of(Src.Src{path, text2, toks2, tree2, bound2, items2})) : Bool}

# LAW: hole's findings on a LAWS.bend are the same for any two sources at
# that path
# BOLT-SCOPE-4
law scope_hole:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +text2: String
  for +toks2: List<&2, Lex.Tok>
  for +tree2: Tree.Node
  for +bound2: Bind.Bound
  for +items2: List<&2, Outline.Item>
  for +e: {Paths.is_laws(path) == True{} : Bool}
  {Hole.check(Src.Src{path, text, toks, tree, bound, items})
    == Hole.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: doc's findings on a PROOF.bend or a file under `tests` are the same
# for any two sources at that path
# BOLT-SCOPE-4
law scope_doc:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +text2: String
  for +toks2: List<&2, Lex.Tok>
  for +tree2: Tree.Node
  for +bound2: Bind.Bound
  for +items2: List<&2, Outline.Item>
  for +e: {Bool.or(Paths.is_proof(path), Paths.is_test(path)) == True{} : Bool}
  {Doc.check(Src.Src{path, text, toks, tree, bound, items})
    == Doc.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: param's findings on a PROOF.bend are the same for any two sources at
# that path
# BOLT-SCOPE-4
law scope_param:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +text2: String
  for +toks2: List<&2, Lex.Tok>
  for +tree2: Tree.Node
  for +bound2: Bind.Bound
  for +items2: List<&2, Outline.Item>
  for +e: {Paths.is_proof(path) == True{} : Bool}
  {Param.check(Src.Src{path, text, toks, tree, bound, items})
    == Param.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# the findings of each rule a LAWS.bend or a PROOF.bend exempts, rule by rule
def scope.law_file(+ss: Src.Src) -> List<&2, List<&2, F.Finding>>:
  [Pick.check(ss), Tail.check(ss), Concat.check(ss), Eager.check(ss), Rewalk.check(ss), Strict.check(ss),
    Hoist.check(ss), Index.check(ss), Ring.check(ss), Table.check(ss), UnitRule.check(ss)]

# LAW: on a LAWS.bend or a PROOF.bend, the findings of each rule its header
# exempts there (pick, tail, concat, eager, rewalk, strict, hoist, index,
# ring, table, unit) are the same for any two sources at that path
# BOLT-SCOPE-4
law scope_law_file:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +text2: String
  for +toks2: List<&2, Lex.Tok>
  for +tree2: Tree.Node
  for +bound2: Bind.Bound
  for +items2: List<&2, Outline.Item>
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {scope.law_file(Src.Src{path, text, toks, tree, bound, items})
    == scope.law_file(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, List<&2, F.Finding>>}

# LAW: closed's findings on a file that is not a LAWS.bend are the same for
# any two sources at that path
# BOLT-SCOPE-4
law scope_closed:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +text2: String
  for +toks2: List<&2, Lex.Tok>
  for +tree2: Tree.Node
  for +bound2: Bind.Bound
  for +items2: List<&2, Outline.Item>
  for +e: {Paths.is_laws(path) == False{} : Bool}
  {Closed.check(Src.Src{path, text, toks, tree, bound, items})
    == Closed.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# trace: a reading of SPEC.md and a count of its defects, written apart from
# the rule (bolt/rules/laws/trace.bend), in file order and without its
# accumulators; the rule's Row, Mark and Mode types carry what is read
# ---------------------------------------------------------------------------

# the pieces of a table line cut at each bar: the text before the first cut,
# then the text after each cut
type trace.Cut is Data:
  trace.Cut{head: List<&2, Char>, tail: List<&2, List<&2, Char>>}

# a char in front of the pieces after it: a bar starts a new first piece, any
# other char joins the first
def trace.piece(bar: Bool, cc: Char, cut: trace.Cut) -> trace.Cut:
  match bar:
    case True{}:
      trace.Cut{h, t} = cut
      trace.Cut{[], h <> t}
    case False{}:
      trace.Cut{h, t} = cut
      trace.Cut{cc <> h, t}

# the pieces of a line, cut at each `|` that does not follow a `\` (`\|` is a
# bar inside a cell); esc says the char before was a `\`
def trace.split(cs: List<&2, Char>, esc: Bool) -> trace.Cut:
  match cs:
    case Nil{}:
      trace.Cut{[], []}
    case Con{+cc, t}:
      trace.piece(Bool.and(Char.is_eq(cc, '|'), Bool.not(esc)), cc, trace.split(t, Char.is_eq(cc, '\\')))

# the pieces p, ps but the last, each as text with spaces trimmed
def trace.mid(ps: List<&2, List<&2, Char>>, pp: List<&2, Char>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{q, rest}:
      String.trim(String.from_list(pp)) <> trace.mid(rest, q)

# the pieces between two cuts
def trace.inner(cut: trace.Cut) -> List<&2, String>:
  match cut:
    case trace.Cut{_h, Nil{}}:
      Nil{}
    case trace.Cut{_h, Con{q, rest}}:
      trace.mid(rest, q)

# the cells of a table line: the text between each bar and the next, trimmed
def trace.cells(line: String) -> List<&2, String>:
  trace.inner(trace.split(String.to_list(String.trim(line)), False{}))

# the entries of a Law cell cut at `;`: each piece trimmed, the empty ones
# dropped
def trace.laws(ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{ss, rest}:
      +e = String.trim(ss)
      +more = trace.laws(rest)
      Bool.pick(List<&2, String>, String.is_empty(e), more, e <> more)

# what a trimmed line of SPEC.md is: a requirement table's header, a trust
# table's header, a table line (`|` first), or prose
type trace.Line is Data:
  trace.ReqHeader{}
  trace.TrustHeader{}
  trace.Bar{}
  trace.Prose{}

# what the trimmed line is
def trace.line(+tt: String) -> trace.Line:
  Bool.pick(trace.Line, String.eq(tt, "| ID | Requirement | Level | Status | Law |"), trace.ReqHeader{},
    Bool.pick(trace.Line, String.eq(tt, "| ID | Assumption | Why it is trusted |"), trace.TrustHeader{},
      Bool.pick(trace.Line, String.starts_with(tt, "|"), trace.Bar{}, trace.Prose{})))

# the place after a table line: the line under a header is its rule, and the
# rows follow it
def trace.on_bar(mm: Trace.Mode) -> Trace.Mode:
  match mm:
    case Trace.Out{}:
      Trace.Out{}
    case Trace.ReqHead{}:
      Trace.Reqs{}
    case Trace.Reqs{}:
      Trace.Reqs{}
    case Trace.TrustHead{}:
      Trace.Trusts{}
    case Trace.Trusts{}:
      Trace.Trusts{}

# the place after a line: a header opens its table, prose closes any table
def trace.after(kk: trace.Line, mm: Trace.Mode) -> Trace.Mode:
  match kk:
    case trace.ReqHeader{}:
      Trace.ReqHead{}
    case trace.TrustHeader{}:
      Trace.TrustHead{}
    case trace.Bar{}:
      trace.on_bar(mm)
    case trace.Prose{}:
      Trace.Out{}

# the cells of a requirement row, when there are five, as the row at line n
def trace.req_row(cs: List<&2, String>, +nn: U32) -> List<&2, Trace.Row>:
  match cs:
    case Con{id, Con{_what, Con{lv, Con{st, Con{cell, Nil{}}}}}}:
      [Trace.Row{id, lv, st, trace.laws(String.split(cell, ';')), nn}]
    case _other:
      Nil{}

# the cells of a trust row, when there are three, as the ID at line n
def trace.trust_row(cs: List<&2, String>, +nn: U32) -> List<&2, Trace.Mark>:
  match cs:
    case Con{id, Con{_what, Con{_why, Nil{}}}}:
      [Trace.Mark{id, nn}]
    case _other:
      Nil{}

# the requirement row a table line is, in place m
def trace.req_in(mm: Trace.Mode, +tt: String, +nn: U32) -> List<&2, Trace.Row>:
  match mm:
    case Trace.Reqs{}:
      trace.req_row(trace.cells(tt), nn)
    case _other:
      Nil{}

# the trust row a table line is, in place m
def trace.trust_in(mm: Trace.Mode, +tt: String, +nn: U32) -> List<&2, Trace.Mark>:
  match mm:
    case Trace.Trusts{}:
      trace.trust_row(trace.cells(tt), nn)
    case _other:
      Nil{}

# 1 when the table line in place m is a row with the wrong number of cells
def trace.bad_in(mm: Trace.Mode, +tt: String) -> Nat:
  match mm:
    case Trace.Reqs{}:
      Bool.pick(Nat, Nat.is_eq(List.length(&2, String, trace.cells(tt)), 5n), 0n, 1n)
    case Trace.Trusts{}:
      Bool.pick(Nat, Nat.is_eq(List.length(&2, String, trace.cells(tt)), 3n), 0n, 1n)
    case _other:
      0n

# the requirement row a line of kind k is, in place m
def trace.req_at(kk: trace.Line, mm: Trace.Mode, +tt: String, +nn: U32) -> List<&2, Trace.Row>:
  match kk:
    case trace.Bar{}:
      trace.req_in(mm, tt, nn)
    case _other:
      Nil{}

# the trust row a line of kind k is, in place m
def trace.trust_at(kk: trace.Line, mm: Trace.Mode, +tt: String, +nn: U32) -> List<&2, Trace.Mark>:
  match kk:
    case trace.Bar{}:
      trace.trust_in(mm, tt, nn)
    case _other:
      Nil{}

# 1 when a line of kind k, in place m, is a row with the wrong number of cells
def trace.bad_at(kk: trace.Line, mm: Trace.Mode, +tt: String) -> Nat:
  match kk:
    case trace.Bar{}:
      trace.bad_in(mm, tt)
    case _other:
      0n

# the requirement rows of the lines, in file order, the first at line n in
# place m
def trace.reqs(ls: List<&2, String>, +nn: U32, +mm: Trace.Mode) -> List<&2, Trace.Row>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{ll, rest}:
      +tt = String.trim(ll)
      +kk = trace.line(tt)
      List.append(&2, Trace.Row, trace.req_at(kk, mm, tt, nn), trace.reqs(rest, (nn + 1 : U32), trace.after(kk, mm)))

# the trust rows of the lines, in file order
def trace.trusts(ls: List<&2, String>, +nn: U32, +mm: Trace.Mode) -> List<&2, Trace.Mark>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{ll, rest}:
      +tt = String.trim(ll)
      +kk = trace.line(tt)
      List.append(&2, Trace.Mark, trace.trust_at(kk, mm, tt, nn), trace.trusts(rest, (nn + 1 : U32),
        trace.after(kk, mm)))

# how many table rows of the lines have the wrong number of cells
def trace.bad(ls: List<&2, String>, +mm: Trace.Mode) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Con{ll, rest}:
      +tt = String.trim(ll)
      +kk = trace.line(tt)
      Nat.add(trace.bad_at(kk, mm, tt), trace.bad(rest, trace.after(kk, mm)))

# 1 when b holds, else 0
def trace.one(bb: Bool) -> Nat:
  Bool.pick(Nat, bb, 1n, 0n)

# is the char an uppercase letter?
def trace.upper(cc: Char) -> Bool:
  +u = Char.to_u32(cc)
  Bool.and(U32.is_ge(u, 65), U32.is_le(u, 90))

# is the char an uppercase letter or a digit?
def trace.alnum(cc: Char) -> Bool:
  +u = Char.to_u32(cc)
  Bool.or(Bool.and(U32.is_ge(u, 65), U32.is_le(u, 90)), Bool.and(U32.is_ge(u, 48), U32.is_le(u, 57)))

# does the rest of the text end an ID, read so far to a `-` (dashed) or not,
# and at the start of an empty segment (empty) or not: every char a `-` that
# ends a segment with a char in it, or an uppercase letter or digit, and the
# last segment, after a `-`, not empty
def trace.run(ss: String, dashed: Bool, empty: Bool) -> Bool:
  match ss:
    case SNil{}:
      Bool.and(dashed, Bool.not(empty))
    case SCon{+cc, t}:
      +dd = Char.is_eq(cc, '-')
      Bool.and(Bool.pick(Bool, dd, Bool.not(empty), trace.alnum(cc)), trace.run(t, Bool.or(dd, dashed), dd))

# does the text start with an uppercase letter?
def trace.lead(ss: String) -> Bool:
  match ss:
    case SNil{}:
      False{}
    case SCon{cc, _t}:
      trace.upper(cc)

# is the text an ID, `[A-Z][A-Z0-9]*(-[A-Z0-9]+)+`: an uppercase letter,
# then two or more segments of uppercase letters and digits joined by `-`
def trace.is_id(+ss: String) -> Bool:
  Bool.and(trace.run(ss, False{}, True{}), trace.lead(ss))

# how many rows have the ID
def trace.many(rs: List<&2, Trace.Row>, +id: String) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{Trace.Row{+i, _lv, _st, _ls, _n}, rest}:
      +mm = trace.many(rest, id)
      Bool.pick(Nat, String.eq(i, id), 1n+mm, mm)

# how many trust rows have the ID
def trace.marks(ms: List<&2, Trace.Mark>, +id: String) -> Nat:
  match ms:
    case Nil{}:
      0n
    case Con{Trace.Mark{+i, _n}, rest}:
      +mm = trace.marks(rest, id)
      Bool.pick(Nat, String.eq(i, id), 1n+mm, mm)

# is a row of this level and status a claim: Proved, and proved or pending?
def trace.claim(+lv: String, +st: String) -> Bool:
  Bool.and(String.eq(lv, "Proved"), Bool.or(String.eq(st, "proved"), String.eq(st, "pending")))

# does a row that is a claim list the ID?
def trace.claimed(rs: List<&2, Trace.Row>, +id: String) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{Trace.Row{+i, +lv, +st, _ls, _n}, rest}:
      Bool.or(Bool.and(trace.claim(lv, st), String.eq(i, id)), trace.claimed(rest, id))

# is the row's shape wrong: neither a claim nor a Trusted row with an empty
# status, a proved row that names no law, or a Trusted row that names one
def trace.misshapen(+lv: String, +st: String, +ls: List<&2, String>) -> Bool:
  +trusted = Bool.and(String.eq(lv, "Trusted"), String.is_empty(st))
  +none = List.is_empty(&2, String, ls)
  Bool.or(Bool.not(Bool.or(trace.claim(lv, st), trusted)),
    Bool.or(Bool.and(Bool.and(String.eq(lv, "Proved"), String.eq(st, "proved")), none),
      Bool.and(trusted, Bool.not(none))))

# the laws of the first LAWS.bend read at the path
def trace.file(ds: List<&2, Digest.Digest>, +pp: String) -> Maybe<&2, List<&2, Digest.Law>>:
  match ds:
    case Nil{}:
      None{}
    case Con{Digest.Digest{_path, +norm, _dir, is_laws, _lf, _ex, _tops, _says, _deps, _uns, laws}, rest}:
      Bool.pick(Maybe<&2, List<&2, Digest.Law>>, Bool.and(is_laws, String.eq(norm, pp)), Some{laws},
        trace.file(rest, pp))

# the first law of that name
def trace.law(ls: List<&2, Digest.Law>, +name: String) -> Maybe<&2, Digest.Law>:
  match ls:
    case Nil{}:
      None{}
    case Con{Digest.Law{+nn, +ll, +bb, +dd}, rest}:
      Bool.pick(Maybe<&2, Digest.Law>, String.eq(nn, name), Some{Digest.Law{nn, ll, bb, dd}}, trace.law(rest, name))

# is a line of the comment block the ID, spaces trimmed?
def trace.tagged(doc: List<&2, String>, +id: String) -> Bool:
  match doc:
    case Nil{}:
      False{}
    case Con{dd, rest}:
      Bool.or(String.eq(String.trim(dd), id), trace.tagged(rest, id))

# the defects of the law an entry names, if there is one: none, or no binder
# and no tag of the row
def trace.law_at(mm: Maybe<&2, Digest.Law>, +id: String) -> Nat:
  match mm:
    case None{}:
      1n
    case Some{Digest.Law{_n, _l, bb, dd}}:
      Nat.add(trace.one(Bool.not(bb)), trace.one(Bool.not(trace.tagged(dd, id))))

# the defects of an entry whose file was looked up: no such file, or the law's
def trace.file_at(mm: Maybe<&2, List<&2, Digest.Law>>, +name: String, +id: String) -> Nat:
  match mm:
    case None{}:
      1n
    case Some{ls}:
      trace.law_at(trace.law(ls, name), id)

# the defects of a Law entry, as its words: not `<path> <law>`, or the file's
def trace.entry(ws: List<&2, String>, +ds: List<&2, Digest.Digest>, +id: String) -> Nat:
  match ws:
    case Con{path, Con{name, Nil{}}}:
      trace.file_at(trace.file(ds, Imports.norm(path)), name, id)
    case _other:
      1n

# the defects of each Law entry of a row
def trace.entries(es: List<&2, String>, +ds: List<&2, Digest.Digest>, +id: String) -> Nat:
  match es:
    case Nil{}:
      0n
    case Con{e, rest}:
      Nat.add(trace.entry(String.split(e, ' '), ds, id), trace.entries(rest, ds, id))

# the defects of a requirement row, among the requirement rows rs and the
# trust rows ts: not an ID, listed twice, the wrong shape, Trusted with no
# trust row, and those of each Law entry when it is a claim
def trace.row(rr: Trace.Row, +rs: List<&2, Trace.Row>, +ts: List<&2, Trace.Mark>, +ds: List<&2, Digest.Digest>) -> Nat:
  match rr:
    case Trace.Row{+id, +lv, +st, +es, _n}:
      Nat.add(trace.one(Bool.not(trace.is_id(id))),
        Nat.add(trace.one(Nat.is_gt(trace.many(rs, id), 1n)),
          Nat.add(trace.one(trace.misshapen(lv, st, es)),
            Nat.add(trace.one(Bool.and(String.eq(lv, "Trusted"), Nat.is_eq(trace.marks(ts, id), 0n))),
              Bool.pick(Nat, trace.claim(lv, st), trace.entries(es, ds, id), 0n)))))

# the defects of each requirement row of xs
def trace.rows(
  xs: List<&2, Trace.Row>,
  +rs: List<&2, Trace.Row>,
  +ts: List<&2, Trace.Mark>,
  +ds: List<&2, Digest.Digest>
) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, rest}:
      Nat.add(trace.row(x, rs, ts, ds), trace.rows(rest, rs, ts, ds))

# the defects of each trust row of ms, among all: not an ID, listed twice
def trace.trust(ms: List<&2, Trace.Mark>, +all: List<&2, Trace.Mark>) -> Nat:
  match ms:
    case Nil{}:
      0n
    case Con{Trace.Mark{+id, _n}, rest}:
      Nat.add(Nat.add(trace.one(Bool.not(trace.is_id(id))), trace.one(Nat.is_gt(trace.marks(all, id), 1n))),
        trace.trust(rest, all))

# the tags of a comment block that name an ID no claim lists
def trace.stray(doc: List<&2, String>, +rs: List<&2, Trace.Row>) -> Nat:
  match doc:
    case Nil{}:
      0n
    case Con{dd, rest}:
      +tt = String.trim(dd)
      +mm = trace.stray(rest, rs)
      Bool.pick(Nat, Bool.and(trace.is_id(tt), Bool.not(trace.claimed(rs, tt))), 1n+mm, mm)

# the stray tags of each law
def trace.stray_laws(ls: List<&2, Digest.Law>, +rs: List<&2, Trace.Row>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Con{Digest.Law{_n, _l, _b, dd}, rest}:
      Nat.add(trace.stray(dd, rs), trace.stray_laws(rest, rs))

# the stray tags of each file read
def trace.strays(ds: List<&2, Digest.Digest>, +rs: List<&2, Trace.Row>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Digest.Digest{_path, _norm, _dir, _il, _lf, _ex, _tops, _says, _deps, _uns, laws}, rest}:
      Nat.add(trace.stray_laws(laws, rs), trace.strays(rest, rs))

# every defect of SPEC.md's lines against the files read: each table row with
# the wrong number of cells, each requirement row's, each trust row's, and
# each stray tag
def trace.count(+ls: List<&2, String>, +ds: List<&2, Digest.Digest>) -> Nat:
  +rs = trace.reqs(ls, 0, Trace.Out{})
  +ts = trace.trusts(ls, 0, Trace.Out{})
  Nat.add(trace.bad(ls, Trace.Out{}),
    Nat.add(trace.rows(rs, rs, ts, ds), Nat.add(trace.trust(ts, ts), trace.strays(ds, rs))))

# LAW: run over the whole tree, trace reports one finding for each defect of
# SPEC.md's text against the files read, as trace.count counts them, and
# nothing else: on a well-formed SPEC.md whose Law entries name quantified laws
# tagged with their rows, and whose tags name claims, it reports nothing
# BOLT-LAW-5
law trace_counts:
  for +text: String
  for +ds: List<&2, Digest.Digest>
  {List.length(&2, F.Finding, Trace.check(True{}, Some{text}, ds)) == trace.count(String.lines(text), ds) : Nat}

# LAW: run over the whole tree with no SPEC.md to read, trace reports that,
# once
# BOLT-LAW-5
law trace_unread:
  for +ds: List<&2, Digest.Digest>
  {List.length(&2, F.Finding, Trace.check(True{}, None{}, ds)) == 1n : Nat}

# LAW: run over files named on the line, trace reports nothing
# BOLT-LAW-5
law trace_named:
  for mm: Maybe<&2, String>
  for ds: List<&2, Digest.Digest>
  {Trace.check(False{}, mm, ds) == [] : List<&2, F.Finding>}

# coverage's reading of a file (BOLT-LAW-1). coverage_reports above states
# the rule over every list of digests; these state the digest of every file:
# what the rule grades in it (its path, whether it is a LAWS.bend, whether it
# is let off, its defs and types, and each type's constructors) and what its
# laws name, which is the binder's (BOLT-SYN-5) resolution of each use in the
# statement of a quantified law of a LAWS.bend. A use the binder resolves to
# an item of the file is a mention of that item of the law's own file; one it
# resolves through an import alias is a mention of the item of the file that
# import names. A binder, a free name (Base, or unknown), the law's own name
# (a binder), and every use in a closed law name nothing. So a type counts as
# named only when a law uses it or one of its constructors: a use of another
# def of its file is a mention of that def, never of the type.

# the constructors the outline lists right after a type, up to the next
# item that is not one
def coverage.ctors_of(items: List<&2, Outline.Item>) -> List<&2, String>:
  match items:
    case Con{Outline.Item{Outline.ICtor{}, name, _line, _sig, _doc, _path}, rest}:
      name <> coverage.ctors_of(rest)
    case _other:
      []

# the defs and types of the outline, each by name and line, a type with its
# constructors
def coverage.tops(items: List<&2, Outline.Item>) -> List<&2, Digest.Top>:
  match items:
    case Nil{}:
      []
    case Con{Outline.Item{Outline.IDef{}, name, line, _sig, _doc, _path}, rest}:
      Digest.Top{Outline.IDef{}, name, line, []} <> coverage.tops(rest)
    case Con{Outline.Item{Outline.IType{}, name, line, _sig, _doc, _path}, +rest}:
      Digest.Top{Outline.IType{}, name, line, coverage.ctors_of(rest)} <> coverage.tops(rest)
    case Con{_other, rest}:
      coverage.tops(rest)

# the file the first import of this alias names, resolved against the
# importing file
def coverage.alias(items: List<&2, Outline.Item>, +name: String, +from: String) -> Maybe<&2, String>:
  match items:
    case Nil{}:
      None{}
    case Con{Outline.Item{Outline.IImport{}, +nm, _line, _sig, _doc, +path}, rest}:
      +more = coverage.alias(rest, name, from)
      Bool.pick(Maybe<&2, String>, String.eq(nm, name), Some{Imports.resolve(from, path)}, more)
    case Con{_other, rest}:
      coverage.alias(rest, name, from)

# the item behind an alias, when an import names it
def coverage.behind(mm: Maybe<&2, String>, name: String) -> List<&2, Digest.Mention>:
  match mm:
    case None{}:
      []
    case Some{pp}:
      [Digest.Mention{pp, name}]

# what a use the binder resolved names: an item of the file, or an item
# behind an import alias; a binder or a free name names nothing
def coverage.target(tt: Bind.Target, items: List<&2, Outline.Item>, +file: String) -> List<&2, Digest.Mention>:
  match tt:
    case Bind.TItem{name}:
      [Digest.Mention{file, name}]
    case Bind.TQual{al, name}:
      coverage.behind(coverage.alias(items, al, file), name)
    case _other:
      []

# is the line on the statement of a quantified law of the tree: from its
# header's first token to its body's last?
def coverage.in_law(root: Tree.Node, +ln: U32) -> Bool:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SLaw{}, kids, +body}, rest}:
      Bool.or(Bool.and(Closed.binds(body), Bool.and(U32.is_le(Tree.line(kids), ln),
        U32.is_le(ln, Tree.line.of(List.head(&2, Lex.Tok, Tree.leaves.go(body, [])))))), coverage.in_law(rest, ln))
    case Tree.NCons{_h, rest}:
      coverage.in_law(rest, ln)
    case _other:
      False{}

# what the uses on the quantified laws' statements name, in order
def coverage.said(
  us: List<&2, Bind.Use>,
  +root: Tree.Node,
  +items: List<&2, Outline.Item>,
  +file: String
) -> List<&2, Digest.Mention>:
  match us:
    case Nil{}:
      []
    case Con{Bind.Use{_n, ln, _c, tt}, rest}:
      +more = coverage.said(rest, root, items, file)
      Bool.pick(List<&2, Digest.Mention>, coverage.in_law(root, ln),
        List.append(&2, Digest.Mention, coverage.target(tt, items, file), more), more)

# the uses the binder recorded
def coverage.uses(bb: Bind.Bound) -> List<&2, Bind.Use>:
  match bb:
    case Bind.Bound{_bs, us, _scs}:
      us

# what the coverage rule reads of a digest
type CoverageView is Data:
  CoverageView{norm: String, is_laws: Bool, exempt: Bool, tops: List<&2, Digest.Top>, says: List<&2, Digest.Mention>}

# a digest as the coverage rule reads it
def coverage.view(dd: Digest.Digest) -> CoverageView:
  match dd:
    case Digest.Digest{_path, norm, _dir, is_laws, _is_law_file, exempt, tops, says, _deps, _unsafes, _laws}:
      CoverageView{norm, is_laws, exempt, tops, says}

# LAW: whatever a file's text, tokens, tree, binding structure and outline,
# its digest grades it at its normalized path, is a LAWS.bend by its path, is
# let off exactly when that path is a law file or a test, lists the outline's
# defs and types (a type with the constructors listed right after it), and
# names, when it is a LAWS.bend, exactly what the binder resolved each use on
# a quantified law's statement to, through an import alias or in the file;
# any other file names nothing
# BOLT-LAW-1
law coverage_digest:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {coverage.view(Digest.of(Src.Src{path, text, toks, tree, bound, items}))
    == CoverageView{Imports.norm(path), Paths.is_laws(path),
      Bool.or(Paths.is_law_file(Imports.norm(path)), Paths.is_test(Imports.norm(path))), coverage.tops(items),
      Bool.pick(List<&2, Digest.Mention>, Paths.is_laws(path),
        coverage.said(coverage.uses(bound), tree, items, Imports.norm(path)), [])}
    : CoverageView}

# LAW: read from its path and text as the linter reads every file, a file's
# laws name exactly what the binder (Bind.of_tree, BOLT-SYN-5) resolves each
# use on a quantified law's statement to, when the file is a LAWS.bend
# BOLT-LAW-1
law coverage_binder:
  for +path: String
  for +text: String
  {coverage.view(Digest.of(Src.of(path, text)))
    == CoverageView{Imports.norm(path), Paths.is_laws(path),
      Bool.or(Paths.is_law_file(Imports.norm(path)), Paths.is_test(Imports.norm(path))),
      coverage.tops(Outline.of_tokens(text, Lex.tokens(text))),
      Bool.pick(List<&2, Digest.Mention>, Paths.is_laws(path),
        coverage.said(coverage.uses(Bind.of_tree(Tree.parse(text), String.lines(text))), Tree.parse(text),
          Outline.of_tokens(text, Lex.tokens(text)), Imports.norm(path)), [])}
    : CoverageView}

# unsafe (BOLT-LAW-3), the reach. unsafe_reports reads what a law file
# reaches as unsafe.closure, the import walk the rule runs. These laws pin
# that walk to a spec written apart from it: the files in the run are the
# digests' paths, a file imports what its digest records, and what a file
# reaches is the least list that holds it and is shut: every file in the run
# that one of its files imports is in it. The walk counts down a fuel of one
# per digest; unsafe_shut says it never runs out.

# what the file at pp imports relatively, as the first digest of that path
# records it; nothing when no digest has the path
def unsafe.imports(ds: List<&2, Digest.Digest>, +pp: String) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      +more = unsafe.imports(rest, pp)
      Bool.pick(List<&2, String>, String.eq(norm, pp), deps, more)

# is the file at pp in the run: does a digest have that path?
def unsafe.read(ds: List<&2, Digest.Digest>, +pp: String) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      +more = unsafe.read(rest, pp)
      Bool.or(String.eq(norm, pp), more)

# every path of xs that is in the run is in ss
def unsafe.held(+ds: List<&2, Digest.Digest>, +ss: List<&2, String>, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      +more = unsafe.held(ds, ss, rest)
      Bool.and(Bool.or(Bool.not(unsafe.read(ds, x)), Imports.has(ss, x)), more)

# ss is shut over ps: every file in the run that a file of ps imports is in ss
def unsafe.shut(+ds: List<&2, Digest.Digest>, +ss: List<&2, String>, ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+p, rest}:
      +more = unsafe.shut(ds, ss, rest)
      Bool.and(unsafe.held(ds, ss, unsafe.imports(ds, p)), more)

# LAW: over every list of digests, what the file at from reaches holds it
# BOLT-LAW-3
law unsafe_from:
  for +ds: List<&2, Digest.Digest>
  for +from: String
  {Imports.has(unsafe.closure(ds, from), from) == True{} : Bool}

# LAW: over every list of digests, what a file reaches is shut: every file in
# the run that one of its files imports is in it. So the walk's fuel never
# cuts it short
# BOLT-LAW-3
law unsafe_shut:
  for +ds: List<&2, Digest.Digest>
  for +from: String
  {unsafe.shut(ds, unsafe.closure(ds, from), unsafe.closure(ds, from)) == True{} : Bool}

# LAW: and it is the least such list: every list that holds from and is shut
# holds each file it reaches, so it reaches only files a chain of relative
# imports through the run leads to
# BOLT-LAW-3
law unsafe_least:
  for +ds: List<&2, Digest.Digest>
  for +from: String
  for +ss: List<&2, String>
  for +pp: String
  for hf: {Imports.has(ss, from) == True{} : Bool}
  for hs: {unsafe.shut(ds, ss, ss) == True{} : Bool}
  for hp: {Imports.has(unsafe.closure(ds, from), pp) == True{} : Bool}
  {Imports.has(ss, pp) == True{} : Bool}

# Inert text (BOLT-RULE-INERT). A comment or a string literal says what it
# likes: changing what it says leaves every rule whose pattern is code with
# the same findings. A source is read here with each such token cut to its
# first char (`#` or `"`), everything else left as it is; two sources that
# read the same that way differ at most in what their comments and strings
# say, token for token, kinds and positions kept. The lexer starts a token
# with `"` or `#` exactly when it is a string or a comment (inert.ok): what
# a rule compares a string's text with, a name or a keyword, never starts
# that way.

# a comment or a string literal: a token whose text is not code
def inert.blanks(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TStr{}:
      True{}
    case Lex.TComment{}:
      True{}
    case other:
      False{}

# a text cut to its first char
def inert.cut(tt: String) -> String:
  match tt:
    case SNil{}:
      SNil{}
    case SCon{h, _t}:
      SCon{h, SNil{}}

# the text, cut when it is not code
def inert.keep(bb: Bool, tt: String) -> String:
  match bb:
    case True{}:
      inert.cut(tt)
    case False{}:
      tt

# a token with what it says cut when it is a comment or a string
def inert.tok(tk: Lex.Tok) -> Lex.Tok:
  match tk:
    case Lex.Tok{+k, t, l, c}:
      Lex.Tok{k, inert.keep(inert.blanks(k), t), l, c}

# the tokens, each read that way
def inert.toks(ts: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      inert.tok(h) <> inert.toks(t)

# a tree with each leaf read that way; brackets and statement kinds as they are
def inert.node(nn: Tree.Node) -> Tree.Node:
  match nn:
    case Tree.Leaf{tok}:
      Tree.Leaf{inert.tok(tok)}
    case Tree.Group{open, kids, close}:
      Tree.Group{open, inert.node(kids), close}
    case Tree.Stmt{kind, kids, body}:
      Tree.Stmt{kind, inert.node(kids), inert.node(body)}
    case Tree.NNil{}:
      Tree.NNil{}
    case Tree.NCons{h, t}:
      Tree.NCons{inert.node(h), inert.node(t)}

# `"` or `#`: the first char of a string or a comment
def inert.mark(cc: Char) -> Bool:
  match cc:
    case Chr{+x}:
      Bool.or(U32.is_eq(x, 34), U32.is_eq(x, 35))

# does the text start with `"` or `#`?
def inert.marked(tt: String) -> Bool:
  match tt:
    case SNil{}:
      False{}
    case SCon{h, _t}:
      inert.mark(h)

# a text starts with `"` or `#` exactly when bb says it is not code
def inert.fits.go(bb: Bool, tt: String) -> Bool:
  match bb:
    case True{}:
      inert.marked(tt)
    case False{}:
      Bool.not(inert.marked(tt))

# a token as the lexer makes it: marked exactly when it is a comment or a string
def inert.fits(tk: Lex.Tok) -> Bool:
  match tk:
    case Lex.Tok{+k, t, _l, _c}:
      inert.fits.go(inert.blanks(k), t)

# every token as the lexer makes it
def inert.oks(ts: List<&2, Lex.Tok>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(inert.fits(h), inert.oks(t))

# every leaf as the lexer makes it
def inert.ok(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.Leaf{tok}:
      inert.fits(tok)
    case Tree.Group{_open, kids, _close}:
      inert.ok(kids)
    case Tree.Stmt{_kind, kids, body}:
      Bool.and(inert.ok(kids), inert.ok(body))
    case Tree.NNil{}:
      True{}
    case Tree.NCons{h, t}:
      Bool.and(inert.ok(h), inert.ok(t))

# LAW: hole reads what no comment or string says: two sources whose tokens
# read the same with comments and strings cut have the same findings
# BOLT-RULE-INERT
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
  for e: {inert.toks(toks) == inert.toks(toks2) : List<&2, Lex.Tok>}
  {Hole.check(Src.Src{path, text, toks, tree, bound, items})
    == Hole.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: put reads what no comment or string says: two sources as the lexer
# makes them whose tokens read the same with comments and strings cut have
# the same findings
# BOLT-RULE-INERT
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
  for ok: {inert.oks(toks) == True{} : Bool}
  for ok2: {inert.oks(toks2) == True{} : Bool}
  for e: {inert.toks(toks) == inert.toks(toks2) : List<&2, Lex.Tok>}
  {Put.check(Src.Src{path, text, toks, tree, bound, items})
    == Put.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: tail reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings (a
# string's text is only ever compared with the def's name or `Bool.pick`)
# BOLT-RULE-INERT
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
  for +ok: {inert.ok(tree) == True{} : Bool}
  for +ok2: {inert.ok(tree2) == True{} : Bool}
  for e: {inert.node(tree) == inert.node(tree2) : Tree.Node}
  {Tail.check(Src.Src{path, text, toks, tree, bound, items})
    == Tail.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: pick reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings
# BOLT-RULE-INERT
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
  for +ok: {inert.ok(tree) == True{} : Bool}
  for +ok2: {inert.ok(tree2) == True{} : Bool}
  for e: {inert.node(tree) == inert.node(tree2) : Tree.Node}
  {Pick.check(Src.Src{path, text, toks, tree, bound, items})
    == Pick.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: strict reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings
# BOLT-RULE-INERT
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
  for +ok: {inert.ok(tree) == True{} : Bool}
  for +ok2: {inert.ok(tree2) == True{} : Bool}
  for e: {inert.node(tree) == inert.node(tree2) : Tree.Node}
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

# which lines start with `#`
def inert.hashes(ls: List<&2, String>) -> List<&2, Bool>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      String.starts_with(h, "#") <> inert.hashes(t)

# LAW: doc reads no comment or string: two sources whose items have the same
# kinds, names and lines, and whose lines (one that starts inside a string
# literal read as empty) start with `#` alike, have the same findings, what
# their comments and strings say aside
# BOLT-RULE-INERT
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
  for el: {inert.hashes(Doc.lines(text, toks)) == inert.hashes(Doc.lines(text2, toks2)) : List<&2, Bool>}
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
# BOLT-RULE-INERT
law inert_param:
  for +b1: List<&2, Bind.Bind>
  for +b2: List<&2, Bind.Bind>
  for +path: String
  for e: {inert.binds(b1) == inert.binds(b2) : List<&2, Bind.Bind>}
  {Param.check.on(b1, path) == Param.check.on(b2, path) : List<&2, F.Finding>}

# LAW: table reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings (a
# string's text is only ever compared with a call's or a table's name)
# BOLT-RULE-INERT
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
  for +ok: {inert.ok(tree) == True{} : Bool}
  for +ok2: {inert.ok(tree2) == True{} : Bool}
  for e: {inert.node(tree) == inert.node(tree2) : Tree.Node}
  {Table.check(Src.Src{path, text, toks, tree, bound, items})
    == Table.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: index reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings
# BOLT-RULE-INERT
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
  for +ok: {inert.ok(tree) == True{} : Bool}
  for +ok2: {inert.ok(tree2) == True{} : Bool}
  for e: {inert.node(tree) == inert.node(tree2) : Tree.Node}
  {Index.check(Src.Src{path, text, toks, tree, bound, items})
    == Index.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: concat reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings
# BOLT-RULE-INERT
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
  for +ok: {inert.ok(tree) == True{} : Bool}
  for +ok2: {inert.ok(tree2) == True{} : Bool}
  for e: {inert.node(tree) == inert.node(tree2) : Tree.Node}
  {Concat.check(Src.Src{path, text, toks, tree, bound, items})
    == Concat.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: unit reads what no string says: two sources as the lexer makes them
# whose trees read the same with strings cut have the same findings
# BOLT-RULE-INERT
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
  for +ok: {inert.ok(tree) == True{} : Bool}
  for +ok2: {inert.ok(tree2) == True{} : Bool}
  for e: {inert.node(tree) == inert.node(tree2) : Tree.Node}
  {UnitRule.check(Src.Src{path, text, toks, tree, bound, items})
    == UnitRule.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}
