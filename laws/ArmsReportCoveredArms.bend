# `arms` also reports, in a match of any number of scrutinees and at any
# depth, each case arm that an arm above it in the same match covers, once,
# and nothing else; an arm its Nat check already reports
# (laws/ArmsReportCoveredNatArms.bend) is not reported again. The checker
# takes such an arm and the match answers with the one above, so it never
# runs.
#
# An arm's pattern is read as parts (Arms.read: Arms.parts, over its tokens
# up to the `:` that ends it; a pattern with no `:` among its own tokens
# wraps onto the next line, and is not read): a binder (a plain name or `_`), a word (a constructor's
# name, or a number or char literal), `kn+`, a string literal, a bracket, a
# comma and `<>`. An earlier pattern covers a later one (Arms.covers) when
# they read the same part for part, save that a binder of the earlier stands
# for a whole item of the later, and, when no `<>` follows the binder, for
# every `<> item` after that one too. The laws under the count say what that
# answers on the shapes a match is written in. The tree is read with what
# its string literals say left out (Arms.blank), so a string is never the
# same as another, and what one says changes no finding
# (laws/InertArmsCover.bend).
#
# Trusted, not proved: that an arm covered this way is one Bend's own
# matcher never reaches. bolt cannot call Bend's matcher from Bend; the
# reading is checked against bend 2.0.40 (a binder above a constructor arm,
# a literal twice, one shape under two sets of names, a two-scrutinee
# catch-all, each of which answers with the arm above).
#
# also rests on: laws/InertArmsCover.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/tokens.bend as T
import ../src/rules/correctness/arms.bend as Arms

# does the pattern of some arm above cover these parts?
def cover.some(seen: List<&2, Arms.Seen>, +ps: List<&2, Arms.Part>) -> Bool:
  match seen:
    case Nil{}:
      False{}
    case Con{Arms.Seen{line, parts}, rest}:
      Bool.or(Arms.covers(parts, Some{ps}), cover.some(rest, ps))

# how many of a match's case arms an arm above them covers, seen the arms
# above so far, those the Nat check reports left out: nat says the match has
# one scrutinee, so that check reads it, wide its widest n+p arm so far
def cover.arms(body: Tree.Node, +seen: List<&2, Arms.Seen>, +wide: Maybe<&2, Arms.Wide>, +nat: Bool) -> Nat:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, b}, rest}:
      +pat = T.pattern(kids)
      +m = cover.arms(rest, Arms.Seen{Tree.line(pat), Arms.read(pat)} <> seen, Arms.widen(wide, Arms.arm(pat)), nat)
      Bool.pick(Nat, Bool.and(Bool.not(Bool.and(nat, Arms.told(wide, Arms.arm(pat)))),
        cover.some(seen, Arms.read(pat))), 1n+m, m)
    case Tree.NCons{h, rest}:
      cover.arms(rest, seen, wide, nat)
    case other:
      0n

# how many covered arms the matches under the node hold, at any depth
def cover_count(nn: Tree.Node) -> Nat:
  match nn:
    case Tree.NCons{Tree.Stmt{kind, +kids, +body}, rest}:
      Nat.add(Bool.pick(Nat, T.keyword(kids, "match"), cover.arms(body, [], None{}, Arms.single(kids)), 0n),
        Nat.add(cover_count(body), cover_count(rest)))
    case Tree.NCons{h, rest}:
      cover_count(rest)
    case other:
      0n

# LAW: arms' cover check reports one finding for each case arm of a match,
# at any depth, that the pattern of an arm above it in the same match
# covers and the Nat check does not report, and none for any other arm
law arms_cover_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Arms.cover(Src.Src{path, text, toks, tree, bound, items}))
    == cover_count(Arms.blank(tree)) : Nat}

# LAW: a word covers a word exactly when their texts are the same: the same
# literal or constructor twice is covered, another is not
law arms_cover_word:
  for +tt: String
  for +uu: String
  {Arms.covers([Arms.PWord{tt}], Some{[Arms.PWord{uu}]}) == String.eq(tt, uu) : Bool}

# LAW: the same literal twice is covered (`case 139:` above `case 139:`)
law arms_cover_same_word:
  for +tt: String
  {Arms.covers([Arms.PWord{tt}], Some{[Arms.PWord{tt}]}) == True{} : Bool}

# LAW: a lone binder covers a literal or a constructor's name (`case other:`
# above `case 0:`)
law arms_cover_binder_word:
  for tt: String
  {Arms.covers([Arms.PAny{}], Some{[Arms.PWord{tt}]}) == True{} : Bool}

# LAW: a lone binder covers a constructor with its fields (`case other:`
# above `case Con{h, t}:`), whatever its brackets hold
law arms_cover_binder_ctor:
  for tt: String
  for open: String
  for close: String
  {Arms.covers([Arms.PAny{}],
    Some{[Arms.PWord{tt}, Arms.POpen{open}, Arms.PAny{}, Arms.PComma{}, Arms.PAny{}, Arms.PClose{close}]})
    == True{} : Bool}

# LAW: a lone binder covers a constructor that holds a constructor, to the
# bracket that closes the outer one (`case other:` above `case Some{Nil{}}:`)
law arms_cover_binder_nested:
  for tt: String
  for uu: String
  for open: String
  for close: String
  {Arms.covers([Arms.PAny{}], Some{[Arms.PWord{tt}, Arms.POpen{open}, Arms.PWord{uu}, Arms.POpen{open},
    Arms.PClose{close}, Arms.PClose{close}]}) == True{} : Bool}

# LAW: a binder covers a string literal, which is one item: two binders
# cover a string and a word (`case a b:` above `case "x" 0:`)
law arms_cover_binder_string:
  for tt: String
  {Arms.covers([Arms.PAny{}, Arms.PAny{}], Some{[Arms.PStr{}, Arms.PWord{tt}]}) == True{} : Bool}

# LAW: a lone binder covers `kn+p` (`case n:` above `case 2n+p:`)
law arms_cover_binder_plus:
  for tt: String
  {Arms.covers([Arms.PAny{}], Some{[Arms.PPlus{tt}, Arms.PAny{}]}) == True{} : Bool}

# LAW: a word never covers a binder: a literal or a constructor arm above a
# catch-all leaves the catch-all reachable
law arms_cover_word_not_binder:
  for tt: String
  {Arms.covers([Arms.PWord{tt}], Some{[Arms.PAny{}]}) == False{} : Bool}

# LAW: one shape under other names is covered: a constructor with two
# binders covers the same constructor with two binders (`case Some{x}:`
# above `case Some{y}:`; a binder's name is not read)
law arms_cover_same_shape:
  for +tt: String
  for +open: String
  for +close: String
  {Arms.covers([Arms.PWord{tt}, Arms.POpen{open}, Arms.PAny{}, Arms.PComma{}, Arms.PAny{}, Arms.PClose{close}],
    Some{[Arms.PWord{tt}, Arms.POpen{open}, Arms.PAny{}, Arms.PComma{}, Arms.PAny{}, Arms.PClose{close}]})
    == True{} : Bool}

# LAW: a binder a `<>` follows stands for one item, and the last binder for
# every `<> item` left: `h <> t` covers a list pattern of three items
law arms_cover_head_tail:
  for tt: String
  for uu: String
  for vv: String
  {Arms.covers([Arms.PAny{}, Arms.PCons{}, Arms.PAny{}],
    Some{[Arms.PWord{tt}, Arms.PCons{}, Arms.PWord{uu}, Arms.PCons{}, Arms.PWord{vv}]}) == True{} : Bool}

# LAW: a lone binder covers a whole list pattern, every `<> item` of it
# (`case xs:` above `case h <> Nil{}:`)
law arms_cover_binder_list:
  for tt: String
  for open: String
  for close: String
  {Arms.covers([Arms.PAny{}],
    Some{[Arms.PAny{}, Arms.PCons{}, Arms.PWord{tt}, Arms.POpen{open}, Arms.PClose{close}]}) == True{} : Bool}

# LAW: a longer list pattern does not cover a shorter one: `a <> b <> c`
# leaves `h <> t` reachable, whatever t is
law arms_cover_longer_not:
  for tt: String
  {Arms.covers([Arms.PAny{}, Arms.PCons{}, Arms.PAny{}, Arms.PCons{}, Arms.PAny{}],
    Some{[Arms.PAny{}, Arms.PCons{}, Arms.PWord{tt}]}) == False{} : Bool}

# LAW: a string literal covers nothing, itself included, whatever follows:
# what a string says is not read
law arms_cover_string_never:
  for +ps: List<&2, Arms.Part>
  for +qs: List<&2, Arms.Part>
  {Arms.covers(Arms.PStr{} <> ps, Some{Arms.PStr{} <> qs}) == False{} : Bool}

# LAW: what is not understood covers nothing
law arms_cover_unread_never:
  for +ps: List<&2, Arms.Part>
  for qs: List<&2, Arms.Part>
  {Arms.covers(Arms.PBad{} <> ps, Some{qs}) == False{} : Bool}

# LAW: nothing covers a pattern that was not read
law arms_cover_unread_not:
  for ps: List<&2, Arms.Part>
  {Arms.covers(ps, Some{[Arms.PBad{}]}) == False{} : Bool}

# LAW: a pattern with no `:` among its own tokens, one that wraps onto the
# next line, is not read: it is one part that is not understood
law arms_reads_wrapped:
  for +pat: Tree.Node
  for e: {Arms.ended(pat) == False{} : Bool}
  {Arms.read(pat) == [Arms.PBad{}] : List<&2, Arms.Part>}

# LAW: a pattern that ends at a `:` is read from its tokens up to it
law arms_reads_ended:
  for +pat: Tree.Node
  for e: {Arms.ended(pat) == True{} : Bool}
  {Arms.read(pat) == Arms.parts(Tree.leaves(Arms.cut(pat))) : List<&2, Arms.Part>}

# LAW: a plain name is read as a binder, whatever it is called
law arms_reads_name:
  for tt: String
  for ll: U32
  for cc: U32
  {Arms.parts([Lex.Tok{Lex.TName{}, tt, ll, cc}]) == [Arms.PAny{}] : List<&2, Arms.Part>}

# LAW: a plain name a `{` follows is a constructor's name, not a binder
law arms_reads_ctor:
  for tt: String
  for ll: U32
  for cc: U32
  {Arms.parts([Lex.Tok{Lex.TName{}, tt, ll, cc}, Lex.Tok{Lex.TOpen{}, "{", ll, cc}, Lex.Tok{Lex.TClose{}, "}", ll, cc}])
    == [Arms.PWord{tt}, Arms.POpen{"{"}, Arms.PClose{"}"}] : List<&2, Arms.Part>}

# LAW: a `+` before a name is a quantity mark and is not read: `+h` is a
# binder
law arms_reads_mark:
  for tt: String
  for ll: U32
  for cc: U32
  {Arms.parts([Lex.Tok{Lex.TOp{}, "+", ll, cc}, Lex.Tok{Lex.TName{}, tt, ll, cc}]) == [Arms.PAny{}]
    : List<&2, Arms.Part>}

# LAW: a number a `+` follows is `kn+`, and what it adds to is read after it
law arms_reads_plus:
  for +kk: String
  for tt: String
  for ll: U32
  for cc: U32
  {Arms.parts([Lex.Tok{Lex.TNum{}, kk, ll, cc}, Lex.Tok{Lex.TOp{}, "+", ll, cc}, Lex.Tok{Lex.TName{}, tt, ll, cc}])
    == [Arms.PPlus{kk}, Arms.PAny{}] : List<&2, Arms.Part>}

# LAW: a pattern ends at its `:`: an inline body after it is not read
# (`case 139: 1` is the pattern `139`)
law arms_reads_to_colon:
  for tt: String
  for uu: String
  for ll: U32
  for cc: U32
  for rest: Tree.Node
  {Arms.cut(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, tt, ll, cc}},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, uu, ll, cc}}, rest}})
    == Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, tt, ll, cc}}, Tree.NNil{}} : Tree.Node}

# LAW: a string literal is read as one part that holds nothing it says
law arms_reads_string:
  for tt: String
  for ll: U32
  for cc: U32
  {Arms.parts([Lex.Tok{Lex.TStr{}, tt, ll, cc}]) == [Arms.PStr{}] : List<&2, Arms.Part>}
