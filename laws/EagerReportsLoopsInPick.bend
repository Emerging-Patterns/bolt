# `eager` reports exactly a looping def of the file called in a `Bool.pick`
# branch.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/eager.bend as Eager
import ../src/rules/calls.bend as Calls

# eager (laws/EagerReportsLoopsInPick.bend). eager walks each def's body tree carrying three
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
law eager_plain:
  for kk: Lex.TokKind
  for +hot: Bool
  for +seg: U32
  for keep: Bool
  for e: {eager.plain(kk) == True{} : Bool}
  {(Eager.work.hot(kk, hot, seg, keep), Eager.work.seg(kk, seg), Eager.work.name(kk))
    == (hot, seg, True{}) : Bool & U32 & Bool}
