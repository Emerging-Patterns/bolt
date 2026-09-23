# rule eager: a branch of a `Bool.pick` calls a recursive def of the same
# file. Bool.pick is an ordinary def, so both branch arguments are evaluated
# before the call: the work in a branch runs whatever the condition says, and
# the condition never saves it. `pick` catches the self-call and `strict` the
# one under Bool.and/or; a call to a neighbour is the same bug and neither
# sees it (a game's overlap test moved out of a pick branch took a scene from
# 31 to 55 fps; one `gaps(..)` in a branch here ran on every file the linter
# read, 88 s of a 100 s run). Bind the call above the pick (`+x = gaps(..)`),
# or take the branch lazily (`Lazy.stop`, `Lazy.or_else` from lazy/lazy.bend:
# the last argument is a `Unit -> T` thunk, applied only on the branch that
# needs it). Two things keep it off idiomatic code: only a call to a def of
# this file counts, and only to one that loops (it calls itself, or reaches
# something that does), since a Base call and a one-line accessor are
# everywhere and cost nothing; only the branch arguments count, not the type
# and the condition, which run whatever is written; and what sits after a
# `=>` is a lambda's body, which the call does not run. The body ends at the
# next comma of its group, so an argument after it counts again.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../../../lazy/lazy.bend as Lazy
import ../calls.bend as Calls

# every name a node calls, `f(..)`, at any depth
def called(nn: Tree.Node) -> List<&2, String>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +more = List.concat(&2, String, [called(kids), called(rest)])
      Bool.pick(List<&2, String>, String.eq(o, "("), t <> more, more)
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      List.concat(&2, String, [called(kids), called(rest)])
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      List.concat(&2, String, [called(kids), called(body), called(rest)])
    case Tree.NCons{h, rest}:
      called(rest)
    case other:
      Nil{}

# does the list hold a name the set has?
def any_of(cs: List<&2, String>, +set: List<&2, String>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{c, t}:
      Lazy.or_else(List.contains(~String, ~String.eq, set, c), _u => any_of(t, set))

def loops.go(ds: List<&2, Calls.Def>, +acc: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      acc
    case Con{Calls.Def{+name, sig, body}, rest}:
      +cs = called(body)
      +deep = Bool.or(List.contains(~String, ~String.eq, cs, name), any_of(cs, acc))
      loops.go(rest, Bool.pick(List<&2, String>, deep, name <> acc, acc))

# the defs of the file that loop: one that calls itself, or that reaches one
# that does (a def is defined above its use and there is no mutual recursion,
# so one pass down the file settles it)
def loops(ds: List<&2, Calls.Def>) -> List<&2, String>:
  loops.go(ds, [])

# the hot a leaf leaves behind: a `=>` clears it for the lambda's body; a
# comma of a pick's own group moves to its next argument, hot from the third
# on (0 the type, 1 the condition, 2 and 3 the branches), and a comma of any
# other group returns it to keep; any other leaf leaves it as it was
def work.hot(kk: Lex.TokKind, +hot: Bool, +seg: U32, +keep: Bool) -> Bool:
  match kk:
    case Lex.TLam{}:
      False{}
    case Lex.TComma{}:
      +in_pick = U32.is_lt(seg, 9)
      +next = Bool.pick(U32, in_pick, (seg + 1 : U32), seg)
      Bool.pick(Bool, in_pick, Bool.not(U32.is_lt(next, 2)), keep)
    case other:
      hot

# the argument a leaf leaves behind: a comma of a pick's own group moves on
def work.seg(kk: Lex.TokKind, +seg: U32) -> U32:
  match kk:
    case Lex.TComma{}:
      Bool.pick(U32, U32.is_lt(seg, 9), (seg + 1 : U32), seg)
    case other:
      seg

# can the leaf name a call (it is neither a `=>` nor a comma)?
def work.name(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TLam{}:
      False{}
    case Lex.TComma{}:
      False{}
    case other:
      True{}

# the work under a def's body: hot says the node sits in a branch argument of
# a `Bool.pick` (so it runs whatever the condition), seg counts the arguments
# of the pick whose group this chain is (0 the type, 1 the condition, 2 and 3
# the branches; 9 for a chain that is not a pick's), and keep is what hot
# returns to at the next comma of a chain that is not a pick's, so a `=>`
# clears hot for the lambda's own body and not for the arguments after it. A
# leaf moves the state by its kind (work.hot, work.seg); a `=>` or a comma
# before a group names no call, so that group is walked as any other
def work(
  nn: Tree.Node,
  +ns: List<&2, String>,
  +self: String,
  +path: String,
  +hot: Bool,
  +seg: U32,
  +keep: Bool
) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, +t, +l, +c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +now = work.hot(k, hot, seg, keep)
      +call = Bool.and(work.name(k), String.eq(o, "("))
      +is_pick = Bool.and(call, String.eq(t, "Bool.pick"))
      +mine = Bool.and(Bool.not(String.eq(t, self)), List.contains(~String, ~String.eq, ns, t))
      +report = Bool.and(now, Bool.and(call, mine))
      +inner = Bool.and(now, Bool.not(is_pick))
      +more = List.concat(&2, F.Finding,
        [work(kids, ns, self, path, inner, Bool.pick(U32, is_pick, 0, 9), inner),
          work(rest, ns, self, path, now, work.seg(k, seg), keep)])
      Bool.pick(List<&2, F.Finding>, report,
        F.Finding{path, l, c, U32.from_nat(String.length(t)), "eager",
          t ++ " is called in a branch of Bool.pick, which evaluates both branches, so it runs whatever the condition; bind it above the pick, or use Lazy.stop."}
          <> more,
        more)
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, t, l, c}}, rest}:
      work(rest, ns, self, path, work.hot(k, hot, seg, keep), work.seg(k, seg), keep)
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      List.concat(&2, F.Finding, [work(kids, ns, self, path, hot, 9, hot), work(rest, ns, self, path, hot, seg, keep)])
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      List.concat(&2, F.Finding, [work(kids, ns, self, path, False{}, 9, False{}),
        work(body, ns, self, path, False{}, 9, False{}),
        work(rest, ns, self, path, hot, seg, keep)])
    case Tree.NCons{h, rest}:
      work(rest, ns, self, path, hot, seg, keep)
    case other:
      Nil{}

def check.go(
  ds: List<&2, Calls.Def>,
  +ns: List<&2, String>,
  +path: String,
  acc: List<&2, List<&2, F.Finding>>
) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, +sig, body}, rest}:
      check.go(rest, ns, path,
        Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
          _u => work(body, ns, name, path, False{}, 9, False{})) <> acc)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  +ds = Calls.defs(tree)
  check.go(ds, loops(ds), path, [])
