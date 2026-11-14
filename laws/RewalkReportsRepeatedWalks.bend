# `rewalk` reports exactly, in each straight piece of a def that is not a law
# or a proof (its body outside case arms, or one case arm's body), each call
# of a walk (a looping def of the file other than the def itself, or a listed
# Base walk) whose result is read for a single value (indexed on the spot, an
# accessor's collection argument, or alone the right of an `=` let of one name
# that is a record field or is read at least once and only indexed or as an
# accessor's collection argument) and follows no twin so read, when a twin
# keeps its result whole: another call in the piece, at another position, of
# the same walk on the same argument (the same text, and the same number of
# lets before it of each name in it).
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/pedantic/rewalk.bend as Rewalk
import ../src/rules/calls.bend as Calls

# The recursion rule, rewalk (laws/RewalkReportsRepeatedWalks.bend). It reads each def of the file
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
      List.concat(&2, Rewalk.Site, [Rewalk.open_site(String.eq(o, "("), Rewalk.indexed(rest), t, args, Rewalk.Spot{l,
        c, U32.from_nat(String.length(t))}, self, lp), rewalk.gather(kids, self, lp, bs),
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
law rewalk_local_counts:
  for +nn: Tree.Node
  for +self: String
  for +lp: List<&2, String>
  for +path: String
  {List.length(&2, F.Finding, Rewalk.local(nn, self, lp, path)) == rewalk.piece(nn, self, lp) : Nat}

# LAW: under any node, rewalk reports each case arm's piece on its own
law rewalk_visit_counts:
  for nn: Tree.Node
  for +self: String
  for +lp: List<&2, String>
  for +path: String
  {List.length(&2, F.Finding, Rewalk.visit(nn, self, lp, path)) == rewalk.arms(nn, self, lp) : Nat}

# LAW: rewalk reports exactly those findings, def by def, over the defs of
# the tree, with the looping defs the law finds
law rewalk_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Rewalk.check(Src.Src{path, text, toks, tree, bound, items}))
    == rewalk.total(Calls.defs(tree), rewalk.loops(Calls.defs(tree), []), path) : Nat}
