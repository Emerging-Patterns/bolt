# rule rewalk: one straight piece of a def calls the same walk twice on the
# same argument, and one result is used only for a single value (a get of one
# index, one field, or a let whose name is only read that way) while the other
# result is kept whole. Take the value from that other result. The same
# argument is the same text with no let of any name it uses (`=` or `<-`,
# taking effect at the end of the let) between the two calls. A different
# case arm is a different path, and two narrow reads are left alone. A walk is
# a def of this file that loops, or a Base walk (`List.map` and the like).
# Laws and proofs do not run. This is not `twice`, which is duplicate literals
# in a list pattern.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../calls.bend as Calls
import ../../../lazy/lazy.bend as Lazy

# how the result of a call is used
type How is Data:
  HWide{}
  HSlot{}
  HLet{binder: String}
  HField{}

# one expensive call
type Site is Data:
  Site{name: String, args: String, line: U32, col: U32, len: U32, how: How}

# a narrow read and a wide read of one name
type Hit is Data:
  Hit{wide: Bool, slot: Bool}

# where an accessor reads its collection
type Slot is Data:
  Slot{on: Bool, at: Nat}

# a position a mark pass recorded
type Pos is Data:
  Pos{line: U32, col: U32}

# the left of `=` : one name, and whether a group makes it a field
type Lhs is Data:
  Lhs{seen: Bool, extra: Bool, field: Bool, nm: String}

# a let of one name, and where it takes effect
type Bind is Data:
  Bind{nm: String, line: U32, col: U32}

# a let whose right-hand side is one call
type Note is Data:
  Note{line: U32, col: U32, how: How}

# neither read
def none_hit() -> Hit:
  Hit{False{}, False{}}

# either read from two results
def either(aa: Hit, +bb: Hit) -> Hit:
  Hit{+w1, +s1} = aa
  Hit{+w2, +s2} = bb
  Hit{Bool.or(w1, w2), Bool.or(s1, s2)}

# a mention of the name: wide, unless this position is a narrow slot
def name_slot(+slot: Bool) -> Hit:
  match slot:
    case True{}:
      Hit{False{}, True{}}
    case False{}:
      Hit{True{}, False{}}

# a mention of the name, or nothing when it is a different name
def name_hit(+same: Bool, +slot: Bool) -> Hit:
  match same:
    case False{}:
      none_hit()
    case True{}:
      name_slot(slot)

# which argument a narrow accessor reads
def slot_pick(+list: Bool, +str: Bool, +arr: Bool) -> Slot:
  match list str arr:
    case True{} b c:
      Slot{True{}, 2n}
    case False{} True{} c:
      Slot{True{}, 0n}
    case False{} False{} True{}:
      Slot{True{}, 1n}
    case False{} False{} False{}:
      Slot{False{}, 0n}

# List.get / head / last / length, String.get / length, Array.get; not List.set
def slot_of(+tt: String) -> Slot:
  slot_pick(
    List.contains(~String, ~String.eq, ["List.get", "List.head", "List.last", "List.length"], tt),
    Bool.or(String.eq(tt, "String.get"), String.eq(tt, "String.length")),
    String.eq(tt, "Array.get"))

# after a comma, still inside the slot argument?
def step_is_zero(pp: Nat) -> Bool:
  match pp:
    case 0n:
      True{}
    case 1n+k:
      False{}

# after a comma, is the next argument the slot?
def step_hot_live(left: Nat) -> Bool:
  match left:
    case 0n:
      False{}
    case 1n+p:
      step_is_zero(p)

# the slot flag after a comma
def step_hot(+hot: Bool, +left: Nat, +live: Bool) -> Bool:
  match live:
    case False{}:
      hot
    case True{}:
      step_hot_live(left)

# the arguments still to skip after a comma
def step_left_live(left: Nat) -> Nat:
  match left:
    case 0n:
      0n
    case 1n+p:
      p

# the arguments still to skip after a comma
def step_left(+left: Nat, +live: Bool) -> Nat:
  match live:
    case False{}:
      left
    case True{}:
      step_left_live(left)

# the chain is exactly one call
def as_open(+open: Bool, tok: Lex.Tok) -> Maybe<&2, Lex.Tok>:
  match open:
    case True{}:
      Some{tok}
    case False{}:
      None{}

# the inside of one pair of parentheses, when it is exactly a call
def as_inside(nn: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match nn:
    case Tree.NCons{Tree.Leaf{tok}, Tree.NCons{Tree.Group{Lex.Tok{k, +o, l, c}, kids, close}, Tree.NNil{}}}:
      as_open(String.eq(o, "("), tok)
    case other:
      None{}

# a parenthesized call, or nothing
def as_wrapped(+paren: Bool, kids: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match paren:
    case True{}:
      as_inside(kids)
    case False{}:
      None{}

# the chain is exactly one call, or one pair of parentheses around one: its callee
def as_call(nn: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match nn:
    case Tree.NCons{Tree.Group{Lex.Tok{k, +o, l, c}, +kids, close}, Tree.NNil{}}:
      as_wrapped(String.eq(o, "("), kids)
    case Tree.NCons{Tree.Leaf{tok}, Tree.NCons{Tree.Group{Lex.Tok{k, +o, l, c}, kids, close}, Tree.NNil{}}}:
      as_open(String.eq(o, "("), tok)
    case other:
      None{}

# the callee, when this argument is exactly a call
def pos_of(mm: Maybe<&2, Lex.Tok>) -> List<&2, Pos>:
  match mm:
    case None{}:
      Nil{}
    case Some{Lex.Tok{k, t, l, c}}:
      [Pos{l, c}]

# the collection argument's call, when this is a narrow accessor
def mark_slot(ss: Slot, +as: List<&2, Tree.Node>) -> List<&2, Pos>:
  Slot{on, at} = ss
  match on:
    case False{}:
      Nil{}
    case True{}:
      pos_of(as_call(Calls.arg(as, at)))

# calls that sit in a narrow accessor's collection argument
def mark(nn: Tree.Node) -> List<&2, Pos>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +here = Lazy.stop(List<&2, Pos>, Bool.not(String.eq(o, "(")), [], _u => mark_slot(slot_of(t), Calls.args(kids)))
      List.concat(&2, Pos, [here, mark(kids), mark(rest)])
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      List.concat(&2, Pos, [mark(kids), mark(rest)])
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, +kids, body}, rest}:
      List.concat(&2, Pos, [mark(kids), mark(rest)])
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      List.concat(&2, Pos, [mark(kids), mark(body), mark(rest)])
    case Tree.NCons{h, rest}:
      mark(rest)
    case other:
      Nil{}

# the name before a group is a narrow read, a callee, or an ordinary mention
def here_call(+call: Bool, +tt: String, +name: String, +hot: Bool) -> Hit:
  match call:
    case True{}:
      name_hit(String.eq(tt, name), False{})
    case False{}:
      name_hit(String.eq(tt, name), hot)

# the name before a group is a narrow read, a callee, or an ordinary mention
def here_hit(+brack: Bool, +call: Bool, +tt: String, +name: String, +hot: Bool) -> Hit:
  match brack:
    case True{}:
      name_hit(String.eq(tt, name), True{})
    case False{}:
      here_call(call, tt, name, hot)

# a bracket's inside is cold; a call's arguments start before the slot
def inner_hot_call(+call: Bool, +hot: Bool) -> Bool:
  match call:
    case True{}:
      False{}
    case False{}:
      hot

# a bracket's inside is cold; a call's arguments start before the slot
def inner_hot(+brack: Bool, +call: Bool, +hot: Bool) -> Bool:
  match brack:
    case True{}:
      False{}
    case False{}:
      inner_hot_call(call, hot)

# the argument index a slot reads
def slot_at(ss: Slot) -> Nat:
  Slot{on, at} = ss
  at

# the slot index of a call; a bracket has none
def inner_left_call(+call: Bool, +tt: String) -> Nat:
  match call:
    case True{}:
      slot_at(slot_of(tt))
    case False{}:
      0n

# the slot index of a call; a bracket has none
def inner_left(+brack: Bool, +call: Bool, +tt: String) -> Nat:
  match brack:
    case True{}:
      0n
    case False{}:
      inner_left_call(call, tt)

# whether an accessor has a collection argument
def slot_on(ss: Slot) -> Bool:
  Slot{on, at} = ss
  on

# only a call's arguments count commas as separators
def inner_live_call(+call: Bool, +tt: String) -> Bool:
  match call:
    case True{}:
      slot_on(slot_of(tt))
    case False{}:
      False{}

# only a call's arguments count commas as separators
def inner_live(+brack: Bool, +call: Bool, +tt: String) -> Bool:
  match brack:
    case True{}:
      False{}
    case False{}:
      inner_live_call(call, tt)

# does the chain bind?
def has_eq(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest}:
      True{}
    case Tree.NCons{h, rest}:
      has_eq(rest)
    case other:
      False{}

# a read counts only once the left of `=` is over
def hit_keep(skip: Bool, hh: Hit) -> Hit:
  match skip:
    case True{}:
      none_hit()
    case False{}:
      hh

# inside a call, unless this chain is still the left of a let
def pick_hot(+skip: Bool, +brack: Bool, +call: Bool, +hot: Bool) -> Bool:
  match skip:
    case True{}:
      False{}
    case False{}:
      inner_hot(brack, call, hot)

# inside a call, unless this chain is still the left of a let
def pick_left(+skip: Bool, +brack: Bool, +call: Bool, +tt: String) -> Nat:
  match skip:
    case True{}:
      0n
    case False{}:
      inner_left(brack, call, tt)

# inside a call, unless this chain is still the left of a let
def pick_live(+skip: Bool, +brack: Bool, +call: Bool, +tt: String) -> Bool:
  match skip:
    case True{}:
      False{}
    case False{}:
      inner_live(brack, call, tt)

# reads of the name. hot: this chain is a collection argument. live/left: commas
# count toward that argument. skip: ignore names until `=` (the left of a let)
def hits(nn: Tree.Node, +name: String, +hot: Bool, +left: Nat, +live: Bool, +skip: Bool) -> Hit:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest}:
      hits(rest, name, hot, left, live, False{})
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, rest}:
      hits(rest, name, step_hot(hot, left, live), step_left(left, live), live, skip)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +brack = String.eq(o, "[")
      +call = String.eq(o, "(")
      +here = hit_keep(skip, here_hit(brack, call, t, name, hot))
      +inn = hits(kids, name, pick_hot(skip, brack, call, hot), pick_left(skip, brack, call, t),
        pick_live(skip, brack, call, t), skip)
      +aft = hits(rest, name, hot, left, live, skip)
      either(here, either(inn, aft))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}, rest}:
      either(hit_keep(skip, name_hit(String.eq(t, name), hot)), hits(rest, name, hot, left, live, skip))
    case Tree.NCons{Tree.Leaf{tok}, rest}:
      hits(rest, name, hot, left, live, skip)
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      either(hits(kids, name, hot, 0n, False{}, skip), hits(rest, name, hot, left, live, skip))
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      +eq = has_eq(kids)
      +inn = hits(kids, name, False{}, 0n, False{}, eq)
      +bod = hits(body, name, False{}, 0n, False{}, False{})
      +aft = hits(rest, name, hot, left, live, skip)
      either(inn, either(bod, aft))
    case Tree.NCons{h, rest}:
      hits(rest, name, hot, left, live, skip)
    case other:
      none_hit()

# a let of one name is narrow when that name is only read narrowly
def narrow_let(hh: Hit) -> Bool:
  Hit{wide, slot} = hh
  Bool.and(slot, Bool.not(wide))

# a slot or a field is narrow; a wide use is not; a let depends on the name's reads
def narrow(hh: How, +body: Tree.Node) -> Bool:
  match hh:
    case HWide{}:
      False{}
    case HSlot{}:
      True{}
    case HField{}:
      True{}
    case HLet{+binder}:
      narrow_let(hits(body, binder, False{}, 0n, False{}, False{}))

# every name a node calls
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

# defs of this file that loop
def loops(ds: List<&2, Calls.Def>) -> List<&2, String>:
  loops.go(ds, [])

# Base walks a rewalk cares about
def heavy(+tt: String) -> Bool:
  List.contains(~String, ~String.eq, [
    "List.map", "List.filter", "List.sort", "List.foldl", "List.foldr", "List.reverse", "List.concat",
    "Array.map", "Array.to_list",
    "String.reverse", "String.to_upper", "String.to_lower", "String.to_list", "String.from_list"], tt)

# a loop of this file, or a Base walk, and not this def itself
def expensive(+tt: String, +self: String, +lp: List<&2, String>) -> Bool:
  Bool.and(Bool.not(String.eq(tt, self)), Bool.or(heavy(tt), List.contains(~String, ~String.eq, lp, tt)))

# the rest of the chain indexes the call
def indexed(rest: Tree.Node) -> Bool:
  match rest:
    case Tree.NCons{Tree.Group{Lex.Tok{k, +o, l, c}, kids, close}, tail}:
      String.eq(o, "[")
    case other:
      False{}

# a slot when the call is indexed, otherwise wide, when the call is expensive
def how_of(+nar: Bool) -> How:
  match nar:
    case True{}:
      HSlot{}
    case False{}:
      HWide{}

# a slot when the call is indexed, otherwise wide, when the call is expensive
def site_how(+mine: Bool, +nar: Bool) -> Maybe<&2, How>:
  match mine:
    case False{}:
      None{}
    case True{}:
      Some{how_of(nar)}

# the call as a site, when it is one
def site_list(mm: Maybe<&2, How>, +name: String, +args: String, +line: U32, +col: U32, +len: U32) -> List<&2, Site>:
  match mm:
    case None{}:
      Nil{}
    case Some{how}:
      [Site{name, args, line, col, len, how}]

# one site when this application is an expensive call
def open_site(
  +open: Bool,
  +indexed: Bool,
  +tt: String,
  +args: String,
  +line: U32,
  +col: U32,
  +len: U32,
  +self: String,
  +lp: List<&2, String>
) -> List<&2, Site>:
  match open:
    case False{}:
      Nil{}
    case True{}:
      site_list(site_how(expensive(tt, self, lp), indexed), tt, args, line, col, len)

# every name under the node
def names(nn: Tree.Node, +acc: List<&2, String>) -> List<&2, String>:
  match nn:
    case Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}:
      t <> acc
    case Tree.Group{open, kids, close}:
      names(kids, acc)
    case Tree.Stmt{kind, kids, body}:
      names(body, names(kids, acc))
    case Tree.NCons{h, rest}:
      names(rest, names(h, acc))
    case other:
      acc

# the names a let binds: every name left of its `=` or `<-`
def lhs_names(nn: Tree.Node, +acc: List<&2, String>) -> List<&2, String>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest}:
      acc
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}}, rest}:
      acc
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}, rest}:
      lhs_names(rest, t <> acc)
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      lhs_names(rest, names(kids, acc))
    case Tree.NCons{h, rest}:
      lhs_names(rest, acc)
    case other:
      acc

# where a let's names take effect: its last token, after the right-hand side
def last_pos(ts: List<&2, Lex.Tok>) -> Pos:
  match ts:
    case Nil{}:
      Pos{0, 0}
    case Con{Lex.Tok{k, t, +l, +c}, rest}:
      Pos{l, c}

# one binding per name, at the let's end
def bind_all(ns: List<&2, String>, +line: U32, +col: U32, +acc: List<&2, Bind>) -> List<&2, Bind>:
  match ns:
    case Nil{}:
      acc
    case Con{+nm, rest}:
      bind_all(rest, line, col, Bind{nm, line, col} <> acc)

# one binding per name, at this position
def bind_at(ns: List<&2, String>, pp: Pos, +acc: List<&2, Bind>) -> List<&2, Bind>:
  Pos{line, col} = pp
  bind_all(ns, line, col, acc)

# the lets of one straight piece; a case arm is not part of it
def binds(nn: Tree.Node, +acc: List<&2, Bind>) -> List<&2, Bind>:
  match nn:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, body}, rest}:
      binds(rest, acc)
    case Tree.NCons{Tree.Stmt{Tree.SLet{}, +kids, +body}, rest}:
      +here = bind_at(lhs_names(kids, []), last_pos(Tree.leaves.go(body, Tree.leaves.go(kids, []))), acc)
      binds(rest, binds(body, here))
    case Tree.NCons{Tree.Stmt{kind, kids, +body}, rest}:
      binds(rest, binds(body, acc))
    case Tree.NCons{h, rest}:
      binds(rest, acc)
    case other:
      acc

# (l1, c1) comes before (l2, c2)
def before(+l1: U32, +c1: U32, +l2: U32, +c2: U32) -> Bool:
  Bool.or(U32.is_lt(l1, l2), Bool.and(U32.is_eq(l1, l2), U32.is_lt(c1, c2)))

# how many lets of this name take effect before this position
def count(bs: List<&2, Bind>, +name: String, +line: U32, +col: U32) -> U32:
  match bs:
    case Nil{}:
      0
    case Con{Bind{+nm, +l, +c}, rest}:
      +more = count(rest, name, line, col)
      Bool.pick(U32, Bool.and(String.eq(nm, name), before(l, c, line, col)), (more + 1 : U32), more)

# which binding of each name an argument reads: two calls with the same text
# read the same values only when no let of those names sits between them
def stamp(ns: List<&2, String>, +bs: List<&2, Bind>, +line: U32, +col: U32) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{+nm, rest}:
      "|" ++ nm ++ "=" ++ U32.show(count(bs, nm, line, col)) ++ stamp(rest, bs, line, col)

# every expensive call, wide unless the call is indexed on the spot; its
# arguments are their text and which let of each name they read
def gather(nn: Tree.Node, +self: String, +lp: List<&2, String>, +bs: List<&2, Bind>) -> List<&2, Site>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, +l, +c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, +rest}}:
      +args = Tree.show(kids) ++ stamp(names(kids, []), bs, l, c)
      +here = open_site(String.eq(o, "("), indexed(rest), t, args, l, c,
        U32.from_nat(String.length(t)), self, lp)
      List.concat(&2, Site, [here, gather(kids, self, lp, bs), gather(rest, self, lp, bs)])
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      List.concat(&2, Site, [gather(kids, self, lp, bs), gather(rest, self, lp, bs)])
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, +kids, body}, rest}:
      List.concat(&2, Site, [gather(kids, self, lp, bs), gather(rest, self, lp, bs)])
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      List.concat(&2, Site, [gather(kids, self, lp, bs), gather(body, self, lp, bs), gather(rest, self, lp, bs)])
    case Tree.NCons{h, rest}:
      gather(rest, self, lp, bs)
    case other:
      Nil{}

# a second name on the left
def add_seen(+seen: Bool, +extra: Bool, +field: Bool, +nm: String, +tt: String) -> Lhs:
  match seen:
    case False{}:
      Lhs{True{}, extra, field, tt}
    case True{}:
      Lhs{True{}, True{}, field, nm}

# names inside a field group, which makes the let a field read
def fold_names(nn: Tree.Node, st: Lhs) -> Lhs:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}, rest}:
      Lhs{seen, extra, field, nm} = st
      fold_names(rest, add_seen(seen, extra, True{}, nm, t))
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      fold_names(rest, fold_names(kids, st))
    case Tree.NCons{h, rest}:
      fold_names(rest, st)
    case other:
      st

# the left of `=`
def eat(nn: Tree.Node, st: Lhs) -> Lhs:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest}:
      st
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}, rest}:
      Lhs{seen, extra, field, nm} = st
      eat(rest, add_seen(seen, extra, field, nm, t))
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      eat(rest, fold_names(kids, st))
    case Tree.NCons{h, rest}:
      eat(rest, st)
    case other:
      st

# a field when the left has a group, otherwise a let of that name
def note_how(+field: Bool, +nm: String) -> How:
  match field:
    case True{}:
      HField{}
    case False{}:
      HLet{nm}

# nothing, and the maybe is consumed
def note_none(mm: Maybe<&2, Lex.Tok>) -> Maybe<&2, Note>:
  match mm:
    case other:
      None{}

# the note when the right-hand side is a call
def note_some(+field: Bool, +nm: String, mm: Maybe<&2, Lex.Tok>) -> Maybe<&2, Note>:
  match mm:
    case Some{Lex.Tok{k, t, l, c}}:
      Some{Note{l, c, note_how(field, nm)}}
    case None{}:
      None{}

# the note for a call, when the left is exactly one name
def note_rhs(+one: Bool, +field: Bool, +nm: String, mm: Maybe<&2, Lex.Tok>) -> Maybe<&2, Note>:
  match one:
    case False{}:
      note_none(mm)
    case True{}:
      note_some(field, nm, mm)

# the tokens after `=`
def rhs_of(nn: Tree.Node) -> Tree.Node:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest}:
      rest
    case Tree.NCons{h, rest}:
      rhs_of(rest)
    case other:
      Tree.NNil{}

# a let or a field binding of exactly one call
def note_from(st: Lhs, +rhs: Tree.Node) -> Maybe<&2, Note>:
  Lhs{seen, extra, field, +nm} = st
  note_rhs(Bool.and(seen, Bool.not(extra)), field, nm, as_call(rhs))

# a let or a field binding of exactly one call
def note_st(+kids: Tree.Node) -> Maybe<&2, Note>:
  note_from(eat(kids, Lhs{False{}, False{}, False{}, ""}), rhs_of(kids))

# one site, retagged when it is the let's call
def retag_one(+hit: Bool, how: How, +note: How, +name: String, +args: String, +line: U32, +col: U32, +len: U32) -> Site:
  match hit:
    case True{}:
      Site{name, args, line, col, len, note}
    case False{}:
      Site{name, args, line, col, len, how}

# a note's line
def note_line(nn: Note) -> U32:
  Note{line, col, how} = nn
  line

# a note's column
def note_col(nn: Note) -> U32:
  Note{line, col, how} = nn
  col

# a note's how
def note_how_of(nn: Note) -> How:
  Note{line, col, how} = nn
  how

# sites whose callee is this let's call take its how
def retag(sites: List<&2, Site>, +note: Note) -> List<&2, Site>:
  match sites:
    case Nil{}:
      Nil{}
    case Con{Site{+name, +args, +line, +col, +len, how}, rest}:
      +nl = note_line(note)
      +nc = note_col(note)
      +nh = note_how_of(note)
      +hit = Bool.and(U32.is_eq(line, nl), U32.is_eq(col, nc))
      retag_one(hit, how, nh, name, args, line, col, len) <> retag(rest, note)

# retag when the statement is a let of a call
def retag_may(mm: Maybe<&2, Note>, sites: List<&2, Site>) -> List<&2, Site>:
  match mm:
    case None{}:
      sites
    case Some{note}:
      retag(sites, note)

# lets of a call retag that call
def apply(nn: Tree.Node, sites: List<&2, Site>) -> List<&2, Site>:
  match nn:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, body}, rest}:
      apply(rest, sites)
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      apply(rest, apply(body, retag_may(note_st(kids), sites)))
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      apply(rest, apply(kids, sites))
    case Tree.NCons{h, rest}:
      apply(rest, sites)
    case other:
      sites

# this position was marked a collection argument
def pinned(+line: U32, +col: U32, ps: List<&2, Pos>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{Pos{l, c}, rest}:
      +here = Bool.and(U32.is_eq(l, line), U32.is_eq(c, col))
      +more = pinned(line, col, rest)
      Bool.or(here, more)

# a wide call at a marked position becomes a slot; a let or a field stays
def pin_wide(how: How, +name: String, +args: String, +line: U32, +col: U32, +len: U32) -> Site:
  match how:
    case HWide{}:
      Site{name, args, line, col, len, HSlot{}}
    case other:
      Site{name, args, line, col, len, other}

# a wide call at a marked position becomes a slot
def pin_how(+hit: Bool, how: How, +name: String, +args: String, +line: U32, +col: U32, +len: U32) -> Site:
  match hit:
    case False{}:
      Site{name, args, line, col, len, how}
    case True{}:
      pin_wide(how, name, args, line, col, len)

# one site
def pin_one(ps: List<&2, Pos>, ss: Site) -> Site:
  Site{+name, +args, +line, +col, +len, how} = ss
  pin_how(pinned(line, col, ps), how, name, args, line, col, len)

# marked collection arguments become slots
def pin(+ps: List<&2, Pos>, sites: List<&2, Site>) -> List<&2, Site>:
  match sites:
    case Nil{}:
      Nil{}
    case Con{s, rest}:
      pin_one(ps, s) <> pin(ps, rest)

# the other site keeps the whole result
def other_full(+yes: Bool, how: How, +body: Tree.Node) -> Bool:
  match yes:
    case False{}:
      False{}
    case True{}:
      Bool.not(narrow(how, body))

# another site has the same callee and the same arguments, and keeps the whole result
def other_go(sites: List<&2, Site>, +name: String, +args: String, +line: U32, +col: U32, +body: Tree.Node) -> Bool:
  match sites:
    case Nil{}:
      False{}
    case Con{Site{+nm, +as, +l, +c, len, how}, rest}:
      +same = Bool.and(String.eq(nm, name), String.eq(as, args))
      +diff = Bool.not(Bool.and(U32.is_eq(l, line), U32.is_eq(c, col)))
      +here = other_full(Bool.and(same, diff), how, body)
      +more = other_go(rest, name, args, line, col, body)
      Bool.or(here, more)

# this earlier site is a narrow read of the same call
def earlier_nar(+yes: Bool, how: How, +body: Tree.Node) -> Bool:
  match yes:
    case False{}:
      False{}
    case True{}:
      narrow(how, body)

# this earlier site is a narrow read of the same call
def earlier_one(ss: Site, +name: String, +args: String, +line: U32, +col: U32, +body: Tree.Node) -> Bool:
  Site{+nm, +as, +l, +c, len, how} = ss
  +same = Bool.and(String.eq(nm, name), String.eq(as, args))
  +diff = Bool.not(Bool.and(U32.is_eq(l, line), U32.is_eq(c, col)))
  earlier_nar(Bool.and(same, diff), how, body)

# a narrow site of this call already reported
def earlier(seen: List<&2, Site>, +name: String, +args: String, +line: U32, +col: U32, +body: Tree.Node) -> Bool:
  match seen:
    case Nil{}:
      False{}
    case Con{s, rest}:
      +here = earlier_one(s, name, args, line, col, body)
      +more = earlier(rest, name, args, line, col, body)
      Bool.or(here, more)

# the finding when no earlier narrow site took this call
def report_fresh(
  +prior: Bool,
  +name: String,
  +line: U32,
  +col: U32,
  +len: U32,
  +path: String
) -> List<&2, F.Finding>:
  match prior:
    case False{}:
      [F.Finding{path, line, col, len, "rewalk",
        name ++ " walks the same argument twice, and one result is used only for a single value; take that value from the other result."}]
    case True{}:
      Nil{}

# the finding, when this is the first narrow site of a duplicated call
def report_nar(
  +nar: Bool,
  +prior: Bool,
  +name: String,
  +line: U32,
  +col: U32,
  +len: U32,
  +path: String
) -> List<&2, F.Finding>:
  match nar:
    case False{}:
      Nil{}
    case True{}:
      report_fresh(prior, name, line, col, len, path)

# the finding when a duplicate exists and this site is the first narrow one
def report_dup(
  +dup: Bool,
  how: How,
  +name: String,
  +args: String,
  +line: U32,
  +col: U32,
  +len: U32,
  +body: Tree.Node,
  +path: String,
  +seen: List<&2, Site>
) -> List<&2, F.Finding>:
  match dup:
    case False{}:
      Nil{}
    case True{}:
      report_nar(narrow(how, body), earlier(seen, name, args, line, col, body), name, line, col, len, path)


# one site
def report_one(
  ss: Site,
  +all: List<&2, Site>,
  +body: Tree.Node,
  +path: String,
  +seen: List<&2, Site>
) -> List<&2, F.Finding>:
  Site{+name, +args, +line, +col, +len, how} = ss
  report_dup(other_go(all, name, args, line, col, body), how, name, args, line, col, len, body, path, seen)

# the first narrow site of each duplicated call
def report(
  sites: List<&2, Site>,
  +all: List<&2, Site>,
  +body: Tree.Node,
  +path: String,
  +seen: List<&2, Site>
) -> List<&2, F.Finding>:
  match sites:
    case Nil{}:
      Nil{}
    case Con{+s, rest}:
      List.append(&2, F.Finding, report_one(s, all, body, path, seen), report(rest, all, body, path, s <> seen))

# findings in one straight region; a case arm is not part of it
def local(+nn: Tree.Node, +self: String, +lp: List<&2, String>, +path: String) -> List<&2, F.Finding>:
  +sites = pin(mark(nn), apply(nn, gather(nn, self, lp, binds(nn, []))))
  report(sites, sites, nn, path, [])

# each case arm on its own, so two arms are not one path
def visit(nn: Tree.Node, +self: String, +lp: List<&2, String>, +path: String) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, +body}, rest}:
      List.concat(&2, F.Finding, [local(body, self, lp, path), visit(body, self, lp, path),
        visit(rest, self, lp, path)])
    case Tree.NCons{Tree.Stmt{kind, +kids, +body}, rest}:
      List.concat(&2, F.Finding, [visit(kids, self, lp, path), visit(body, self, lp, path),
        visit(rest, self, lp, path)])
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      List.concat(&2, F.Finding, [visit(kids, self, lp, path), visit(rest, self, lp, path)])
    case Tree.NCons{h, rest}:
      visit(rest, self, lp, path)
    case other:
      Nil{}

def check.go(
  ds: List<&2, Calls.Def>,
  +lp: List<&2, String>,
  +path: String,
  acc: List<&2, List<&2, F.Finding>>
) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      check.go(rest, lp, path,
        Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
          _u => List.concat(&2, F.Finding, [local(body, name, lp, path), visit(body, name, lp, path)])) <> acc)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  +ds = Calls.defs(tree)
  check.go(ds, loops(ds), path, [])
