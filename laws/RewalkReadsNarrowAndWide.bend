# What rewalk reads before it decides (laws/RewalkReportsRepeatedWalks.bend
# says what it reports). A read of a name is wide (the whole value is used)
# or narrow (one element or the length is, through an accessor's slot or an
# index). The walk carries whether it is in an accessor's slot, how many
# arguments are left before it, and whether it is still on the left of a
# let. A call made twice is worth a finding when it is expensive: a Base walk
# or a loop of the file. Each law is one of those small decisions.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/rules/pedantic/rewalk.bend as Rewalk
import ./defs/Chains.bend as D2

# LAW: a different name is no read of the name
law name_hit_other_name:
  for +slot: Bool
  {Rewalk.name_hit(False{}, slot) == Rewalk.Hit{False{}, False{}} : Rewalk.Hit}

# LAW: the name itself is a narrow read in a narrow slot and a wide read
# anywhere else
law name_hit_same_name:
  for +slot: Bool
  {Rewalk.name_hit(True{}, slot)
    == Bool.pick(Rewalk.Hit, slot, Rewalk.Hit{False{}, True{}}, Rewalk.Hit{True{}, False{}}) : Rewalk.Hit}

# LAW: two results read the name wide when either does, and narrow when
# either does
law either_joins_reads:
  for w1: Bool
  for s1: Bool
  for w2: Bool
  for s2: Bool
  {Rewalk.either(Rewalk.Hit{w1, s1}, Rewalk.Hit{w2, s2}) == Rewalk.Hit{Bool.or(w1, w2), Bool.or(s1, s2)} : Rewalk.Hit}

# LAW: a List accessor reads its collection at argument 2, a String accessor
# at argument 0, Array.get at argument 1, and anything else at none
law slot_by_accessor_family:
  for +list: Bool
  for +str: Bool
  for +arr: Bool
  {Rewalk.slot_pick(list, str, arr)
    == Bool.pick(Rewalk.Slot, list, Rewalk.Slot{True{}, 2n},
      Bool.pick(Rewalk.Slot, str, Rewalk.Slot{True{}, 0n},
        Bool.pick(Rewalk.Slot, arr, Rewalk.Slot{True{}, 1n}, Rewalk.Slot{False{}, 0n}))) : Rewalk.Slot}

# LAW: the narrow accessors are List.get, List.head, List.last and
# List.length; String.get and String.length; and Array.get. List.set is not
# one
law slot_of_named_accessors:
  for +tt: String
  {Rewalk.slot_of(tt)
    == Rewalk.slot_pick(
      List.contains(~String, ~String.eq, ["List.get", "List.head", "List.last", "List.length"], tt),
      Bool.or(String.eq(tt, "String.get"), String.eq(tt, "String.length")), String.eq(tt, "Array.get")) : Rewalk.Slot}

# LAW: after a comma the walk is still in the slot argument only when no
# argument was left to pass
law step_is_zero_of_none_left:
  for pp: Nat
  for e: {pp == 0n : Nat}
  {Rewalk.step_is_zero(pp) == True{} : Bool}

# LAW: with one or more left, it is not
law step_is_zero_of_some_left:
  for k: Nat
  {Rewalk.step_is_zero(1n+k) == False{} : Bool}

# LAW: after a comma the next argument is the slot when exactly one was left
law step_hot_live_counts_down:
  for p: Nat
  {Rewalk.step_hot_live(1n+p) == Rewalk.step_is_zero(p) : Bool}

# LAW: with none left, no later argument is the slot
law step_hot_live_of_none_left:
  for left: Nat
  for e: {left == 0n : Nat}
  {Rewalk.step_hot_live(left) == False{} : Bool}

# LAW: a name called is a wide read of it
law here_call_callee_is_wide:
  for +tt: String
  for +name: String
  for +hot: Bool
  {Rewalk.here_call(True{}, tt, name, hot) == Rewalk.name_hit(String.eq(tt, name), False{}) : Rewalk.Hit}

# LAW: a name before any other group is read as its position reads it
law here_call_mention_keeps_slot:
  for +tt: String
  for +name: String
  for +hot: Bool
  {Rewalk.here_call(False{}, tt, name, hot) == Rewalk.name_hit(String.eq(tt, name), hot) : Rewalk.Hit}

# LAW: a name indexed with `[` is a narrow read of it
law here_hit_index_is_narrow:
  for +call: Bool
  for +tt: String
  for +name: String
  for +hot: Bool
  {Rewalk.here_hit(True{}, call, tt, name, hot) == Rewalk.name_hit(String.eq(tt, name), True{}) : Rewalk.Hit}

# LAW: any other name before a group is read as a call or a mention
law here_hit_otherwise_call:
  for +call: Bool
  for +tt: String
  for +name: String
  for +hot: Bool
  {Rewalk.here_hit(False{}, call, tt, name, hot) == Rewalk.here_call(call, tt, name, hot) : Rewalk.Hit}

# LAW: a call's arguments start outside the slot
law inner_hot_call_cold:
  for +hot: Bool
  {Rewalk.inner_hot_call(True{}, hot) == False{} : Bool}

# LAW: any other group's inside is as hot as the group
law inner_hot_call_keeps:
  for +hot: Bool
  {Rewalk.inner_hot_call(False{}, hot) == hot : Bool}

# LAW: a bracket's inside is never the slot
law inner_hot_bracket_cold:
  for +call: Bool
  for +hot: Bool
  {Rewalk.inner_hot(True{}, call, hot) == False{} : Bool}

# LAW: any other group's inside is read as a call's or a plain group's
law inner_hot_otherwise_call:
  for +call: Bool
  for +hot: Bool
  {Rewalk.inner_hot(False{}, call, hot) == Rewalk.inner_hot_call(call, hot) : Bool}

# LAW: a call's commas separate arguments when the callee is a narrow
# accessor
law inner_live_call_of_accessor:
  for +tt: String
  {Rewalk.inner_live_call(True{}, tt) == Rewalk.slot_on(Rewalk.slot_of(tt)) : Bool}

# LAW: what is no call counts no commas
law inner_live_call_needs_call:
  for +tt: String
  {Rewalk.inner_live_call(False{}, tt) == False{} : Bool}

# LAW: a bracket's inside counts no commas
law inner_live_bracket_counts_none:
  for +call: Bool
  for +tt: String
  {Rewalk.inner_live(True{}, call, tt) == False{} : Bool}

# LAW: any other group's inside counts them as a call does
law inner_live_otherwise_call:
  for +call: Bool
  for +tt: String
  {Rewalk.inner_live(False{}, call, tt) == Rewalk.inner_live_call(call, tt) : Bool}

# LAW: a chain binds when it holds a `=` leaf
law has_eq_at_equals:
  for t: String
  for l: U32
  for c: U32
  for rest: Tree.Node
  {Rewalk.has_eq(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest}) == True{} : Bool}

# LAW: any other node is passed over
law has_eq_passes_other:
  for h: Tree.Node
  for rest: Tree.Node
  for e: {D2.chains.node_of(h, [Lex.TEq{}]) == False{} : Bool}
  {Rewalk.has_eq(Tree.NCons{h, rest}) == Rewalk.has_eq(rest) : Bool}

# LAW: what is no chain binds nothing
law has_eq_needs_a_chain:
  for nn: Tree.Node
  for e: {D2.chains.is_cons(nn) == False{} : Bool}
  {Rewalk.has_eq(nn) == False{} : Bool}

# LAW: on the left of a let, nothing is in a slot
law pick_hot_skips_left_side:
  for +brack: Bool
  for +call: Bool
  for +hot: Bool
  {Rewalk.pick_hot(True{}, brack, call, hot) == False{} : Bool}

# LAW: past it, a group's inside is read as inner_hot reads it
law pick_hot_otherwise_inner:
  for +brack: Bool
  for +call: Bool
  for +hot: Bool
  {Rewalk.pick_hot(False{}, brack, call, hot) == Rewalk.inner_hot(brack, call, hot) : Bool}

# LAW: on the left of a let, no commas are counted
law pick_live_skips_left_side:
  for +brack: Bool
  for +call: Bool
  for +tt: String
  {Rewalk.pick_live(True{}, brack, call, tt) == False{} : Bool}

# LAW: past it, they are counted as inner_live counts them
law pick_live_otherwise_inner:
  for +brack: Bool
  for +call: Bool
  for +tt: String
  {Rewalk.pick_live(False{}, brack, call, tt) == Rewalk.inner_live(brack, call, tt) : Bool}

# LAW: a let of one name is narrow when the name is read narrowly and never
# wide
law narrow_let_only_narrow_reads:
  for wide: Bool
  for slot: Bool
  {Rewalk.narrow_let(Rewalk.Hit{wide, slot}) == Bool.and(slot, Bool.not(wide)) : Bool}

# LAW: a call is expensive when it is not the def itself and is a Base walk
# or a loop of the file
law expensive_walk_or_loop:
  for +tt: String
  for +self: String
  for +lp: List<&2, String>
  {Rewalk.expensive(tt, self, lp)
    == Bool.and(Bool.not(String.eq(tt, self)), Bool.or(Rewalk.heavy(tt), List.contains(~String, ~String.eq, lp, tt)))
    : Bool}

# LAW: a call is indexed when the group right after it opens with `[`
law indexed_by_bracket:
  for k: Lex.TokKind
  for +o: String
  for l: U32
  for c: U32
  for kids: Tree.Node
  for close: Maybe<&2, Lex.Tok>
  for tail: Tree.Node
  {Rewalk.indexed(Tree.NCons{Tree.Group{Lex.Tok{k, o, l, c}, kids, close}, tail}) == String.eq(o, "[") : Bool}

# LAW: what is no chain indexes nothing
law indexed_needs_a_chain:
  for rest: Tree.Node
  for e: {D2.chains.is_cons(rest) == False{} : Bool}
  {Rewalk.indexed(rest) == False{} : Bool}

# LAW: one position comes before another by line, then by column
law before_by_line_then_column:
  for +l1: U32
  for +c1: U32
  for +l2: U32
  for +c2: U32
  {Rewalk.before(l1, c1, l2, c2) == Bool.or(U32.is_lt(l1, l2), Bool.and(U32.is_eq(l1, l2), U32.is_lt(c1, c2)))
    : Bool}

# LAW: the first name on the left of a let is the let's name
law add_seen_first_name:
  for +extra: Bool
  for +field: Bool
  for +nm: String
  for +tt: String
  {Rewalk.add_seen(False{}, extra, field, nm, tt) == Rewalk.Lhs{True{}, extra, field, tt} : Rewalk.Lhs}

# LAW: a second name makes it a let of more than one, and the first is kept
law add_seen_second_name:
  for +extra: Bool
  for +field: Bool
  for +nm: String
  for +tt: String
  {Rewalk.add_seen(True{}, extra, field, nm, tt) == Rewalk.Lhs{True{}, True{}, field, nm} : Rewalk.Lhs}

# LAW: a name inside a field group is a name on the left, and makes the let
# a field read
law fold_names_marks_field:
  for +t: String
  for l: U32
  for c: U32
  for rest: Tree.Node
  for seen: Bool
  for extra: Bool
  for field: Bool
  for nm: String
  {Rewalk.fold_names(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, rest}, Rewalk.Lhs{seen, extra, field, nm})
    == Rewalk.fold_names(rest, Rewalk.add_seen(seen, extra, True{}, nm, t)) : Rewalk.Lhs}

# LAW: a let notes its call when its left is exactly one name
law note_from_one_name:
  for seen: Bool
  for extra: Bool
  for field: Bool
  for +nm: String
  for +rhs: Tree.Node
  {Rewalk.note_from(Rewalk.Lhs{seen, extra, field, nm}, rhs)
    == Rewalk.note_rhs(Bool.and(seen, Bool.not(extra)), field, nm, Rewalk.as_call(rhs)) : Maybe<&2, Rewalk.Note>}

# LAW: a statement's note is read from its left, starting with no name seen,
# and the tokens after its `=`
law note_st_reads_both_sides:
  for +kids: Tree.Node
  {Rewalk.note_st(kids)
    == Rewalk.note_from(Rewalk.eat(kids, Rewalk.Lhs{False{}, False{}, False{}, ""}), Rewalk.rhs_of(kids))
    : Maybe<&2, Rewalk.Note>}
