# `idle` reports exactly one finding, on the parameter's name, for each idle
# parameter of each def of a file that is judged, and none for anything
# else; in a LAWS.bend or a PROOF.bend none at all, so told a file's role by
# its name it finds what it finds.
#
# A def is judged when it is not exempt (a law file, a proof file, a def
# that is a proof: src/rules/calls.bend's `exempt`) and calls itself. A
# parameter is idle when it counts (it has a type, is neither erased nor a
# template, and its name does not start with `_`), the signature names it
# once, the body reads it, and no reading of it strays: every one sits in
# the parameter's own argument of a self-call. So no result of the def
# depends on it.
#
# The walk that finds a stray reading. A reading is a name leaf spelled as
# the parameter, or as it then a dot. A leaf and then a `(` group are a
# self-call when the leaf is the def's name: the walk enters the group at
# argument 0, and each comma among the group's own kids moves it to the
# next argument. The own argument is the one at the parameter's place among
# the def's parameters. Inside any other node met on the way (a group that
# is no self-call's, a statement) the walk keeps only whether it is in the
# own argument, so commas deeper down move nothing. A reading is a stray
# when the walk is not in the own argument where it meets it.
#
# Not proved here: that no comment or string changes a finding
# (laws/CodeRulesIgnoreCommentsAndStrings.bend does not list this rule; it
# reads names' texts and a group's opening bracket, never a string's or a
# comment's text).
import Base
import ../src/finding.bend as F
import ../src/paths.bend as Paths
import ../src/role.bend as Role
import ../src/src.bend as Src
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/syntax/bind.bend as Bind
import ../src/syntax/outline.bend as Outline
import ../src/rules/calls.bend as Calls
import ../src/rules/suspicious/idle.bend as Idle

# is the parameter with this name token idle? One with no name of its own
# is not
def hit(m: Maybe<&2, Lex.Tok>, p: Tree.Node, slot: Nat, sig: Tree.Node, body: Tree.Node, name: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{Lex.Tok{_k, nm, _l, _c}}:
      Idle.idle(p, slot, sig, body, nm, name)

# how many of the parameters, the first of them at this place, are idle,
# added to a count
def idle_params(
  ps: List<&2, Tree.Node>,
  +slot: Nat,
  +sig: Tree.Node,
  +body: Tree.Node,
  +name: String,
  after: Nat
) -> Nat:
  match ps:
    case Nil{}:
      after
    case Con{+p, rest}:
      +m = idle_params(rest, 1n+slot, sig, body, name, after)
      Bool.pick(Nat, hit(Idle.named(p), p, slot, sig, body, name), 1n+m, m)

# how many parameters the rule reports over the defs
def idle_count(ds: List<&2, Calls.Def>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      +m = idle_count(rest, path)
      Bool.pick(Nat, Idle.judged(path, sig, body, name), idle_params(Calls.params(sig), 0n, sig, body, name, m), m)

# LAW: over a file's defs, the rule reports one finding for each idle
# parameter of each def that is judged, and none for anything else
law idle_counts:
  for ds: List<&2, Calls.Def>
  for +path: String
  {List.length(&2, F.Finding, Idle.check.go(ds, path)) == idle_count(ds, path) : Nat}

# LAW: the finding sits on the parameter's name, over its length, and says
# which def passes it back to itself
law idle_cites_parameter:
  for +nm: String
  for l: U32
  for c: U32
  for +name: String
  for path: String
  {Idle.cite(nm, l, c, name, path) == F.Finding{path, l, c, U32.from_nat(String.length(nm)), "idle",
    "Parameter " ++ nm ++ " is read only where " ++ name
      ++ " passes it back to itself, so no result depends on it; delete it, or read it where it was meant to count."}
    : F.Finding}

# LAW: the rule reports nothing in a LAWS.bend or a PROOF.bend, whatever the
# source holds
law idle_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {Idle.check(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: the rule, which checks nothing in a law or proof file, told a file's
# role by its name finds what it finds
law role_idle:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {Role.skip(Role.of_path(path), _u => Idle.check(Src.Src{path, text, toks, tree, bound, items}))
    == Idle.check(Src.Src{path, text, toks, tree, bound, items}) : List<&2, F.Finding>}

# LAW: a def that is exempt is not judged
law judged_skips_exempt:
  for path: String
  for sig: Tree.Node
  for body: Tree.Node
  for name: String
  for e: {Calls.exempt(path, sig) == True{} : Bool}
  {Idle.judged(path, sig, body, name) == False{} : Bool}

# LAW: nor is a def that does not call itself
law judged_skips_plain_def:
  for path: String
  for sig: Tree.Node
  for body: Tree.Node
  for name: String
  for e: {Calls.calls(body, name) == False{} : Bool}
  {Idle.judged(path, sig, body, name) == False{} : Bool}

# LAW: a parameter that counts, named once in the signature, read in the
# body and never astray, is idle
law idle_holds:
  for p: Tree.Node
  for +slot: Nat
  for sig: Tree.Node
  for +body: Tree.Node
  for +nm: String
  for +name: String
  for e1: {Idle.counts(p, nm) == True{} : Bool}
  for e2: {Nat.is_eq(Idle.spelled(sig, nm), 1n) == True{} : Bool}
  for e3: {Nat.is_eq(Idle.spelled(body, nm), 0n) == False{} : Bool}
  for e4: {Idle.stray(body, Idle.AOut{}, slot, nm, name) == False{} : Bool}
  {Idle.idle(p, slot, sig, body, nm, name) == True{} : Bool}

# LAW: a parameter that does not count is not idle
law idle_skips_uncounted:
  for p: Tree.Node
  for +slot: Nat
  for sig: Tree.Node
  for +body: Tree.Node
  for +nm: String
  for +name: String
  for e: {Idle.counts(p, nm) == False{} : Bool}
  {Idle.idle(p, slot, sig, body, nm, name) == False{} : Bool}

# LAW: nor is one the signature names again, or not at all
law idle_skips_named_again:
  for p: Tree.Node
  for +slot: Nat
  for sig: Tree.Node
  for +body: Tree.Node
  for +nm: String
  for +name: String
  for e: {Nat.is_eq(Idle.spelled(sig, nm), 1n) == False{} : Bool}
  {Idle.idle(p, slot, sig, body, nm, name) == False{} : Bool}

# LAW: nor is one the body never reads
law idle_skips_unread:
  for p: Tree.Node
  for +slot: Nat
  for sig: Tree.Node
  for +body: Tree.Node
  for +nm: String
  for +name: String
  for e: {Nat.is_eq(Idle.spelled(body, nm), 0n) == True{} : Bool}
  {Idle.idle(p, slot, sig, body, nm, name) == False{} : Bool}

# LAW: nor is one a reading of which strays
law idle_skips_stray:
  for p: Tree.Node
  for +slot: Nat
  for sig: Tree.Node
  for +body: Tree.Node
  for +nm: String
  for +name: String
  for e: {Idle.stray(body, Idle.AOut{}, slot, nm, name) == True{} : Bool}
  {Idle.idle(p, slot, sig, body, nm, name) == False{} : Bool}

# LAW: a parameter whose name starts with `_` does not count
law counts_skips_ignored:
  for p: Tree.Node
  for nm: String
  for e: {String.starts_with(nm, "_") == True{} : Bool}
  {Idle.counts(p, nm) == False{} : Bool}

# LAW: nor does one that is not live: untyped, erased or a template
law counts_skips_unlive:
  for p: Tree.Node
  for nm: String
  for e: {Calls.is_live(p) == False{} : Bool}
  {Idle.counts(p, nm) == False{} : Bool}

# LAW: a name spelled as the parameter reads it
law reads_sees_the_name:
  for k: Lex.TokKind
  for +nm: String
  for e: {Lex.is_name(k) == True{} : Bool}
  {Idle.reads(k, nm, nm) == True{} : Bool}

# LAW: and so does a name spelled as the parameter and then a dot
law reads_sees_dotted_name:
  for k: Lex.TokKind
  for +t: String
  for +nm: String
  for e: {Lex.is_name(k) == True{} : Bool}
  for d: {String.starts_with(t, nm ++ ".") == True{} : Bool}
  {Idle.reads(k, t, nm) == True{} : Bool}

# LAW: a name spelled any other way does not
law reads_skips_other_name:
  for k: Lex.TokKind
  for +t: String
  for +nm: String
  for e: {String.eq(t, nm) == False{} : Bool}
  for d: {String.starts_with(t, nm ++ ".") == False{} : Bool}
  {Idle.reads(k, t, nm) == False{} : Bool}

# LAW: nor does a token that is no name, whatever its text
law reads_skips_other_token:
  for k: Lex.TokKind
  for +t: String
  for +nm: String
  for e: {Lex.is_name(k) == False{} : Bool}
  {Idle.reads(k, t, nm) == False{} : Bool}

# LAW: a leaf that reads the name is spelled once
law spelled_counts_reading:
  for k: Lex.TokKind
  for t: String
  for l: U32
  for c: U32
  for +nm: String
  for e: {Idle.reads(k, t, nm) == True{} : Bool}
  {Idle.spelled(Tree.Leaf{Lex.Tok{k, t, l, c}}, nm) == 1n : Nat}

# LAW: and any other leaf not at all
law spelled_skips_other_leaf:
  for k: Lex.TokKind
  for t: String
  for l: U32
  for c: U32
  for +nm: String
  for e: {Idle.reads(k, t, nm) == False{} : Bool}
  {Idle.spelled(Tree.Leaf{Lex.Tok{k, t, l, c}}, nm) == 0n : Nat}

# LAW: a chain is spelled as often as its first node and the rest together
law spelled_adds_chain:
  for h: Tree.Node
  for rest: Tree.Node
  for +nm: String
  {Idle.spelled(Tree.NCons{h, rest}, nm) == Nat.add(Idle.spelled(h, nm), Idle.spelled(rest, nm)) : Nat}

# LAW: a group as often as what is inside it
law spelled_reads_group:
  for open: Lex.Tok
  for kids: Tree.Node
  for cl: Maybe<&2, Lex.Tok>
  for +nm: String
  {Idle.spelled(Tree.Group{open, kids, cl}, nm) == Idle.spelled(kids, nm) : Nat}

# LAW: a statement as often as its own tokens and the statements under it
# together
law spelled_adds_statement:
  for sk: Tree.StmtKind
  for kids: Tree.Node
  for body: Tree.Node
  for +nm: String
  {Idle.spelled(Tree.Stmt{sk, kids, body}, nm) == Nat.add(Idle.spelled(kids, nm), Idle.spelled(body, nm)) : Nat}

# LAW: a parameter's name is the first lowercase name of its chain
law named_takes_lowercase_name:
  for t: String
  for l: U32
  for c: U32
  for rest: Tree.Node
  {Idle.named(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, rest})
    == Some{Lex.Tok{Lex.TName{}, t, l, c}} : Maybe<&2, Lex.Tok>}

# LAW: one whose colon comes first has none: a type parameter
law named_stops_at_colon:
  for t: String
  for l: U32
  for c: U32
  for rest: Tree.Node
  {Idle.named(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}}, rest}) == None{} : Maybe<&2, Lex.Tok>}

# LAW: a sign before the name (`+`, `-`, `~`) is passed over
law named_passes_sign:
  for t: String
  for l: U32
  for c: U32
  for rest: Tree.Node
  {Idle.named(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, t, l, c}}, rest}) == Idle.named(rest) : Maybe<&2, Lex.Tok>}

# LAW: a reading met outside the own argument is a stray
law stray_sees_reading_outside:
  for k: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for +at: Idle.At
  for +slot: Nat
  for +nm: String
  for +name: String
  for e: {Idle.reads(k, t, nm) == True{} : Bool}
  for o: {Idle.own(at, slot) == False{} : Bool}
  {Idle.stray(Tree.Leaf{Lex.Tok{k, t, l, c}}, at, slot, nm, name) == True{} : Bool}

# LAW: a leaf met in the own argument is none, whatever it reads
law stray_passes_own_argument:
  for k: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for +at: Idle.At
  for +slot: Nat
  for +nm: String
  for +name: String
  for o: {Idle.own(at, slot) == True{} : Bool}
  {Idle.stray(Tree.Leaf{Lex.Tok{k, t, l, c}}, at, slot, nm, name) == False{} : Bool}

# LAW: a leaf that does not read the parameter is none, wherever it is met
law stray_passes_other_leaf:
  for k: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for +at: Idle.At
  for +slot: Nat
  for +nm: String
  for +name: String
  for e: {Idle.reads(k, t, nm) == False{} : Bool}
  {Idle.stray(Tree.Leaf{Lex.Tok{k, t, l, c}}, at, slot, nm, name) == False{} : Bool}

# LAW: the def's name and then a `(` group are a self-call: its arguments
# are walked from argument 0, and what follows the group from where the
# walk stood
law stray_enters_self_call:
  for +k: Lex.TokKind
  for l: U32
  for c: U32
  for ko: Lex.TokKind
  for lo: U32
  for co: U32
  for kids: Tree.Node
  for cl: Maybe<&2, Lex.Tok>
  for rest: Tree.Node
  for +at: Idle.At
  for +slot: Nat
  for +nm: String
  for +name: String
  {Idle.stray(
      Tree.NCons{Tree.Leaf{Lex.Tok{k, name, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{ko, "(", lo, co}, kids, cl}, rest}},
      at, slot, nm, name)
    == Bool.or(Bool.and(Idle.reads(k, name, nm), Bool.not(Idle.own(at, slot))),
      Bool.or(Idle.stray(kids, Idle.AArg{0n}, slot, nm, name),
        Idle.stray(rest, Idle.past(Lex.is_comma(k), at), slot, nm, name))) : Bool}

# LAW: a group after any other leaf is no self-call: the walk goes inside
# it keeping only whether it is in the own argument
law stray_stays_in_other_call:
  for +k: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for ko: Lex.TokKind
  for o: String
  for lo: U32
  for co: U32
  for kids: Tree.Node
  for cl: Maybe<&2, Lex.Tok>
  for rest: Tree.Node
  for +at: Idle.At
  for +slot: Nat
  for +nm: String
  for +name: String
  for e: {String.eq(t, name) == False{} : Bool}
  {Idle.stray(
      Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{ko, o, lo, co}, kids, cl}, rest}},
      at, slot, nm, name)
    == Bool.or(Bool.and(Idle.reads(k, t, nm), Bool.not(Idle.own(at, slot))),
      Bool.or(Idle.stray(kids, Idle.inner(Idle.past(Lex.is_comma(k), at), slot), slot, nm, name),
        Idle.stray(rest, Idle.past(Lex.is_comma(k), at), slot, nm, name))) : Bool}

# LAW: nor is a group that `(` does not open, after the def's name or not
law stray_stays_in_other_bracket:
  for +k: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for ko: Lex.TokKind
  for o: String
  for lo: U32
  for co: U32
  for kids: Tree.Node
  for cl: Maybe<&2, Lex.Tok>
  for rest: Tree.Node
  for +at: Idle.At
  for +slot: Nat
  for +nm: String
  for +name: String
  for e: {String.eq(o, "(") == False{} : Bool}
  {Idle.stray(
      Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{ko, o, lo, co}, kids, cl}, rest}},
      at, slot, nm, name)
    == Bool.or(Bool.and(Idle.reads(k, t, nm), Bool.not(Idle.own(at, slot))),
      Bool.or(Idle.stray(kids, Idle.inner(Idle.past(Lex.is_comma(k), at), slot), slot, nm, name),
        Idle.stray(rest, Idle.past(Lex.is_comma(k), at), slot, nm, name))) : Bool}

# LAW: a comma among a self-call's arguments is no reading, and what
# follows it is walked in the next argument
law stray_comma_starts_next_argument:
  for t: String
  for l: U32
  for c: U32
  for tok: Lex.Tok
  for rest: Tree.Node
  for place: Nat
  for +slot: Nat
  for +nm: String
  for +name: String
  {Idle.stray(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, Tree.NCons{Tree.Leaf{tok}, rest}},
      Idle.AArg{place}, slot, nm, name)
    == Idle.stray(Tree.NCons{Tree.Leaf{tok}, rest}, Idle.AArg{1n+place}, slot, nm, name) : Bool}

# LAW: a group that follows no leaf is walked inside, keeping only whether
# the walk is in the own argument, and what follows it from where the walk
# stood
law stray_walks_bare_group:
  for open: Lex.Tok
  for kids: Tree.Node
  for cl: Maybe<&2, Lex.Tok>
  for rest: Tree.Node
  for +at: Idle.At
  for +slot: Nat
  for +nm: String
  for +name: String
  {Idle.stray(Tree.NCons{Tree.Group{open, kids, cl}, rest}, at, slot, nm, name)
    == Bool.or(Idle.stray(kids, Idle.inner(at, slot), slot, nm, name), Idle.stray(rest, at, slot, nm, name)) : Bool}

# LAW: a statement is walked through its own tokens and the statements
# under it
law stray_walks_statement:
  for sk: Tree.StmtKind
  for kids: Tree.Node
  for body: Tree.Node
  for +at: Idle.At
  for +slot: Nat
  for +nm: String
  for +name: String
  {Idle.stray(Tree.Stmt{sk, kids, body}, at, slot, nm, name)
    == Bool.or(Idle.stray(kids, at, slot, nm, name), Idle.stray(body, at, slot, nm, name)) : Bool}

# LAW: among a self-call's arguments, the own argument is the one at the
# parameter's place
law own_argument_at_its_place:
  for +slot: Nat
  {Idle.own(Idle.AArg{slot}, slot) == True{} : Bool}

# LAW: and no argument at another place is
law own_argument_nowhere_else:
  for place: Nat
  for slot: Nat
  for e: {Nat.is_eq(place, slot) == False{} : Bool}
  {Idle.own(Idle.AArg{place}, slot) == False{} : Bool}

# LAW: a comma among a self-call's arguments moves the walk to the next one
law past_comma_moves_on:
  for place: Nat
  {Idle.past(True{}, Idle.AArg{place}) == Idle.AArg{1n+place} : Idle.At}

# LAW: inside a node the walk is in the own argument exactly when it was
# before going in
law inner_keeps_own:
  for at: Idle.At
  for +slot: Nat
  {Idle.own(Idle.inner(at, slot), slot) == Idle.own(at, slot) : Bool}

# LAW: and once inside, a comma moves nothing
law inner_ignores_commas:
  for at: Idle.At
  for slot: Nat
  for comma: Bool
  {Idle.past(comma, Idle.inner(at, slot)) == Idle.inner(at, slot) : Idle.At}
