# `negate` reports exactly one finding, on the `Bool.not` token, for each
# `U32` or `Nat` comparison negated among a file's significant tokens,
# outside a law and a def that is a proof, and none for anything else; in a
# law file or a proof file none at all, so told a file's role by its name it
# finds what it finds.
#
# The shape. A dotted `Bool.not`, `(`, a dotted name, `(`, any tokens up to
# the `)` that closes that bracket (brackets opened on the way are passed
# over), and `)` right after. The name has a word when it is one of the six
# comparisons of `U32` or of `Nat`: the opposite comparison of the same
# type. Any other name has none and is not reported.
#
# What the fix rests on is a law here too: for every pair of arguments, each
# of the six comparisons of `U32`, and of `Nat`, negated, is the comparison
# the rule names (negated_u32_is_its_word, negated_nat_is_its_word). So the
# rewrite keeps every result.
#
# Not proved here: that no comment or string changes a finding (the rule
# reads the significant tokens' kinds and the texts of code tokens only;
# laws/CodeRulesIgnoreCommentsAndStrings.bend does not list it).
import Base
import ../src/finding.bend as F
import ../src/paths.bend as Paths
import ../src/role.bend as Role
import ../src/src.bend as Src
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/syntax/bind.bend as Bind
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/empty.bend as Empty
import ../src/rules/style/negate.bend as Negate

# the six comparisons
type Six is Data:
  Eq{}
  Ne{}
  Lt{}
  Le{}
  Gt{}
  Ge{}

# a comparison's name after its type
def name(s: Six) -> String:
  match s:
    case Eq{}:
      "is_eq"
    case Ne{}:
      "is_ne"
    case Lt{}:
      "is_lt"
    case Le{}:
      "is_le"
    case Gt{}:
      "is_gt"
    case Ge{}:
      "is_ge"

# the comparison that holds exactly when this one does not
def flip(s: Six) -> Six:
  match s:
    case Eq{}:
      Ne{}
    case Ne{}:
      Eq{}
    case Lt{}:
      Ge{}
    case Le{}:
      Gt{}
    case Gt{}:
      Le{}
    case Ge{}:
      Lt{}

# a comparison of two U32, as Base names it
def u32(s: Six, a: U32, b: U32) -> Bool:
  match s:
    case Eq{}:
      U32.is_eq(a, b)
    case Ne{}:
      U32.is_ne(a, b)
    case Lt{}:
      U32.is_lt(a, b)
    case Le{}:
      U32.is_le(a, b)
    case Gt{}:
      U32.is_gt(a, b)
    case Ge{}:
      U32.is_ge(a, b)

# a comparison of two Nat, as Base names it
def nat(s: Six, a: Nat, b: Nat) -> Bool:
  match s:
    case Eq{}:
      Nat.is_eq(a, b)
    case Ne{}:
      Nat.is_ne(a, b)
    case Lt{}:
      Nat.is_lt(a, b)
    case Le{}:
      Nat.is_le(a, b)
    case Gt{}:
      Nat.is_gt(a, b)
    case Ge{}:
      Nat.is_ge(a, b)

# LAW: each comparison of two U32, negated, is the comparison flip names,
# for every pair
law negated_u32_is_its_word:
  for s: Six
  for a: U32
  for b: U32
  {Bool.not(u32(s, a, b)) == u32(flip(s), a, b) : Bool}

# LAW: and so is each comparison of two Nat
law negated_nat_is_its_word:
  for s: Six
  for a: Nat
  for b: Nat
  {Bool.not(nat(s, a, b)) == nat(flip(s), a, b) : Bool}

# LAW: the rule's opposite of a comparison's name is the name of its flip
law opposite_names_flip:
  for s: Six
  {Negate.opposite(name(s)) == name(flip(s)) : String}

# LAW: a name that is none of the six has no opposite
law opposite_needs_comparison:
  for +op: String
  for e1: {String.eq(op, "is_eq") == False{} : Bool}
  for e2: {String.eq(op, "is_ne") == False{} : Bool}
  for e3: {String.eq(op, "is_lt") == False{} : Bool}
  for e4: {String.eq(op, "is_ge") == False{} : Bool}
  for e5: {String.eq(op, "is_gt") == False{} : Bool}
  for e6: {String.eq(op, "is_le") == False{} : Bool}
  {Negate.opposite(op) == "" : String}

# LAW: the word for a U32 comparison is the U32 comparison flip names
law word_of_u32_comparison:
  for s: Six
  {Negate.word("U32." ++ name(s)) == "U32." ++ name(flip(s)) : String}

# LAW: and for a Nat comparison the Nat one
law word_of_nat_comparison:
  for s: Six
  {Negate.word("Nat." ++ name(s)) == "Nat." ++ name(flip(s)) : String}

# LAW: a name of neither type has no word: `F32`, `Char`, `Cmp`, a
# qualified or aliased name
law word_needs_u32_or_nat:
  for +t: String
  for e: {String.starts_with(t, "U32.") == False{} : Bool}
  for o: {String.starts_with(t, "Nat.") == False{} : Bool}
  {Negate.word(t) == "" : String}

# LAW: a name of one of the two types that is none of the six comparisons
# has no word
law under_needs_comparison:
  for ty: String
  for op: String
  for e: {String.is_empty(Negate.opposite(op)) == True{} : Bool}
  {Negate.under(ty, op) == "" : String}

# how many tokens open a negated comparison the rule has a word for, a
# token in a law or a def that is a proof (Empty.item) aside
def negated(toks: List<&2, Lex.Tok>, skip: Bool) -> Nat:
  match toks:
    case Nil{}:
      0n
    case Con{Lex.Tok{+k, +t, _l, _c}, +rest}:
      +sk = Empty.item(k, t, rest, skip)
      +m = negated(rest, sk)
      Bool.pick(Nat, String.is_empty(Negate.found(sk, k, t, rest)), m, 1n+m)

# LAW: over any tokens, the rule reports one finding for each token that
# opens a negated comparison it has a word for, and none for any other
law negate_counts:
  for toks: List<&2, Lex.Tok>
  for +path: String
  for skip: Bool
  {List.length(&2, F.Finding, Negate.walk(toks, path, skip)) == negated(toks, skip) : Nat}

# LAW: the finding sits on the `Bool.not`, over its eight chars, and names
# the word
law negate_cites_bool_not:
  for +w: String
  for path: String
  for l: U32
  for c: U32
  {Negate.cite(w, path, l, c) == F.Finding{path, l, c, 8, "negate",
    "Bool.not of this comparison is " ++ w ++ ", the same Bool for every pair of arguments; write " ++ w ++ "(..)."}
    : F.Finding}

# LAW: the rule reports nothing in a LAWS.bend or a PROOF.bend, whatever the
# source holds
law negate_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_law_file(path) == True{} : Bool}
  {Negate.check(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: told a file's role by its name, the rule finds what it finds
law role_negate:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {Negate.check.role(Role.of_path(path), Src.Src{path, text, toks, tree, bound, items})
    == Negate.check(Src.Src{path, text, toks, tree, bound, items}) : List<&2, F.Finding>}

# LAW: told a law file's or a proof file's role, it reports nothing
law role_negate_exempt:
  for r: Role.Role
  for e: {Role.is_law_file(r) == True{} : Bool}
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {Negate.check.role(r, Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: in a law or a def that is a proof no token has a word
law found_skips_proofs:
  for k: Lex.TokKind
  for t: String
  for rest: List<&2, Lex.Tok>
  {Negate.found(True{}, k, t, rest) == "" : String}

# LAW: outside them, a token that is no dotted `Bool.not` has none
law found_needs_bool_not:
  for k: Lex.TokKind
  for t: String
  for rest: List<&2, Lex.Tok>
  for e: {Negate.named(k, t) == False{} : Bool}
  {Negate.found(False{}, k, t, rest) == "" : String}

# LAW: and a dotted `Bool.not` has the word the tokens after it give
law found_reads_after_bool_not:
  for rest: List<&2, Lex.Tok>
  {Negate.found(False{}, Lex.TDotted{}, "Bool.not", rest) == Negate.at(rest) : String}

# LAW: `(`, a dotted name, `(`, then tokens whose closing bracket has a `)`
# right after: the name's word
law at_reads_negated_call:
  for l1: U32
  for c1: U32
  for +t2: String
  for l2: U32
  for c2: U32
  for l3: U32
  for c3: U32
  for rest: List<&2, Lex.Tok>
  for e: {Negate.ends(Negate.shut(rest, 0n, False{})) == True{} : Bool}
  {Negate.at(Lex.Tok{Lex.TOpen{}, "(", l1, c1} <> Lex.Tok{Lex.TDotted{}, t2, l2, c2}
      <> Lex.Tok{Lex.TOpen{}, "(", l3, c3} <> rest)
    == Negate.word(t2) : String}

# LAW: when no `)` follows right after it (the argument goes on, or the
# tokens run out), nothing
law at_needs_closing_bracket_next:
  for l1: U32
  for c1: U32
  for +t2: String
  for l2: U32
  for c2: U32
  for l3: U32
  for c3: U32
  for rest: List<&2, Lex.Tok>
  for e: {Negate.ends(Negate.shut(rest, 0n, False{})) == False{} : Bool}
  {Negate.at(Lex.Tok{Lex.TOpen{}, "(", l1, c1} <> Lex.Tok{Lex.TDotted{}, t2, l2, c2}
      <> Lex.Tok{Lex.TOpen{}, "(", l3, c3} <> rest)
    == "" : String}

# LAW: a name that is not dotted after the `(` (a parameter, a local) is no
# comparison of Base
law at_needs_dotted_name:
  for k1: Lex.TokKind
  for t1: String
  for l1: U32
  for c1: U32
  for +t2: String
  for l2: U32
  for c2: U32
  for k3: Lex.TokKind
  for t3: String
  for l3: U32
  for c3: U32
  for rest: List<&2, Lex.Tok>
  {Negate.at(Lex.Tok{k1, t1, l1, c1} <> Lex.Tok{Lex.TName{}, t2, l2, c2} <> Lex.Tok{k3, t3, l3, c3} <> rest) == ""
    : String}

# LAW: and when the third token is no `(`, nothing: the name is not called
law at_needs_call:
  for l1: U32
  for c1: U32
  for +t2: String
  for l2: U32
  for c2: U32
  for k3: Lex.TokKind
  for t3: String
  for l3: U32
  for c3: U32
  for rest: List<&2, Lex.Tok>
  for e: {String.eq(Empty.code(k3, t3), "(") == False{} : Bool}
  {Negate.at(Lex.Tok{Lex.TOpen{}, "(", l1, c1} <> Lex.Tok{Lex.TDotted{}, t2, l2, c2} <> Lex.Tok{k3, t3, l3, c3} <> rest)
    == "" : String}

# LAW: a call the tokens end inside has no word
law at_needs_arguments_closed:
  for l1: U32
  for c1: U32
  for +t2: String
  for l2: U32
  for c2: U32
  for l3: U32
  for c3: U32
  {Negate.at(Lex.Tok{Lex.TOpen{}, "(", l1, c1} <> Lex.Tok{Lex.TDotted{}, t2, l2, c2}
      <> Lex.Tok{Lex.TOpen{}, "(", l3, c3} <> Nil{})
    == "" : String}

# LAW: nor has one the tokens end right after
law at_needs_token_after_call:
  for l1: U32
  for c1: U32
  for +t2: String
  for l2: U32
  for c2: U32
  for l3: U32
  for c3: U32
  for t4: String
  for l4: U32
  for c4: U32
  {Negate.at(Lex.Tok{Lex.TOpen{}, "(", l1, c1} <> Lex.Tok{Lex.TDotted{}, t2, l2, c2}
      <> Lex.Tok{Lex.TOpen{}, "(", l3, c3} <> Lex.Tok{Lex.TClose{}, t4, l4, c4} <> Nil{})
    == "" : String}

# LAW: a string that says `Bool.not` is no `Bool.not`
law named_skips_string:
  for t: String
  {Negate.named(Lex.TStr{}, t) == False{} : Bool}

# LAW: nor is a comment that does
law named_skips_comment:
  for t: String
  {Negate.named(Lex.TComment{}, t) == False{} : Bool}

# LAW: once the closing bracket was read, what follows is what is left
law shut_stops_at_close:
  for toks: List<&2, Lex.Tok>
  for +d: Nat
  {Negate.shut(toks, d, True{}) == Some{toks} : Maybe<&2, List<&2, Lex.Tok>>}

# LAW: a closing bracket with none open inside closes the group
law shut_closes_at_depth_zero:
  for t: String
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  {Negate.shut(Lex.Tok{Lex.TClose{}, t, l, c} <> rest, 0n, False{}) == Some{rest}
    : Maybe<&2, List<&2, Lex.Tok>>}

# LAW: an opening bracket on the way is one more to close
law shut_counts_opening_bracket:
  for t: String
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  for +d: Nat
  {Negate.shut(Lex.Tok{Lex.TOpen{}, t, l, c} <> rest, d, False{}) == Negate.shut(rest, 1n+d, False{})
    : Maybe<&2, List<&2, Lex.Tok>>}

# LAW: and a closing one inside closes that one, not the group
law shut_passes_inner_close:
  for t: String
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  for +d: Nat
  {Negate.shut(Lex.Tok{Lex.TClose{}, t, l, c} <> rest, 1n+d, False{}) == Negate.shut(rest, d, False{})
    : Maybe<&2, List<&2, Lex.Tok>>}

# LAW: a comma between arguments is passed over
law shut_passes_comma:
  for t: String
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  for +d: Nat
  {Negate.shut(Lex.Tok{Lex.TComma{}, t, l, c} <> rest, d, False{}) == Negate.shut(rest, d, False{})
    : Maybe<&2, List<&2, Lex.Tok>>}

# LAW: where the tokens run out with the bracket still open, there is no
# close
law shut_runs_out:
  for +d: Nat
  {Negate.shut(Nil{}, d, False{}) == None{} : Maybe<&2, List<&2, Lex.Tok>>}

# LAW: a `)` right after the close ends the negation
law ends_at_closing_bracket:
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  {Negate.ends(Some{Lex.Tok{Lex.TClose{}, ")", l, c} <> rest}) == True{} : Bool}

# LAW: an operator there does not: the argument goes on
law ends_not_at_operator:
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  {Negate.ends(Some{Lex.Tok{Lex.TOp{}, "&&", l, c} <> rest}) == False{} : Bool}
