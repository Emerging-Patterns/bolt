# `numeral` reports exactly one finding, on the `U32.to_nat` token, for each
# conversion of a `U32` literal among a file's significant tokens, outside a
# law and a def that is a proof, and none for anything else; in a law file
# or a proof file none at all, so told a file's role by its name it finds
# what it finds.
#
# The shape. A dotted `U32.to_nat`, `(`, a number token whose text is
# decimal digits and nothing else, and `)`, right after one another. The
# finding names the literal: the digits and then `n`.
#
# Not a law here: that `U32.to_nat(k)` and `kn` are one value for every
# literal k. Each instance is closed (two numerals the checker reduces), so
# no binder states the family; it rests on how bend reads a `Nat` literal
# (`bend guide`: one past `256n` is `U32.to_nat` of the number). Not proved
# either: that no comment or string changes a finding (the rule reads the
# significant tokens' kinds and the texts of code tokens only;
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
import ../src/rules/style/numeral.bend as Numeral

# how many tokens open a conversion of a literal, a token in a law or a def
# that is a proof (Empty.item) aside
def converted(toks: List<&2, Lex.Tok>, skip: Bool) -> Nat:
  match toks:
    case Nil{}:
      0n
    case Con{Lex.Tok{+k, +t, _l, _c}, +rest}:
      +sk = Empty.item(k, t, rest, skip)
      +m = converted(rest, sk)
      Bool.pick(Nat, String.is_empty(Numeral.found(sk, k, t, rest)), m, 1n+m)

# LAW: over any tokens, the rule reports one finding for each token that
# opens a conversion of a literal, and none for any other
law numeral_counts:
  for toks: List<&2, Lex.Tok>
  for +path: String
  for skip: Bool
  {List.length(&2, F.Finding, Numeral.walk(toks, path, skip)) == converted(toks, skip) : Nat}

# LAW: the finding sits on the `U32.to_nat`, over its ten chars, and names
# the literal
law numeral_cites_conversion:
  for +ds: String
  for path: String
  for l: U32
  for c: U32
  {Numeral.cite(ds, path, l, c) == F.Finding{path, l, c, 10, "numeral",
    "U32.to_nat(" ++ ds ++ ") is the Nat literal " ++ ds ++ "n; write " ++ ds ++ "n."} : F.Finding}

# LAW: the rule reports nothing in a LAWS.bend or a PROOF.bend, whatever the
# source holds
law numeral_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_law_file(path) == True{} : Bool}
  {Numeral.check(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: told a file's role by its name, the rule finds what it finds
law role_numeral:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {Numeral.check.role(Role.of_path(path), Src.Src{path, text, toks, tree, bound, items})
    == Numeral.check(Src.Src{path, text, toks, tree, bound, items}) : List<&2, F.Finding>}

# LAW: told a law file's or a proof file's role, it reports nothing
law role_numeral_exempt:
  for r: Role.Role
  for e: {Role.is_law_file(r) == True{} : Bool}
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {Numeral.check.role(r, Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: in a law or a def that is a proof no token opens one
law found_skips_proofs:
  for k: Lex.TokKind
  for t: String
  for rest: List<&2, Lex.Tok>
  {Numeral.found(True{}, k, t, rest) == "" : String}

# LAW: outside them, a token that is no dotted `U32.to_nat` opens none
law found_needs_to_nat:
  for k: Lex.TokKind
  for t: String
  for rest: List<&2, Lex.Tok>
  for e: {Numeral.named(k, t) == False{} : Bool}
  {Numeral.found(False{}, k, t, rest) == "" : String}

# LAW: and a dotted `U32.to_nat` opens what the tokens after it give
law found_reads_after_to_nat:
  for rest: List<&2, Lex.Tok>
  {Numeral.found(False{}, Lex.TDotted{}, "U32.to_nat", rest) == Numeral.at(rest) : String}

# LAW: a string that says `U32.to_nat` is no `U32.to_nat`
law named_skips_string:
  for t: String
  {Numeral.named(Lex.TStr{}, t) == False{} : Bool}

# LAW: nor is a comment that does
law named_skips_comment:
  for t: String
  {Numeral.named(Lex.TComment{}, t) == False{} : Bool}

# LAW: `(`, a number in digits, `)`: its digits
law at_reads_literal:
  for l1: U32
  for c1: U32
  for +t2: String
  for l2: U32
  for c2: U32
  for l3: U32
  for c3: U32
  for rest: List<&2, Lex.Tok>
  for e: {Numeral.digits(t2) == True{} : Bool}
  {Numeral.at(Lex.Tok{Lex.TOpen{}, "(", l1, c1} <> Lex.Tok{Lex.TNum{}, t2, l2, c2} <> Lex.Tok{Lex.TClose{}, ")", l3, c3}
      <> rest)
    == t2 : String}

# LAW: a number written any other way (`5n`, `1.5`) is not one
law at_needs_digits_alone:
  for l1: U32
  for c1: U32
  for +t2: String
  for l2: U32
  for c2: U32
  for l3: U32
  for c3: U32
  for rest: List<&2, Lex.Tok>
  for e: {Numeral.digits(t2) == False{} : Bool}
  {Numeral.at(Lex.Tok{Lex.TOpen{}, "(", l1, c1} <> Lex.Tok{Lex.TNum{}, t2, l2, c2} <> Lex.Tok{Lex.TClose{}, ")", l3, c3}
      <> rest)
    == "" : String}

# LAW: a name there is no literal: `U32.to_nat(n)` converts a value
law at_needs_number:
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
  {Numeral.at(Lex.Tok{k1, t1, l1, c1} <> Lex.Tok{Lex.TName{}, t2, l2, c2} <> Lex.Tok{k3, t3, l3, c3} <> rest) == ""
    : String}

# LAW: when something other than `)` follows the number, nothing: the
# argument goes on (`U32.to_nat(1 + x)`)
law at_needs_closing_bracket:
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
  for e: {String.eq(Empty.code(k3, t3), ")") == False{} : Bool}
  {Numeral.at(Lex.Tok{Lex.TOpen{}, "(", l1, c1} <> Lex.Tok{Lex.TNum{}, t2, l2, c2} <> Lex.Tok{k3, t3, l3, c3} <> rest)
    == "" : String}

# LAW: and when no `(` comes first, nothing
law at_needs_opening_bracket:
  for k1: Lex.TokKind
  for t1: String
  for l1: U32
  for c1: U32
  for +t2: String
  for l2: U32
  for c2: U32
  for l3: U32
  for c3: U32
  for rest: List<&2, Lex.Tok>
  for e: {String.eq(Empty.code(k1, t1), "(") == False{} : Bool}
  {Numeral.at(Lex.Tok{k1, t1, l1, c1} <> Lex.Tok{Lex.TNum{}, t2, l2, c2} <> Lex.Tok{Lex.TClose{}, ")", l3, c3} <> rest)
    == "" : String}

# LAW: a text is digits when it is not empty and every char of it is one
law digits_needs_every_char:
  for +t: String
  for e: {Numeral.digits.all(String.to_list(t)) == False{} : Bool}
  {Numeral.digits(t) == False{} : Bool}

# LAW: chars are all digits when the first is one and the rest are
law digits_all_reads_each:
  for c: Char
  for rest: List<&2, Char>
  for e: {Char.is_digit(c) == True{} : Bool}
  {Numeral.digits.all(c <> rest) == Numeral.digits.all(rest) : Bool}

# LAW: so a single digit is all digits
law digits_all_holds_of_one_digit:
  for c: Char
  for e: {Char.is_digit(c) == True{} : Bool}
  {Numeral.digits.all(c <> Nil{}) == True{} : Bool}

# LAW: and not when one of them is no digit, whatever follows
law digits_all_stops_at_other_char:
  for c: Char
  for rest: List<&2, Char>
  for e: {Char.is_digit(c) == False{} : Bool}
  {Numeral.digits.all(c <> rest) == False{} : Bool}

# LAW: a number token in digits is a literal: its text
law literal_takes_digits:
  for +t: String
  for e: {Numeral.digits(t) == True{} : Bool}
  {Numeral.literal(Lex.TNum{}, t) == t : String}
