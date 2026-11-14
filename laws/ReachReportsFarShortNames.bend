# `reach` reports exactly one finding for each binder that is a parameter, a
# let, do-bind or lambda name, or a pattern name, and that some use reads
# from more than `max` lines below its line by a name spelled with one
# character, `max` being the limit the rule is run at, unless the binder's name is one capital letter, it is a
# parameter that is a quantity (bare, or typed `: Quant`), or it sits in a
# def that is a proof; none for any other binder, and none at all in a
# PROOF.bend. A binder sits in the item bound last before it, and a def is a
# proof when the line of its name is among those `Reach.proofs` reads from
# the file's significant tokens: the token after each `def` whose header
# src/rules/suspicious/empty.bend's `proofy` reads as a proof.
#
# A use that is within the limit, that spells a name of more than one
# character, or that reads anything but a binder of the file is never far,
# so a file with no far use has no finding.
#
# A name is spelled with one character when, its `_` aside, it is one letter
# or digit written one or more times. That reading is proved for the letter
# `n` and an `x` after it, not for every pair of characters: `n` written any
# number of times is one character, whatever `_` stand before or after it;
# an `x` anywhere after it makes two; and `_` alone are none.
import Base
import ../src/finding.bend as F
import ../src/rules/style/reach.bend as Reach
import ../src/syntax/bind.bend as Bind
import ../src/syntax/lex.bend as Lex
import ../src/paths.bend as Paths
import ../src/rules/tokens.bend as T

# a binder of a kind reach counts: a parameter, a let, do-bind or lambda
# name, or a pattern name
def counted(k: Bind.BindKind) -> Bool:
  match k:
    case Bind.KParam{}:
      True{}
    case Bind.KLocal{}:
      True{}
    case Bind.KPat{}:
      True{}
    case Bind.KItem{}:
      False{}
    case Bind.KCtor{}:
      False{}
    case Bind.KTypeParam{}:
      False{}
    case Bind.KField{}:
      False{}
    case Bind.KFor{}:
      False{}
    case Bind.KTypeVar{}:
      False{}

# does a use that refers to this target, by this name on this line, read the
# binder at (line, col) from more than max lines below, the name spelled
# with one character?
def reads_far(name: String, ul: U32, t: Bind.Target, line: U32, col: U32, max: U32) -> Bool:
  match t:
    case Bind.TLocal{+tl, tc}:
      Bool.and(Bool.and(U32.is_gt(ul, (tl + max : U32)), Reach.one(name)),
        Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col)))
    case Bind.TItem{_n}:
      False{}
    case Bind.TQual{_a, _n}:
      False{}
    case Bind.TFree{}:
      False{}

# does any of the uses read the binder at (line, col) so?
def read_far(uses: List<&2, Bind.Use>, +line: U32, +col: U32, +max: U32) -> Bool:
  match uses:
    case Nil{}:
      False{}
    case Con{Bind.Use{name, ul, _uc, t}, rest}:
      Bool.or(reads_far(name, ul, t, line, col, max), read_far(rest, line, col, max))

# is the binder one reach reports? item: the line of the item it sits in
def carried(
  +k: Bind.BindKind,
  nm: String,
  line: U32,
  col: U32,
  note: String,
  uses: List<&2, Bind.Use>,
  ps: List<&2, U32>,
  item: U32,
  max: U32
) -> Bool:
  Bool.and(read_far(uses, line, col, max),
    Bool.and(counted(k), Bool.and(Bool.not(Reach.allowed(k, nm, note)), Bool.not(Reach.has(ps, item)))))

# how many of the binders reach reports. item: the line of the item the
# binders so far sit in
def far_count(
  binds: List<&2, Bind.Bind>,
  +uses: List<&2, Bind.Use>,
  +ps: List<&2, U32>,
  item: U32,
  +max: U32
) -> Nat:
  match binds:
    case Nil{}:
      0n
    case Con{Bind.Bind{nm, +line, col, +k, note}, rest}:
      +at = Reach.at_item(k, line, item)
      +m = far_count(rest, uses, ps, at, max)
      Bool.pick(Nat, carried(k, nm, line, col, note, uses, ps, at, max), 1n+m, m)

# `n`, written once more than the count
def ens(kn: Nat) -> List<&2, Char>:
  match kn:
    case 0n:
      ['n']
    case 1n+p:
      'n' <> ens(p)

# that many `_`, then the rest
def unders(un: Nat, rest: List<&2, Char>) -> List<&2, Char>:
  match un:
    case 0n:
      rest
    case 1n+p:
      '_' <> unders(p, rest)

# LAW: over a file's binders, uses and tokens, at any limit, reach reports
# one finding for each binder of a kind that counts that a use reads from
# more than that many lines below by a one-character name, that is not left alone and sits in no def
# that is a proof; none for any other binder, and none at all in a PROOF.bend
law reach_counts:
  for +binds: List<&2, Bind.Bind>
  for +uses: List<&2, Bind.Use>
  for +toks: List<&2, Lex.Tok>
  for +path: String
  for +max: U32
  {List.length(&2, F.Finding, Reach.check.on(binds, uses, toks, path, max))
    == Bool.pick(Nat, Paths.is_proof(path), 0n, far_count(binds, uses, Reach.proofs(T.sig(toks)), 0, max)) : Nat}

# LAW: a use within the limit of its binder is not far, whatever its name
law reach_near_use_is_not_far:
  for +name: String
  for +line: U32
  for +tl: U32
  for tc: U32
  for +max: U32
  for e: {U32.is_gt(line, (tl + max : U32)) == False{} : Bool}
  {Reach.far.hit(name, line, Bind.TLocal{tl, tc}, max) == None{} : Maybe<&2, Bind.Pos>}

# LAW: a use of a name of more than one character is not far, however far
# below its binder it is
law reach_longer_name_is_not_far:
  for +name: String
  for +line: U32
  for +tl: U32
  for tc: U32
  for +max: U32
  for e: {Reach.one(name) == False{} : Bool}
  {Reach.far.hit(name, line, Bind.TLocal{tl, tc}, max) == None{} : Maybe<&2, Bind.Pos>}

# LAW: a file none of whose uses is far has no finding, whatever it binds
law reach_silent_without_far_uses:
  for +binds: List<&2, Bind.Bind>
  for +uses: List<&2, Bind.Use>
  for +toks: List<&2, Lex.Tok>
  for +path: String
  for +max: U32
  for e: {Reach.far(uses, max) == Nil{} : List<&2, Bind.Pos>}
  {Reach.check.on(binds, uses, toks, path, max) == Nil{} : List<&2, F.Finding>}

# LAW: `n` written any number of times, after any number of `_`, is spelled
# with one character
law reach_repeated_letter_is_one:
  for kn: Nat
  for un: Nat
  {Reach.one.go(unders(un, ens(kn))) == True{} : Bool}

# LAW: any number of `_` after the `n`s leave it one character
law reach_trailing_underscores_keep_one:
  for kn: Nat
  for un: Nat
  {Reach.one.go(List.append(&2, Char, ens(kn), unders(un, Nil{}))) == True{} : Bool}

# LAW: an `x` anywhere after the `n`s makes a name of two characters
law reach_second_letter_makes_two:
  for kn: Nat
  for un: Nat
  for rest: List<&2, Char>
  {Reach.one.go(unders(un, List.append(&2, Char, ens(kn), 'x' <> rest))) == False{} : Bool}

# LAW: `_` alone, any number of them, spell no character
law reach_underscores_are_none:
  for un: Nat
  {Reach.one.go(unders(un, Nil{})) == False{} : Bool}
