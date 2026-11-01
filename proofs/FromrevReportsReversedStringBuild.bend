# proofs of laws/FromrevReportsReversedStringBuild.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/paths.bend as Paths
import ../src/rules/suspicious/fromrev.bend as Fromrev
import ../laws/FromrevReportsReversedStringBuild.bend as Laws
import ./lemmas/Nat.bend as M1
import ./lemmas/PutEarlyStop.bend as M2

# fromrev
# -------

# an and of four, grouped either way
law fromrev.and4:
  for p: Bool
  for q: Bool
  for r: Bool
  for w: Bool
  {Bool.and(p, Bool.and(q, Bool.and(r, w))) == Bool.and(Bool.and(p, q), Bool.and(r, w)) : Bool}

def fromrev.and4(p, _q, _r, _w):
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

# the rule's test of a run is the law's
law fromrev.at:
  for +t: String
  for toks: List<&2, Lex.Tok>
  {Fromrev.at(t, toks) == Laws.fromrev_at(t, toks) : Bool}

def fromrev.at(t, toks):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k1, a, l1, c1}, r1}:
      match r1:
        case Nil{}:
          {==}
        case Con{Lex.Tok{k2, b, l2, c2}, r2}:
          match r2:
            case Nil{}:
              {==}
            case Con{Lex.Tok{k3, d, l3, c3}, r3}:
              fromrev.and4(String.eq(t, "String.from_list"), String.eq(a, "("), String.eq(b, "List.reverse"),
                String.eq(d, "("))

# fromrev's walk counts the runs
law fromrev.walk:
  for toks: List<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Fromrev.walk(toks, path)) == Laws.fromrev_count(toks) : Nat}

def fromrev.walk(toks, path):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, +t, +l, +c}, +rest}:
      +x = {F.Finding{path, l, c, 16, "fromrev",
          "String.from_list(List.reverse(..)) walks the list twice and builds one it throws away; fold it onto a String with SCon in one pass."}
        : F.Finding}
      %fromrev.at(t, rest) : {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, Fromrev.at(t, rest),
        x <> Fromrev.walk(rest, path), Fromrev.walk(rest, path)))
        == Bool.pick(Nat, _, 1n+Laws.fromrev_count(rest), Laws.fromrev_count(rest)) : Nat}
      M1.nat.pick(Fromrev.at(t, rest), x, Fromrev.walk(rest, path), Laws.fromrev_count(rest), fromrev.walk(rest, path))

def Laws.fromrev_counts(path, _text, toks, _tree, _bound, _items):
  M2.put.stop(Paths.is_law_file(path), Fromrev.walk(T.sig(toks), path), Laws.fromrev_count(T.sig(toks)),
    fromrev.walk(T.sig(toks), path))
