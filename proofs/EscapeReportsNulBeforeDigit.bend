# proofs of laws/EscapeReportsNulBeforeDigit.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/correctness/escape.bend as Esc
import ../src/rules/correctness/pick.bend as Pick
import ../laws/EscapeReportsNulBeforeDigit.bend as Laws
import ./lemmas/Pick.bend as M1

# what follows a `\0` adds one finding when it opens with a digit
law esc.after:
  for s: List<&2, Esc.Sym>
  for +path: String
  for +line: U32
  for +col: U32
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Esc.after(s, path, line, col, more)) == Nat.add(Laws.nul_lead(s), m) : Nat}

def esc.after(s, _path, _line, _col, more, m, ih):
  match s:
    case Con{Esc.SZero{}, t}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
    case Con{Esc.SDigit{d}, t}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
    case Con{Esc.SSlash{}, t}:
      ih
    case Con{Esc.SOther{o}, t}:
      ih
    case Nil{}:
      ih

def Laws.escape_scan_counts(s, path, line, col):
  match s:
    case Con{Esc.SSlash{}, Con{Esc.SZero{}, +rest}}:
      esc.after(rest, path, line, col, Esc.scan(rest, path, line, (col + 2 : U32)), Laws.nul_count(rest),
        Laws.escape_scan_counts(rest, path, line, (col + 2 : U32)))
    case Con{Esc.SSlash{}, Con{Esc.SSlash{}, rest}}:
      Laws.escape_scan_counts(rest, path, line, (col + 2 : U32))
    case Con{Esc.SSlash{}, Con{Esc.SDigit{d}, rest}}:
      Laws.escape_scan_counts(rest, path, line, (col + 2 : U32))
    case Con{Esc.SSlash{}, Con{Esc.SOther{o}, rest}}:
      Laws.escape_scan_counts(rest, path, line, (col + 2 : U32))
    case Con{Esc.SSlash{}, Nil{}}:
      {==}
    case Con{Esc.SZero{}, rest}:
      Laws.escape_scan_counts(rest, path, line, (col + 1 : U32))
    case Con{Esc.SDigit{d}, rest}:
      Laws.escape_scan_counts(rest, path, line, (col + 1 : U32))
    case Con{Esc.SOther{o}, rest}:
      Laws.escape_scan_counts(rest, path, line, (col + 1 : U32))
    case Nil{}:
      {==}

# a literal's findings onto the rest's
law esc.lit:
  for +t: String
  for +l: U32
  for +c: U32
  for +rest: List<&2, Lex.Tok>
  for +path: String
  for ih: {List.length(&2, F.Finding, Esc.check.go(rest, path)) == Laws.esc_count(rest) : Nat}
  {List.length(&2, F.Finding,
    List.append(&2, F.Finding, Esc.scan(Esc.syms(String.to_list(t)), path, l, c), Esc.check.go(rest, path)))
    == Nat.add(Laws.nul_count(Esc.syms(String.to_list(t))), Laws.esc_count(rest)) : Nat}

def esc.lit(t, l, c, rest, path, ih):
  Equal.trans(Nat,
    List.length(&2, F.Finding,
      List.append(&2, F.Finding, Esc.scan(Esc.syms(String.to_list(t)), path, l, c), Esc.check.go(rest, path))),
    Nat.add(List.length(&2, F.Finding, Esc.scan(Esc.syms(String.to_list(t)), path, l, c)),
      List.length(&2, F.Finding, Esc.check.go(rest, path))),
    Nat.add(Laws.nul_count(Esc.syms(String.to_list(t))), Laws.esc_count(rest)),
    M1.esc.app(Esc.scan(Esc.syms(String.to_list(t)), path, l, c), Esc.check.go(rest, path)),
    M1.esc.add(List.length(&2, F.Finding, Esc.scan(Esc.syms(String.to_list(t)), path, l, c)),
      Laws.nul_count(Esc.syms(String.to_list(t))), List.length(&2, F.Finding, Esc.check.go(rest, path)),
      Laws.esc_count(rest), Laws.escape_scan_counts(Esc.syms(String.to_list(t)), path, l, c), ih))

# one token onto a list the law holds for
law esc.step:
  for k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +rest: List<&2, Lex.Tok>
  for +path: String
  for ih: {List.length(&2, F.Finding, Esc.check.go(rest, path)) == Laws.esc_count(rest) : Nat}
  {List.length(&2, F.Finding, Esc.check.go(Lex.Tok{k, t, l, c} <> rest, path))
    == Laws.esc_count(Lex.Tok{k, t, l, c} <> rest) : Nat}

def esc.step(k, t, l, c, rest, path, ih):
  match k:
    case Lex.TStr{}:
      esc.lit(t, l, c, rest, path, ih)
    case Lex.TChar{}:
      esc.lit(t, l, c, rest, path, ih)
    case Lex.TName{}:
      ih
    case Lex.TUpper{}:
      ih
    case Lex.TDotted{}:
      ih
    case Lex.TWild{}:
      ih
    case Lex.TKey{}:
      ih
    case Lex.TNum{}:
      ih
    case Lex.TComment{}:
      ih
    case Lex.TSpace{}:
      ih
    case Lex.TNewline{}:
      ih
    case Lex.TOp{}:
      ih
    case Lex.TColon{}:
      ih
    case Lex.TEq{}:
      ih
    case Lex.TBind{}:
      ih
    case Lex.TArrow{}:
      ih
    case Lex.TLam{}:
      ih
    case Lex.TAll{}:
      ih
    case Lex.TAmp{}:
      ih
    case Lex.TOpen{}:
      ih
    case Lex.TClose{}:
      ih
    case Lex.TComma{}:
      ih

def Laws.escape_counts(toks, path):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, t, l, c}, +rest}:
      esc.step(k, t, l, c, rest, path, Laws.escape_counts(rest, path))

def Laws.escape_octal_digits(d):
  match d:
    case Laws.D1{}:
      {==}
    case Laws.D2{}:
      {==}
    case Laws.D3{}:
      {==}
    case Laws.D4{}:
      {==}
    case Laws.D5{}:
      {==}
    case Laws.D6{}:
      {==}
    case Laws.D7{}:
      {==}
    case Laws.D8{}:
      {==}
    case Laws.D9{}:
      {==}

def Laws.escape_names_one_digit(a):
  match a:
    case Laws.O0{}:
      {==}
    case Laws.O1{}:
      {==}
    case Laws.O2{}:
      {==}
    case Laws.O3{}:
      {==}
    case Laws.O4{}:
      {==}
    case Laws.O5{}:
      {==}
    case Laws.O6{}:
      {==}
    case Laws.O7{}:
      {==}

def Laws.escape_names_two_digits(a, b):
  match a:
    case Laws.O0{}:
      match b:
        case Laws.O0{}:
          {==}
        case Laws.O1{}:
          {==}
        case Laws.O2{}:
          {==}
        case Laws.O3{}:
          {==}
        case Laws.O4{}:
          {==}
        case Laws.O5{}:
          {==}
        case Laws.O6{}:
          {==}
        case Laws.O7{}:
          {==}
    case Laws.O1{}:
      match b:
        case Laws.O0{}:
          {==}
        case Laws.O1{}:
          {==}
        case Laws.O2{}:
          {==}
        case Laws.O3{}:
          {==}
        case Laws.O4{}:
          {==}
        case Laws.O5{}:
          {==}
        case Laws.O6{}:
          {==}
        case Laws.O7{}:
          {==}
    case Laws.O2{}:
      match b:
        case Laws.O0{}:
          {==}
        case Laws.O1{}:
          {==}
        case Laws.O2{}:
          {==}
        case Laws.O3{}:
          {==}
        case Laws.O4{}:
          {==}
        case Laws.O5{}:
          {==}
        case Laws.O6{}:
          {==}
        case Laws.O7{}:
          {==}
    case Laws.O3{}:
      match b:
        case Laws.O0{}:
          {==}
        case Laws.O1{}:
          {==}
        case Laws.O2{}:
          {==}
        case Laws.O3{}:
          {==}
        case Laws.O4{}:
          {==}
        case Laws.O5{}:
          {==}
        case Laws.O6{}:
          {==}
        case Laws.O7{}:
          {==}
    case Laws.O4{}:
      match b:
        case Laws.O0{}:
          {==}
        case Laws.O1{}:
          {==}
        case Laws.O2{}:
          {==}
        case Laws.O3{}:
          {==}
        case Laws.O4{}:
          {==}
        case Laws.O5{}:
          {==}
        case Laws.O6{}:
          {==}
        case Laws.O7{}:
          {==}
    case Laws.O5{}:
      match b:
        case Laws.O0{}:
          {==}
        case Laws.O1{}:
          {==}
        case Laws.O2{}:
          {==}
        case Laws.O3{}:
          {==}
        case Laws.O4{}:
          {==}
        case Laws.O5{}:
          {==}
        case Laws.O6{}:
          {==}
        case Laws.O7{}:
          {==}
    case Laws.O6{}:
      match b:
        case Laws.O0{}:
          {==}
        case Laws.O1{}:
          {==}
        case Laws.O2{}:
          {==}
        case Laws.O3{}:
          {==}
        case Laws.O4{}:
          {==}
        case Laws.O5{}:
          {==}
        case Laws.O6{}:
          {==}
        case Laws.O7{}:
          {==}
    case Laws.O7{}:
      match b:
        case Laws.O0{}:
          {==}
        case Laws.O1{}:
          {==}
        case Laws.O2{}:
          {==}
        case Laws.O3{}:
          {==}
        case Laws.O4{}:
          {==}
        case Laws.O5{}:
          {==}
        case Laws.O6{}:
          {==}
        case Laws.O7{}:
          {==}
