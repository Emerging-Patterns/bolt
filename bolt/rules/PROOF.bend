# bolt/rules: the proofs. `bend PROOF.bend` is the gate.
import Base
import ../../syntax/lex.bend as Lex
import ../finding.bend as F
import ./tokens.bend as T
import ./suspicious/nat.bend as NatRule
import ./correctness/escape.bend as Esc
import ./style/param.bend as Param
import ../../syntax/bind.bend as Bind
import ../paths.bend as Paths
import ../../lazy/lazy.bend as Lazy
import ./correctness/put.bend as Put
import ./correctness/hole.bend as Hole
import ./laws/trace.bend as Trace
import ./style/space.bend as Space
import ../src.bend as Src
import ../../syntax/tree.bend as Tree
import ../../syntax/outline.bend as Outline
import ./calls.bend as Calls
import ./style/doc.bend as Doc
import ./correctness/pick.bend as Pick
import ./pedantic/tail.bend as Tail
import ./suspicious/concat.bend as Concat
import ./suspicious/eager.bend as Eager
import ./suspicious/rewalk.bend as Rewalk
import ./suspicious/strict.bend as Strict
import ./suspicious/hoist.bend as Hoist
import ./suspicious/index.bend as Index
import ./suspicious/ring.bend as Ring
import ./suspicious/table.bend as Table
import ./suspicious/unit.bend as UnitRule
import ./correctness/chars.bend as Chars
import ./correctness/strings.bend as Strings
import ./LAWS.bend as Laws

# a finding in front when b holds adds one to the count
law nat.pick:
  for b: Bool
  for -x: F.Finding
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, b, x <> more, more)) == Bool.pick(Nat, b, 1n+m, m)
    : Nat}

def nat.pick(b, _x, more, m, ih):
  match b:
    case True{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
    case False{}:
      ih

# one token onto a list the law holds for
law nat.step:
  for kk: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for +rest: List<&2, Lex.Tok>
  for +path: String
  for ih: {List.length(&2, F.Finding, NatRule.check.go(rest, path)) == Laws.big_count(rest) : Nat}
  {List.length(&2, F.Finding, NatRule.check.go(Lex.Tok{kk, t, l, c} <> rest, path))
    == Laws.big_count(Lex.Tok{kk, t, l, c} <> rest) : Nat}

def nat.step(kk, t, l, c, rest, path, ih):
  match kk:
    case Lex.TNum{}:
      nat.pick(NatRule.big(t), F.Finding{path, l, c, T.width(t), "nat",
        t ++ " is " ++ T.stem(t) ++ " unary cells; Nat literals of 1000 or more are unary, so use U32, or U32.to_nat at run time."},
        NatRule.check.go(rest, path), Laws.big_count(rest), ih)
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
    case Lex.TStr{}:
      ih
    case Lex.TChar{}:
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

def Laws.nat_counts(toks, path):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{kk, t, l, c}, +rest}:
      nat.step(kk, t, l, c, rest, path, Laws.nat_counts(rest, path))

# the length of two lists appended is the sum of theirs
law esc.app:
  for a: List<&2, F.Finding>
  for b: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.append(&2, F.Finding, a, b))
    == Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, b)) : Nat}

def esc.app(a, b):
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, List.append(&2, F.Finding, t, b)),
        Nat.add(List.length(&2, F.Finding, t), List.length(&2, F.Finding, b)), esc.app(t, b))

# equal summands give equal sums
law esc.add:
  for -a: Nat
  for -b: Nat
  for -c: Nat
  for -d: Nat
  for e1: {a == b : Nat}
  for e2: {c == d : Nat}
  {Nat.add(a, c) == Nat.add(b, d) : Nat}

def esc.add(a, b, c, d, e1, e2):
  Equal.trans(Nat, Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), Equal.cong(Nat, Nat, x => Nat.add(x, c), a, b, e1),
    Equal.cong(Nat, Nat, y => Nat.add(b, y), c, d, e2))

# what follows a `\0` adds one finding when it opens with a digit
law esc.after:
  for ss: List<&2, Esc.Sym>
  for +path: String
  for +line: U32
  for +col: U32
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Esc.after(ss, path, line, col, more)) == Nat.add(Laws.nul_lead(ss), m) : Nat}

def esc.after(ss, _path, _line, _col, more, m, ih):
  match ss:
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

def Laws.escape_scan_counts(ss, path, line, col):
  match ss:
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
    esc.app(Esc.scan(Esc.syms(String.to_list(t)), path, l, c), Esc.check.go(rest, path)),
    esc.add(List.length(&2, F.Finding, Esc.scan(Esc.syms(String.to_list(t)), path, l, c)),
      Laws.nul_count(Esc.syms(String.to_list(t))), List.length(&2, F.Finding, Esc.check.go(rest, path)),
      Laws.esc_count(rest), Laws.escape_scan_counts(Esc.syms(String.to_list(t)), path, l, c), ih))

# one token onto a list the law holds for
law esc.step:
  for kk: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +rest: List<&2, Lex.Tok>
  for +path: String
  for ih: {List.length(&2, F.Finding, Esc.check.go(rest, path)) == Laws.esc_count(rest) : Nat}
  {List.length(&2, F.Finding, Esc.check.go(Lex.Tok{kk, t, l, c} <> rest, path))
    == Laws.esc_count(Lex.Tok{kk, t, l, c} <> rest) : Nat}

def esc.step(kk, t, l, c, rest, path, ih):
  match kk:
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
    case Con{Lex.Tok{kk, t, l, c}, +rest}:
      esc.step(kk, t, l, c, rest, path, Laws.escape_counts(rest, path))

# one capital, to the rule and to the law
law param.letter:
  for cs: List<&2, Char>
  {Param.check.letter(cs) == Laws.one_upper(cs) : Bool}

def param.letter(cs):
  match cs:
    case Nil{}:
      {==}
    case Con{ch, r}:
      match r:
        case Nil{}:
          {==}
        case Con{d2, t}:
          {==}

# the rule's hit is the law's too_short
law param.hit:
  for kk: Bind.BindKind
  for +nm: String
  for +note: String
  {Bool.and(Param.check.is_param(kk),
      Bool.and(Param.check.short(nm), Bool.not(Param.check.allowed(nm, note)))) == Laws.too_short(kk, nm, note) : Bool}

def param.hit(kk, nm, note):
  match kk:
    case Bind.KParam{}:
      Equal.cong(Bool, Bool,
        z => Bool.and(Nat.is_lt(String.length(nm), 2n),
          Bool.not(Bool.or(z, Bool.or(Bool.not(String.contains(note, ":")), String.ends_with(note, ": Quant"))))),
        Param.check.letter(String.to_list(nm)), Laws.one_upper(String.to_list(nm)),
        param.letter(String.to_list(nm)))
    case Bind.KItem{}:
      {==}
    case Bind.KCtor{}:
      {==}
    case Bind.KTypeParam{}:
      {==}
    case Bind.KField{}:
      {==}
    case Bind.KLocal{}:
      {==}
    case Bind.KPat{}:
      {==}
    case Bind.KFor{}:
      {==}
    case Bind.KTypeVar{}:
      {==}

# one binder onto a list the law holds for
law param.step:
  for +nm: String
  for +line: U32
  for +col: U32
  for +kk: Bind.BindKind
  for +note: String
  for +rest: List<&2, Bind.Bind>
  for +path: String
  for ih: {List.length(&2, F.Finding, Param.check.go(rest, path)) == Laws.short_count(rest) : Nat}
  {List.length(&2, F.Finding, Param.check.go(Bind.Bind{nm, line, col, kk, note} <> rest, path))
    == Laws.short_count(Bind.Bind{nm, line, col, kk, note} <> rest) : Nat}

def param.step(nm, line, col, kk, note, rest, path, ih):
  Equal.trans(Nat,
    List.length(&2, F.Finding, Param.check.go(Bind.Bind{nm, line, col, kk, note} <> rest, path)),
    Bool.pick(Nat, Bool.and(Param.check.is_param(kk),
      Bool.and(Param.check.short(nm), Bool.not(Param.check.allowed(nm, note)))),
      1n+Laws.short_count(rest), Laws.short_count(rest)),
    Bool.pick(Nat, Laws.too_short(kk, nm, note), 1n+Laws.short_count(rest), Laws.short_count(rest)),
    nat.pick(Bool.and(Param.check.is_param(kk),
      Bool.and(Param.check.short(nm), Bool.not(Param.check.allowed(nm, note)))),
      F.Finding{path, line, col, U32.from_nat(String.length(nm)), "param",
        "Parameter " ++ nm ++ " is shorter than 2 characters."},
      Param.check.go(rest, path), Laws.short_count(rest), ih),
    Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, 1n+Laws.short_count(rest), Laws.short_count(rest)),
      Bool.and(Param.check.is_param(kk),
      Bool.and(Param.check.short(nm), Bool.not(Param.check.allowed(nm, note)))),
      Laws.too_short(kk, nm, note), param.hit(kk, nm, note)))

# param's walk counts the short parameters
law param.go:
  for binds: List<&2, Bind.Bind>
  for +path: String
  {List.length(&2, F.Finding, Param.check.go(binds, path)) == Laws.short_count(binds) : Nat}

def param.go(binds, path):
  match binds:
    case Nil{}:
      {==}
    case Con{Bind.Bind{nm, line, col, kk, note}, +rest}:
      param.step(nm, line, col, kk, note, rest, path, param.go(rest, path))

# an early exit to no findings counts 0, else what the rest counts
law param.stop:
  for b: Bool
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, b, [], _u => more))
    == Bool.pick(Nat, b, 0n, m) : Nat}

def param.stop(b, _more, _m, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def Laws.param_counts(binds, path):
  param.stop(Paths.is_proof(path), Param.check.go(binds, path), Laws.short_count(binds), param.go(binds, path))

# a lone token: no call follows it
law put.one:
  for kk: Lex.TokKind
  for t: String
  for l: U32
  for c: U32
  for +path: String
  {List.length(&2, F.Finding, Put.calls(Lex.Tok{kk, t, l, c} <> [], path))
    == Laws.put_count(Lex.Tok{kk, t, l, c} <> []) : Nat}

def put.one(kk, _t, _l, _c, _path):
  match kk:
    case Lex.TName{}:
      {==}
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      {==}
    case Lex.TWild{}:
      {==}
    case Lex.TKey{}:
      {==}
    case Lex.TNum{}:
      {==}
    case Lex.TStr{}:
      {==}
    case Lex.TChar{}:
      {==}
    case Lex.TComment{}:
      {==}
    case Lex.TSpace{}:
      {==}
    case Lex.TNewline{}:
      {==}
    case Lex.TOp{}:
      {==}
    case Lex.TColon{}:
      {==}
    case Lex.TEq{}:
      {==}
    case Lex.TBind{}:
      {==}
    case Lex.TArrow{}:
      {==}
    case Lex.TLam{}:
      {==}
    case Lex.TAll{}:
      {==}
    case Lex.TAmp{}:
      {==}
    case Lex.TOpen{}:
      {==}
    case Lex.TClose{}:
      {==}
    case Lex.TComma{}:
      {==}

# a `Map.put` token, then any token, onto a list the law holds for
law put.dot:
  for kk: Lex.TokKind
  for +t: String
  for +o: String
  for +l: U32
  for +c: U32
  for l2: U32
  for c2: U32
  for +r: List<&2, Lex.Tok>
  for +path: String
  for ih1: {List.length(&2, F.Finding, Put.calls(Lex.Tok{kk, o, l2, c2} <> r, path))
    == Laws.put_count(Lex.Tok{kk, o, l2, c2} <> r) : Nat}
  for ih2: {List.length(&2, F.Finding, Put.calls(r, path)) == Laws.put_count(r) : Nat}
  {List.length(&2, F.Finding, Put.calls(Lex.Tok{Lex.TDotted{}, t, l, c} <> Lex.Tok{kk, o, l2, c2} <> r, path))
    == Laws.put_count(Lex.Tok{Lex.TDotted{}, t, l, c} <> Lex.Tok{kk, o, l2, c2} <> r) : Nat}

def put.dot(kk, t, o, l, c, _l2, _c2, r, path, ih1, ih2):
  match kk:
    case Lex.TName{}:
      ih1
    case Lex.TUpper{}:
      ih1
    case Lex.TDotted{}:
      ih1
    case Lex.TWild{}:
      ih1
    case Lex.TKey{}:
      ih1
    case Lex.TNum{}:
      ih1
    case Lex.TStr{}:
      ih1
    case Lex.TChar{}:
      ih1
    case Lex.TComment{}:
      ih1
    case Lex.TSpace{}:
      ih1
    case Lex.TNewline{}:
      ih1
    case Lex.TOp{}:
      ih1
    case Lex.TColon{}:
      ih1
    case Lex.TEq{}:
      ih1
    case Lex.TBind{}:
      ih1
    case Lex.TArrow{}:
      ih1
    case Lex.TLam{}:
      ih1
    case Lex.TAll{}:
      ih1
    case Lex.TAmp{}:
      ih1
    case Lex.TOpen{}:
      nat.pick(Bool.and(String.eq(t, "Map.put"), String.eq(o, "(")),
        F.Finding{path, l, c, 7, "put", "Map.put never compares keys, so a new key overwrites another entry; use Map.set."},
        Put.calls(r, path), Laws.put_count(r), ih2)
    case Lex.TClose{}:
      ih1
    case Lex.TComma{}:
      ih1

# two tokens onto a list the law holds for
law put.pair:
  for kk: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for k2: Lex.TokKind
  for +o: String
  for +l2: U32
  for +c2: U32
  for +r: List<&2, Lex.Tok>
  for +path: String
  for ih1: {List.length(&2, F.Finding, Put.calls(Lex.Tok{k2, o, l2, c2} <> r, path))
    == Laws.put_count(Lex.Tok{k2, o, l2, c2} <> r) : Nat}
  for ih2: {List.length(&2, F.Finding, Put.calls(r, path)) == Laws.put_count(r) : Nat}
  {List.length(&2, F.Finding, Put.calls(Lex.Tok{kk, t, l, c} <> Lex.Tok{k2, o, l2, c2} <> r, path))
    == Laws.put_count(Lex.Tok{kk, t, l, c} <> Lex.Tok{k2, o, l2, c2} <> r) : Nat}

def put.pair(kk, t, l, c, k2, o, l2, c2, r, path, ih1, ih2):
  match kk:
    case Lex.TName{}:
      ih1
    case Lex.TUpper{}:
      ih1
    case Lex.TDotted{}:
      put.dot(k2, t, o, l, c, l2, c2, r, path, ih1, ih2)
    case Lex.TWild{}:
      ih1
    case Lex.TKey{}:
      ih1
    case Lex.TNum{}:
      ih1
    case Lex.TStr{}:
      ih1
    case Lex.TChar{}:
      ih1
    case Lex.TComment{}:
      ih1
    case Lex.TSpace{}:
      ih1
    case Lex.TNewline{}:
      ih1
    case Lex.TOp{}:
      ih1
    case Lex.TColon{}:
      ih1
    case Lex.TEq{}:
      ih1
    case Lex.TBind{}:
      ih1
    case Lex.TArrow{}:
      ih1
    case Lex.TLam{}:
      ih1
    case Lex.TAll{}:
      ih1
    case Lex.TAmp{}:
      ih1
    case Lex.TOpen{}:
      ih1
    case Lex.TClose{}:
      ih1
    case Lex.TComma{}:
      ih1

# put's calls count the `Map.put(` sites
law put.calls:
  for toks: List<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Put.calls(toks, path)) == Laws.put_count(toks) : Nat}

def put.calls(toks, path):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{kk, t, l, c}, +rest}:
      match rest:
        case Nil{}:
          put.one(kk, t, l, c, path)
        case Con{Lex.Tok{k2, o, l2, c2}, r}:
          put.pair(kk, t, l, c, k2, o, l2, c2, r, path, put.calls(rest, path), put.calls(r, path))

# the first token is `Map.put` the same way to the rule and to the law
law put.named:
  for toks: List<&2, Lex.Tok>
  {Put.defines.named(toks) == Laws.put_named(toks) : Bool}

def put.named(toks):
  match toks:
    case Con{Lex.Tok{k, t, l, c}, rest}:
      {==}
    case Nil{}:
      {==}

# the early-exit or of a Bool and a thunk is the plain or
law put.or:
  for a: Bool
  for -x: Bool
  for -y: Bool
  for ih: {x == y : Bool}
  {Lazy.or_else(a, _u => x) == Bool.or(a, y) : Bool}

def put.or(a, _x, _y, ih):
  match a:
    case True{}:
      {==}
    case False{}:
      ih

# a `def` keyword onto a list the law holds for
law put.key:
  for +t: String
  for +rest: List<&2, Lex.Tok>
  for ih: {Put.defines(rest) == Laws.put_defined(rest) : Bool}
  {Lazy.or_else(Bool.and(String.eq(t, "def"), Put.defines.named(rest)), _u => Put.defines(rest))
    == Bool.or(Bool.and(String.eq(t, "def"), Laws.put_named(rest)), Laws.put_defined(rest)) : Bool}

def put.key(t, rest, ih):
  Equal.trans(Bool,
    Lazy.or_else(Bool.and(String.eq(t, "def"), Put.defines.named(rest)), _u => Put.defines(rest)),
    Bool.or(Bool.and(String.eq(t, "def"), Put.defines.named(rest)), Laws.put_defined(rest)),
    Bool.or(Bool.and(String.eq(t, "def"), Laws.put_named(rest)), Laws.put_defined(rest)),
    put.or(Bool.and(String.eq(t, "def"), Put.defines.named(rest)), Put.defines(rest), Laws.put_defined(rest), ih),
    Equal.cong(Bool, Bool, z => Bool.or(Bool.and(String.eq(t, "def"), z), Laws.put_defined(rest)),
      Put.defines.named(rest), Laws.put_named(rest), put.named(rest)))

# one token onto a list the law holds for
law put.head:
  for kk: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for +rest: List<&2, Lex.Tok>
  for ih: {Put.defines(rest) == Laws.put_defined(rest) : Bool}
  {Put.defines(Lex.Tok{kk, t, l, c} <> rest) == Laws.put_defined(Lex.Tok{kk, t, l, c} <> rest) : Bool}

def put.head(kk, t, _l, _c, rest, ih):
  match kk:
    case Lex.TName{}:
      ih
    case Lex.TUpper{}:
      ih
    case Lex.TDotted{}:
      ih
    case Lex.TWild{}:
      ih
    case Lex.TKey{}:
      put.key(t, rest, ih)
    case Lex.TNum{}:
      ih
    case Lex.TStr{}:
      ih
    case Lex.TChar{}:
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

# put's exemption test is the law's
law put.defines:
  for toks: List<&2, Lex.Tok>
  {Put.defines(toks) == Laws.put_defined(toks) : Bool}

def put.defines(toks):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{kk, t, l, c}, +rest}:
      put.head(kk, t, l, c, rest, put.defines(rest))

# an early exit to no findings counts 0, else what the rest counts
law put.stop:
  for b: Bool
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, b, [], _u => more)) == Bool.pick(Nat, b, 0n, m) : Nat}

def put.stop(b, _more, _m, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def Laws.put_counts(toks, path):
  Equal.trans(Nat,
    List.length(&2, F.Finding, Put.check.on(toks, path)),
    Bool.pick(Nat, Put.defines(toks), 0n, Laws.put_count(toks)),
    Bool.pick(Nat, Laws.put_defined(toks), 0n, Laws.put_count(toks)),
    put.stop(Put.defines(toks), Put.calls(toks, path), Laws.put_count(toks), put.calls(toks, path)),
    Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, 0n, Laws.put_count(toks)),
      Put.defines(toks), Laws.put_defined(toks), put.defines(toks)))

# one token onto a list the TODO test agrees on
law hole.todo.step:
  for kk: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for +rest: List<&2, Lex.Tok>
  for ih: {Hole.check.todo(rest) == Laws.todo_next(rest) : Bool}
  {Hole.check.todo(Lex.Tok{kk, t, l, c} <> rest) == Laws.todo_next(Lex.Tok{kk, t, l, c} <> rest) : Bool}

def hole.todo.step(kk, _t, _l, _c, _rest, ih):
  match kk:
    case Lex.TNum{}:
      {==}
    case Lex.TName{}:
      {==}
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      {==}
    case Lex.TWild{}:
      {==}
    case Lex.TKey{}:
      {==}
    case Lex.TStr{}:
      {==}
    case Lex.TChar{}:
      {==}
    case Lex.TComment{}:
      ih
    case Lex.TSpace{}:
      ih
    case Lex.TNewline{}:
      ih
    case Lex.TOp{}:
      {==}
    case Lex.TColon{}:
      {==}
    case Lex.TEq{}:
      {==}
    case Lex.TBind{}:
      {==}
    case Lex.TArrow{}:
      {==}
    case Lex.TLam{}:
      {==}
    case Lex.TAll{}:
      {==}
    case Lex.TAmp{}:
      {==}
    case Lex.TOpen{}:
      {==}
    case Lex.TClose{}:
      {==}
    case Lex.TComma{}:
      {==}

# the TODO test is the same to the rule and to the law
law hole.todo:
  for toks: List<&2, Lex.Tok>
  {Hole.check.todo(toks) == Laws.todo_next(toks) : Bool}

def hole.todo(toks):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{kk, t, l, c}, +rest}:
      hole.todo.step(kk, t, l, c, rest, hole.todo(rest))

# the early-exit and of a Bool and a thunk is the plain and
law hole.and:
  for a: Bool
  for -x: Bool
  for -y: Bool
  for ih: {x == y : Bool}
  {Lazy.and_then(a, _u => x) == Bool.and(a, y) : Bool}

def hole.and(a, _x, _y, ih):
  match a:
    case True{}:
      ih
    case False{}:
      {==}

# a finding in front unless b fails adds one to the count
law hole.stop:
  for b: Bool
  for -x: F.Finding
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(b), more, _u => x <> more))
    == Bool.pick(Nat, b, 1n+m, m) : Nat}

def hole.stop(b, _x, more, m, ih):
  match b:
    case True{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
    case False{}:
      ih

# one token onto a list the law holds for
law hole.step:
  for kk: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +rest: List<&2, Lex.Tok>
  for +path: String
  for ih: {List.length(&2, F.Finding, Hole.check.go(rest, path)) == Laws.hole_count(rest) : Nat}
  {List.length(&2, F.Finding, Hole.check.go(Lex.Tok{kk, t, l, c} <> rest, path))
    == Laws.hole_count(Lex.Tok{kk, t, l, c} <> rest) : Nat}

def hole.step(kk, t, l, c, rest, path, ih):
  match kk:
    case Lex.TNum{}:
      ih
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
    case Lex.TStr{}:
      ih
    case Lex.TChar{}:
      ih
    case Lex.TComment{}:
      ih
    case Lex.TSpace{}:
      ih
    case Lex.TNewline{}:
      ih
    case Lex.TOp{}:
      Equal.trans(Nat,
        List.length(&2, F.Finding, Hole.check.go(Lex.Tok{Lex.TOp{}, t, l, c} <> rest, path)),
        Bool.pick(Nat, Lazy.and_then(String.eq(t, "?"), _u => Hole.check.todo(rest)),
          1n+Laws.hole_count(rest), Laws.hole_count(rest)),
        Laws.hole_count(Lex.Tok{Lex.TOp{}, t, l, c} <> rest),
        hole.stop(Lazy.and_then(String.eq(t, "?"), _u => Hole.check.todo(rest)),
          F.Finding{path, l, c, Hole.check.width(rest, l, c), "hole", "A ?TODO is left here."},
          Hole.check.go(rest, path), Laws.hole_count(rest), ih),
        Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, 1n+Laws.hole_count(rest), Laws.hole_count(rest)),
          Lazy.and_then(String.eq(t, "?"), _u => Hole.check.todo(rest)),
          Bool.and(String.eq(t, "?"), Laws.todo_next(rest)),
          hole.and(String.eq(t, "?"), Hole.check.todo(rest), Laws.todo_next(rest), hole.todo(rest))))
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

# hole's walk counts the `?TODO` holes
law hole.go:
  for toks: List<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Hole.check.go(toks, path)) == Laws.hole_count(toks) : Nat}

def hole.go(toks, path):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{kk, t, l, c}, +rest}:
      hole.step(kk, t, l, c, rest, path, hole.go(rest, path))

def Laws.hole_counts(toks, path):
  put.stop(Paths.is_laws(path), Hole.check.go(toks, path), Laws.hole_count(toks), hole.go(toks, path))
def Laws.trace_pending_judged(_id, _e, _es, _nn, sp, _ds):
  match sp:
    case Trace.Spec{_m, _r, _t, _b}:
      {==}

def Laws.trace_pending_shape(_ls):
  {==}

def Laws.trace_proved_shape(ls):
  match ls:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      {==}

def Laws.trace_trusted_shape(ls):
  match ls:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      {==}

def Laws.trace_pending_claimed(_i, _ls, _n, _rs, _id):
  {==}

def Laws.trace_trusted_unclaimed(_i, _st, _ls, _n, _rs, _id):
  {==}

def Laws.trace_unlisted_unclaimed(_id):
  {==}

# a tab among the chars, to the rule and to the law
law sp.tab:
  for cs: List<&2, Char>
  {Space.has_tab(cs) == Laws.tabbed(cs) : Bool}

def sp.tab(cs):
  match cs:
    case Nil{}:
      {==}
    case Con{c, t}:
      put.or(Char.is_eq(c, '\t'), Space.has_tab(t), Laws.tabbed(t), sp.tab(t))

# trailing whitespace, to the rule and to the law
law sp.tail:
  for cs: List<&2, Char>
  {Space.trailing(cs) == Laws.ends_space(cs) : Bool}

def sp.tail(cs):
  match cs:
    case Nil{}:
      {==}
    case Con{c, +t}:
      match t:
        case Nil{}:
          {==}
        case Con{d, r}:
          sp.tail(t)

# one finding for a line with trailing whitespace, else one for a tab
law sp.two:
  for a: Bool
  for b: Bool
  for -x: F.Finding
  for -y: F.Finding
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding,
    Bool.pick(List<&2, F.Finding>, a, x <> more, Bool.pick(List<&2, F.Finding>, b, y <> more, more)))
    == Bool.pick(Nat, Bool.or(a, b), 1n+m, m) : Nat}

def sp.two(a, b, _x, y, more, m, ih):
  match a:
    case True{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
    case False{}:
      nat.pick(b, y, more, m, ih)

# one line onto lines the law holds for
law sp.line:
  for +line: String
  for +rest: List<&2, String>
  for +path: String
  for +nn: U32
  for ih: {List.length(&2, F.Finding, Space.check.go(rest, path, (nn + 1 : U32))) == Laws.space_count(rest) : Nat}
  {List.length(&2, F.Finding, Space.check.go(line <> rest, path, nn)) == Laws.space_count(line <> rest) : Nat}

def sp.line(line, rest, path, nn, ih):
  Equal.trans(Nat,
    List.length(&2, F.Finding, Space.check.go(line <> rest, path, nn)),
    Bool.pick(Nat, Bool.or(Space.trailing(String.to_list(line)), Space.has_tab(String.to_list(line))),
      1n+Laws.space_count(rest), Laws.space_count(rest)),
    Laws.space_count(line <> rest),
    sp.two(Space.trailing(String.to_list(line)), Space.has_tab(String.to_list(line)),
      F.Finding{path, nn, (U32.from_nat(List.length(&2, Char, String.to_list(line))) - 1 : U32), 1, "space",
        "Line has trailing whitespace."},
      F.Finding{path, nn, 0, 1, "space", "Line contains a tab; indent with spaces."},
      Space.check.go(rest, path, (nn + 1 : U32)), Laws.space_count(rest), ih),
    Equal.trans(Nat,
      Bool.pick(Nat, Bool.or(Space.trailing(String.to_list(line)), Space.has_tab(String.to_list(line))),
        1n+Laws.space_count(rest), Laws.space_count(rest)),
      Bool.pick(Nat, Bool.or(Laws.ends_space(String.to_list(line)), Space.has_tab(String.to_list(line))),
        1n+Laws.space_count(rest), Laws.space_count(rest)),
      Laws.space_count(line <> rest),
      Equal.cong(Bool, Nat,
        z => Bool.pick(Nat, Bool.or(z, Space.has_tab(String.to_list(line))), 1n+Laws.space_count(rest),
          Laws.space_count(rest)),
        Space.trailing(String.to_list(line)), Laws.ends_space(String.to_list(line)), sp.tail(String.to_list(line))),
      Equal.cong(Bool, Nat,
        z => Bool.pick(Nat, Bool.or(Laws.ends_space(String.to_list(line)), z), 1n+Laws.space_count(rest),
          Laws.space_count(rest)),
        Space.has_tab(String.to_list(line)), Laws.tabbed(String.to_list(line)), sp.tab(String.to_list(line)))))

def Laws.space_line_counts(lines, path, nn):
  match lines:
    case Nil{}:
      {==}
    case Con{line, +rest}:
      sp.line(line, rest, path, nn, Laws.space_line_counts(rest, path, (nn + 1 : U32)))

# one token onto tokens the law holds for, at the width after it
law sp.wstep:
  for kk: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for +rest: List<&2, Lex.Tok>
  for +path: String
  for +nn: U32
  for +acc: U32
  for nl: {List.length(&2, F.Finding, Space.widths(rest, path, (nn + 1 : U32), 0)) == Laws.wide_count(rest, 0) : Nat}
  for ih: {List.length(&2, F.Finding, Space.widths(rest, path, nn, (acc + Space.width_of(kk, t) : U32)))
    == Laws.wide_count(rest, (acc + Space.width_of(kk, t) : U32)) : Nat}
  {List.length(&2, F.Finding, Space.widths(Lex.Tok{kk, t, l, c} <> rest, path, nn, acc))
    == Laws.wide_count(Lex.Tok{kk, t, l, c} <> rest, acc) : Nat}

def sp.wstep(kk, _t, _l, _c, rest, path, nn, acc, nl, ih):
  match kk:
    case Lex.TNewline{}:
      nat.pick(U32.is_gt(acc, 120), F.Finding{path, nn, 120, 0, "space", "Line exceeds the 120-character limit."},
        Space.widths(rest, path, (nn + 1 : U32), 0), Laws.wide_count(rest, 0), nl)
    case Lex.TStr{}:
      ih
    case Lex.TComment{}:
      ih
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
    case Lex.TChar{}:
      ih
    case Lex.TSpace{}:
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

def Laws.space_width_counts(toks, path, nn, acc):
  match toks:
    case Nil{}:
      nat.pick(U32.is_gt(acc, 120), F.Finding{path, nn, 120, 0, "space", "Line exceeds the 120-character limit."},
        [], 0n, {==})
    case Con{Lex.Tok{+kk, +t, l, c}, +rest}:
      sp.wstep(kk, t, l, c, rest, path, nn, acc, Laws.space_width_counts(rest, path, (nn + 1 : U32), 0),
        Laws.space_width_counts(rest, path, nn, (acc + Space.width_of(kk, t) : U32)))

def Laws.space_counts(path, text, toks, tree, bound, items):
  Equal.trans(Nat,
    List.length(&2, F.Finding, Space.check(Src.Src{path, text, toks, tree, bound, items})),
    Nat.add(List.length(&2, F.Finding, Space.check.go(String.lines(text), path, 0)),
      List.length(&2, F.Finding, Space.widths(toks, path, 0, 0))),
    Nat.add(Laws.space_count(String.lines(text)), Laws.wide_count(toks, 0)),
    esc.app(Space.check.go(String.lines(text), path, 0), Space.widths(toks, path, 0, 0)),
    esc.add(List.length(&2, F.Finding, Space.check.go(String.lines(text), path, 0)),
      Laws.space_count(String.lines(text)), List.length(&2, F.Finding, Space.widths(toks, path, 0, 0)),
      Laws.wide_count(toks, 0), Laws.space_line_counts(String.lines(text), path, 0),
      Laws.space_width_counts(toks, path, 0, 0)))

# The header exemptions (BOLT-RULE-EXEMPT). A rule that stops on its path
# stops with Nil; one that walks the file's defs stops on every def of a law
# file, so the walk gathers only empty lists and joins them into Nil.

# a stop whose condition holds gives its Nil
law ex.stop:
  for b: Bool
  for e: {b == True{} : Bool}
  for -f: Unit -> List<&2, F.Finding>
  {Lazy.stop(List<&2, F.Finding>, b, Nil{}, f) == Nil{} : List<&2, F.Finding>}

def ex.stop(b, e, f):
  s = Equal.sym(Bool, b, True{}, e)
  %s : {Lazy.stop(List<&2, F.Finding>, _, Nil{}, f) == Nil{} : List<&2, F.Finding>}
  {==}

# n empty finding lists: what a def walk gathers in a law file
def ex.rep(n: Nat) -> List<&2, List<&2, F.Finding>>:
  List.replicate(List<&2, F.Finding>, n, Nil{})

# reversing empty lists onto an accumulator adds nothing to its join
law ex.flat:
  for n: Nat
  for acc: List<&2, List<&2, F.Finding>>
  {List.concat(&2, F.Finding, List.reverse.go(&2, List<&2, F.Finding>, ex.rep(n), acc))
    == List.concat(&2, F.Finding, acc) : List<&2, F.Finding>}

def ex.flat(n, acc):
  match n:
    case 0n:
      {==}
    case 1n+p:
      ex.flat(p, Nil{} <> acc)

# a def whose stop holds pushes one more empty list onto the walk
law ex.push:
  for b: Bool
  for e: {b == True{} : Bool}
  for -f: Unit -> List<&2, F.Finding>
  for -n: Nat
  for -k: List<&2, List<&2, F.Finding>> -> List<&2, F.Finding>
  for ih: {k(ex.rep(1n+n)) == Nil{} : List<&2, F.Finding>}
  {k(Lazy.stop(List<&2, F.Finding>, b, Nil{}, f) <> ex.rep(n)) == Nil{} : List<&2, F.Finding>}

def ex.push(b, e, f, n, k, ih):
  s = Equal.sym(Bool, b, True{}, e)
  %s : {k(Lazy.stop(List<&2, F.Finding>, _, Nil{}, f) <> ex.rep(n)) == Nil{} : List<&2, F.Finding>}
  ih

# a law file exempts every def of it
law ex.calls:
  for +path: String
  for sig: Tree.Node
  for e: {Paths.is_law_file(path) == True{} : Bool}
  {Calls.exempt(path, sig) == True{} : Bool}

def ex.calls(path, sig, e):
  s = Equal.sym(Bool, Paths.is_law_file(path), True{}, e)
  %s : {Bool.or(_, Calls.returns_proof(sig)) == True{} : Bool}
  {==}

# not (x and not True) holds whatever x is
law ex.nand:
  for x: Bool
  {Bool.not(Bool.and(x, Bool.not(True{}))) == True{} : Bool}

def ex.nand(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# a guard `not (x and not exempt)` holds in a law file
law ex.guard:
  for x: Bool
  for +path: String
  for sig: Tree.Node
  for e: {Paths.is_law_file(path) == True{} : Bool}
  {Bool.not(Bool.and(x, Bool.not(Calls.exempt(path, sig)))) == True{} : Bool}

def ex.guard(x, path, sig, e):
  s = Equal.sym(Bool, Calls.exempt(path, sig), True{}, ex.calls(path, sig, e))
  %s : {Bool.not(Bool.and(x, Bool.not(_))) == True{} : Bool}
  ex.nand(x)

def Laws.hole_exempt(path, _text, toks, _tree, _bound, _items, e):
  ex.stop(Paths.is_laws(path), e, _u => Hole.check.go(toks, path))

def Laws.doc_exempt(path, text, _toks, _tree, _bound, items, e):
  ex.stop(Bool.or(Paths.is_proof(path), Paths.is_test(path)), e,
    _u => Doc.check.go(items, path, String.lines(text)))

def Laws.param_exempt(path, _text, _toks, _tree, bound, _items, e):
  match bound:
    case Bind.Bound{binds, _uses, _scopes}:
      ex.stop(Paths.is_proof(path), e, _u => Param.check.go(binds, path))

# pick's def walk gathers nothing in a law file
law ex.pick:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +n: Nat
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {Pick.check.go(ds, path, ex.rep(n)) == Nil{} : List<&2, F.Finding>}

def ex.pick(ds, path, n, e):
  match ds:
    case Nil{}:
      ex.flat(n, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      ex.push(
        Calls.exempt(path, sig),
        ex.calls(path, sig, e),
        _u => Pick.picks(body, name, path, False{}), n,
        v => Pick.check.go(rest, path, v), ex.pick(rest, path, 1n+n, e))

def Laws.pick_exempt(path, _text, _toks, tree, _bound, _items, e):
  ex.pick(Calls.defs(tree), path, 0n, e)

# tail's def walk gathers nothing in a law file
law ex.tail:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +n: Nat
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {Tail.check.go(ds, path, ex.rep(n)) == Nil{} : List<&2, F.Finding>}

def ex.tail(ds, path, n, e):
  match ds:
    case Nil{}:
      ex.flat(n, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      ex.push(
        Bool.not(Bool.and(Calls.seq(sig), Bool.not(Calls.exempt(path, sig)))),
        ex.guard(Calls.seq(sig), path, sig, e),
        _u => Tail.walk(body, name, path, False{}), n,
        v => Tail.check.go(rest, path, v), ex.tail(rest, path, 1n+n, e))

def Laws.tail_exempt(path, _text, _toks, tree, _bound, _items, e):
  ex.tail(Calls.defs(tree), path, 0n, e)

# concat's def walk gathers nothing in a law file
law ex.concat:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +n: Nat
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {Concat.check.go(ds, path, ex.rep(n)) == Nil{} : List<&2, F.Finding>}

def ex.concat(ds, path, n, e):
  match ds:
    case Nil{}:
      ex.flat(n, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      ex.push(
        Calls.exempt(path, sig),
        ex.calls(path, sig, e),
        _u => Concat.walk(body, name, Calls.names(sig), path), n,
        v => Concat.check.go(rest, path, v), ex.concat(rest, path, 1n+n, e))

def Laws.concat_exempt(path, _text, _toks, tree, _bound, _items, e):
  ex.concat(Calls.defs(tree), path, 0n, e)

# eager's def walk gathers nothing in a law file
law ex.eager:
  for ds: List<&2, Calls.Def>
  for +ns: List<&2, String>
  for +path: String
  for +n: Nat
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {Eager.check.go(ds, ns, path, ex.rep(n)) == Nil{} : List<&2, F.Finding>}

def ex.eager(ds, ns, path, n, e):
  match ds:
    case Nil{}:
      ex.flat(n, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      ex.push(
        Calls.exempt(path, sig),
        ex.calls(path, sig, e),
        _u => Eager.work(body, ns, name, path, False{}, 9, False{}), n,
        v => Eager.check.go(rest, ns, path, v), ex.eager(rest, ns, path, 1n+n, e))

def Laws.eager_exempt(path, _text, _toks, tree, _bound, _items, e):
  +ds = Calls.defs(tree)
  ex.eager(ds, Eager.loops(ds), path, 0n, e)

# rewalk's def walk gathers nothing in a law file
law ex.rewalk:
  for ds: List<&2, Calls.Def>
  for +lp: List<&2, String>
  for +path: String
  for +n: Nat
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {Rewalk.check.go(ds, lp, path, ex.rep(n)) == Nil{} : List<&2, F.Finding>}

def ex.rewalk(ds, lp, path, n, e):
  match ds:
    case Nil{}:
      ex.flat(n, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      ex.push(
        Calls.exempt(path, sig),
        ex.calls(path, sig, e),
        _u => List.concat(&2, F.Finding,
          [Rewalk.local(body, name, lp, path), Rewalk.visit(body, name, lp, path)]), n,
        v => Rewalk.check.go(rest, lp, path, v), ex.rewalk(rest, lp, path, 1n+n, e))

def Laws.rewalk_exempt(path, _text, _toks, tree, _bound, _items, e):
  +ds = Calls.defs(tree)
  ex.rewalk(ds, Rewalk.loops(ds), path, 0n, e)

# strict's def walk gathers nothing in a law file
law ex.strict:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +n: Nat
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {Strict.check.go(ds, path, ex.rep(n)) == Nil{} : List<&2, F.Finding>}

def ex.strict(ds, path, n, e):
  match ds:
    case Nil{}:
      ex.flat(n, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      ex.push(
        Calls.exempt(path, sig),
        ex.calls(path, sig, e),
        _u => Strict.walk(body, name, path, False{}, False{}), n,
        v => Strict.check.go(rest, path, v), ex.strict(rest, path, 1n+n, e))

def Laws.strict_exempt(path, _text, _toks, tree, _bound, _items, e):
  ex.strict(Calls.defs(tree), path, 0n, e)

# hoist's def walk gathers nothing in a law file
law ex.hoist:
  for ds: List<&2, Calls.Def>
  for +wide: List<&2, String>
  for +path: String
  for +n: Nat
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {Hoist.check.go(ds, wide, path, ex.rep(n)) == Nil{} : List<&2, F.Finding>}

def ex.hoist(ds, wide, path, n, e):
  match ds:
    case Nil{}:
      ex.flat(n, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      ex.push(
        Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))),
        ex.guard(Calls.calls(body, name), path, sig, e),
        _u => Hoist.walk(body, name, wide, Hoist.carried(sig, body, name), path, True{}), n,
        v => Hoist.check.go(rest, wide, path, v), ex.hoist(rest, wide, path, 1n+n, e))

def Laws.hoist_exempt(path, _text, _toks, tree, _bound, _items, e):
  +ds = Calls.defs(tree)
  ex.hoist(ds, Hoist.wide_defs(ds, Nil{}), path, 0n, e)

# index's def walk gathers nothing in a law file
law ex.index:
  for ds: List<&2, Calls.Def>
  for +mods: List<&2, String>
  for +path: String
  for +n: Nat
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {Index.check.go(ds, mods, path, ex.rep(n)) == Nil{} : List<&2, F.Finding>}

def ex.index(ds, mods, path, n, e):
  match ds:
    case Nil{}:
      ex.flat(n, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      ex.push(
        Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))),
        ex.guard(Calls.calls(body, name), path, sig, e),
        _u => Index.walk(body, path, Table.scope(body, mods)), n,
        v => Index.check.go(rest, mods, path, v), ex.index(rest, mods, path, 1n+n, e))

def Laws.index_exempt(path, _text, _toks, tree, _bound, _items, e):
  +ds = Calls.defs(tree)
  ex.index(ds, Table.modules(ds, Nil{}), path, 0n, e)

# ring's def walk gathers nothing in a law file
law ex.ring:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +n: Nat
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {Ring.check.go(ds, path, ex.rep(n)) == Nil{} : List<&2, F.Finding>}

def ex.ring(ds, path, n, e):
  match ds:
    case Nil{}:
      ex.flat(n, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      ex.push(
        Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))),
        ex.guard(Calls.calls(body, name), path, sig, e),
        _u => Ring.walk(body, name, Calls.names(sig), path, Ring.windows(sig, body)), n,
        v => Ring.check.go(rest, path, v), ex.ring(rest, path, 1n+n, e))

def Laws.ring_exempt(path, _text, _toks, tree, _bound, _items, e):
  ex.ring(Calls.defs(tree), path, 0n, e)

# table's def walk gathers nothing in a law file
law ex.table:
  for ds: List<&2, Calls.Def>
  for +mods: List<&2, String>
  for +path: String
  for +n: Nat
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {Table.check.go(ds, mods, path, ex.rep(n)) == Nil{} : List<&2, F.Finding>}

def ex.table(ds, mods, path, n, e):
  match ds:
    case Nil{}:
      ex.flat(n, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      ex.push(
        Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))),
        ex.guard(Calls.calls(body, name), path, sig, e),
        _u => Table.walk(body, path, Table.scope(body, mods)), n,
        v => Table.check.go(rest, mods, path, v), ex.table(rest, mods, path, 1n+n, e))

def Laws.table_exempt(path, _text, _toks, tree, _bound, _items, e):
  +ds = Calls.defs(tree)
  ex.table(ds, Table.modules(ds, Nil{}), path, 0n, e)

# unit's def walk gathers nothing in a law file
law ex.unit:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +n: Nat
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {UnitRule.check.go(ds, path, ex.rep(n)) == Nil{} : List<&2, F.Finding>}

def ex.unit(ds, path, n, e):
  match ds:
    case Nil{}:
      ex.flat(n, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      ex.push(
        Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))),
        ex.guard(Calls.calls(body, name), path, sig, e),
        _u => UnitRule.walk(body, None{}, name, path, True{}), n,
        v => UnitRule.check.go(rest, path, v), ex.unit(rest, path, 1n+n, e))

def Laws.unit_exempt(path, _text, _toks, tree, _bound, _items, e):
  ex.unit(Calls.defs(tree), path, 0n, e)

# The match rules, chars and strings: a statement's walk joins three lists,
# its own finding, its body's and the rest's, so the count is their sum.

# appending nothing keeps the length
law chars.nil:
  for xs: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.append(&2, F.Finding, xs, [])) == List.length(&2, F.Finding, xs) : Nat}

def chars.nil(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, List.append(&2, F.Finding, t, [])),
        List.length(&2, F.Finding, t), chars.nil(t))

# three lists joined count as the sum of their counts
law chars.three:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for +c: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c]))
    == Nat.add(List.length(&2, F.Finding, a), Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c)))
    : Nat}

def chars.three(a, b, c):
  +bc = List.append(&2, F.Finding, b, List.append(&2, F.Finding, c, []))
  Equal.trans(Nat,
    List.length(&2, F.Finding, List.append(&2, F.Finding, a, bc)),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, bc)),
    Nat.add(List.length(&2, F.Finding, a), Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c))),
    esc.app(a, bc),
    esc.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, a), List.length(&2, F.Finding, bc),
      Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c)), {==},
      Equal.trans(Nat,
        List.length(&2, F.Finding, bc),
        Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, List.append(&2, F.Finding, c, []))),
        Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c)),
        esc.app(b, List.append(&2, F.Finding, c, [])),
        esc.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, b),
          List.length(&2, F.Finding, List.append(&2, F.Finding, c, [])), List.length(&2, F.Finding, c), {==},
          chars.nil(c)))))

# a lone finding when b holds counts one, else none
law chars.one:
  for b: Bool
  for -x: F.Finding
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, b, [x], [])) == Bool.pick(Nat, b, 1n, 0n) : Nat}

def chars.one(b, _x):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a statement that is not a match adds nothing; a match adds what its report does
law chars.gate:
  for b: Bool
  for -more: List<&2, F.Finding>
  for -g: Bool
  for ih: {List.length(&2, F.Finding, more) == Bool.pick(Nat, g, 1n, 0n) : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(b), [], _u => more))
    == Bool.pick(Nat, Bool.and(b, g), 1n, 0n) : Nat}

def chars.gate(b, _more, _g, ih):
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# the rule's keyword test is the law's
law chars.key:
  for kids: Tree.Node
  {T.keyword(kids, "match") == Laws.chars.is_match(kids) : Bool}

def chars.key(kids):
  match kids:
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{o, gk, cl}:
      {==}
    case Tree.Stmt{kind, sk, sb}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{h, rest}:
      match h:
        case Tree.Leaf{Lex.Tok{kind, t, l, c}}:
          match kind:
            case Lex.TName{}:
              {==}
            case Lex.TUpper{}:
              {==}
            case Lex.TDotted{}:
              {==}
            case Lex.TWild{}:
              {==}
            case Lex.TKey{}:
              {==}
            case Lex.TNum{}:
              {==}
            case Lex.TStr{}:
              {==}
            case Lex.TChar{}:
              {==}
            case Lex.TComment{}:
              {==}
            case Lex.TSpace{}:
              {==}
            case Lex.TNewline{}:
              {==}
            case Lex.TOp{}:
              {==}
            case Lex.TColon{}:
              {==}
            case Lex.TEq{}:
              {==}
            case Lex.TBind{}:
              {==}
            case Lex.TArrow{}:
              {==}
            case Lex.TLam{}:
              {==}
            case Lex.TAll{}:
              {==}
            case Lex.TAmp{}:
              {==}
            case Lex.TOpen{}:
              {==}
            case Lex.TClose{}:
              {==}
            case Lex.TComma{}:
              {==}
        case Tree.Group{o, gk, cl}:
          {==}
        case Tree.Stmt{kind, sk, sb}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{nh, nt}:
          {==}

# the rule's literal test on the pattern is the law's on the case
law chars.lit:
  for kids: Tree.Node
  {Chars.literal(T.pattern(kids)) == Laws.chars.opens(kids) : U32}

def chars.lit(kids):
  match kids:
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{o, gk, cl}:
      {==}
    case Tree.Stmt{kind, sk, sb}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{h, rest}:
      match rest:
        case Tree.Leaf{tok}:
          {==}
        case Tree.Group{o, gk, cl}:
          {==}
        case Tree.Stmt{kind, sk, sb}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{h2, r2}:
          match h2:
            case Tree.Leaf{Lex.Tok{kind, +t, l, c}}:
              match kind:
                case Lex.TName{}:
                  {==}
                case Lex.TUpper{}:
                  {==}
                case Lex.TDotted{}:
                  {==}
                case Lex.TWild{}:
                  {==}
                case Lex.TKey{}:
                  {==}
                case Lex.TNum{}:
                  {==}
                case Lex.TStr{}:
                  {==}
                case Lex.TChar{}:
                  {==}
                case Lex.TComment{}:
                  {==}
                case Lex.TSpace{}:
                  {==}
                case Lex.TNewline{}:
                  {==}
                case Lex.TOp{}:
                  {==}
                case Lex.TColon{}:
                  {==}
                case Lex.TEq{}:
                  {==}
                case Lex.TBind{}:
                  {==}
                case Lex.TArrow{}:
                  {==}
                case Lex.TLam{}:
                  {==}
                case Lex.TAll{}:
                  {==}
                case Lex.TAmp{}:
                  {==}
                case Lex.TOpen{}:
                  {==}
                case Lex.TClose{}:
                  {==}
                case Lex.TComma{}:
                  {==}
            case Tree.Group{o, gk, cl}:
              {==}
            case Tree.Stmt{kind, sk, sb}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{nh, nt}:
              {==}

# a case statement onto a body the law holds for, at the rule's count
law chars.step:
  for +rest: Tree.Node
  for +nn: U32
  for +kids: Tree.Node
  for ih: {Chars.tally(rest, (nn + Chars.literal(T.pattern(kids)) : U32))
    == Laws.chars.arms(rest, (nn + Chars.literal(T.pattern(kids)) : U32)) : U32}
  {Chars.tally(rest, (nn + Chars.literal(T.pattern(kids)) : U32))
    == Laws.chars.arms(rest, (nn + Laws.chars.opens(kids) : U32)) : U32}

def chars.step(rest, nn, kids, ih):
  Equal.trans(U32,
    Chars.tally(rest, (nn + Chars.literal(T.pattern(kids)) : U32)),
    Laws.chars.arms(rest, (nn + Chars.literal(T.pattern(kids)) : U32)),
    Laws.chars.arms(rest, (nn + Laws.chars.opens(kids) : U32)),
    ih,
    Equal.cong(U32, U32, z => Laws.chars.arms(rest, (nn + z : U32)),
      Chars.literal(T.pattern(kids)), Laws.chars.opens(kids), chars.lit(kids)))

# chars' tally counts the arms the law counts
law chars.tally:
  for body: Tree.Node
  for +nn: U32
  {Chars.tally(body, nn) == Laws.chars.arms(body, nn) : U32}

def chars.tally(body, nn):
  match body:
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{o, gk, cl}:
      {==}
    case Tree.Stmt{kind, sk, sb}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          chars.tally(rest, nn)
        case Tree.Group{o, gk, cl}:
          chars.tally(rest, nn)
        case Tree.Stmt{kind, +kids, b}:
          match kind:
            case Tree.SDef{}:
              chars.tally(rest, nn)
            case Tree.SType{}:
              chars.tally(rest, nn)
            case Tree.SLaw{}:
              chars.tally(rest, nn)
            case Tree.SImport{}:
              chars.tally(rest, nn)
            case Tree.SCase{}:
              chars.step(rest, nn, kids, chars.tally(rest, (nn + Chars.literal(T.pattern(kids)) : U32)))
            case Tree.SFor{}:
              chars.tally(rest, nn)
            case Tree.SLet{}:
              chars.tally(rest, nn)
            case Tree.STerm{}:
              chars.tally(rest, nn)
        case Tree.NNil{}:
          chars.tally(rest, nn)
        case Tree.NCons{nh, nt}:
          chars.tally(rest, nn)

# a statement's own finding: one when it is a match over more than eight
# char arms
law chars.stmt:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Chars.on_stmt(kids, body, path))
    == Bool.pick(Nat, Bool.and(Laws.chars.is_match(kids), U32.is_gt(Laws.chars.arms(body, 0), 8)), 1n, 0n) : Nat}

def chars.stmt(kids, body, path):
  +n = Chars.tally(body, 0)
  Equal.trans(Nat,
    List.length(&2, F.Finding, Chars.on_stmt(kids, body, path)),
    Bool.pick(Nat, Bool.and(T.keyword(kids, "match"), U32.is_gt(n, 8)), 1n, 0n),
    Bool.pick(Nat, Bool.and(Laws.chars.is_match(kids), U32.is_gt(Laws.chars.arms(body, 0), 8)), 1n, 0n),
    chars.gate(T.keyword(kids, "match"), Chars.report(n, path, Tree.line(kids), Tree.col(kids)), U32.is_gt(n, 8),
      chars.one(U32.is_gt(n, 8), F.Finding{path, Tree.line(kids), Tree.col(kids), 5, "chars",
        "A match over " ++ U32.show(n) ++ " character literals exceeds the limit of 8 and blows up compile time and"
        ++ " memory; compare Char.to_u32(c) instead."})),
    Equal.trans(Nat,
      Bool.pick(Nat, Bool.and(T.keyword(kids, "match"), U32.is_gt(n, 8)), 1n, 0n),
      Bool.pick(Nat, Bool.and(Laws.chars.is_match(kids), U32.is_gt(n, 8)), 1n, 0n),
      Bool.pick(Nat, Bool.and(Laws.chars.is_match(kids), U32.is_gt(Laws.chars.arms(body, 0), 8)), 1n, 0n),
      Equal.cong(Bool, Nat, z => Bool.pick(Nat, Bool.and(z, U32.is_gt(n, 8)), 1n, 0n),
        T.keyword(kids, "match"), Laws.chars.is_match(kids), chars.key(kids)),
      Equal.cong(U32, Nat, z => Bool.pick(Nat, Bool.and(Laws.chars.is_match(kids), U32.is_gt(z, 8)), 1n, 0n),
        n, Laws.chars.arms(body, 0), chars.tally(body, 0))))

# a statement onto the rest: its finding, its body's and the rest's
law chars.sum:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for +c: List<&2, F.Finding>
  for -x: Nat
  for -y: Nat
  for -z: Nat
  for e1: {List.length(&2, F.Finding, a) == x : Nat}
  for e2: {List.length(&2, F.Finding, b) == y : Nat}
  for e3: {List.length(&2, F.Finding, c) == z : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])) == Nat.add(x, Nat.add(y, z)) : Nat}

def chars.sum(a, b, c, x, y, z, e1, e2, e3):
  Equal.trans(Nat,
    List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])),
    Nat.add(List.length(&2, F.Finding, a), Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c))),
    Nat.add(x, Nat.add(y, z)),
    chars.three(a, b, c),
    esc.add(List.length(&2, F.Finding, a), x,
      Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c)), Nat.add(y, z), e1,
      esc.add(List.length(&2, F.Finding, b), y, List.length(&2, F.Finding, c), z, e2, e3)))

# chars' walk counts the matches the law counts
law chars.walk:
  for nn: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Chars.walk(nn, path)) == Laws.chars.count(nn) : Nat}

def chars.walk(nn, path):
  match nn:
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{o, gk, cl}:
      {==}
    case Tree.Stmt{kind, sk, sb}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          chars.walk(rest, path)
        case Tree.Group{o, gk, cl}:
          chars.walk(rest, path)
        case Tree.Stmt{kind, +kids, +body}:
          chars.sum(Chars.on_stmt(kids, body, path), Chars.walk(body, path), Chars.walk(rest, path),
            Bool.pick(Nat, Bool.and(Laws.chars.is_match(kids), U32.is_gt(Laws.chars.arms(body, 0), 8)), 1n, 0n),
            Laws.chars.count(body), Laws.chars.count(rest),
            chars.stmt(kids, body, path), chars.walk(body, path), chars.walk(rest, path))
        case Tree.NNil{}:
          chars.walk(rest, path)
        case Tree.NCons{nh, nt}:
          chars.walk(rest, path)

def Laws.chars_counts(path, _text, _toks, tree, _bound, _items):
  chars.walk(tree, path)

# the chars of a closed string arm, else zero, to the rule and to the law
law strings.pick:
  for b: Bool
  for -x: U32
  {Strings.size(Bool.pick(Maybe<&2, U32>, b, Some{x}, None{})) == Bool.pick(U32, b, x, 0) : U32}

def strings.pick(b, _x):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the rule's string arm test on the pattern is the law's on the case
law strings.lit:
  for kids: Tree.Node
  {Strings.size(Strings.literal(T.pattern(kids))) == Laws.strings.size(kids) : U32}

def strings.lit(kids):
  match kids:
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{o, gk, cl}:
      {==}
    case Tree.Stmt{kind, sk, sb}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{h, rest}:
      match rest:
        case Tree.Leaf{tok}:
          {==}
        case Tree.Group{o, gk, cl}:
          {==}
        case Tree.Stmt{kind, sk, sb}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{h2, r2}:
          match h2:
            case Tree.Leaf{Lex.Tok{kind, +t, l, c}}:
              match kind:
                case Lex.TName{}:
                  {==}
                case Lex.TUpper{}:
                  {==}
                case Lex.TDotted{}:
                  {==}
                case Lex.TWild{}:
                  {==}
                case Lex.TKey{}:
                  {==}
                case Lex.TNum{}:
                  {==}
                case Lex.TStr{}:
                  strings.pick(Strings.terminated(t), (U32.from_nat(String.length(t)) - 2 : U32))
                case Lex.TChar{}:
                  {==}
                case Lex.TComment{}:
                  {==}
                case Lex.TSpace{}:
                  {==}
                case Lex.TNewline{}:
                  {==}
                case Lex.TOp{}:
                  {==}
                case Lex.TColon{}:
                  {==}
                case Lex.TEq{}:
                  {==}
                case Lex.TBind{}:
                  {==}
                case Lex.TArrow{}:
                  {==}
                case Lex.TLam{}:
                  {==}
                case Lex.TAll{}:
                  {==}
                case Lex.TAmp{}:
                  {==}
                case Lex.TOpen{}:
                  {==}
                case Lex.TClose{}:
                  {==}
                case Lex.TComma{}:
                  {==}
            case Tree.Group{o, gk, cl}:
              {==}
            case Tree.Stmt{kind, sk, sb}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{nh, nt}:
              {==}

# a body with no case left: the report reads the chars so far
law strings.base:
  for +nn: U32
  for +ch: U32
  for +path: String
  for +ll: U32
  for +cc: U32
  {List.length(&2, F.Finding, Strings.report(Strings.Tally{nn, ch}, path, ll, cc))
    == Bool.pick(Nat, U32.is_gt(ch, 64), 1n, 0n) : Nat}

def strings.base(nn, ch, path, ll, cc):
  chars.one(U32.is_gt(ch, 64), F.Finding{path, ll, cc, 5, "strings",
    "A match over " ++ U32.show(nn) ++ " string literals totals " ++ U32.show(ch)
    ++ " characters, over the 64-character limit, and blows up compile time and memory;"
    ++ " map the string to a sum type once."})

# a case statement onto a body the law holds for, at the rule's count
law strings.step:
  for +rest: Tree.Node
  for +nn: U32
  for +ch: U32
  for +kids: Tree.Node
  for +path: String
  for +ll: U32
  for +cc: U32
  for ih: {List.length(&2, F.Finding, Strings.report(Strings.tally(rest,
      (nn + Strings.one(Strings.literal(T.pattern(kids))) : U32),
      (ch + Strings.size(Strings.literal(T.pattern(kids))) : U32)), path, ll, cc))
    == Bool.pick(Nat, U32.is_gt(Laws.strings.total(rest, (ch + Strings.size(Strings.literal(T.pattern(kids))) : U32)),
      64), 1n, 0n) : Nat}
  {List.length(&2, F.Finding, Strings.report(Strings.tally(rest,
      (nn + Strings.one(Strings.literal(T.pattern(kids))) : U32),
      (ch + Strings.size(Strings.literal(T.pattern(kids))) : U32)), path, ll, cc))
    == Bool.pick(Nat, U32.is_gt(Laws.strings.total(rest, (ch + Laws.strings.size(kids) : U32)), 64), 1n, 0n) : Nat}

def strings.step(rest, nn, ch, kids, path, ll, cc, ih):
  Equal.trans(Nat,
    List.length(&2, F.Finding, Strings.report(Strings.tally(rest,
      (nn + Strings.one(Strings.literal(T.pattern(kids))) : U32),
      (ch + Strings.size(Strings.literal(T.pattern(kids))) : U32)), path, ll, cc)),
    Bool.pick(Nat, U32.is_gt(Laws.strings.total(rest, (ch + Strings.size(Strings.literal(T.pattern(kids))) : U32)),
      64), 1n, 0n),
    Bool.pick(Nat, U32.is_gt(Laws.strings.total(rest, (ch + Laws.strings.size(kids) : U32)), 64), 1n, 0n),
    ih,
    Equal.cong(U32, Nat, z => Bool.pick(Nat, U32.is_gt(Laws.strings.total(rest, (ch + z : U32)), 64), 1n, 0n),
      Strings.size(Strings.literal(T.pattern(kids))), Laws.strings.size(kids), strings.lit(kids)))

# strings' tally reports when the chars the law totals are over 64
law strings.tally:
  for body: Tree.Node
  for +nn: U32
  for +ch: U32
  for +path: String
  for +ll: U32
  for +cc: U32
  {List.length(&2, F.Finding, Strings.report(Strings.tally(body, nn, ch), path, ll, cc))
    == Bool.pick(Nat, U32.is_gt(Laws.strings.total(body, ch), 64), 1n, 0n) : Nat}

def strings.tally(body, nn, ch, path, ll, cc):
  match body:
    case Tree.Leaf{tok}:
      strings.base(nn, ch, path, ll, cc)
    case Tree.Group{o, gk, cl}:
      strings.base(nn, ch, path, ll, cc)
    case Tree.Stmt{kind, sk, sb}:
      strings.base(nn, ch, path, ll, cc)
    case Tree.NNil{}:
      strings.base(nn, ch, path, ll, cc)
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          strings.tally(rest, nn, ch, path, ll, cc)
        case Tree.Group{o, gk, cl}:
          strings.tally(rest, nn, ch, path, ll, cc)
        case Tree.Stmt{kind, +kids, b}:
          match kind:
            case Tree.SDef{}:
              strings.tally(rest, nn, ch, path, ll, cc)
            case Tree.SType{}:
              strings.tally(rest, nn, ch, path, ll, cc)
            case Tree.SLaw{}:
              strings.tally(rest, nn, ch, path, ll, cc)
            case Tree.SImport{}:
              strings.tally(rest, nn, ch, path, ll, cc)
            case Tree.SCase{}:
              strings.step(rest, nn, ch, kids, path, ll, cc,
                strings.tally(rest, (nn + Strings.one(Strings.literal(T.pattern(kids))) : U32),
                  (ch + Strings.size(Strings.literal(T.pattern(kids))) : U32), path, ll, cc))
            case Tree.SFor{}:
              strings.tally(rest, nn, ch, path, ll, cc)
            case Tree.SLet{}:
              strings.tally(rest, nn, ch, path, ll, cc)
            case Tree.STerm{}:
              strings.tally(rest, nn, ch, path, ll, cc)
        case Tree.NNil{}:
          strings.tally(rest, nn, ch, path, ll, cc)
        case Tree.NCons{nh, nt}:
          strings.tally(rest, nn, ch, path, ll, cc)

# a statement's own finding: one when it is a match whose closed string arms
# total over 64 chars
law strings.stmt:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Strings.on_stmt(kids, body, path))
    == Bool.pick(Nat, Bool.and(Laws.chars.is_match(kids), U32.is_gt(Laws.strings.total(body, 0), 64)), 1n, 0n) : Nat}

def strings.stmt(kids, body, path):
  Equal.trans(Nat,
    List.length(&2, F.Finding, Strings.on_stmt(kids, body, path)),
    Bool.pick(Nat, Bool.and(T.keyword(kids, "match"), U32.is_gt(Laws.strings.total(body, 0), 64)), 1n, 0n),
    Bool.pick(Nat, Bool.and(Laws.chars.is_match(kids), U32.is_gt(Laws.strings.total(body, 0), 64)), 1n, 0n),
    chars.gate(T.keyword(kids, "match"),
      Strings.report(Strings.tally(body, 0, 0), path, Tree.line(kids), Tree.col(kids)),
      U32.is_gt(Laws.strings.total(body, 0), 64),
      strings.tally(body, 0, 0, path, Tree.line(kids), Tree.col(kids))),
    Equal.cong(Bool, Nat, z => Bool.pick(Nat, Bool.and(z, U32.is_gt(Laws.strings.total(body, 0), 64)), 1n, 0n),
      T.keyword(kids, "match"), Laws.chars.is_match(kids), chars.key(kids)))

# strings' walk counts the matches the law counts
law strings.walk:
  for nn: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Strings.walk(nn, path)) == Laws.strings.count(nn) : Nat}

def strings.walk(nn, path):
  match nn:
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{o, gk, cl}:
      {==}
    case Tree.Stmt{kind, sk, sb}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          strings.walk(rest, path)
        case Tree.Group{o, gk, cl}:
          strings.walk(rest, path)
        case Tree.Stmt{kind, +kids, +body}:
          chars.sum(Strings.on_stmt(kids, body, path), Strings.walk(body, path), Strings.walk(rest, path),
            Bool.pick(Nat, Bool.and(Laws.chars.is_match(kids), U32.is_gt(Laws.strings.total(body, 0), 64)), 1n, 0n),
            Laws.strings.count(body), Laws.strings.count(rest),
            strings.stmt(kids, body, path), strings.walk(body, path), strings.walk(rest, path))
        case Tree.NNil{}:
          strings.walk(rest, path)
        case Tree.NCons{nh, nt}:
          strings.walk(rest, path)

def Laws.strings_counts(path, _text, _toks, tree, _bound, _items):
  strings.walk(tree, path)
