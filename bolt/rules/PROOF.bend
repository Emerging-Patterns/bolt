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
import ./correctness/arms.bend as Arms
import ./correctness/twice.bend as Twice
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

# The match rules (BOLT-RULE-C005, BOLT-RULE-C007). A rule reads a case
# pattern through nested patterns, so each proof below takes the tree apart one
# constructor at a time, every constructor named, until the rule's match and
# the law's both reduce.

# a list with nothing appended is as long as before
law arms.nil:
  for xs: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.append(&2, F.Finding, xs, Nil{})) == List.length(&2, F.Finding, xs) : Nat}

def arms.nil(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, List.append(&2, F.Finding, t, Nil{})), List.length(&2,
        F.Finding, t), arms.nil(t))

# three lists joined are as long as the three together
law arms.cat:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for +c: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])) == Nat.add(List.length(&2, F.Finding, a),
      Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c))) : Nat}

def arms.cat(a, b, c):
  Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, a, List.append(&2, F.Finding, b,
    List.append(&2, F.Finding, c, Nil{})))), Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding,
    List.append(&2, F.Finding, b, List.append(&2, F.Finding, c, Nil{})))),
    Nat.add(List.length(&2, F.Finding, a), Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c))),
    esc.app(a, List.append(&2, F.Finding, b, List.append(&2, F.Finding, c, Nil{}))),
    Equal.cong(Nat, Nat, n => Nat.add(List.length(&2, F.Finding, a), n), List.length(&2, F.Finding, List.append(&2,
      F.Finding, b, List.append(&2, F.Finding, c, Nil{}))), Nat.add(List.length(&2, F.Finding, b), List.length(&2,
      F.Finding, c)),
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, b, List.append(&2, F.Finding, c, Nil{}))),
        Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, List.append(&2, F.Finding, c, Nil{}))),
        Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c)),
        esc.app(b, List.append(&2, F.Finding, c, Nil{})),
        Equal.cong(Nat, Nat, n => Nat.add(List.length(&2, F.Finding, b), n), List.length(&2, F.Finding, List.append(&2,
          F.Finding, c, Nil{})), List.length(&2, F.Finding, c), arms.nil(c)))))

# an early exit on the negation counts as a pick on the condition
law arms.flip:
  for s: Bool
  for -x: Nat
  {Bool.pick(Nat, Bool.not(s), 0n, x) == Bool.pick(Nat, s, x, 0n) : Nat}

def arms.flip(s, _x):
  match s:
    case True{}:
      {==}
    case False{}:
      {==}

# equal summands give equal sums, the second of three
law arms.add3:
  for -a: Nat
  for -b: Nat
  for -c: Nat
  for -d: Nat
  for -e: Nat
  for -f: Nat
  for e1: {a == b : Nat}
  for e2: {c == d : Nat}
  for e3: {e == f : Nat}
  {Nat.add(a, Nat.add(c, e)) == Nat.add(b, Nat.add(d, f)) : Nat}

def arms.add3(a, b, c, d, e, f, e1, e2, e3):
  esc.add(a, b, Nat.add(c, e), Nat.add(d, f), e1, esc.add(c, d, e, f, e2, e3))

# the k an arm matches every Nat from, if any
def arms.up(aa: Arms.Arm) -> Maybe<&2, U32>:
  match aa:
    case Arms.APlus{k, t, l, c, n}:
      Some{k}
    case other:
      None{}

# the least Nat an arm matches, if any
def arms.lo(aa: Arms.Arm) -> Maybe<&2, U32>:
  match aa:
    case Arms.APlus{k, t, l, c, n}:
      Some{k}
    case Arms.ALit{k, l, c, n}:
      Some{k}
    case Arms.AOther{}:
      None{}

# the k of the widest arm so far, if any
def arms.floor(ww: Maybe<&2, Arms.Wide>) -> Maybe<&2, U32>:
  match ww:
    case None{}:
      None{}
    case Some{Arms.Wide{k, text}}:
      Some{k}

# a picked from-k-up arm, read from above
law arms.pick_up:
  for b: Bool
  for +k: U32
  for t: String
  for l: U32
  for c: U32
  for n: U32
  {arms.up(Bool.pick(Arms.Arm, b, Arms.APlus{k, t, l, c, n}, Arms.AOther{})) == Bool.pick(Maybe<&2, U32>, b, Some{k},
      None{}) : Maybe<&2, U32>}

def arms.pick_up(b, _k, _t, _l, _c, _n):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a picked from-k-up arm, read from below, when `or`ed with no `:`
law arms.pick_lo:
  for b: Bool
  for +k: U32
  for t: String
  for l: U32
  for c: U32
  for n: U32
  {arms.lo(Bool.pick(Arms.Arm, b, Arms.APlus{k, t, l, c, n}, Arms.AOther{})) == Bool.pick(Maybe<&2, U32>, Bool.or(b,
      False{}), Some{k}, None{}) : Maybe<&2, U32>}

def arms.pick_lo(b, _k, _t, _l, _c, _n):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a picked from-k-up arm, read from below
law arms.pick_lo1:
  for b: Bool
  for +k: U32
  for t: String
  for l: U32
  for c: U32
  for n: U32
  {arms.lo(Bool.pick(Arms.Arm, b, Arms.APlus{k, t, l, c, n}, Arms.AOther{})) == Bool.pick(Maybe<&2, U32>, b, Some{k},
      None{}) : Maybe<&2, U32>}

def arms.pick_lo1(b, _k, _t, _l, _c, _n):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# what follows a Nat literal, read by the rule and by the law, from above
law arms.shape_up:
  for rest: Tree.Node
  for +k: U32
  for +tt: String
  for +line: U32
  for +col: U32
  {arms.up(Arms.lit.shape(rest, k, tt, line, col)) == Bool.pick(Maybe<&2, U32>, Laws.arms.plus(rest), Some{k},
      None{}) : Maybe<&2, U32>}

def arms.shape_up(rest, k, tt, line, col):
  match rest:
    case Tree.Leaf{Lex.Tok{+k1, +x2, +l3, +c4}}:
      {==}
    case Tree.Group{+op5, +ks6, +cl7}:
      {==}
    case Tree.Stmt{+sk8, +sks9, +sb10}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h11, +t12}:
      match h11:
        case Tree.Leaf{Lex.Tok{+k13, +x14, +l15, +c16}}:
          match k13:
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
              match t12:
                case Tree.Leaf{Lex.Tok{+k17, +x18, +l19, +c20}}:
                  {==}
                case Tree.Group{+op21, +ks22, +cl23}:
                  {==}
                case Tree.Stmt{+sk24, +sks25, +sb26}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h27, +t28}:
                  match h27:
                    case Tree.Leaf{Lex.Tok{+k29, +x30, +l31, +c32}}:
                      match t28:
                        case Tree.Leaf{Lex.Tok{+k33, +x34, +l35, +c36}}:
                          {==}
                        case Tree.Group{+op37, +ks38, +cl39}:
                          {==}
                        case Tree.Stmt{+sk40, +sks41, +sb42}:
                          {==}
                        case Tree.NNil{}:
                          {==}
                        case Tree.NCons{+h43, +t44}:
                          match h43:
                            case Tree.Leaf{Lex.Tok{+k45, +x46, +l47, +c48}}:
                              match k45:
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
                                  arms.pick_up(String.eq(x14, "+"), k, tt ++ "+" ++ x30, line, col, T.width(tt))
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
                            case Tree.Group{+op49, +ks50, +cl51}:
                              {==}
                            case Tree.Stmt{+sk52, +sks53, +sb54}:
                              {==}
                            case Tree.NNil{}:
                              {==}
                            case Tree.NCons{+h55, +t56}:
                              {==}
                    case Tree.Group{+op57, +ks58, +cl59}:
                      {==}
                    case Tree.Stmt{+sk60, +sks61, +sb62}:
                      {==}
                    case Tree.NNil{}:
                      {==}
                    case Tree.NCons{+h63, +t64}:
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
        case Tree.Group{+op65, +ks66, +cl67}:
          {==}
        case Tree.Stmt{+sk68, +sks69, +sb70}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h71, +t72}:
          {==}

# what follows a Nat literal, read by the rule and by the law, from below
law arms.shape_lo:
  for rest: Tree.Node
  for +k: U32
  for +tt: String
  for +line: U32
  for +col: U32
  {arms.lo(Arms.lit.shape(rest, k, tt, line, col)) == Bool.pick(Maybe<&2, U32>, Bool.or(Laws.arms.plus(rest),
      Laws.arms.exact(rest)), Some{k}, None{}) : Maybe<&2, U32>}

def arms.shape_lo(rest, k, tt, line, col):
  match rest:
    case Tree.Leaf{Lex.Tok{+k73, +x74, +l75, +c76}}:
      {==}
    case Tree.Group{+op77, +ks78, +cl79}:
      {==}
    case Tree.Stmt{+sk80, +sks81, +sb82}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h83, +t84}:
      match h83:
        case Tree.Leaf{Lex.Tok{+k85, +x86, +l87, +c88}}:
          match k85:
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
              match t84:
                case Tree.Leaf{Lex.Tok{+k89, +x90, +l91, +c92}}:
                  {==}
                case Tree.Group{+op93, +ks94, +cl95}:
                  {==}
                case Tree.Stmt{+sk96, +sks97, +sb98}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h99, +t100}:
                  match h99:
                    case Tree.Leaf{Lex.Tok{+k101, +x102, +l103, +c104}}:
                      match t100:
                        case Tree.Leaf{Lex.Tok{+k105, +x106, +l107, +c108}}:
                          {==}
                        case Tree.Group{+op109, +ks110, +cl111}:
                          {==}
                        case Tree.Stmt{+sk112, +sks113, +sb114}:
                          {==}
                        case Tree.NNil{}:
                          {==}
                        case Tree.NCons{+h115, +t116}:
                          match h115:
                            case Tree.Leaf{Lex.Tok{+k117, +x118, +l119, +c120}}:
                              match k117:
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
                                  arms.pick_lo(String.eq(x86, "+"), k, tt ++ "+" ++ x102, line, col, T.width(tt))
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
                            case Tree.Group{+op121, +ks122, +cl123}:
                              {==}
                            case Tree.Stmt{+sk124, +sks125, +sb126}:
                              {==}
                            case Tree.NNil{}:
                              {==}
                            case Tree.NCons{+h127, +t128}:
                              {==}
                    case Tree.Group{+op129, +ks130, +cl131}:
                      {==}
                    case Tree.Stmt{+sk132, +sks133, +sb134}:
                      {==}
                    case Tree.NNil{}:
                      {==}
                    case Tree.NCons{+h135, +t136}:
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
        case Tree.Group{+op137, +ks138, +cl139}:
          {==}
        case Tree.Stmt{+sk140, +sks141, +sb142}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h143, +t144}:
          {==}

# a Nat literal's arm, once its value is read, from above
law arms.of_up:
  for mm: Maybe<&2, U32>
  for +tt: String
  for +rest: Tree.Node
  for +line: U32
  for +col: U32
  {arms.up(Arms.lit.of(mm, tt, rest, line, col)) == Laws.arms.num(mm, Laws.arms.plus(rest)) : Maybe<&2, U32>}

def arms.of_up(mm, tt, rest, line, col):
  match mm:
    case None{}:
      {==}
    case Some{k}:
      arms.shape_up(rest, k, tt, line, col)

# a Nat literal's arm, once its value is read, from below
law arms.of_lo:
  for mm: Maybe<&2, U32>
  for +tt: String
  for +rest: Tree.Node
  for +line: U32
  for +col: U32
  {arms.lo(Arms.lit.of(mm, tt, rest, line, col)) == Laws.arms.num(mm, Bool.or(Laws.arms.plus(rest),
      Laws.arms.exact(rest))) : Maybe<&2, U32>}

def arms.of_lo(mm, tt, rest, line, col):
  match mm:
    case None{}:
      {==}
    case Some{k}:
      arms.shape_lo(rest, k, tt, line, col)

# a lone binder inside `Succ{..}`, to the rule and to the law
law arms.binder:
  for kk: Lex.TokKind
  {Arms.binder(kk) == Laws.arms.binder(kk) : Bool}

def arms.binder(kk):
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

# a case pattern's arm, to the rule and to the law, from above
law arms.up_is:
  for pat: Tree.Node
  {arms.up(Arms.arm(pat)) == Laws.arms.from(pat) : Maybe<&2, U32>}

def arms.up_is(pat):
  match pat:
    case Tree.Leaf{Lex.Tok{+k145, +x146, +l147, +c148}}:
      {==}
    case Tree.Group{+op149, +ks150, +cl151}:
      {==}
    case Tree.Stmt{+sk152, +sks153, +sb154}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h155, +t156}:
      match h155:
        case Tree.Leaf{Lex.Tok{+k157, +x158, +l159, +c160}}:
          match k157:
            case Lex.TName{}:
              {==}
            case Lex.TUpper{}:
              match t156:
                case Tree.Leaf{Lex.Tok{+k161, +x162, +l163, +c164}}:
                  {==}
                case Tree.Group{+op165, +ks166, +cl167}:
                  {==}
                case Tree.Stmt{+sk168, +sks169, +sb170}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h171, +t172}:
                  match h171:
                    case Tree.Leaf{Lex.Tok{+k173, +x174, +l175, +c176}}:
                      {==}
                    case Tree.Group{+op177, +ks178, +cl179}:
                      match ks178:
                        case Tree.Leaf{Lex.Tok{+k180, +x181, +l182, +c183}}:
                          {==}
                        case Tree.Group{+op184, +ks185, +cl186}:
                          {==}
                        case Tree.Stmt{+sk187, +sks188, +sb189}:
                          {==}
                        case Tree.NNil{}:
                          {==}
                        case Tree.NCons{+h190, +t191}:
                          match h190:
                            case Tree.Leaf{Lex.Tok{+k192, +x193, +l194, +c195}}:
                              match t191:
                                case Tree.Leaf{Lex.Tok{+k196, +x197, +l198, +c199}}:
                                  {==}
                                case Tree.Group{+op200, +ks201, +cl202}:
                                  {==}
                                case Tree.Stmt{+sk203, +sks204, +sb205}:
                                  {==}
                                case Tree.NNil{}:
                                  Equal.trans(Maybe<&2, U32>, arms.up(Bool.pick(Arms.Arm, Bool.and(String.eq(x158,
                                    "Succ"), Arms.binder(k192)), Arms.APlus{1, "Succ{" ++ x193 ++ "}", l159, c160, 4},
                                    Arms.AOther{})),
                                    arms.up(Bool.pick(Arms.Arm, Bool.and(String.eq(x158, "Succ"),
                                      Laws.arms.binder(k192)), Arms.APlus{1, "Succ{" ++ x193 ++ "}", l159, c160, 4},
                                      Arms.AOther{})),
                                    Bool.pick(Maybe<&2, U32>, Bool.and(String.eq(x158, "Succ"),
                                      Laws.arms.binder(k192)), Some{1}, None{}),
                                    Equal.cong(Bool, Maybe<&2, U32>, z => arms.up(Bool.pick(Arms.Arm,
                                      Bool.and(String.eq(x158, "Succ"), z), Arms.APlus{1, "Succ{" ++ x193 ++ "}", l159,
                                      c160, 4}, Arms.AOther{})),
                                      Arms.binder(k192), Laws.arms.binder(k192), arms.binder(k192)),
                                    arms.pick_up(Bool.and(String.eq(x158, "Succ"), Laws.arms.binder(k192)), 1,
                                      "Succ{" ++ x193 ++ "}", l159, c160, 4))
                                case Tree.NCons{+h206, +t207}:
                                  {==}
                            case Tree.Group{+op208, +ks209, +cl210}:
                              {==}
                            case Tree.Stmt{+sk211, +sks212, +sb213}:
                              {==}
                            case Tree.NNil{}:
                              {==}
                            case Tree.NCons{+h214, +t215}:
                              {==}
                    case Tree.Stmt{+sk216, +sks217, +sb218}:
                      {==}
                    case Tree.NNil{}:
                      {==}
                    case Tree.NCons{+h219, +t220}:
                      {==}
            case Lex.TDotted{}:
              {==}
            case Lex.TWild{}:
              {==}
            case Lex.TKey{}:
              {==}
            case Lex.TNum{}:
              arms.of_up(T.nat_value(x158), x158, t156, l159, c160)
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
        case Tree.Group{+op221, +ks222, +cl223}:
          {==}
        case Tree.Stmt{+sk224, +sks225, +sb226}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h227, +t228}:
          {==}

# a case pattern's arm, to the rule and to the law, from below
law arms.lo_is:
  for pat: Tree.Node
  {arms.lo(Arms.arm(pat)) == Laws.arms.least(pat) : Maybe<&2, U32>}

def arms.lo_is(pat):
  match pat:
    case Tree.Leaf{Lex.Tok{+k229, +x230, +l231, +c232}}:
      {==}
    case Tree.Group{+op233, +ks234, +cl235}:
      {==}
    case Tree.Stmt{+sk236, +sks237, +sb238}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h239, +t240}:
      match h239:
        case Tree.Leaf{Lex.Tok{+k241, +x242, +l243, +c244}}:
          match k241:
            case Lex.TName{}:
              {==}
            case Lex.TUpper{}:
              match t240:
                case Tree.Leaf{Lex.Tok{+k245, +x246, +l247, +c248}}:
                  {==}
                case Tree.Group{+op249, +ks250, +cl251}:
                  {==}
                case Tree.Stmt{+sk252, +sks253, +sb254}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h255, +t256}:
                  match h255:
                    case Tree.Leaf{Lex.Tok{+k257, +x258, +l259, +c260}}:
                      {==}
                    case Tree.Group{+op261, +ks262, +cl263}:
                      match ks262:
                        case Tree.Leaf{Lex.Tok{+k264, +x265, +l266, +c267}}:
                          {==}
                        case Tree.Group{+op268, +ks269, +cl270}:
                          {==}
                        case Tree.Stmt{+sk271, +sks272, +sb273}:
                          {==}
                        case Tree.NNil{}:
                          {==}
                        case Tree.NCons{+h274, +t275}:
                          match h274:
                            case Tree.Leaf{Lex.Tok{+k276, +x277, +l278, +c279}}:
                              match t275:
                                case Tree.Leaf{Lex.Tok{+k280, +x281, +l282, +c283}}:
                                  {==}
                                case Tree.Group{+op284, +ks285, +cl286}:
                                  {==}
                                case Tree.Stmt{+sk287, +sks288, +sb289}:
                                  {==}
                                case Tree.NNil{}:
                                  Equal.trans(Maybe<&2, U32>, arms.lo(Bool.pick(Arms.Arm, Bool.and(String.eq(x242,
                                    "Succ"), Arms.binder(k276)), Arms.APlus{1, "Succ{" ++ x277 ++ "}", l243, c244, 4},
                                    Arms.AOther{})),
                                    arms.lo(Bool.pick(Arms.Arm, Bool.and(String.eq(x242, "Succ"),
                                      Laws.arms.binder(k276)), Arms.APlus{1, "Succ{" ++ x277 ++ "}", l243, c244, 4},
                                      Arms.AOther{})),
                                    Bool.pick(Maybe<&2, U32>, Bool.and(String.eq(x242, "Succ"),
                                      Laws.arms.binder(k276)), Some{1}, None{}),
                                    Equal.cong(Bool, Maybe<&2, U32>, z => arms.lo(Bool.pick(Arms.Arm,
                                      Bool.and(String.eq(x242, "Succ"), z), Arms.APlus{1, "Succ{" ++ x277 ++ "}", l243,
                                      c244, 4}, Arms.AOther{})),
                                      Arms.binder(k276), Laws.arms.binder(k276), arms.binder(k276)),
                                    arms.pick_lo1(Bool.and(String.eq(x242, "Succ"), Laws.arms.binder(k276)), 1,
                                      "Succ{" ++ x277 ++ "}", l243, c244, 4))
                                case Tree.NCons{+h290, +t291}:
                                  {==}
                            case Tree.Group{+op292, +ks293, +cl294}:
                              {==}
                            case Tree.Stmt{+sk295, +sks296, +sb297}:
                              {==}
                            case Tree.NNil{}:
                              {==}
                            case Tree.NCons{+h298, +t299}:
                              {==}
                    case Tree.Stmt{+sk300, +sks301, +sb302}:
                      {==}
                    case Tree.NNil{}:
                      {==}
                    case Tree.NCons{+h303, +t304}:
                      {==}
            case Lex.TDotted{}:
              {==}
            case Lex.TWild{}:
              {==}
            case Lex.TKey{}:
              {==}
            case Lex.TNum{}:
              arms.of_lo(T.nat_value(x242), x242, t240, l243, c244)
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
        case Tree.Group{+op305, +ks306, +cl307}:
          {==}
        case Tree.Stmt{+sk308, +sks309, +sb310}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h311, +t312}:
          {==}

# one scrutinee, to the rule and to the law
law arms.single:
  for kids: Tree.Node
  {Arms.single(kids) == Laws.arms.single(kids) : Bool}

def arms.single(kids):
  match kids:
    case Tree.Leaf{Lex.Tok{+k313, +x314, +l315, +c316}}:
      {==}
    case Tree.Group{+op317, +ks318, +cl319}:
      {==}
    case Tree.Stmt{+sk320, +sks321, +sb322}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h323, +t324}:
      match h323:
        case Tree.Leaf{Lex.Tok{+k325, +x326, +l327, +c328}}:
          match k325:
            case Lex.TName{}:
              {==}
            case Lex.TUpper{}:
              {==}
            case Lex.TDotted{}:
              {==}
            case Lex.TWild{}:
              {==}
            case Lex.TKey{}:
              match t324:
                case Tree.Leaf{Lex.Tok{+k329, +x330, +l331, +c332}}:
                  {==}
                case Tree.Group{+op333, +ks334, +cl335}:
                  {==}
                case Tree.Stmt{+sk336, +sks337, +sb338}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h339, +t340}:
                  match t340:
                    case Tree.Leaf{Lex.Tok{+k341, +x342, +l343, +c344}}:
                      {==}
                    case Tree.Group{+op345, +ks346, +cl347}:
                      {==}
                    case Tree.Stmt{+sk348, +sks349, +sb350}:
                      {==}
                    case Tree.NNil{}:
                      {==}
                    case Tree.NCons{+h351, +t352}:
                      match h351:
                        case Tree.Leaf{Lex.Tok{+k353, +x354, +l355, +c356}}:
                          match k353:
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
                              match t352:
                                case Tree.Leaf{Lex.Tok{+k357, +x358, +l359, +c360}}:
                                  {==}
                                case Tree.Group{+op361, +ks362, +cl363}:
                                  {==}
                                case Tree.Stmt{+sk364, +sks365, +sb366}:
                                  {==}
                                case Tree.NNil{}:
                                  {==}
                                case Tree.NCons{+h367, +t368}:
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
                        case Tree.Group{+op369, +ks370, +cl371}:
                          {==}
                        case Tree.Stmt{+sk372, +sks373, +sb374}:
                          {==}
                        case Tree.NNil{}:
                          {==}
                        case Tree.NCons{+h375, +t376}:
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
        case Tree.Group{+op377, +ks378, +cl379}:
          {==}
        case Tree.Stmt{+sk380, +sks381, +sb382}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h383, +t384}:
          {==}

# an arm against the widest one above: a finding exactly when the law's hit
law arms.verdict:
  for ww: Maybe<&2, Arms.Wide>
  for aa: Arms.Arm
  for +path: String
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Arms.verdict(ww, aa, path, more)) == Bool.pick(Nat, Laws.arms.hit(arms.floor(ww),
      arms.lo(aa)), 1n+m, m) : Nat}

def arms.verdict(ww, aa, path, more, m, ih):
  match ww:
    case None{}:
      ih
    case Some{Arms.Wide{+k, +text}}:
      match aa:
        case Arms.APlus{+j, t, +l, +c, +n}:
          nat.pick(U32.is_ge(j, k), F.Finding{path, l, c, n, "arms",
            "Unreachable: case " ++ text ++ " above already matches every " ++ U32.show(j)
              ++ "n+..; put the narrow arms first."}, more, m, ih)
        case Arms.ALit{+j, +l, +c, +n}:
          nat.pick(U32.is_ge(j, k), F.Finding{path, l, c, n, "arms",
            "Unreachable: case " ++ text ++ " above already matches " ++ U32.show(j)
              ++ "n; put the narrow arms first."}, more, m, ih)
        case Arms.AOther{}:
          ih

# a picked widest arm, read by its k
law arms.pick_floor:
  for b: Bool
  for +j: U32
  for t2: String
  for +k: U32
  for text: String
  {arms.floor(Bool.pick(Maybe<&2, Arms.Wide>, b, Some{Arms.Wide{j, t2}}, Some{Arms.Wide{k, text}}))
    == Bool.pick(Maybe<&2, U32>, b, Some{j}, Some{k}) : Maybe<&2, U32>}

def arms.pick_floor(b, _j, _t2, _k, _text):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the widest arm after one more, read by its k, is the law's lower bound
law arms.widen:
  for ww: Maybe<&2, Arms.Wide>
  for aa: Arms.Arm
  {arms.floor(Arms.widen(ww, aa)) == Laws.arms.lower(arms.floor(ww), arms.up(aa)) : Maybe<&2, U32>}

def arms.widen(ww, aa):
  match ww:
    case None{}:
      match aa:
        case Arms.APlus{j, t2, l, c, n}:
          {==}
        case Arms.ALit{j, l, c, n}:
          {==}
        case Arms.AOther{}:
          {==}
    case Some{Arms.Wide{+k, +text}}:
      match aa:
        case Arms.APlus{+j, +t2, l, c, n}:
          arms.pick_floor(U32.is_lt(j, k), j, t2, k, text)
        case Arms.ALit{j, l, c, n}:
          {==}
        case Arms.AOther{}:
          {==}

# one case arm onto the rest of a match the law holds for
law arms.case:
  for +pat: Tree.Node
  for +rest: Tree.Node
  for +wide: Maybe<&2, Arms.Wide>
  for +path: String
  for ih: {List.length(&2, F.Finding, Arms.arms(rest, Arms.widen(wide, Arms.arm(pat)),
    path)) == Laws.arms.covered(rest, arms.floor(Arms.widen(wide, Arms.arm(pat)))) : Nat}
  {List.length(&2, F.Finding, Arms.verdict(wide, Arms.arm(pat), path, Arms.arms(rest, Arms.widen(wide, Arms.arm(pat)),
      path))) == Bool.pick(Nat, Laws.arms.hit(arms.floor(wide), Laws.arms.least(pat)), 1n+Laws.arms.covered(rest,
      Laws.arms.lower(arms.floor(wide), Laws.arms.from(pat))), Laws.arms.covered(rest,
      Laws.arms.lower(arms.floor(wide), Laws.arms.from(pat)))) : Nat}

def arms.case(pat, rest, wide, path, ih):
  Equal.trans(Nat, List.length(&2, F.Finding, Arms.verdict(wide, Arms.arm(pat), path, Arms.arms(rest, Arms.widen(wide,
    Arms.arm(pat)), path))),
    Bool.pick(Nat, Laws.arms.hit(arms.floor(wide), arms.lo(Arms.arm(pat))), 1n+Laws.arms.covered(rest,
      arms.floor(Arms.widen(wide, Arms.arm(pat)))), Laws.arms.covered(rest, arms.floor(Arms.widen(wide,
      Arms.arm(pat))))),
    Bool.pick(Nat, Laws.arms.hit(arms.floor(wide), Laws.arms.least(pat)), 1n+Laws.arms.covered(rest,
      Laws.arms.lower(arms.floor(wide), Laws.arms.from(pat))), Laws.arms.covered(rest,
      Laws.arms.lower(arms.floor(wide), Laws.arms.from(pat)))),
    arms.verdict(wide, Arms.arm(pat), path, Arms.arms(rest, Arms.widen(wide, Arms.arm(pat)), path),
      Laws.arms.covered(rest, arms.floor(Arms.widen(wide, Arms.arm(pat)))), ih),
    Equal.trans(Nat, Bool.pick(Nat, Laws.arms.hit(arms.floor(wide), arms.lo(Arms.arm(pat))), 1n+Laws.arms.covered(rest,
      arms.floor(Arms.widen(wide, Arms.arm(pat)))), Laws.arms.covered(rest, arms.floor(Arms.widen(wide,
      Arms.arm(pat))))),
      Bool.pick(Nat, Laws.arms.hit(arms.floor(wide), Laws.arms.least(pat)), 1n+Laws.arms.covered(rest,
        arms.floor(Arms.widen(wide, Arms.arm(pat)))), Laws.arms.covered(rest, arms.floor(Arms.widen(wide,
        Arms.arm(pat))))),
      Bool.pick(Nat, Laws.arms.hit(arms.floor(wide), Laws.arms.least(pat)), 1n+Laws.arms.covered(rest,
        Laws.arms.lower(arms.floor(wide), Laws.arms.from(pat))), Laws.arms.covered(rest,
        Laws.arms.lower(arms.floor(wide), Laws.arms.from(pat)))),
      Equal.cong(Maybe<&2, U32>, Nat, z => Bool.pick(Nat, Laws.arms.hit(arms.floor(wide), z),
        1n+Laws.arms.covered(rest, arms.floor(Arms.widen(wide, Arms.arm(pat)))), Laws.arms.covered(rest,
        arms.floor(Arms.widen(wide, Arms.arm(pat))))),
        arms.lo(Arms.arm(pat)), Laws.arms.least(pat), arms.lo_is(pat)),
      Equal.cong(Maybe<&2, U32>, Nat,
        z => Bool.pick(Nat, Laws.arms.hit(arms.floor(wide), Laws.arms.least(pat)), 1n+Laws.arms.covered(rest, z),
          Laws.arms.covered(rest, z)),
        arms.floor(Arms.widen(wide, Arms.arm(pat))), Laws.arms.lower(arms.floor(wide), Laws.arms.from(pat)),
        Equal.trans(Maybe<&2, U32>, arms.floor(Arms.widen(wide, Arms.arm(pat))), Laws.arms.lower(arms.floor(wide),
          arms.up(Arms.arm(pat))),
          Laws.arms.lower(arms.floor(wide), Laws.arms.from(pat)),
          arms.widen(wide, Arms.arm(pat)),
          Equal.cong(Maybe<&2, U32>, Maybe<&2, U32>, z => Laws.arms.lower(arms.floor(wide), z), arms.up(Arms.arm(pat)),
            Laws.arms.from(pat),
            arms.up_is(pat))))))

# a match's arms, the widest above them read by its k
law arms.go:
  for body: Tree.Node
  for +wide: Maybe<&2, Arms.Wide>
  for +path: String
  {List.length(&2, F.Finding, Arms.arms(body, wide, path)) == Laws.arms.covered(body, arms.floor(wide)) : Nat}

def arms.go(body, wide, path):
  match body:
    case Tree.Leaf{Lex.Tok{+k385, +x386, +l387, +c388}}:
      {==}
    case Tree.Group{+op389, +ks390, +cl391}:
      {==}
    case Tree.Stmt{+sk392, +sks393, +sb394}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h395, +t396}:
      match h395:
        case Tree.Leaf{Lex.Tok{+k397, +x398, +l399, +c400}}:
          arms.go(t396, wide, path)
        case Tree.Group{+op401, +ks402, +cl403}:
          arms.go(t396, wide, path)
        case Tree.Stmt{+sk404, +sks405, +sb406}:
          match sk404:
            case Tree.SDef{}:
              arms.go(t396, wide, path)
            case Tree.SType{}:
              arms.go(t396, wide, path)
            case Tree.SLaw{}:
              arms.go(t396, wide, path)
            case Tree.SImport{}:
              arms.go(t396, wide, path)
            case Tree.SCase{}:
              arms.case(T.pattern(sks405), t396, wide, path,
                arms.go(t396, Arms.widen(wide, Arms.arm(T.pattern(sks405))), path))
            case Tree.SFor{}:
              arms.go(t396, wide, path)
            case Tree.SLet{}:
              arms.go(t396, wide, path)
            case Tree.STerm{}:
              arms.go(t396, wide, path)
        case Tree.NNil{}:
          arms.go(t396, wide, path)
        case Tree.NCons{+h407, +t408}:
          arms.go(t396, wide, path)

# one statement onto the rest, its body and the rest both holding the law
law arms.stmt:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +path: String
  for ihb: {List.length(&2, F.Finding, Arms.walk(body, path)) == Laws.arms_count(body) : Nat}
  for ihr: {List.length(&2, F.Finding, Arms.walk(rest, path)) == Laws.arms_count(rest) : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [Lazy.stop(List<&2, F.Finding>, Bool.not(Arms.single(kids)),
      [], _u => Arms.arms(body, None{}, path)), Arms.walk(body, path), Arms.walk(rest, path)]))
    == Nat.add(Bool.pick(Nat, Laws.arms.single(kids), Laws.arms.covered(body, None{}), 0n),
      Nat.add(Laws.arms_count(body), Laws.arms_count(rest))) : Nat}

def arms.stmt(kids, body, rest, path, ihb, ihr):
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [Lazy.stop(List<&2, F.Finding>,
    Bool.not(Arms.single(kids)), [], _u => Arms.arms(body, None{}, path)), Arms.walk(body, path), Arms.walk(rest,
    path)])),
    Nat.add(List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(Arms.single(kids)), [],
      _u => Arms.arms(body, None{}, path))), Nat.add(List.length(&2, F.Finding, Arms.walk(body, path)), List.length(&2,
      F.Finding, Arms.walk(rest, path)))),
    Nat.add(Bool.pick(Nat, Laws.arms.single(kids), Laws.arms.covered(body, None{}), 0n), Nat.add(Laws.arms_count(body),
      Laws.arms_count(rest))),
    arms.cat(Lazy.stop(List<&2, F.Finding>, Bool.not(Arms.single(kids)), [], _u => Arms.arms(body, None{}, path)),
      Arms.walk(body, path), Arms.walk(rest, path)),
    arms.add3(List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(Arms.single(kids)), [],
      _u => Arms.arms(body, None{}, path))), Bool.pick(Nat, Laws.arms.single(kids), Laws.arms.covered(body, None{}),
      0n), List.length(&2, F.Finding, Arms.walk(body, path)), Laws.arms_count(body), List.length(&2, F.Finding,
      Arms.walk(rest, path)), Laws.arms_count(rest),
      Equal.trans(Nat, List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(Arms.single(kids)), [],
        _u => Arms.arms(body, None{}, path))), Bool.pick(Nat, Bool.not(Arms.single(kids)), 0n, Laws.arms.covered(body,
        None{})), Bool.pick(Nat, Laws.arms.single(kids), Laws.arms.covered(body, None{}), 0n),
        param.stop(Bool.not(Arms.single(kids)), Arms.arms(body, None{}, path), Laws.arms.covered(body, None{}),
          arms.go(body, None{}, path)),
        Equal.trans(Nat, Bool.pick(Nat, Bool.not(Arms.single(kids)), 0n, Laws.arms.covered(body, None{})),
          Bool.pick(Nat, Arms.single(kids), Laws.arms.covered(body, None{}), 0n), Bool.pick(Nat,
            Laws.arms.single(kids), Laws.arms.covered(body, None{}), 0n),
          arms.flip(Arms.single(kids), Laws.arms.covered(body, None{})),
          Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, Laws.arms.covered(body, None{}), 0n), Arms.single(kids),
            Laws.arms.single(kids),
            arms.single(kids)))),
      ihb, ihr))

# every statement at any depth, each single-scrutinee match's arms read
law arms.walk:
  for nn: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Arms.walk(nn, path)) == Laws.arms_count(nn) : Nat}

def arms.walk(nn, path):
  match nn:
    case Tree.Leaf{Lex.Tok{+k409, +x410, +l411, +c412}}:
      {==}
    case Tree.Group{+op413, +ks414, +cl415}:
      {==}
    case Tree.Stmt{+sk416, +sks417, +sb418}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h419, +t420}:
      match h419:
        case Tree.Leaf{Lex.Tok{+k421, +x422, +l423, +c424}}:
          arms.walk(t420, path)
        case Tree.Group{+op425, +ks426, +cl427}:
          arms.walk(t420, path)
        case Tree.Stmt{+sk428, +sks429, +sb430}:
          arms.stmt(sks429, sb430, t420, path, arms.walk(sb430, path), arms.walk(t420, path))
        case Tree.NNil{}:
          arms.walk(t420, path)
        case Tree.NCons{+h431, +t432}:
          arms.walk(t420, path)

def Laws.arms_counts(path, _text, _toks, tree, _bound, _items):
  arms.walk(tree, path)

# the text of a token, if any
def twice.text(mm: Maybe<&2, Lex.Tok>) -> Maybe<&2, String>:
  match mm:
    case None{}:
      None{}
    case Some{Lex.Tok{k, t, l, c}}:
      Some{t}

# a picked literal token, read by its text
law twice.pick_text:
  for b: Bool
  for kk: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  {twice.text(Bool.pick(Maybe<&2, Lex.Tok>, b, Some{Lex.Tok{kk, t, l, c}}, None{})) == Bool.pick(Maybe<&2, String>, b,
      Some{t}, None{}) : Maybe<&2, String>}

def twice.pick_text(b, _kk, _t, _l, _c):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a pattern opening `Con{..}`, its literal to the rule and to the law
law twice.head_con:
  for kk: Lex.TokKind
  for +tx: String
  for l: U32
  for c: U32
  for op: Lex.Tok
  for ks: Tree.Node
  for cl: Maybe<&2, Lex.Tok>
  for rest: Tree.Node
  {twice.text(Twice.head(Tree.NCons{Tree.Leaf{Lex.Tok{kk, tx, l, c}}, Tree.NCons{Tree.Group{op, ks, cl},
      rest}})) == Laws.twice.first(Tree.NCons{Tree.Leaf{Lex.Tok{kk, tx, l, c}}, Tree.NCons{Tree.Group{op, ks, cl},
      rest}}) : Maybe<&2, String>}

def twice.head_con(kk, tx, _l, _c, _op, ks, _cl, _rest):
  match kk:
    case Lex.TName{}:
      {==}
    case Lex.TUpper{}:
      match ks:
        case Tree.Leaf{Lex.Tok{+k433, +x434, +l435, +c436}}:
          {==}
        case Tree.Group{+op437, +ks438, +cl439}:
          {==}
        case Tree.Stmt{+sk440, +sks441, +sb442}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h443, +t444}:
          match h443:
            case Tree.Leaf{Lex.Tok{+k445, +x446, +l447, +c448}}:
              twice.pick_text(Bool.and(String.eq(tx, "Con"), T.is_lit(k445)), k445, x446, l447, c448)
            case Tree.Group{+op449, +ks450, +cl451}:
              {==}
            case Tree.Stmt{+sk452, +sks453, +sb454}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h455, +t456}:
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

# a pattern opening with a token, its literal to the rule and to the law
law twice.head2:
  for kk: Lex.TokKind
  for +tx: String
  for +l: U32
  for +c: U32
  for +t: Tree.Node
  {twice.text(Twice.head(Tree.NCons{Tree.Leaf{Lex.Tok{kk, tx, l, c}},
      t})) == Laws.twice.first(Tree.NCons{Tree.Leaf{Lex.Tok{kk, tx, l, c}}, t}) : Maybe<&2, String>}

def twice.head2(kk, tx, l, c, t):
  match kk:
    case Lex.TName{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k457, +x458, +l459, +c460}}:
          {==}
        case Tree.Group{+op461, +ks462, +cl463}:
          {==}
        case Tree.Stmt{+sk464, +sks465, +sb466}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h467, +t468}:
          match h467:
            case Tree.Leaf{Lex.Tok{+k469, +x470, +l471, +c472}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TName{}), String.eq(x470, "<>")), Lex.TName{}, tx, l, c)
            case Tree.Group{+op473, +ks474, +cl475}:
              twice.head_con(Lex.TName{}, tx, l, c, op473, ks474, cl475, t468)
            case Tree.Stmt{+sk476, +sks477, +sb478}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h479, +t480}:
              {==}
    case Lex.TUpper{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k481, +x482, +l483, +c484}}:
          {==}
        case Tree.Group{+op485, +ks486, +cl487}:
          {==}
        case Tree.Stmt{+sk488, +sks489, +sb490}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h491, +t492}:
          match h491:
            case Tree.Leaf{Lex.Tok{+k493, +x494, +l495, +c496}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TUpper{}), String.eq(x494, "<>")), Lex.TUpper{}, tx, l, c)
            case Tree.Group{+op497, +ks498, +cl499}:
              twice.head_con(Lex.TUpper{}, tx, l, c, op497, ks498, cl499, t492)
            case Tree.Stmt{+sk500, +sks501, +sb502}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h503, +t504}:
              {==}
    case Lex.TDotted{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k505, +x506, +l507, +c508}}:
          {==}
        case Tree.Group{+op509, +ks510, +cl511}:
          {==}
        case Tree.Stmt{+sk512, +sks513, +sb514}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h515, +t516}:
          match h515:
            case Tree.Leaf{Lex.Tok{+k517, +x518, +l519, +c520}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TDotted{}), String.eq(x518, "<>")), Lex.TDotted{}, tx, l, c)
            case Tree.Group{+op521, +ks522, +cl523}:
              twice.head_con(Lex.TDotted{}, tx, l, c, op521, ks522, cl523, t516)
            case Tree.Stmt{+sk524, +sks525, +sb526}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h527, +t528}:
              {==}
    case Lex.TWild{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k529, +x530, +l531, +c532}}:
          {==}
        case Tree.Group{+op533, +ks534, +cl535}:
          {==}
        case Tree.Stmt{+sk536, +sks537, +sb538}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h539, +t540}:
          match h539:
            case Tree.Leaf{Lex.Tok{+k541, +x542, +l543, +c544}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TWild{}), String.eq(x542, "<>")), Lex.TWild{}, tx, l, c)
            case Tree.Group{+op545, +ks546, +cl547}:
              twice.head_con(Lex.TWild{}, tx, l, c, op545, ks546, cl547, t540)
            case Tree.Stmt{+sk548, +sks549, +sb550}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h551, +t552}:
              {==}
    case Lex.TKey{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k553, +x554, +l555, +c556}}:
          {==}
        case Tree.Group{+op557, +ks558, +cl559}:
          {==}
        case Tree.Stmt{+sk560, +sks561, +sb562}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h563, +t564}:
          match h563:
            case Tree.Leaf{Lex.Tok{+k565, +x566, +l567, +c568}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TKey{}), String.eq(x566, "<>")), Lex.TKey{}, tx, l, c)
            case Tree.Group{+op569, +ks570, +cl571}:
              twice.head_con(Lex.TKey{}, tx, l, c, op569, ks570, cl571, t564)
            case Tree.Stmt{+sk572, +sks573, +sb574}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h575, +t576}:
              {==}
    case Lex.TNum{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k577, +x578, +l579, +c580}}:
          {==}
        case Tree.Group{+op581, +ks582, +cl583}:
          {==}
        case Tree.Stmt{+sk584, +sks585, +sb586}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h587, +t588}:
          match h587:
            case Tree.Leaf{Lex.Tok{+k589, +x590, +l591, +c592}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TNum{}), String.eq(x590, "<>")), Lex.TNum{}, tx, l, c)
            case Tree.Group{+op593, +ks594, +cl595}:
              twice.head_con(Lex.TNum{}, tx, l, c, op593, ks594, cl595, t588)
            case Tree.Stmt{+sk596, +sks597, +sb598}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h599, +t600}:
              {==}
    case Lex.TStr{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k601, +x602, +l603, +c604}}:
          {==}
        case Tree.Group{+op605, +ks606, +cl607}:
          {==}
        case Tree.Stmt{+sk608, +sks609, +sb610}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h611, +t612}:
          match h611:
            case Tree.Leaf{Lex.Tok{+k613, +x614, +l615, +c616}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TStr{}), String.eq(x614, "<>")), Lex.TStr{}, tx, l, c)
            case Tree.Group{+op617, +ks618, +cl619}:
              twice.head_con(Lex.TStr{}, tx, l, c, op617, ks618, cl619, t612)
            case Tree.Stmt{+sk620, +sks621, +sb622}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h623, +t624}:
              {==}
    case Lex.TChar{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k625, +x626, +l627, +c628}}:
          {==}
        case Tree.Group{+op629, +ks630, +cl631}:
          {==}
        case Tree.Stmt{+sk632, +sks633, +sb634}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h635, +t636}:
          match h635:
            case Tree.Leaf{Lex.Tok{+k637, +x638, +l639, +c640}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TChar{}), String.eq(x638, "<>")), Lex.TChar{}, tx, l, c)
            case Tree.Group{+op641, +ks642, +cl643}:
              twice.head_con(Lex.TChar{}, tx, l, c, op641, ks642, cl643, t636)
            case Tree.Stmt{+sk644, +sks645, +sb646}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h647, +t648}:
              {==}
    case Lex.TComment{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k649, +x650, +l651, +c652}}:
          {==}
        case Tree.Group{+op653, +ks654, +cl655}:
          {==}
        case Tree.Stmt{+sk656, +sks657, +sb658}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h659, +t660}:
          match h659:
            case Tree.Leaf{Lex.Tok{+k661, +x662, +l663, +c664}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TComment{}), String.eq(x662, "<>")), Lex.TComment{}, tx, l, c)
            case Tree.Group{+op665, +ks666, +cl667}:
              twice.head_con(Lex.TComment{}, tx, l, c, op665, ks666, cl667, t660)
            case Tree.Stmt{+sk668, +sks669, +sb670}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h671, +t672}:
              {==}
    case Lex.TSpace{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k673, +x674, +l675, +c676}}:
          {==}
        case Tree.Group{+op677, +ks678, +cl679}:
          {==}
        case Tree.Stmt{+sk680, +sks681, +sb682}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h683, +t684}:
          match h683:
            case Tree.Leaf{Lex.Tok{+k685, +x686, +l687, +c688}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TSpace{}), String.eq(x686, "<>")), Lex.TSpace{}, tx, l, c)
            case Tree.Group{+op689, +ks690, +cl691}:
              twice.head_con(Lex.TSpace{}, tx, l, c, op689, ks690, cl691, t684)
            case Tree.Stmt{+sk692, +sks693, +sb694}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h695, +t696}:
              {==}
    case Lex.TNewline{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k697, +x698, +l699, +c700}}:
          {==}
        case Tree.Group{+op701, +ks702, +cl703}:
          {==}
        case Tree.Stmt{+sk704, +sks705, +sb706}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h707, +t708}:
          match h707:
            case Tree.Leaf{Lex.Tok{+k709, +x710, +l711, +c712}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TNewline{}), String.eq(x710, "<>")), Lex.TNewline{}, tx, l, c)
            case Tree.Group{+op713, +ks714, +cl715}:
              twice.head_con(Lex.TNewline{}, tx, l, c, op713, ks714, cl715, t708)
            case Tree.Stmt{+sk716, +sks717, +sb718}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h719, +t720}:
              {==}
    case Lex.TOp{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k721, +x722, +l723, +c724}}:
          {==}
        case Tree.Group{+op725, +ks726, +cl727}:
          {==}
        case Tree.Stmt{+sk728, +sks729, +sb730}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h731, +t732}:
          match h731:
            case Tree.Leaf{Lex.Tok{+k733, +x734, +l735, +c736}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TOp{}), String.eq(x734, "<>")), Lex.TOp{}, tx, l, c)
            case Tree.Group{+op737, +ks738, +cl739}:
              twice.head_con(Lex.TOp{}, tx, l, c, op737, ks738, cl739, t732)
            case Tree.Stmt{+sk740, +sks741, +sb742}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h743, +t744}:
              {==}
    case Lex.TColon{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k745, +x746, +l747, +c748}}:
          {==}
        case Tree.Group{+op749, +ks750, +cl751}:
          {==}
        case Tree.Stmt{+sk752, +sks753, +sb754}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h755, +t756}:
          match h755:
            case Tree.Leaf{Lex.Tok{+k757, +x758, +l759, +c760}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TColon{}), String.eq(x758, "<>")), Lex.TColon{}, tx, l, c)
            case Tree.Group{+op761, +ks762, +cl763}:
              twice.head_con(Lex.TColon{}, tx, l, c, op761, ks762, cl763, t756)
            case Tree.Stmt{+sk764, +sks765, +sb766}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h767, +t768}:
              {==}
    case Lex.TEq{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k769, +x770, +l771, +c772}}:
          {==}
        case Tree.Group{+op773, +ks774, +cl775}:
          {==}
        case Tree.Stmt{+sk776, +sks777, +sb778}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h779, +t780}:
          match h779:
            case Tree.Leaf{Lex.Tok{+k781, +x782, +l783, +c784}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TEq{}), String.eq(x782, "<>")), Lex.TEq{}, tx, l, c)
            case Tree.Group{+op785, +ks786, +cl787}:
              twice.head_con(Lex.TEq{}, tx, l, c, op785, ks786, cl787, t780)
            case Tree.Stmt{+sk788, +sks789, +sb790}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h791, +t792}:
              {==}
    case Lex.TBind{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k793, +x794, +l795, +c796}}:
          {==}
        case Tree.Group{+op797, +ks798, +cl799}:
          {==}
        case Tree.Stmt{+sk800, +sks801, +sb802}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h803, +t804}:
          match h803:
            case Tree.Leaf{Lex.Tok{+k805, +x806, +l807, +c808}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TBind{}), String.eq(x806, "<>")), Lex.TBind{}, tx, l, c)
            case Tree.Group{+op809, +ks810, +cl811}:
              twice.head_con(Lex.TBind{}, tx, l, c, op809, ks810, cl811, t804)
            case Tree.Stmt{+sk812, +sks813, +sb814}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h815, +t816}:
              {==}
    case Lex.TArrow{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k817, +x818, +l819, +c820}}:
          {==}
        case Tree.Group{+op821, +ks822, +cl823}:
          {==}
        case Tree.Stmt{+sk824, +sks825, +sb826}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h827, +t828}:
          match h827:
            case Tree.Leaf{Lex.Tok{+k829, +x830, +l831, +c832}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TArrow{}), String.eq(x830, "<>")), Lex.TArrow{}, tx, l, c)
            case Tree.Group{+op833, +ks834, +cl835}:
              twice.head_con(Lex.TArrow{}, tx, l, c, op833, ks834, cl835, t828)
            case Tree.Stmt{+sk836, +sks837, +sb838}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h839, +t840}:
              {==}
    case Lex.TLam{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k841, +x842, +l843, +c844}}:
          {==}
        case Tree.Group{+op845, +ks846, +cl847}:
          {==}
        case Tree.Stmt{+sk848, +sks849, +sb850}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h851, +t852}:
          match h851:
            case Tree.Leaf{Lex.Tok{+k853, +x854, +l855, +c856}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TLam{}), String.eq(x854, "<>")), Lex.TLam{}, tx, l, c)
            case Tree.Group{+op857, +ks858, +cl859}:
              twice.head_con(Lex.TLam{}, tx, l, c, op857, ks858, cl859, t852)
            case Tree.Stmt{+sk860, +sks861, +sb862}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h863, +t864}:
              {==}
    case Lex.TAll{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k865, +x866, +l867, +c868}}:
          {==}
        case Tree.Group{+op869, +ks870, +cl871}:
          {==}
        case Tree.Stmt{+sk872, +sks873, +sb874}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h875, +t876}:
          match h875:
            case Tree.Leaf{Lex.Tok{+k877, +x878, +l879, +c880}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TAll{}), String.eq(x878, "<>")), Lex.TAll{}, tx, l, c)
            case Tree.Group{+op881, +ks882, +cl883}:
              twice.head_con(Lex.TAll{}, tx, l, c, op881, ks882, cl883, t876)
            case Tree.Stmt{+sk884, +sks885, +sb886}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h887, +t888}:
              {==}
    case Lex.TAmp{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k889, +x890, +l891, +c892}}:
          {==}
        case Tree.Group{+op893, +ks894, +cl895}:
          {==}
        case Tree.Stmt{+sk896, +sks897, +sb898}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h899, +t900}:
          match h899:
            case Tree.Leaf{Lex.Tok{+k901, +x902, +l903, +c904}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TAmp{}), String.eq(x902, "<>")), Lex.TAmp{}, tx, l, c)
            case Tree.Group{+op905, +ks906, +cl907}:
              twice.head_con(Lex.TAmp{}, tx, l, c, op905, ks906, cl907, t900)
            case Tree.Stmt{+sk908, +sks909, +sb910}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h911, +t912}:
              {==}
    case Lex.TOpen{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k913, +x914, +l915, +c916}}:
          {==}
        case Tree.Group{+op917, +ks918, +cl919}:
          {==}
        case Tree.Stmt{+sk920, +sks921, +sb922}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h923, +t924}:
          match h923:
            case Tree.Leaf{Lex.Tok{+k925, +x926, +l927, +c928}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TOpen{}), String.eq(x926, "<>")), Lex.TOpen{}, tx, l, c)
            case Tree.Group{+op929, +ks930, +cl931}:
              twice.head_con(Lex.TOpen{}, tx, l, c, op929, ks930, cl931, t924)
            case Tree.Stmt{+sk932, +sks933, +sb934}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h935, +t936}:
              {==}
    case Lex.TClose{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k937, +x938, +l939, +c940}}:
          {==}
        case Tree.Group{+op941, +ks942, +cl943}:
          {==}
        case Tree.Stmt{+sk944, +sks945, +sb946}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h947, +t948}:
          match h947:
            case Tree.Leaf{Lex.Tok{+k949, +x950, +l951, +c952}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TClose{}), String.eq(x950, "<>")), Lex.TClose{}, tx, l, c)
            case Tree.Group{+op953, +ks954, +cl955}:
              twice.head_con(Lex.TClose{}, tx, l, c, op953, ks954, cl955, t948)
            case Tree.Stmt{+sk956, +sks957, +sb958}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h959, +t960}:
              {==}
    case Lex.TComma{}:
      match t:
        case Tree.Leaf{Lex.Tok{+k961, +x962, +l963, +c964}}:
          {==}
        case Tree.Group{+op965, +ks966, +cl967}:
          {==}
        case Tree.Stmt{+sk968, +sks969, +sb970}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h971, +t972}:
          match h971:
            case Tree.Leaf{Lex.Tok{+k973, +x974, +l975, +c976}}:
              twice.pick_text(Bool.and(T.is_lit(Lex.TComma{}), String.eq(x974, "<>")), Lex.TComma{}, tx, l, c)
            case Tree.Group{+op977, +ks978, +cl979}:
              twice.head_con(Lex.TComma{}, tx, l, c, op977, ks978, cl979, t972)
            case Tree.Stmt{+sk980, +sks981, +sb982}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h983, +t984}:
              {==}

# the literal a list pattern opens with, to the rule and to the law
law twice.head:
  for pat: Tree.Node
  {twice.text(Twice.head(pat)) == Laws.twice.first(pat) : Maybe<&2, String>}

def twice.head(pat):
  match pat:
    case Tree.Leaf{Lex.Tok{+k985, +x986, +l987, +c988}}:
      {==}
    case Tree.Group{+op989, +ks990, +cl991}:
      {==}
    case Tree.Stmt{+sk992, +sks993, +sb994}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h995, +t996}:
      match h995:
        case Tree.Leaf{Lex.Tok{+k997, +x998, +l999, +c1000}}:
          twice.head2(k997, x998, l999, c1000, t996)
        case Tree.Group{+op1001, +ks1002, +cl1003}:
          match t996:
            case Tree.Leaf{Lex.Tok{+k1004, +x1005, +l1006, +c1007}}:
              {==}
            case Tree.Group{+op1008, +ks1009, +cl1010}:
              {==}
            case Tree.Stmt{+sk1011, +sks1012, +sb1013}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h1014, +t1015}:
              {==}
        case Tree.Stmt{+sk1016, +sks1017, +sb1018}:
          match t996:
            case Tree.Leaf{Lex.Tok{+k1019, +x1020, +l1021, +c1022}}:
              {==}
            case Tree.Group{+op1023, +ks1024, +cl1025}:
              {==}
            case Tree.Stmt{+sk1026, +sks1027, +sb1028}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h1029, +t1030}:
              {==}
        case Tree.NNil{}:
          match t996:
            case Tree.Leaf{Lex.Tok{+k1031, +x1032, +l1033, +c1034}}:
              {==}
            case Tree.Group{+op1035, +ks1036, +cl1037}:
              {==}
            case Tree.Stmt{+sk1038, +sks1039, +sb1040}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h1041, +t1042}:
              {==}
        case Tree.NCons{+h1043, +t1044}:
          match t996:
            case Tree.Leaf{Lex.Tok{+k1045, +x1046, +l1047, +c1048}}:
              {==}
            case Tree.Group{+op1049, +ks1050, +cl1051}:
              {==}
            case Tree.Stmt{+sk1052, +sks1053, +sb1054}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h1055, +t1056}:
              {==}

# a list pattern past its first element, to the rule and to the law
law twice.tail:
  for pat: Tree.Node
  {Twice.tail(pat) == Laws.twice.after(pat) : Tree.Node}

def twice.tail(pat):
  match pat:
    case Tree.Leaf{Lex.Tok{+k1057, +x1058, +l1059, +c1060}}:
      {==}
    case Tree.Group{+op1061, +ks1062, +cl1063}:
      {==}
    case Tree.Stmt{+sk1064, +sks1065, +sb1066}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h1067, +t1068}:
      match h1067:
        case Tree.Leaf{Lex.Tok{+k1069, +x1070, +l1071, +c1072}}:
          match k1069:
            case Lex.TName{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1073, +x1074, +l1075, +c1076}}:
                  {==}
                case Tree.Group{+op1077, +ks1078, +cl1079}:
                  {==}
                case Tree.Stmt{+sk1080, +sks1081, +sb1082}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1083, +t1084}:
                  {==}
            case Lex.TUpper{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1085, +x1086, +l1087, +c1088}}:
                  {==}
                case Tree.Group{+op1089, +ks1090, +cl1091}:
                  {==}
                case Tree.Stmt{+sk1092, +sks1093, +sb1094}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1095, +t1096}:
                  match h1095:
                    case Tree.Leaf{Lex.Tok{+k1097, +x1098, +l1099, +c1100}}:
                      {==}
                    case Tree.Group{+op1101, +ks1102, +cl1103}:
                      match ks1102:
                        case Tree.Leaf{Lex.Tok{+k1104, +x1105, +l1106, +c1107}}:
                          {==}
                        case Tree.Group{+op1108, +ks1109, +cl1110}:
                          {==}
                        case Tree.Stmt{+sk1111, +sks1112, +sb1113}:
                          {==}
                        case Tree.NNil{}:
                          {==}
                        case Tree.NCons{+h1114, +t1115}:
                          match t1115:
                            case Tree.Leaf{Lex.Tok{+k1116, +x1117, +l1118, +c1119}}:
                              {==}
                            case Tree.Group{+op1120, +ks1121, +cl1122}:
                              {==}
                            case Tree.Stmt{+sk1123, +sks1124, +sb1125}:
                              {==}
                            case Tree.NNil{}:
                              {==}
                            case Tree.NCons{+h1126, +t1127}:
                              {==}
                    case Tree.Stmt{+sk1128, +sks1129, +sb1130}:
                      {==}
                    case Tree.NNil{}:
                      {==}
                    case Tree.NCons{+h1131, +t1132}:
                      {==}
            case Lex.TDotted{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1133, +x1134, +l1135, +c1136}}:
                  {==}
                case Tree.Group{+op1137, +ks1138, +cl1139}:
                  {==}
                case Tree.Stmt{+sk1140, +sks1141, +sb1142}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1143, +t1144}:
                  {==}
            case Lex.TWild{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1145, +x1146, +l1147, +c1148}}:
                  {==}
                case Tree.Group{+op1149, +ks1150, +cl1151}:
                  {==}
                case Tree.Stmt{+sk1152, +sks1153, +sb1154}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1155, +t1156}:
                  {==}
            case Lex.TKey{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1157, +x1158, +l1159, +c1160}}:
                  {==}
                case Tree.Group{+op1161, +ks1162, +cl1163}:
                  {==}
                case Tree.Stmt{+sk1164, +sks1165, +sb1166}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1167, +t1168}:
                  {==}
            case Lex.TNum{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1169, +x1170, +l1171, +c1172}}:
                  {==}
                case Tree.Group{+op1173, +ks1174, +cl1175}:
                  {==}
                case Tree.Stmt{+sk1176, +sks1177, +sb1178}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1179, +t1180}:
                  {==}
            case Lex.TStr{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1181, +x1182, +l1183, +c1184}}:
                  {==}
                case Tree.Group{+op1185, +ks1186, +cl1187}:
                  {==}
                case Tree.Stmt{+sk1188, +sks1189, +sb1190}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1191, +t1192}:
                  {==}
            case Lex.TChar{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1193, +x1194, +l1195, +c1196}}:
                  {==}
                case Tree.Group{+op1197, +ks1198, +cl1199}:
                  {==}
                case Tree.Stmt{+sk1200, +sks1201, +sb1202}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1203, +t1204}:
                  {==}
            case Lex.TComment{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1205, +x1206, +l1207, +c1208}}:
                  {==}
                case Tree.Group{+op1209, +ks1210, +cl1211}:
                  {==}
                case Tree.Stmt{+sk1212, +sks1213, +sb1214}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1215, +t1216}:
                  {==}
            case Lex.TSpace{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1217, +x1218, +l1219, +c1220}}:
                  {==}
                case Tree.Group{+op1221, +ks1222, +cl1223}:
                  {==}
                case Tree.Stmt{+sk1224, +sks1225, +sb1226}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1227, +t1228}:
                  {==}
            case Lex.TNewline{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1229, +x1230, +l1231, +c1232}}:
                  {==}
                case Tree.Group{+op1233, +ks1234, +cl1235}:
                  {==}
                case Tree.Stmt{+sk1236, +sks1237, +sb1238}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1239, +t1240}:
                  {==}
            case Lex.TOp{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1241, +x1242, +l1243, +c1244}}:
                  {==}
                case Tree.Group{+op1245, +ks1246, +cl1247}:
                  {==}
                case Tree.Stmt{+sk1248, +sks1249, +sb1250}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1251, +t1252}:
                  {==}
            case Lex.TColon{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1253, +x1254, +l1255, +c1256}}:
                  {==}
                case Tree.Group{+op1257, +ks1258, +cl1259}:
                  {==}
                case Tree.Stmt{+sk1260, +sks1261, +sb1262}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1263, +t1264}:
                  {==}
            case Lex.TEq{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1265, +x1266, +l1267, +c1268}}:
                  {==}
                case Tree.Group{+op1269, +ks1270, +cl1271}:
                  {==}
                case Tree.Stmt{+sk1272, +sks1273, +sb1274}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1275, +t1276}:
                  {==}
            case Lex.TBind{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1277, +x1278, +l1279, +c1280}}:
                  {==}
                case Tree.Group{+op1281, +ks1282, +cl1283}:
                  {==}
                case Tree.Stmt{+sk1284, +sks1285, +sb1286}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1287, +t1288}:
                  {==}
            case Lex.TArrow{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1289, +x1290, +l1291, +c1292}}:
                  {==}
                case Tree.Group{+op1293, +ks1294, +cl1295}:
                  {==}
                case Tree.Stmt{+sk1296, +sks1297, +sb1298}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1299, +t1300}:
                  {==}
            case Lex.TLam{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1301, +x1302, +l1303, +c1304}}:
                  {==}
                case Tree.Group{+op1305, +ks1306, +cl1307}:
                  {==}
                case Tree.Stmt{+sk1308, +sks1309, +sb1310}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1311, +t1312}:
                  {==}
            case Lex.TAll{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1313, +x1314, +l1315, +c1316}}:
                  {==}
                case Tree.Group{+op1317, +ks1318, +cl1319}:
                  {==}
                case Tree.Stmt{+sk1320, +sks1321, +sb1322}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1323, +t1324}:
                  {==}
            case Lex.TAmp{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1325, +x1326, +l1327, +c1328}}:
                  {==}
                case Tree.Group{+op1329, +ks1330, +cl1331}:
                  {==}
                case Tree.Stmt{+sk1332, +sks1333, +sb1334}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1335, +t1336}:
                  {==}
            case Lex.TOpen{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1337, +x1338, +l1339, +c1340}}:
                  {==}
                case Tree.Group{+op1341, +ks1342, +cl1343}:
                  {==}
                case Tree.Stmt{+sk1344, +sks1345, +sb1346}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1347, +t1348}:
                  {==}
            case Lex.TClose{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1349, +x1350, +l1351, +c1352}}:
                  {==}
                case Tree.Group{+op1353, +ks1354, +cl1355}:
                  {==}
                case Tree.Stmt{+sk1356, +sks1357, +sb1358}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1359, +t1360}:
                  {==}
            case Lex.TComma{}:
              match t1068:
                case Tree.Leaf{Lex.Tok{+k1361, +x1362, +l1363, +c1364}}:
                  {==}
                case Tree.Group{+op1365, +ks1366, +cl1367}:
                  {==}
                case Tree.Stmt{+sk1368, +sks1369, +sb1370}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h1371, +t1372}:
                  {==}
        case Tree.Group{+op1373, +ks1374, +cl1375}:
          match t1068:
            case Tree.Leaf{Lex.Tok{+k1376, +x1377, +l1378, +c1379}}:
              {==}
            case Tree.Group{+op1380, +ks1381, +cl1382}:
              {==}
            case Tree.Stmt{+sk1383, +sks1384, +sb1385}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h1386, +t1387}:
              {==}
        case Tree.Stmt{+sk1388, +sks1389, +sb1390}:
          match t1068:
            case Tree.Leaf{Lex.Tok{+k1391, +x1392, +l1393, +c1394}}:
              {==}
            case Tree.Group{+op1395, +ks1396, +cl1397}:
              {==}
            case Tree.Stmt{+sk1398, +sks1399, +sb1400}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h1401, +t1402}:
              {==}
        case Tree.NNil{}:
          match t1068:
            case Tree.Leaf{Lex.Tok{+k1403, +x1404, +l1405, +c1406}}:
              {==}
            case Tree.Group{+op1407, +ks1408, +cl1409}:
              {==}
            case Tree.Stmt{+sk1410, +sks1411, +sb1412}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h1413, +t1414}:
              {==}
        case Tree.NCons{+h1415, +t1416}:
          match t1068:
            case Tree.Leaf{Lex.Tok{+k1417, +x1418, +l1419, +c1420}}:
              {==}
            case Tree.Group{+op1421, +ks1422, +cl1423}:
              {==}
            case Tree.Stmt{+sk1424, +sks1425, +sb1426}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{+h1427, +t1428}:
              {==}

# a literal against a second, a finding exactly when the law's same
law twice.same2:
  for k: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for bb: Maybe<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Twice.same(Some{Lex.Tok{k, t, l, c}}, bb, path)) == Bool.pick(Nat,
      Laws.twice.same(Some{t}, twice.text(bb)), 1n, 0n) : Nat}

def twice.same2(_k, t, _l, _c, bb, path):
  match bb:
    case None{}:
      {==}
    case Some{Lex.Tok{k2, +t2, +l2, +c2}}:
      nat.pick(String.eq(t, t2), F.Finding{path, l2, c2, T.width(t2), "twice",
        "The same literal appears twice in one list pattern, which hangs the checker; match one element per step."},
          [], 0n, {==})

# two literals, a finding exactly when the law's same
law twice.same:
  for aa: Maybe<&2, Lex.Tok>
  for bb: Maybe<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Twice.same(aa, bb, path)) == Bool.pick(Nat, Laws.twice.same(twice.text(aa),
      twice.text(bb)), 1n, 0n) : Nat}

def twice.same(aa, bb, path):
  match aa:
    case None{}:
      {==}
    case Some{Lex.Tok{k, t, l, c}}:
      twice.same2(k, t, l, c, bb, path)

# a case pattern, a finding exactly when it opens with the same literal twice
law twice.arm:
  for +pat: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Twice.arm(pat, path)) == Bool.pick(Nat, Laws.twice.same(Laws.twice.first(pat),
      Laws.twice.first(Laws.twice.after(pat))), 1n, 0n) : Nat}

def twice.arm(pat, path):
  Equal.trans(Nat, List.length(&2, F.Finding, Twice.arm(pat, path)), Bool.pick(Nat,
    Laws.twice.same(twice.text(Twice.head(pat)), twice.text(Twice.head(Twice.tail(pat)))), 1n, 0n), Bool.pick(Nat,
    Laws.twice.same(Laws.twice.first(pat), Laws.twice.first(Laws.twice.after(pat))), 1n, 0n),
    twice.same(Twice.head(pat), Twice.head(Twice.tail(pat)), path),
    Equal.trans(Nat, Bool.pick(Nat, Laws.twice.same(twice.text(Twice.head(pat)),
      twice.text(Twice.head(Twice.tail(pat)))), 1n, 0n), Bool.pick(Nat, Laws.twice.same(Laws.twice.first(pat),
      twice.text(Twice.head(Twice.tail(pat)))), 1n, 0n), Bool.pick(Nat, Laws.twice.same(Laws.twice.first(pat),
      Laws.twice.first(Laws.twice.after(pat))), 1n, 0n),
      Equal.cong(Maybe<&2, String>, Nat, z => Bool.pick(Nat, Laws.twice.same(z,
        twice.text(Twice.head(Twice.tail(pat)))), 1n, 0n), twice.text(Twice.head(pat)), Laws.twice.first(pat),
        twice.head(pat)),
      Equal.cong(Maybe<&2, String>, Nat, z => Bool.pick(Nat, Laws.twice.same(Laws.twice.first(pat), z), 1n, 0n),
        twice.text(Twice.head(Twice.tail(pat))), Laws.twice.first(Laws.twice.after(pat)),
        Equal.trans(Maybe<&2, String>, twice.text(Twice.head(Twice.tail(pat))),
          twice.text(Twice.head(Laws.twice.after(pat))), Laws.twice.first(Laws.twice.after(pat)),
          Equal.cong(Tree.Node, Maybe<&2, String>, z => twice.text(Twice.head(z)), Twice.tail(pat),
            Laws.twice.after(pat),
            twice.tail(pat)),
          twice.head(Laws.twice.after(pat))))))

# a case statement onto the rest, its body and the rest both holding the law
law twice.case:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +path: String
  for ihb: {List.length(&2, F.Finding, Twice.walk(body, path)) == Laws.twice.cases(body) : Nat}
  for ihr: {List.length(&2, F.Finding, Twice.walk(rest, path)) == Laws.twice.cases(rest) : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [Twice.arm(T.pattern(kids), path), Twice.walk(body, path),
      Twice.walk(rest, path)])) == Nat.add(Bool.pick(Nat, Laws.twice.dup(T.pattern(kids)), 1n, 0n),
      Nat.add(Laws.twice.cases(body), Laws.twice.cases(rest))) : Nat}

def twice.case(kids, body, rest, path, ihb, ihr):
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [Twice.arm(T.pattern(kids), path),
    Twice.walk(body, path), Twice.walk(rest, path)])), Nat.add(List.length(&2, F.Finding, Twice.arm(T.pattern(kids),
    path)), Nat.add(List.length(&2, F.Finding, Twice.walk(body, path)), List.length(&2, F.Finding, Twice.walk(rest,
    path)))),
    Nat.add(Bool.pick(Nat, Laws.twice.dup(T.pattern(kids)), 1n, 0n), Nat.add(Laws.twice.cases(body),
      Laws.twice.cases(rest))),
    arms.cat(Twice.arm(T.pattern(kids), path), Twice.walk(body, path), Twice.walk(rest, path)),
    arms.add3(List.length(&2, F.Finding, Twice.arm(T.pattern(kids), path)), Bool.pick(Nat,
      Laws.twice.dup(T.pattern(kids)), 1n, 0n), List.length(&2, F.Finding, Twice.walk(body, path)),
      Laws.twice.cases(body), List.length(&2, F.Finding, Twice.walk(rest, path)), Laws.twice.cases(rest),
      twice.arm(T.pattern(kids), path), ihb, ihr))

# any other statement onto the rest, its body and the rest both holding the law
law twice.stmt:
  for +body: Tree.Node
  for +rest: Tree.Node
  for +path: String
  for ihb: {List.length(&2, F.Finding, Twice.walk(body, path)) == Laws.twice.cases(body) : Nat}
  for ihr: {List.length(&2, F.Finding, Twice.walk(rest, path)) == Laws.twice.cases(rest) : Nat}
  {List.length(&2, F.Finding, List.append(&2, F.Finding, Twice.walk(body, path), Twice.walk(rest,
      path))) == Nat.add(Laws.twice.cases(body), Laws.twice.cases(rest)) : Nat}

def twice.stmt(body, rest, path, ihb, ihr):
  Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, Twice.walk(body, path), Twice.walk(rest,
    path))), Nat.add(List.length(&2, F.Finding, Twice.walk(body, path)), List.length(&2, F.Finding, Twice.walk(rest,
    path))), Nat.add(Laws.twice.cases(body), Laws.twice.cases(rest)),
    esc.app(Twice.walk(body, path), Twice.walk(rest, path)),
    esc.add(List.length(&2, F.Finding, Twice.walk(body, path)), Laws.twice.cases(body), List.length(&2, F.Finding,
      Twice.walk(rest, path)), Laws.twice.cases(rest), ihb, ihr))

# every case statement at any depth, each pattern read
law twice.walk:
  for nn: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Twice.walk(nn, path)) == Laws.twice.cases(nn) : Nat}

def twice.walk(nn, path):
  match nn:
    case Tree.Leaf{Lex.Tok{+k1429, +x1430, +l1431, +c1432}}:
      {==}
    case Tree.Group{+op1433, +ks1434, +cl1435}:
      {==}
    case Tree.Stmt{+sk1436, +sks1437, +sb1438}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h1439, +t1440}:
      match h1439:
        case Tree.Leaf{Lex.Tok{+k1441, +x1442, +l1443, +c1444}}:
          twice.walk(t1440, path)
        case Tree.Group{+op1445, +ks1446, +cl1447}:
          twice.walk(t1440, path)
        case Tree.Stmt{+sk1448, +sks1449, +sb1450}:
          match sk1448:
            case Tree.SDef{}:
              twice.stmt(sb1450, t1440, path, twice.walk(sb1450, path), twice.walk(t1440, path))
            case Tree.SType{}:
              twice.stmt(sb1450, t1440, path, twice.walk(sb1450, path), twice.walk(t1440, path))
            case Tree.SLaw{}:
              twice.stmt(sb1450, t1440, path, twice.walk(sb1450, path), twice.walk(t1440, path))
            case Tree.SImport{}:
              twice.stmt(sb1450, t1440, path, twice.walk(sb1450, path), twice.walk(t1440, path))
            case Tree.SCase{}:
              twice.case(sks1449, sb1450, t1440, path, twice.walk(sb1450, path), twice.walk(t1440, path))
            case Tree.SFor{}:
              twice.stmt(sb1450, t1440, path, twice.walk(sb1450, path), twice.walk(t1440, path))
            case Tree.SLet{}:
              twice.stmt(sb1450, t1440, path, twice.walk(sb1450, path), twice.walk(t1440, path))
            case Tree.STerm{}:
              twice.stmt(sb1450, t1440, path, twice.walk(sb1450, path), twice.walk(t1440, path))
        case Tree.NNil{}:
          twice.walk(t1440, path)
        case Tree.NCons{+h1451, +t1452}:
          twice.walk(t1440, path)

# a def's cases, read when it calls itself
law twice.def:
  for mm: Maybe<&2, String>
  for +body: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Twice.check.def(mm, body, path)) == Laws.twice.def(mm, body) : Nat}

def twice.def(mm, body, path):
  match mm:
    case None{}:
      {==}
    case Some{+name}:
      Equal.trans(Nat, List.length(&2, F.Finding, Twice.check.def(Some{name}, body, path)), Bool.pick(Nat,
        Bool.not(Calls.calls(body, name)), 0n, Laws.twice.cases(body)),
        Bool.pick(Nat, Calls.calls(body, name), Laws.twice.cases(body), 0n),
        param.stop(Bool.not(Calls.calls(body, name)), Twice.walk(body, path), Laws.twice.cases(body),
          twice.walk(body, path)),
        arms.flip(Calls.calls(body, name), Laws.twice.cases(body)))

# the top-level defs, each read when it calls itself
law twice.go:
  for root: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Twice.check.go(root, path)) == Laws.twice_count(root) : Nat}

def twice.go(root, path):
  match root:
    case Tree.Leaf{Lex.Tok{+k1453, +x1454, +l1455, +c1456}}:
      {==}
    case Tree.Group{+op1457, +ks1458, +cl1459}:
      {==}
    case Tree.Stmt{+sk1460, +sks1461, +sb1462}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h1463, +t1464}:
      match h1463:
        case Tree.Leaf{Lex.Tok{+k1465, +x1466, +l1467, +c1468}}:
          twice.go(t1464, path)
        case Tree.Group{+op1469, +ks1470, +cl1471}:
          twice.go(t1464, path)
        case Tree.Stmt{+sk1472, +sks1473, +sb1474}:
          match sk1472:
            case Tree.SDef{}:
              Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding,
                Twice.check.def(Bind.declared(sks1473), sb1474, path), Twice.check.go(t1464, path))),
                Nat.add(List.length(&2, F.Finding, Twice.check.def(Bind.declared(sks1473), sb1474, path)),
                List.length(&2, F.Finding, Twice.check.go(t1464, path))),
                Nat.add(Laws.twice.def(Bind.declared(sks1473), sb1474), Laws.twice_count(t1464)),
                esc.app(Twice.check.def(Bind.declared(sks1473), sb1474, path), Twice.check.go(t1464, path)),
                esc.add(List.length(&2, F.Finding, Twice.check.def(Bind.declared(sks1473), sb1474, path)),
                  Laws.twice.def(Bind.declared(sks1473), sb1474), List.length(&2, F.Finding, Twice.check.go(t1464,
                  path)), Laws.twice_count(t1464), twice.def(Bind.declared(sks1473), sb1474, path), twice.go(t1464,
                  path)))
            case Tree.SType{}:
              twice.go(t1464, path)
            case Tree.SLaw{}:
              twice.go(t1464, path)
            case Tree.SImport{}:
              twice.go(t1464, path)
            case Tree.SCase{}:
              twice.go(t1464, path)
            case Tree.SFor{}:
              twice.go(t1464, path)
            case Tree.SLet{}:
              twice.go(t1464, path)
            case Tree.STerm{}:
              twice.go(t1464, path)
        case Tree.NNil{}:
          twice.go(t1464, path)
        case Tree.NCons{+h1475, +t1476}:
          twice.go(t1464, path)

def Laws.twice_counts(path, _text, _toks, tree, _bound, _items):
  twice.go(tree, path)
