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

# The eager Bool combinators (BOLT-RULE-C003, BOLT-RULE-U002). A walk joins
# the finding lists of a node's parts; each count adds their counts.

# appending Nil keeps a list's length
law pick.nil:
  for a: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.append(&2, F.Finding, a, Nil{})) == List.length(&2, F.Finding, a) : Nat}

def pick.nil(a):
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, List.append(&2, F.Finding, t, Nil{})),
        List.length(&2, F.Finding, t), pick.nil(t))

# two lists of known lengths appended: the sum
law pick.join:
  for a: List<&2, F.Finding>
  for r: List<&2, F.Finding>
  for -ma: Nat
  for -mr: Nat
  for ea: {List.length(&2, F.Finding, a) == ma : Nat}
  for er: {List.length(&2, F.Finding, r) == mr : Nat}
  {List.length(&2, F.Finding, List.append(&2, F.Finding, a, r)) == Nat.add(ma, mr) : Nat}

def pick.join(a, r, ma, mr, ea, er):
  Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, a, r)),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, r)), Nat.add(ma, mr),
    esc.app(a, r), esc.add(List.length(&2, F.Finding, a), ma, List.length(&2, F.Finding, r), mr, ea, er))

# the last list of a join: Nil appended
law pick.last:
  for b: List<&2, F.Finding>
  for -mb: Nat
  for eb: {List.length(&2, F.Finding, b) == mb : Nat}
  {List.length(&2, F.Finding, List.append(&2, F.Finding, b, Nil{})) == mb : Nat}

def pick.last(b, mb, eb):
  Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, b, Nil{})),
    List.length(&2, F.Finding, b), mb, pick.nil(b), eb)

# either finding of a pick is the law's hit: a branch calls the def
law pick.either:
  for p: Bool
  for q: Bool
  for a: Bool
  for b: Bool
  {Bool.or(Bool.and(Bool.and(p, Bool.not(q)), Bool.and(a, b)),
      Bool.and(Bool.and(p, Bool.not(Bool.and(Bool.and(p, Bool.not(q)), Bool.and(a, b)))),
        Bool.and(Bool.not(q), Bool.or(a, b))))
    == Bool.and(p, Bool.and(Bool.not(q), Bool.or(a, b))) : Bool}

def pick.either(p, q, a, b):
  match p q a b:
    case False{} q a b:
      {==}
    case True{} True{} a b:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} b:
      {==}

# quiet or'd with a hush that does not apply is quiet
law pick.off:
  for q: Bool
  for h: Bool
  {q == Bool.or(q, Bool.and(h, False{})) : Bool}

def pick.off(q, h):
  match q h:
    case True{} h:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# quiet or'd with a hush that applies is the plain or
law pick.on:
  for q: Bool
  for h: Bool
  {Bool.or(q, h) == Bool.or(q, Bool.and(h, True{})) : Bool}

def pick.on(q, h):
  match q h:
    case True{} h:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def Laws.pick_mute(q, h, n):
  match n:
    case 0n:
      pick.off(q, h)
    case 1n:
      pick.off(q, h)
    case 2n:
      pick.on(q, h)
    case 3n:
      pick.on(q, h)
    case 4n+p:
      pick.off(q, h)

def Laws.pick_next(k, _n):
  match k:
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

# the walk in a state the law's count reaches another way
law pick.move:
  for +nn: Tree.Node
  for +name: String
  for +path: String
  for +q1: Bool
  for +q2: Bool
  for +h1: Bool
  for +h2: Bool
  for +n1: Nat
  for +n2: Nat
  for eq: {q1 == q2 : Bool}
  for eh: {h1 == h2 : Bool}
  for en: {n1 == n2 : Nat}
  for ih: {List.length(&2, F.Finding, Pick.walk(nn, name, path, q1, h1, n1))
    == Laws.pick.count(nn, name, q1, h1, n1) : Nat}
  {List.length(&2, F.Finding, Pick.walk(nn, name, path, q1, h1, n1)) == Laws.pick.count(nn, name, q2, h2, n2) : Nat}

def pick.move(nn, name, path, q1, q2, h1, h2, n1, n2, eq, eh, en, ih):
  Equal.trans(Nat, List.length(&2, F.Finding, Pick.walk(nn, name, path, q1, h1, n1)),
    Laws.pick.count(nn, name, q1, h1, n1), Laws.pick.count(nn, name, q2, h2, n2), ih,
    Equal.trans(Nat, Laws.pick.count(nn, name, q1, h1, n1), Laws.pick.count(nn, name, q2, h1, n1),
      Laws.pick.count(nn, name, q2, h2, n2), Equal.cong(Bool, Nat, x => Laws.pick.count(nn, name, x, h1, n1), q1, q2,
        eq),
      Equal.trans(Nat, Laws.pick.count(nn, name, q2, h1, n1), Laws.pick.count(nn, name, q2, h2, n1),
        Laws.pick.count(nn, name, q2, h2, n2), Equal.cong(Bool, Nat, x => Laws.pick.count(nn, name, q2, x, n1), h1, h2,
          eh),
        Equal.cong(Nat, Nat, x => Laws.pick.count(nn, name, q2, h2, x), n1, n2, en))))

# the law's count at a pick call, the call being argument at with quiet q
def pick.at(
  +t: String,
  +kids: Tree.Node,
  +rest: Tree.Node,
  +name: String,
  +quiet: Bool,
  +hush: Bool,
  +at: Nat,
  +q: Bool
) -> Nat:
  +hit = Bool.and(String.eq(t, "Bool.pick"), Bool.and(Bool.not(q), Laws.pick.branch(Calls.args(kids), name)))
  +m = Nat.add(Laws.pick.count(kids, name, q, hit, 0n), Laws.pick.count(rest, name, quiet, hush, at))
  Bool.pick(Nat, hit, 1n+m, m)

# a finding for both branches, else one for one branch, adds one to the count
# exactly when a branch calls the def
law pick.hit:
  for p: Bool
  for q: Bool
  for a: Bool
  for b: Bool
  for -x: F.Finding
  for -y: F.Finding
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding,
      Bool.pick(List<&2, F.Finding>, Bool.and(Bool.and(p, Bool.not(q)), Bool.and(a, b)), x <> more,
        Bool.pick(List<&2, F.Finding>,
          Bool.and(Bool.and(p, Bool.not(Bool.and(Bool.and(p, Bool.not(q)), Bool.and(a, b)))),
            Bool.and(Bool.not(q), Bool.or(a, b))), y <> more, more)))
    == Bool.pick(Nat, Bool.and(p, Bool.and(Bool.not(q), Bool.or(a, b))), 1n+m, m) : Nat}

def pick.hit(p, q, a, b, _x, _y, more, m, ih):
  match p q a b:
    case False{} q a b:
      ih
    case True{} True{} a b:
      ih
    case True{} False{} True{} True{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
    case True{} False{} True{} False{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
    case True{} False{} False{} True{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
    case True{} False{} False{} False{}:
      ih

def Laws.pick_walk_counts(nn, name, path, quiet, hush, nth):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{open, +kids, close}:
                      +at = Pick.next(k, nth)
                      +q = Pick.mute(quiet, hush, at)
                      +as = Calls.args(kids)
                      +p = String.eq(t, "Bool.pick")
                      +a = Calls.calls(Calls.arg(as, 2n), name)
                      +b = Calls.calls(Calls.arg(as, 3n), name)
                      +two = Bool.and(Bool.and(p, Bool.not(q)), Bool.and(a, b))
                      +one = Bool.and(Bool.and(p, Bool.not(two)), Bool.and(Bool.not(q), Bool.or(a, b)))
                      +hit = Bool.and(p, Bool.and(Bool.not(q), Bool.or(a, b)))
                      +fk = Pick.walk(kids, name, path, q, Bool.or(two, one), 0n)
                      +fr = Pick.walk(r2, name, path, quiet, hush, at)
                      +ck = Laws.pick.count(kids, name, q, hit, 0n)
                      +cr = Laws.pick.count(r2, name, quiet, hush, at)
                      +found = pick.hit(p, q, a, b,
                        F.Finding{path, l, c, 9, "pick",
                          name ++ " recurses in both branches of Bool.pick, so both calls run; bind the recursive call once above the pick."},
                        F.Finding{path, l, c, 9, "pick",
                          name ++ " recurses in one branch of Bool.pick, so the call runs whatever the condition and there is no early exit; bind it above the pick."},
                        List.concat(&2, F.Finding, [fk, fr]), Nat.add(ck, cr),
                        pick.join(fk, List.append(&2, F.Finding, fr, Nil{}), ck, cr,
                          pick.move(kids, name, path, q, q, Bool.or(two, one), hit, 0n, 0n, {==}, pick.either(p, q, a,
                            b), {==},
                            Laws.pick_walk_counts(kids, name, path, q, Bool.or(two, one), 0n)),
                          pick.last(fr, cr, Laws.pick_walk_counts(r2, name, path, quiet, hush, at))))
                      Equal.trans(Nat, List.length(&2, F.Finding, Pick.walk(Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}},
                        rest}, name, path, quiet, hush, nth)), pick.at(t, kids, r2, name, quiet, hush, at, q),
                        pick.at(t, kids, r2, name, quiet, hush, Laws.pick.step(k, nth), Laws.pick.hushed(quiet, hush,
                          Laws.pick.step(k, nth))), found,
                        Equal.trans(Nat, pick.at(t, kids, r2, name, quiet, hush, at, q), pick.at(t, kids, r2, name,
                          quiet, hush, at, Laws.pick.hushed(quiet, hush, at)),
                          pick.at(t, kids, r2, name, quiet, hush, Laws.pick.step(k, nth), Laws.pick.hushed(quiet, hush,
                            Laws.pick.step(k, nth))),
                          Equal.cong(Bool, Nat, x => pick.at(t, kids, r2, name, quiet, hush, at, x), q,
                            Laws.pick.hushed(quiet, hush, at),
                            Laws.pick_mute(quiet, hush, at)),
                          Equal.cong(Nat, Nat, x => pick.at(t, kids, r2, name, quiet, hush, x, Laws.pick.hushed(quiet,
                            hush, x)), at, Laws.pick.step(k, nth),
                            Laws.pick_next(k, nth))))
                    case Tree.Leaf{x}:
                      pick.move(rest, name, path, quiet, quiet, hush, hush, Pick.next(k, nth), Laws.pick.step(k, nth),
                        {==}, {==},
                        Laws.pick_next(k, nth), Laws.pick_walk_counts(rest, name, path, quiet, hush, Pick.next(k, nth)))
                    case Tree.Stmt{kind, kids, body}:
                      pick.move(rest, name, path, quiet, quiet, hush, hush, Pick.next(k, nth), Laws.pick.step(k, nth),
                        {==}, {==},
                        Laws.pick_next(k, nth), Laws.pick_walk_counts(rest, name, path, quiet, hush, Pick.next(k, nth)))
                    case Tree.NNil{}:
                      pick.move(rest, name, path, quiet, quiet, hush, hush, Pick.next(k, nth), Laws.pick.step(k, nth),
                        {==}, {==},
                        Laws.pick_next(k, nth), Laws.pick_walk_counts(rest, name, path, quiet, hush, Pick.next(k, nth)))
                    case Tree.NCons{x, y}:
                      pick.move(rest, name, path, quiet, quiet, hush, hush, Pick.next(k, nth), Laws.pick.step(k, nth),
                        {==}, {==},
                        Laws.pick_next(k, nth), Laws.pick_walk_counts(rest, name, path, quiet, hush, Pick.next(k, nth)))
                case Tree.Leaf{x}:
                  pick.move(rest, name, path, quiet, quiet, hush, hush, Pick.next(k, nth), Laws.pick.step(k, nth), {==},
                    {==},
                    Laws.pick_next(k, nth), Laws.pick_walk_counts(rest, name, path, quiet, hush, Pick.next(k, nth)))
                case Tree.Group{open, kids, close}:
                  pick.move(rest, name, path, quiet, quiet, hush, hush, Pick.next(k, nth), Laws.pick.step(k, nth), {==},
                    {==},
                    Laws.pick_next(k, nth), Laws.pick_walk_counts(rest, name, path, quiet, hush, Pick.next(k, nth)))
                case Tree.Stmt{kind, kids, body}:
                  pick.move(rest, name, path, quiet, quiet, hush, hush, Pick.next(k, nth), Laws.pick.step(k, nth), {==},
                    {==},
                    Laws.pick_next(k, nth), Laws.pick_walk_counts(rest, name, path, quiet, hush, Pick.next(k, nth)))
                case Tree.NNil{}:
                  pick.move(rest, name, path, quiet, quiet, hush, hush, Pick.next(k, nth), Laws.pick.step(k, nth), {==},
                    {==},
                    Laws.pick_next(k, nth), Laws.pick_walk_counts(rest, name, path, quiet, hush, Pick.next(k, nth)))
        case Tree.Group{open, +kids, close}:
          +fr = Pick.walk(rest, name, path, quiet, hush, nth)
          +cr = Laws.pick.count(rest, name, quiet, hush, nth)
          pick.join(Pick.walk(kids, name, path, Pick.mute(quiet, hush, nth), False{}, 0n), List.append(&2, F.Finding,
            fr, Nil{}),
            Laws.pick.count(kids, name, Laws.pick.hushed(quiet, hush, nth), False{}, 0n), cr,
            pick.move(kids, name, path, Pick.mute(quiet, hush, nth), Laws.pick.hushed(quiet, hush, nth), False{},
              False{}, 0n, 0n, Laws.pick_mute(quiet, hush, nth), {==}, {==},
              Laws.pick_walk_counts(kids, name, path, Pick.mute(quiet, hush, nth), False{}, 0n)),
            pick.last(fr, cr, Laws.pick_walk_counts(rest, name, path, quiet, hush, nth)))
        case Tree.Stmt{kind, +kids, +body}:
          +fb = Pick.walk(body, name, path, Pick.mute(quiet, hush, nth), False{}, 0n)
          +fr = Pick.walk(rest, name, path, quiet, hush, nth)
          +cb = Laws.pick.count(body, name, Laws.pick.hushed(quiet, hush, nth), False{}, 0n)
          +cr = Laws.pick.count(rest, name, quiet, hush, nth)
          pick.join(Pick.walk(kids, name, path, Pick.mute(quiet, hush, nth), False{}, 0n),
            List.append(&2, F.Finding, fb, List.append(&2, F.Finding, fr, Nil{})),
            Laws.pick.count(kids, name, Laws.pick.hushed(quiet, hush, nth), False{}, 0n), Nat.add(cb, cr),
            pick.move(kids, name, path, Pick.mute(quiet, hush, nth), Laws.pick.hushed(quiet, hush, nth), False{},
              False{}, 0n, 0n, Laws.pick_mute(quiet, hush, nth), {==}, {==},
              Laws.pick_walk_counts(kids, name, path, Pick.mute(quiet, hush, nth), False{}, 0n)),
            pick.join(fb, List.append(&2, F.Finding, fr, Nil{}), cb, cr,
              pick.move(body, name, path, Pick.mute(quiet, hush, nth), Laws.pick.hushed(quiet, hush, nth), False{},
                False{}, 0n, 0n, Laws.pick_mute(quiet, hush, nth), {==}, {==},
              Laws.pick_walk_counts(body, name, path, Pick.mute(quiet, hush, nth), False{}, 0n)),
              pick.last(fr, cr, Laws.pick_walk_counts(rest, name, path, quiet, hush, nth))))
        case Tree.NNil{}:
          Laws.pick_walk_counts(rest, name, path, quiet, hush, nth)
        case Tree.NCons{x, y}:
          Laws.pick_walk_counts(rest, name, path, quiet, hush, nth)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

def Laws.pick_picks_counts(nn, name, path, quiet):
  Laws.pick_walk_counts(nn, name, path, quiet, False{}, 0n)

# the findings of lists reversed onto ys: the lengths of acc summed onto theirs
def pick.sum(acc: List<&2, List<&2, F.Finding>>, n: Nat) -> Nat:
  match acc:
    case Nil{}:
      n
    case Con{h, t}:
      pick.sum(t, Nat.add(List.length(&2, F.Finding, h), n))

# reversing finding lists onto ys and joining them: acc's lengths onto ys's
law pick.rev:
  for acc: List<&2, List<&2, F.Finding>>
  for +ys: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, List.reverse.go(&2, List<&2, F.Finding>, acc, ys)))
    == pick.sum(acc, List.length(&2, F.Finding, List.concat(&2, F.Finding, ys))) : Nat}

def pick.rev(acc, ys):
  match acc:
    case Nil{}:
      {==}
    case Con{+h, t}:
      Equal.trans(Nat,
        List.length(&2, F.Finding, List.concat(&2, F.Finding, List.reverse.go(&2, List<&2, F.Finding>, t, h <> ys))),
        pick.sum(t, List.length(&2, F.Finding, List.concat(&2, F.Finding, h <> ys))),
        pick.sum(t, Nat.add(List.length(&2, F.Finding, h), List.length(&2, F.Finding, List.concat(&2, F.Finding, ys)))),
        pick.rev(t, h <> ys),
        Equal.cong(Nat, Nat, n => pick.sum(t, n), List.length(&2, F.Finding, List.concat(&2, F.Finding, h <> ys)),
          Nat.add(List.length(&2, F.Finding, h), List.length(&2, F.Finding, List.concat(&2, F.Finding, ys))),
          esc.app(h, List.concat(&2, F.Finding, ys))))

# one def's findings, exempt or walked
law pick.stop:
  for b: Bool
  for +body: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, b, [], _u => Pick.picks(body, name, path, False{})))
    == Bool.pick(Nat, b, 0n, Laws.pick.count(body, name, False{}, False{}, 0n)) : Nat}

def pick.stop(b, body, name, path):
  match b:
    case True{}:
      {==}
    case False{}:
      Laws.pick_walk_counts(body, name, path, False{}, False{}, 0n)

# pick's def walk: the findings gathered so far, then each def's
law pick.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Pick.check.go(ds, path, acc)) == pick.sum(acc, Laws.pick.defs(ds, path)) : Nat}

def pick.go(ds, path, acc):
  match ds:
    case Nil{}:
      pick.rev(acc, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +x = Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [], _u => Pick.picks(body, name, path, False{}))
      Equal.trans(Nat, List.length(&2, F.Finding, Pick.check.go(rest, path, x <> acc)),
        pick.sum(acc, Nat.add(List.length(&2, F.Finding, x), Laws.pick.defs(rest, path))),
        pick.sum(acc, Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n, Laws.pick.count(body, name, False{}, False{},
          0n)),
          Laws.pick.defs(rest, path))),
        pick.go(rest, path, x <> acc),
        Equal.cong(Nat, Nat, n => pick.sum(acc, Nat.add(n, Laws.pick.defs(rest, path))),
          List.length(&2, F.Finding, x), Bool.pick(Nat, Calls.exempt(path, sig), 0n, Laws.pick.count(body, name,
            False{}, False{}, 0n)),
          pick.stop(Calls.exempt(path, sig), body, name, path)))

def Laws.pick_counts(path, _text, _toks, tree, _bound, _items):
  pick.go(Calls.defs(tree), path, Nil{})

# `&&` or `||` in a stretch, to the rule and to the law, past one token
law strict.segk:
  for k: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for +rest: Tree.Node
  for ih: {Strict.seg_op(rest) == Laws.strict.ops(rest) : Bool}
  {Strict.seg_op(Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, rest})
    == Laws.strict.ops(Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, rest}) : Bool}

def strict.segk(k, t, _l, _c, rest, ih):
  match k:
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
      Equal.cong(Bool, Bool, x => Bool.or(Strict.logic(t), x), Strict.seg_op(rest), Laws.strict.ops(rest), ih)
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
      {==}

# `&&` or `||` in a stretch, to the rule and to the law
law strict.seg:
  for nn: Tree.Node
  {Strict.seg_op(nn) == Laws.strict.ops(nn) : Bool}

def strict.seg(nn):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, l, c}:
              strict.segk(k, t, l, c, rest, strict.seg(rest))
        case Tree.Group{open, kids, close}:
          strict.seg(rest)
        case Tree.Stmt{kind, kids, body}:
          strict.seg(rest)
        case Tree.NNil{}:
          strict.seg(rest)
        case Tree.NCons{x, y}:
          strict.seg(rest)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# the walk at a hot the law's count reaches another way
law strict.hot:
  for +nn: Tree.Node
  for +name: String
  for +path: String
  for +outer: Bool
  for +h1: Bool
  for +h2: Bool
  for e: {h1 == h2 : Bool}
  for ih: {List.length(&2, F.Finding, Strict.walk(nn, name, path, outer, h1))
    == Laws.strict.count(nn, name, outer, h1) : Nat}
  {List.length(&2, F.Finding, Strict.walk(nn, name, path, outer, h1)) == Laws.strict.count(nn, name, outer, h2) : Nat}

def strict.hot(nn, name, path, outer, h1, h2, e, ih):
  Equal.trans(Nat, List.length(&2, F.Finding, Strict.walk(nn, name, path, outer, h1)), Laws.strict.count(nn, name,
    outer, h1), Laws.strict.count(nn, name, outer, h2), ih,
    Equal.cong(Bool, Nat, hh => Laws.strict.count(nn, name, outer, hh), h1, h2, e))


# past a comma: the next stretch is hot in an operand or by its own `&&`/`||`
law strict.comma:
  for +rest: Tree.Node
  for +name: String
  for +path: String
  for +outer: Bool
  for ih: {List.length(&2, F.Finding, Strict.walk(rest, name, path, outer, Bool.or(outer, Strict.seg_op(rest))))
    == Laws.strict.count(rest, name, outer, Bool.or(outer, Strict.seg_op(rest))) : Nat}
  {List.length(&2, F.Finding, Strict.walk(rest, name, path, outer, Bool.or(outer, Strict.seg_op(rest))))
    == Laws.strict.count(rest, name, outer, Bool.or(outer, Laws.strict.ops(rest))) : Nat}

def strict.comma(rest, name, path, outer, ih):
  strict.hot(rest, name, path, outer, Bool.or(outer, Strict.seg_op(rest)), Bool.or(outer, Laws.strict.ops(rest)),
    Equal.cong(Bool, Bool, x => Bool.or(outer, x), Strict.seg_op(rest), Laws.strict.ops(rest), strict.seg(rest)), ih)

# past a `=>`: the lambda body is hot only by its own `&&`/`||`
law strict.lam:
  for +rest: Tree.Node
  for +name: String
  for +path: String
  for +outer: Bool
  for ih: {List.length(&2, F.Finding, Strict.walk(rest, name, path, outer, Strict.seg_op(rest)))
    == Laws.strict.count(rest, name, outer, Strict.seg_op(rest)) : Nat}
  {List.length(&2, F.Finding, Strict.walk(rest, name, path, outer, Strict.seg_op(rest)))
    == Laws.strict.count(rest, name, outer, Laws.strict.ops(rest)) : Nat}

def strict.lam(rest, name, path, outer, ih):
  strict.hot(rest, name, path, outer, Strict.seg_op(rest), Laws.strict.ops(rest), strict.seg(rest), ih)

# is the group after a name an operand: the stretch is hot, or it is the `(`
# of `Bool.and` or `Bool.or`
def strict.inner(+hot: Bool, +o: String, +t: String) -> Bool:
  Bool.or(hot, Bool.and(String.eq(o, "("), Bool.or(String.eq(t, "Bool.and"), String.eq(t, "Bool.or"))))

# a name, then a group: a finding when the name is the def, the group a
# `(` call and the stretch hot; the group an operand when the name is
# `Bool.and` or `Bool.or` or the stretch is hot
law strict.call:
  for +t: String
  for +l: U32
  for +c: U32
  for ok: Lex.TokKind
  for +o: String
  for ol: U32
  for oc: U32
  for +kids: Tree.Node
  for close: Maybe<&2, Lex.Tok>
  for +r2: Tree.Node
  for +name: String
  for +path: String
  for +outer: Bool
  for +hot: Bool
  for ik: {List.length(&2, F.Finding, Strict.walk(kids, name, path, strict.inner(hot, o, t), Bool.or(strict.inner(hot,
    o, t), Strict.seg_op(kids))))
      == Laws.strict.count(kids, name, strict.inner(hot, o, t), Bool.or(strict.inner(hot, o, t),
        Strict.seg_op(kids))) : Nat}
  for ir: {List.length(&2, F.Finding, Strict.walk(r2, name, path, outer, hot))
    == Laws.strict.count(r2, name, outer, hot) : Nat}
  {List.length(&2, F.Finding, Strict.walk(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}},
    Tree.NCons{Tree.Group{Lex.Tok{ok, o, ol, oc}, kids, close}, r2}}, name, path, outer, hot))
      == Laws.strict.count(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{ok, o, ol,
        oc}, kids, close}, r2}}, name, outer, hot) : Nat}

def strict.call(t, l, c, _ok, o, _ol, _oc, kids, _close, r2, name, path, outer, hot, ik, ir):
  +call = String.eq(o, "(")
  +inner = strict.inner(hot, o, t)
  +hk = Bool.or(inner, Strict.seg_op(kids))
  +fk = Strict.walk(kids, name, path, inner, hk)
  +fr = Strict.walk(r2, name, path, outer, hot)
  +ck = Laws.strict.count(kids, name, inner, Bool.or(inner, Laws.strict.ops(kids)))
  +cr = Laws.strict.count(r2, name, outer, hot)
  nat.pick(Bool.and(Bool.and(call, String.eq(t, name)), hot),
    F.Finding{path, l, c, U32.from_nat(String.length(name)), "strict",
      name ++ " recurses inside Bool.and or Bool.or, so both sides always run and there is no short-circuit; bind the call above."},
    List.concat(&2, F.Finding, [fk, fr]), Nat.add(ck, cr),
    pick.join(fk, List.append(&2, F.Finding, fr, Nil{}), ck, cr,
      strict.hot(kids, name, path, inner, hk, Bool.or(inner, Laws.strict.ops(kids)),
        Equal.cong(Bool, Bool, x => Bool.or(inner, x), Strict.seg_op(kids), Laws.strict.ops(kids),
          strict.seg(kids)), ik),
      pick.last(fr, cr, ir)))

def Laws.strict_walk_counts(nn, name, path, outer, hot):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, +l, +c}:
              match k:
                case Lex.TName{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TUpper{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TDotted{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TWild{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TKey{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TNum{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TStr{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TChar{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TComment{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TSpace{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TNewline{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TOp{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TColon{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TEq{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TBind{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TArrow{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TLam{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                                Strict.seg_op(rest)))
                        case Tree.Leaf{x}:
                          strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                            Strict.seg_op(rest)))
                        case Tree.Stmt{kind, kids, body}:
                          strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                            Strict.seg_op(rest)))
                        case Tree.NNil{}:
                          strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                            Strict.seg_op(rest)))
                        case Tree.NCons{x, y}:
                          strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                            Strict.seg_op(rest)))
                    case Tree.Leaf{x}:
                      strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                        Strict.seg_op(rest)))
                    case Tree.Group{open, kids, close}:
                      strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                        Strict.seg_op(rest)))
                    case Tree.Stmt{kind, kids, body}:
                      strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                        Strict.seg_op(rest)))
                    case Tree.NNil{}:
                      strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                        Strict.seg_op(rest)))
                case Lex.TAll{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TAmp{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TOpen{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TClose{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TComma{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                                Bool.or(outer, Strict.seg_op(rest))))
                        case Tree.Leaf{x}:
                          strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                            Bool.or(outer, Strict.seg_op(rest))))
                        case Tree.Stmt{kind, kids, body}:
                          strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                            Bool.or(outer, Strict.seg_op(rest))))
                        case Tree.NNil{}:
                          strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                            Bool.or(outer, Strict.seg_op(rest))))
                        case Tree.NCons{x, y}:
                          strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                            Bool.or(outer, Strict.seg_op(rest))))
                    case Tree.Leaf{x}:
                      strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                        Bool.or(outer, Strict.seg_op(rest))))
                    case Tree.Group{open, kids, close}:
                      strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                        Bool.or(outer, Strict.seg_op(rest))))
                    case Tree.Stmt{kind, kids, body}:
                      strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                        Bool.or(outer, Strict.seg_op(rest))))
                    case Tree.NNil{}:
                      strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                        Bool.or(outer, Strict.seg_op(rest))))
        case Tree.Group{open, +kids, close}:
          +fr = Strict.walk(rest, name, path, outer, hot)
          +hk = Bool.or(hot, Strict.seg_op(kids))
          pick.join(Strict.walk(kids, name, path, hot, hk), List.append(&2, F.Finding, fr, Nil{}),
            Laws.strict.count(kids, name, hot, Bool.or(hot, Laws.strict.ops(kids))), Laws.strict.count(rest, name,
              outer, hot),
            strict.hot(kids, name, path, hot, hk, Bool.or(hot, Laws.strict.ops(kids)),
              Equal.cong(Bool, Bool, x => Bool.or(hot, x), Strict.seg_op(kids), Laws.strict.ops(kids),
                strict.seg(kids)),
              Laws.strict_walk_counts(kids, name, path, hot, hk)),
            pick.last(fr, Laws.strict.count(rest, name, outer, hot), Laws.strict_walk_counts(rest, name, path, outer,
              hot)))
        case Tree.Stmt{kind, +kids, +body}:
          +fb = Strict.walk(body, name, path, False{}, False{})
          +fr = Strict.walk(rest, name, path, outer, hot)
          +cb = Laws.strict.count(body, name, False{}, False{})
          +cr = Laws.strict.count(rest, name, outer, hot)
          pick.join(Strict.walk(kids, name, path, False{}, Strict.seg_op(kids)),
            List.append(&2, F.Finding, fb, List.append(&2, F.Finding, fr, Nil{})),
            Laws.strict.count(kids, name, False{}, Laws.strict.ops(kids)), Nat.add(cb, cr),
            strict.hot(kids, name, path, False{}, Strict.seg_op(kids), Laws.strict.ops(kids), strict.seg(kids),
              Laws.strict_walk_counts(kids, name, path, False{}, Strict.seg_op(kids))),
            pick.join(fb, List.append(&2, F.Finding, fr, Nil{}), cb, cr, Laws.strict_walk_counts(body, name, path,
              False{}, False{}),
              pick.last(fr, cr, Laws.strict_walk_counts(rest, name, path, outer, hot))))
        case Tree.NNil{}:
          Laws.strict_walk_counts(rest, name, path, outer, hot)
        case Tree.NCons{x, y}:
          Laws.strict_walk_counts(rest, name, path, outer, hot)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# one def's findings, exempt or walked
law strict.stop:
  for +b: Bool
  for +body: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, b, [], _u => Strict.walk(body, name, path, False{},
    False{})))
    == Bool.pick(Nat, b, 0n, Laws.strict.count(body, name, False{}, False{})) : Nat}

def strict.stop(b, body, name, path):
  match b:
    case True{}:
      {==}
    case False{}:
      Laws.strict_walk_counts(body, name, path, False{}, False{})

# strict's def walk: the findings gathered so far, then each def's
law strict.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Strict.check.go(ds, path, acc)) == pick.sum(acc, Laws.strict.defs(ds, path)) : Nat}

def strict.go(ds, path, acc):
  match ds:
    case Nil{}:
      pick.rev(acc, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +x = Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [], _u => Strict.walk(body, name, path, False{},
        False{}))
      +cb = Bool.pick(Nat, Calls.exempt(path, sig), 0n, Laws.strict.count(body, name, False{}, False{}))
      Equal.trans(Nat, List.length(&2, F.Finding, Strict.check.go(rest, path, x <> acc)),
        pick.sum(acc, Nat.add(List.length(&2, F.Finding, x), Laws.strict.defs(rest, path))),
        pick.sum(acc, Nat.add(cb, Laws.strict.defs(rest, path))),
        strict.go(rest, path, x <> acc),
        Equal.cong(Nat, Nat, n => pick.sum(acc, Nat.add(n, Laws.strict.defs(rest, path))),
          List.length(&2, F.Finding, x), cb, strict.stop(Calls.exempt(path, sig), body, name, path)))

def Laws.strict_counts(path, _text, _toks, tree, _bound, _items):
  strict.go(Calls.defs(tree), path, Nil{})
