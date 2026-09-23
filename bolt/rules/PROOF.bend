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
