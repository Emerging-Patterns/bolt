# bolt/rules: the proofs. `bend PROOF.bend` is the gate.
import Base
import ../../syntax/lex.bend as Lex
import ../finding.bend as F
import ./tokens.bend as T
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
import ./correctness/foreign.bend as Foreign
import ./correctness/arms.bend as Arms
import ./correctness/twice.bend as Twice
import ./laws/closed.bend as Closed
import ./suspicious/unused.bend as Unused
import ./suspicious/fuel.bend as FuelRule
import ./style/wrap.bend as Wrap
import ./laws/law.bend as Coverage
import ./laws/unsafe.bend as Unsafe
import ./imports.bend as Imports
import ./digest.bend as Digest
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

# tail (BOLT-RULE-P001): the walk counts the self-calls Laws.tail.count
# counts, and the def walk sums them over the defs Laws.tail.total keeps.

# a pick between no findings and a list counts 0 or the list's count
law tail.drop:
  for b: Bool
  for -xs: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, xs) == m : Nat}
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, b, [], xs)) == Bool.pick(Nat, b, 0n, m) : Nat}

def tail.drop(b, _xs, _m, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# adding nothing leaves a Nat as it was
law tail.zero:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}

def tail.zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, tail.zero(p))

# a successor on the right comes out in front
law tail.succ:
  for a: Nat
  for -b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def tail.succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 1n+b), 1n+Nat.add(p, b), tail.succ(p, b))

# addition commutes
law tail.comm:
  for a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

def tail.comm(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, tail.zero(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, b), Nat.add(b, p), tail.comm(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), tail.succ(b, p)))

# addition associates
law tail.assoc:
  for a: Nat
  for -b: Nat
  for -c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def tail.assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), tail.assoc(p, b, c))

# two joined finding lists count the sum of theirs
law tail.cat2:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b]))
    == Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, b)) : Nat}

def tail.cat2(a, b):
  Equal.trans(Nat,
    List.length(&2, F.Finding, List.append(&2, F.Finding, a, List.append(&2, F.Finding, b, Nil{}))),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, List.append(&2, F.Finding, b, Nil{}))),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, b)),
    esc.app(a, List.append(&2, F.Finding, b, Nil{})),
    Equal.cong(Nat, Nat, x => Nat.add(List.length(&2, F.Finding, a), x),
      List.length(&2, F.Finding, List.append(&2, F.Finding, b, Nil{})), List.length(&2, F.Finding, b),
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, b, Nil{})),
        Nat.add(List.length(&2, F.Finding, b), 0n), List.length(&2, F.Finding, b),
        esc.app(b, Nil{}), tail.zero(List.length(&2, F.Finding, b)))))

# three joined finding lists count the sum of theirs
law tail.cat3:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for +c: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c]))
    == Nat.add(List.length(&2, F.Finding, a),
      Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c))) : Nat}

def tail.cat3(a, b, c):
  Equal.trans(Nat,
    List.length(&2, F.Finding, List.append(&2, F.Finding, a, List.concat(&2, F.Finding, [b, c]))),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, List.concat(&2, F.Finding, [b, c]))),
    Nat.add(List.length(&2, F.Finding, a),
      Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c))),
    esc.app(a, List.concat(&2, F.Finding, [b, c])),
    Equal.cong(Nat, Nat, x => Nat.add(List.length(&2, F.Finding, a), x),
      List.length(&2, F.Finding, List.concat(&2, F.Finding, [b, c])),
      Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c)), tail.cat2(b, c)))

# and with False is False
law tail.andf:
  for x: Bool
  {Bool.and(x, False{}) == False{} : Bool}

def tail.andf(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# a head that is not a group after a name: no tail-call test holds
law tail.nongroup:
  for +t: String
  for +name: String
  {Bool.and(String.eq(t, name), False{}) == False{} : Bool}

def tail.nongroup(t, name):
  tail.andf(String.eq(t, name))

# the rule's tail-call test is the law's whole-chain test
law tail.bare:
  for kids: Tree.Node
  for +name: String
  {Tail.bare(kids, name) == Laws.tail.whole(kids, name) : Bool}

def tail.bare(kids, name):
  match kids:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Leaf{Lex.Tok{k, +t, l, c}}:
          match r:
            case Tree.NCons{g, +r2}:
              match g:
                case Tree.Group{Lex.Tok{k2, o, l2, c2}, gk, cl}:
                  match r2:
                    case Tree.Leaf{y}:
                      {==}
                    case Tree.Group{e, f, i}:
                      {==}
                    case Tree.Stmt{e, f, i}:
                      {==}
                    case Tree.NNil{}:
                      {==}
                    case Tree.NCons{e, f}:
                      {==}
                case Tree.Leaf{x}:
                  match r2:
                    case Tree.Leaf{y}:
                      {==}
                    case Tree.Group{e, f, i}:
                      {==}
                    case Tree.Stmt{e, f, i}:
                      {==}
                    case Tree.NNil{}:
                      tail.nongroup(t, name)
                    case Tree.NCons{e, f}:
                      {==}
                case Tree.Stmt{a, b, d}:
                  match r2:
                    case Tree.Leaf{y}:
                      {==}
                    case Tree.Group{e, f, i}:
                      {==}
                    case Tree.Stmt{e, f, i}:
                      {==}
                    case Tree.NNil{}:
                      tail.nongroup(t, name)
                    case Tree.NCons{e, f}:
                      {==}
                case Tree.NNil{}:
                  match r2:
                    case Tree.Leaf{y}:
                      {==}
                    case Tree.Group{e, f, i}:
                      {==}
                    case Tree.Stmt{e, f, i}:
                      {==}
                    case Tree.NNil{}:
                      tail.nongroup(t, name)
                    case Tree.NCons{e, f}:
                      {==}
                case Tree.NCons{a, b}:
                  match r2:
                    case Tree.Leaf{y}:
                      {==}
                    case Tree.Group{e, f, i}:
                      {==}
                    case Tree.Stmt{e, f, i}:
                      {==}
                    case Tree.NNil{}:
                      tail.nongroup(t, name)
                    case Tree.NCons{e, f}:
                      {==}
            case Tree.Leaf{x}:
              {==}
            case Tree.Group{a, b, d}:
              {==}
            case Tree.Stmt{a, b, d}:
              {==}
            case Tree.NNil{}:
              {==}
        case Tree.Group{a, b, d}:
          {==}
        case Tree.Stmt{a, b, d}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{a, b}:
          {==}
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{a, b, d}:
      {==}
    case Tree.Stmt{a, b, d}:
      {==}
    case Tree.NNil{}:
      {==}

# a self-call site, a name then a `(` group, onto a rest the law holds for
law tail.call:
  for k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for k2: Lex.TokKind
  for +o: String
  for l2: U32
  for c2: U32
  for +kids: Tree.Node
  for cl: Maybe<&2, Lex.Tok>
  for +rest: Tree.Node
  for +name: String
  for +path: String
  for +skip: Bool
  for ih1: {List.length(&2, F.Finding, Tail.walk(kids, name, path, False{})) == Laws.tail.count(kids, name, False{})
    : Nat}
  for ih2: {List.length(&2, F.Finding, Tail.walk(rest, name, path, False{})) == Laws.tail.count(rest, name, False{})
    : Nat}
  {List.length(&2, F.Finding,
    Tail.walk(Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}},
      Tree.NCons{Tree.Group{Lex.Tok{k2, o, l2, c2}, kids, cl}, rest}}, name, path, skip))
    == Laws.tail.count(Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}},
      Tree.NCons{Tree.Group{Lex.Tok{k2, o, l2, c2}, kids, cl}, rest}}, name, skip) : Nat}

def tail.call(_k, t, l, c, _k2, o, _l2, _c2, kids, _cl, rest, name, path, skip, ih1, ih2):
  +pk = Bool.and(String.eq(o, "("), String.eq(t, "Bool.pick"))
  +inside = Bool.pick(List<&2, F.Finding>, pk, [], Tail.walk(kids, name, path, False{}))
  +after = Tail.walk(rest, name, path, False{})
  +m = Nat.add(Bool.pick(Nat, pk, 0n, Laws.tail.count(kids, name, False{})), Laws.tail.count(rest, name, False{}))
  nat.pick(Bool.and(Bool.and(String.eq(o, "("), String.eq(t, name)), Bool.not(skip)),
    F.Finding{path, l, c, U32.from_nat(String.length(name)), "tail",
      name ++ " is not a tail call, so a long list or string overflows the JS lane stack; carry an accumulator."},
    List.concat(&2, F.Finding, [inside, after]), m,
    Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [inside, after])),
      Nat.add(List.length(&2, F.Finding, inside), List.length(&2, F.Finding, after)), m,
      tail.cat2(inside, after),
      esc.add(List.length(&2, F.Finding, inside), Bool.pick(Nat, pk, 0n, Laws.tail.count(kids, name, False{})),
        List.length(&2, F.Finding, after), Laws.tail.count(rest, name, False{}),
        tail.drop(pk, Tail.walk(kids, name, path, False{}), Laws.tail.count(kids, name, False{}), ih1), ih2)))

# a group onto a rest the law holds for
law tail.grp:
  for open: Lex.Tok
  for +kids: Tree.Node
  for close: Maybe<&2, Lex.Tok>
  for +rest: Tree.Node
  for +name: String
  for +path: String
  for skip: Bool
  for ih1: {List.length(&2, F.Finding, Tail.walk(kids, name, path, False{})) == Laws.tail.count(kids, name, False{})
    : Nat}
  for ih2: {List.length(&2, F.Finding, Tail.walk(rest, name, path, False{})) == Laws.tail.count(rest, name, False{})
    : Nat}
  {List.length(&2, F.Finding, Tail.walk(Tree.NCons{Tree.Group{open, kids, close}, rest}, name, path, skip))
    == Laws.tail.count(Tree.NCons{Tree.Group{open, kids, close}, rest}, name, skip) : Nat}

def tail.grp(_open, kids, _close, rest, name, path, _skip, ih1, ih2):
  +a = Tail.walk(kids, name, path, False{})
  +b = Tail.walk(rest, name, path, False{})
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b])),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, b)),
    Nat.add(Laws.tail.count(kids, name, False{}), Laws.tail.count(rest, name, False{})),
    tail.cat2(a, b),
    esc.add(List.length(&2, F.Finding, a), Laws.tail.count(kids, name, False{}),
      List.length(&2, F.Finding, b), Laws.tail.count(rest, name, False{}), ih1, ih2))

# a statement onto a rest the law holds for
law tail.stmt:
  for kind: Tree.StmtKind
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +name: String
  for +path: String
  for skip: Bool
  for ih1: {List.length(&2, F.Finding, Tail.walk(kids, name, path, Tail.bare(kids, name)))
    == Laws.tail.count(kids, name, Tail.bare(kids, name)) : Nat}
  for ih2: {List.length(&2, F.Finding, Tail.walk(body, name, path, False{})) == Laws.tail.count(body, name, False{})
    : Nat}
  for ih3: {List.length(&2, F.Finding, Tail.walk(rest, name, path, False{})) == Laws.tail.count(rest, name, False{})
    : Nat}
  {List.length(&2, F.Finding, Tail.walk(Tree.NCons{Tree.Stmt{kind, kids, body}, rest}, name, path, skip))
    == Laws.tail.count(Tree.NCons{Tree.Stmt{kind, kids, body}, rest}, name, skip) : Nat}

def tail.stmt(_kind, kids, body, rest, name, path, _skip, ih1, ih2, ih3):
  +a = Tail.walk(kids, name, path, Tail.bare(kids, name))
  +b = Tail.walk(body, name, path, False{})
  +r = Tail.walk(rest, name, path, False{})
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, r])),
    Nat.add(List.length(&2, F.Finding, a), Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, r))),
    Nat.add(Laws.tail.count(kids, name, Laws.tail.whole(kids, name)),
      Nat.add(Laws.tail.count(body, name, False{}), Laws.tail.count(rest, name, False{}))),
    tail.cat3(a, b, r),
    esc.add(List.length(&2, F.Finding, a), Laws.tail.count(kids, name, Laws.tail.whole(kids, name)),
      Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, r)),
      Nat.add(Laws.tail.count(body, name, False{}), Laws.tail.count(rest, name, False{})),
      Equal.trans(Nat, List.length(&2, F.Finding, a), Laws.tail.count(kids, name, Tail.bare(kids, name)),
        Laws.tail.count(kids, name, Laws.tail.whole(kids, name)), ih1,
        Equal.cong(Bool, Nat, z => Laws.tail.count(kids, name, z), Tail.bare(kids, name),
          Laws.tail.whole(kids, name), tail.bare(kids, name))),
      esc.add(List.length(&2, F.Finding, b), Laws.tail.count(body, name, False{}),
        List.length(&2, F.Finding, r), Laws.tail.count(rest, name, False{}), ih2, ih3)))

def Laws.tail_walk_counts(nn, name, path, skip):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{Lex.Tok{k, t, l, c}}:
          match rest:
            case Tree.NCons{h2, +r2}:
              match h2:
                case Tree.Group{Lex.Tok{k2, o, l2, c2}, +kids, cl}:
                  tail.call(k, t, l, c, k2, o, l2, c2, kids, cl, r2, name, path, skip,
                    Laws.tail_walk_counts(kids, name, path, False{}), Laws.tail_walk_counts(r2, name, path, False{}))
                case Tree.Leaf{x}:
                  Laws.tail_walk_counts(rest, name, path, False{})
                case Tree.Stmt{a, b, d}:
                  Laws.tail_walk_counts(rest, name, path, False{})
                case Tree.NNil{}:
                  Laws.tail_walk_counts(rest, name, path, False{})
                case Tree.NCons{a, b}:
                  Laws.tail_walk_counts(rest, name, path, False{})
            case Tree.Leaf{x}:
              Laws.tail_walk_counts(rest, name, path, False{})
            case Tree.Group{a, b, d}:
              Laws.tail_walk_counts(rest, name, path, False{})
            case Tree.Stmt{a, b, d}:
              Laws.tail_walk_counts(rest, name, path, False{})
            case Tree.NNil{}:
              Laws.tail_walk_counts(rest, name, path, False{})
        case Tree.Group{open, +kids, close}:
          tail.grp(open, kids, close, rest, name, path, skip,
            Laws.tail_walk_counts(kids, name, path, False{}), Laws.tail_walk_counts(rest, name, path, False{}))
        case Tree.Stmt{kind, +kids, +body}:
          tail.stmt(kind, kids, body, rest, name, path, skip,
            Laws.tail_walk_counts(kids, name, path, Tail.bare(kids, name)),
            Laws.tail_walk_counts(body, name, path, False{}), Laws.tail_walk_counts(rest, name, path, False{}))
        case Tree.NNil{}:
          Laws.tail_walk_counts(rest, name, path, False{})
        case Tree.NCons{a, b}:
          Laws.tail_walk_counts(rest, name, path, False{})
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{a, b, d}:
      {==}
    case Tree.Stmt{a, b, d}:
      {==}
    case Tree.NNil{}:
      {==}

# the total count of a list of finding lists
def tail.lens(xss: List<&2, List<&2, F.Finding>>) -> Nat:
  match xss:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(List.length(&2, F.Finding, h), tail.lens(t))

# joined finding lists count what they count apart
law tail.flat:
  for xss: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, xss)) == tail.lens(xss) : Nat}

def tail.flat(xss):
  match xss:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, h, List.concat(&2, F.Finding, t))),
        Nat.add(List.length(&2, F.Finding, h), List.length(&2, F.Finding, List.concat(&2, F.Finding, t))),
        Nat.add(List.length(&2, F.Finding, h), tail.lens(t)),
        esc.app(h, List.concat(&2, F.Finding, t)),
        Equal.cong(Nat, Nat, x => Nat.add(List.length(&2, F.Finding, h), x),
          List.length(&2, F.Finding, List.concat(&2, F.Finding, t)), tail.lens(t), tail.flat(t)))

# reversing finding lists onto an accumulator keeps their total count
law tail.rev:
  for xs: List<&2, List<&2, F.Finding>>
  for +acc: List<&2, List<&2, F.Finding>>
  {tail.lens(List.reverse.go(&2, List<&2, F.Finding>, xs, acc)) == Nat.add(tail.lens(xs), tail.lens(acc)) : Nat}

def tail.rev(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat, tail.lens(List.reverse.go(&2, List<&2, F.Finding>, t, h <> acc)),
        Nat.add(tail.lens(t), Nat.add(List.length(&2, F.Finding, h), tail.lens(acc))),
        Nat.add(Nat.add(List.length(&2, F.Finding, h), tail.lens(t)), tail.lens(acc)),
        tail.rev(t, h <> acc),
        Equal.trans(Nat, Nat.add(tail.lens(t), Nat.add(List.length(&2, F.Finding, h), tail.lens(acc))),
          Nat.add(Nat.add(tail.lens(t), List.length(&2, F.Finding, h)), tail.lens(acc)),
          Nat.add(Nat.add(List.length(&2, F.Finding, h), tail.lens(t)), tail.lens(acc)),
          Equal.sym(Nat, Nat.add(Nat.add(tail.lens(t), List.length(&2, F.Finding, h)), tail.lens(acc)),
            Nat.add(tail.lens(t), Nat.add(List.length(&2, F.Finding, h), tail.lens(acc))),
            tail.assoc(tail.lens(t), List.length(&2, F.Finding, h), tail.lens(acc))),
          Equal.cong(Nat, Nat, x => Nat.add(x, tail.lens(acc)),
            Nat.add(tail.lens(t), List.length(&2, F.Finding, h)),
            Nat.add(List.length(&2, F.Finding, h), tail.lens(t)),
            tail.comm(tail.lens(t), List.length(&2, F.Finding, h)))))

# a def's findings count the walk's when its guard keeps it, else none
law tail.stop:
  for b: Bool
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(b), [], _u => more))
    == Bool.pick(Nat, b, m, 0n) : Nat}

def tail.stop(b, _more, _m, ih):
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# the def walk counts what it has gathered and what the defs left hold
law tail.defs:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Tail.check.go(ds, path, acc))
    == Nat.add(tail.lens(acc), Laws.tail.total(ds, path)) : Nat}

def tail.defs(ds, path, acc):
  match ds:
    case Nil{}:
      Equal.trans(Nat,
        List.length(&2, F.Finding, List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))),
        tail.lens(List.reverse(&2, List<&2, F.Finding>, acc)), Nat.add(tail.lens(acc), 0n),
        tail.flat(List.reverse(&2, List<&2, F.Finding>, acc)), tail.rev(acc, Nil{}))
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +keep = Bool.and(Calls.seq(sig), Bool.not(Calls.exempt(path, sig)))
      +xs = Lazy.stop(List<&2, F.Finding>, Bool.not(keep), [], _u => Tail.walk(body, name, path, False{}))
      +cnt = Bool.pick(Nat, keep, Laws.tail.count(body, name, False{}), 0n)
      +lx = List.length(&2, F.Finding, xs)
      +tot = Laws.tail.total(rest, path)
      +la = tail.lens(acc)
      Equal.trans(Nat, List.length(&2, F.Finding, Tail.check.go(rest, path, xs <> acc)),
        Nat.add(Nat.add(lx, la), tot), Nat.add(la, Nat.add(cnt, tot)),
        tail.defs(rest, path, xs <> acc),
        Equal.trans(Nat, Nat.add(Nat.add(lx, la), tot), Nat.add(Nat.add(la, lx), tot), Nat.add(la, Nat.add(cnt, tot)),
          Equal.cong(Nat, Nat, x => Nat.add(x, tot), Nat.add(lx, la), Nat.add(la, lx), tail.comm(lx, la)),
          Equal.trans(Nat, Nat.add(Nat.add(la, lx), tot), Nat.add(la, Nat.add(lx, tot)), Nat.add(la, Nat.add(cnt, tot)),
            tail.assoc(la, lx, tot),
            Equal.cong(Nat, Nat, x => Nat.add(la, Nat.add(x, tot)), lx, cnt,
              tail.stop(keep, Tail.walk(body, name, path, False{}), Laws.tail.count(body, name, False{}),
                Laws.tail_walk_counts(body, name, path, False{}))))))

def Laws.tail_counts(path, _text, _toks, tree, _bound, _items):
  tail.defs(Calls.defs(tree), path, Nil{})

# foreign (BOLT-RULE-C010): the rule's lanes are the law's imports and
# suffixes, its message is empty exactly when the def is not bad, and its
# header test is the law's.

# the early exits of the header test are the plain and and or
law foreign.hd:
  for a: Bool
  for b: Bool
  for -x: Bool
  for -y: Bool
  for ih: {x == y : Bool}
  {Lazy.stop(Bool, Bool.not(a), False{}, _u => Lazy.or_else(b, _v => x)) == Bool.and(a, Bool.or(b, y)) : Bool}

def foreign.hd(a, b, _x, _y, ih):
  match a:
    case False{}:
      {==}
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          ih

def Laws.foreign_native(lines):
  match lines:
    case Nil{}:
      {==}
    case Con{+line, +rest}:
      foreign.hd(String.starts_with(line, "#"), String.eq(line, "# lanes: native"), Foreign.native_only.go(rest),
        Laws.foreign.headed(rest), Laws.foreign_native(rest))

# a body with no more imports ends with the lanes gathered so far
law foreign.done:
  for cc: Bool
  for js: Bool
  {Some{Foreign.Lanes{cc, js}} == Some{Foreign.Lanes{Bool.or(cc, False{}), Bool.or(js, False{})}}
    : Maybe<&2, Foreign.Lanes>}

def foreign.done(cc, js):
  match cc:
    case True{}:
      match js:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match js:
        case True{}:
          {==}
        case False{}:
          {==}

# gathering a lane early or late gives the same lanes
law foreign.shift:
  for +i: Bool
  for a: Bool
  for +b: Bool
  for +c: Bool
  for d: Bool
  for +e: Bool
  for +f: Bool
  {Bool.pick(Maybe<&2, Foreign.Lanes>, i,
      Some{Foreign.Lanes{Bool.or(Bool.or(a, b), c), Bool.or(Bool.or(d, e), f)}}, None{})
    == Bool.pick(Maybe<&2, Foreign.Lanes>, i,
      Some{Foreign.Lanes{Bool.or(a, Bool.or(b, c)), Bool.or(d, Bool.or(e, f))}}, None{}) : Maybe<&2, Foreign.Lanes>}

def foreign.shift(_i, a, _b, _c, d, _e, _f):
  match a:
    case True{}:
      match d:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match d:
        case True{}:
          {==}
        case False{}:
          {==}

# the rule's lanes of the imports after the first, onto the lanes so far
law foreign.lgo:
  for body: Tree.Node
  for +cc: Bool
  for +js: Bool
  {Foreign.lanes.go(body, cc, js)
    == Bool.pick(Maybe<&2, Foreign.Lanes>, Laws.foreign.imports(body),
      Some{Foreign.Lanes{Bool.or(cc, Laws.foreign.has(body, ".c\"")), Bool.or(js, Laws.foreign.has(body, ".js\""))}},
      None{}) : Maybe<&2, Foreign.Lanes>}

def foreign.lgo(body, cc, js):
  match body:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{kind, +kids, ib}:
          match kind:
            case Tree.SImport{}:
              +ec = String.ends_with(Foreign.target(kids), ".c\"")
              +ej = String.ends_with(Foreign.target(kids), ".js\"")
              Equal.trans(Maybe<&2, Foreign.Lanes>, Foreign.lanes.go(rest, Bool.or(cc, ec), Bool.or(js, ej)),
                Bool.pick(Maybe<&2, Foreign.Lanes>, Laws.foreign.imports(rest),
                  Some{Foreign.Lanes{Bool.or(Bool.or(cc, ec), Laws.foreign.has(rest, ".c\"")),
                    Bool.or(Bool.or(js, ej), Laws.foreign.has(rest, ".js\""))}}, None{}),
                Bool.pick(Maybe<&2, Foreign.Lanes>, Laws.foreign.imports(rest),
                  Some{Foreign.Lanes{Bool.or(cc, Bool.or(ec, Laws.foreign.has(rest, ".c\""))),
                    Bool.or(js, Bool.or(ej, Laws.foreign.has(rest, ".js\"")))}}, None{}),
                foreign.lgo(rest, Bool.or(cc, ec), Bool.or(js, ej)),
                foreign.shift(Laws.foreign.imports(rest), cc, ec, Laws.foreign.has(rest, ".c\""), js, ej,
                  Laws.foreign.has(rest, ".js\"")))
            case Tree.SDef{}:
              {==}
            case Tree.SType{}:
              {==}
            case Tree.SLaw{}:
              {==}
            case Tree.SCase{}:
              {==}
            case Tree.SFor{}:
              {==}
            case Tree.SLet{}:
              {==}
            case Tree.STerm{}:
              {==}
        case Tree.Leaf{x}:
          {==}
        case Tree.Group{a, b, d}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{a, b}:
          {==}
    case Tree.Leaf{x}:
      foreign.done(cc, js)
    case Tree.Group{a, b, d}:
      foreign.done(cc, js)
    case Tree.Stmt{a, b, d}:
      foreign.done(cc, js)
    case Tree.NNil{}:
      foreign.done(cc, js)

# the rule's lanes of a def's body: the law's lanes of a foreign def, else none
law foreign.lanes:
  for body: Tree.Node
  {Foreign.lanes(body)
    == Bool.pick(Maybe<&2, Foreign.Lanes>, Laws.foreign.only(body),
      Some{Foreign.Lanes{Laws.foreign.has(body, ".c\""), Laws.foreign.has(body, ".js\"")}}, None{})
    : Maybe<&2, Foreign.Lanes>}

def foreign.lanes(body):
  match body:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{kind, +kids, ib}:
          match kind:
            case Tree.SImport{}:
              foreign.lgo(rest, String.ends_with(Foreign.target(kids), ".c\""),
                String.ends_with(Foreign.target(kids), ".js\""))
            case Tree.SDef{}:
              {==}
            case Tree.SType{}:
              {==}
            case Tree.SLaw{}:
              {==}
            case Tree.SCase{}:
              {==}
            case Tree.SFor{}:
              {==}
            case Tree.SLet{}:
              {==}
            case Tree.STerm{}:
              {==}
        case Tree.Leaf{x}:
          {==}
        case Tree.Group{a, b, d}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{a, b}:
          {==}
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{a, b, d}:
      {==}
    case Tree.Stmt{a, b, d}:
      {==}
    case Tree.NNil{}:
      {==}

# the rule's message is empty exactly when the lanes are not bad
law foreign.lack:
  for o: Bool
  for c: Bool
  for j: Bool
  for native: Bool
  for +nm: String
  {String.is_empty(Foreign.lack(Bool.pick(Maybe<&2, Foreign.Lanes>, o, Some{Foreign.Lanes{c, j}}, None{}), native, nm))
    == Bool.not(Bool.and(o, Bool.or(Bool.and(c, Bool.and(Bool.not(j), Bool.not(native))), Bool.and(j, Bool.not(c)))))
    : Bool}

def foreign.lack(o, c, j, native, _nm):
  match o:
    case False{}:
      {==}
    case True{}:
      match c:
        case True{}:
          match j:
            case True{}:
              match native:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match native:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match j:
            case True{}:
              match native:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match native:
                case True{}:
                  {==}
                case False{}:
                  {==}

# a finding in front unless the message is empty adds one to the count
law foreign.at2:
  for bad: Bool
  for -x: F.Finding
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, Bool.not(bad), more, x <> more))
    == Bool.pick(Nat, bad, 1n+m, m) : Nat}

def foreign.at2(bad, _x, more, m, ih):
  match bad:
    case True{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
    case False{}:
      ih

# a top-level def onto a rest the law holds for
law foreign.def:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +native: Bool
  for +path: String
  for ih: {List.length(&2, F.Finding, Foreign.check.go(rest, native, path)) == Laws.foreign.count(rest, native) : Nat}
  {List.length(&2, F.Finding, Foreign.check.go(Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest}, native, path))
    == Laws.foreign.count(Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest}, native) : Nat}

def foreign.def(kids, body, rest, native, path, ih):
  +nm = Foreign.name.of(Bind.declared(kids))
  +msg = Foreign.lack(Foreign.lanes(body), native, nm)
  +more = Foreign.check.go(rest, native, path)
  +bad = Laws.foreign.bad(body, native)
  +x = {F.Finding{path, Tree.line(kids), Tree.col(kids), 0, "foreign", msg} : F.Finding}
  +e = Equal.trans(Bool, String.is_empty(msg),
    String.is_empty(Foreign.lack(Bool.pick(Maybe<&2, Foreign.Lanes>, Laws.foreign.only(body),
      Some{Foreign.Lanes{Laws.foreign.has(body, ".c\""), Laws.foreign.has(body, ".js\"")}}, None{}), native, nm)),
    Bool.not(bad),
    Equal.cong(Maybe<&2, Foreign.Lanes>, Bool, z => String.is_empty(Foreign.lack(z, native, nm)), Foreign.lanes(body),
      Bool.pick(Maybe<&2, Foreign.Lanes>, Laws.foreign.only(body),
        Some{Foreign.Lanes{Laws.foreign.has(body, ".c\""), Laws.foreign.has(body, ".js\"")}}, None{}),
      foreign.lanes(body)),
    foreign.lack(Laws.foreign.only(body), Laws.foreign.has(body, ".c\""), Laws.foreign.has(body, ".js\""), native, nm))
  Equal.trans(Nat, List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, String.is_empty(msg), more, x <> more)),
    List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, Bool.not(bad), more, x <> more)),
    Bool.pick(Nat, bad, 1n+Laws.foreign.count(rest, native), Laws.foreign.count(rest, native)),
    Equal.cong(Bool, Nat, z => List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, z, more, x <> more)),
      String.is_empty(msg), Bool.not(bad), e),
    foreign.at2(bad, x, more, Laws.foreign.count(rest, native), ih))

def Laws.foreign_walk_counts(root, native, path):
  match root:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SDef{}:
              foreign.def(kids, body, rest, native, path, Laws.foreign_walk_counts(rest, native, path))
            case Tree.SType{}:
              Laws.foreign_walk_counts(rest, native, path)
            case Tree.SLaw{}:
              Laws.foreign_walk_counts(rest, native, path)
            case Tree.SImport{}:
              Laws.foreign_walk_counts(rest, native, path)
            case Tree.SCase{}:
              Laws.foreign_walk_counts(rest, native, path)
            case Tree.SFor{}:
              Laws.foreign_walk_counts(rest, native, path)
            case Tree.SLet{}:
              Laws.foreign_walk_counts(rest, native, path)
            case Tree.STerm{}:
              Laws.foreign_walk_counts(rest, native, path)
        case Tree.Leaf{x}:
          Laws.foreign_walk_counts(rest, native, path)
        case Tree.Group{a, b, d}:
          Laws.foreign_walk_counts(rest, native, path)
        case Tree.NNil{}:
          Laws.foreign_walk_counts(rest, native, path)
        case Tree.NCons{a, b}:
          Laws.foreign_walk_counts(rest, native, path)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{a, b, d}:
      {==}
    case Tree.Stmt{a, b, d}:
      {==}
    case Tree.NNil{}:
      {==}

def Laws.foreign_counts(path, text, _toks, tree, _bound, _items):
  Equal.trans(Nat, List.length(&2, F.Finding, Foreign.check.go(tree, Foreign.native_only(text), path)),
    Laws.foreign.count(tree, Foreign.native_only(text)),
    Laws.foreign.count(tree, Laws.foreign.headed(String.lines(text))),
    Laws.foreign_walk_counts(tree, Foreign.native_only(text), path),
    Equal.cong(Bool, Nat, z => Laws.foreign.count(tree, z), Foreign.native_only(text),
      Laws.foreign.headed(String.lines(text)), Laws.foreign_native(String.lines(text))))

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
      {==}
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

# closed (BOLT-LAW-2): the rule's binder test is the law's, and a law
# statement adds a finding exactly when it binds nothing.

# a law's binder test, to the rule and to the law
law closed.binds:
  for body: Tree.Node
  {Closed.binds(body) == Laws.closed.bound(body) : Bool}

def closed.binds(body):
  match body:
    case Tree.NCons{h, rest}:
      match h:
        case Tree.Stmt{kind, _kids, _b}:
          match kind:
            case Tree.SFor{}:
              {==}
            case Tree.SDef{}:
              closed.binds(rest)
            case Tree.SType{}:
              closed.binds(rest)
            case Tree.SLaw{}:
              closed.binds(rest)
            case Tree.SImport{}:
              closed.binds(rest)
            case Tree.SCase{}:
              closed.binds(rest)
            case Tree.SLet{}:
              closed.binds(rest)
            case Tree.STerm{}:
              closed.binds(rest)
        case Tree.Leaf{_x}:
          closed.binds(rest)
        case Tree.Group{_a, _b, _d}:
          closed.binds(rest)
        case Tree.NNil{}:
          closed.binds(rest)
        case Tree.NCons{_a, _b}:
          closed.binds(rest)
    case Tree.Leaf{_x}:
      {==}
    case Tree.Group{_a, _b, _d}:
      {==}
    case Tree.Stmt{_a, _b, _d}:
      {==}
    case Tree.NNil{}:
      {==}

# a finding in front unless b holds adds one to the count
law closed.stop:
  for b: Bool
  for -x: F.Finding
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, b, more, _u => x <> more))
    == Bool.pick(Nat, b, m, 1n+m) : Nat}

def closed.stop(b, _x, more, m, ih):
  match b:
    case True{}:
      ih
    case False{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)

# a top-level law onto a rest the law holds for
law closed.law:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +path: String
  for ih: {List.length(&2, F.Finding, Closed.check.go(rest, path)) == Laws.closed.count(rest) : Nat}
  {List.length(&2, F.Finding, Closed.check.go(Tree.NCons{Tree.Stmt{Tree.SLaw{}, kids, body}, rest}, path))
    == Laws.closed.count(Tree.NCons{Tree.Stmt{Tree.SLaw{}, kids, body}, rest}) : Nat}

def closed.law(kids, body, rest, path, ih):
  +more = Closed.check.go(rest, path)
  +m = Laws.closed.count(rest)
  +x = {F.Finding{path, Tree.line(kids), Tree.col(kids), 0, "closed",
    "Law " ++ Closed.name.of(Bind.declared(kids))
      ++ " has no for or exs, so it checks one case; quantify it, or delete it."} : F.Finding}
  Equal.trans(Nat,
    List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Closed.binds(body), more, _u => x <> more)),
    List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Laws.closed.bound(body), more, _u => x <> more)),
    Bool.pick(Nat, Laws.closed.bound(body), m, 1n+m),
    Equal.cong(Bool, Nat, z => List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, z, more, _u => x <> more)),
      Closed.binds(body), Laws.closed.bound(body), closed.binds(body)),
    closed.stop(Laws.closed.bound(body), x, more, m, ih))

def Laws.closed_walk_counts(root, path):
  match root:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SLaw{}:
              closed.law(kids, body, rest, path, Laws.closed_walk_counts(rest, path))
            case Tree.SDef{}:
              Laws.closed_walk_counts(rest, path)
            case Tree.SType{}:
              Laws.closed_walk_counts(rest, path)
            case Tree.SImport{}:
              Laws.closed_walk_counts(rest, path)
            case Tree.SCase{}:
              Laws.closed_walk_counts(rest, path)
            case Tree.SFor{}:
              Laws.closed_walk_counts(rest, path)
            case Tree.SLet{}:
              Laws.closed_walk_counts(rest, path)
            case Tree.STerm{}:
              Laws.closed_walk_counts(rest, path)
        case Tree.Leaf{_x}:
          Laws.closed_walk_counts(rest, path)
        case Tree.Group{_a, _b, _d}:
          Laws.closed_walk_counts(rest, path)
        case Tree.NNil{}:
          Laws.closed_walk_counts(rest, path)
        case Tree.NCons{_a, _b}:
          Laws.closed_walk_counts(rest, path)
    case Tree.Leaf{_x}:
      {==}
    case Tree.Group{_a, _b, _d}:
      {==}
    case Tree.Stmt{_a, _b, _d}:
      {==}
    case Tree.NNil{}:
      {==}

def Laws.closed_counts(path, _text, _toks, tree, _bound, _items):
  Equal.trans(Nat,
    List.length(&2, F.Finding,
      Lazy.stop(List<&2, F.Finding>, Bool.not(Paths.is_laws(path)), [], _u => Closed.check.go(tree, path))),
    Bool.pick(Nat, Bool.not(Paths.is_laws(path)), 0n, Laws.closed.count(tree)),
    Bool.pick(Nat, Paths.is_laws(path), Laws.closed.count(tree), 0n),
    param.stop(Bool.not(Paths.is_laws(path)), Closed.check.go(tree, path), Laws.closed.count(tree),
      Laws.closed_walk_counts(tree, path)),
    arms.flip(Paths.is_laws(path), Laws.closed.count(tree)))

# doc (BOLT-RULE-S001): the rule's early exits are the law's plain picks and
# ands, so an item adds a finding exactly when the law calls it bare.

# the early exit of a Bool search is the plain pick
law doc.pick:
  for c: Bool
  for -a: Bool
  for -x: Bool
  for -y: Bool
  for ih: {x == y : Bool}
  {Lazy.stop(Bool, c, a, _u => x) == Bool.pick(Bool, c, a, y) : Bool}

def doc.pick(c, _a, _x, _y, ih):
  match c:
    case True{}:
      {==}
    case False{}:
      ih

# the `#` test on line nn, to the rule and to the law
law doc.hash:
  for lines: List<&2, String>
  for +nn: U32
  {Doc.check.hash(lines, nn) == Laws.doc.hash(lines, nn) : Bool}

def doc.hash(lines, nn):
  match lines:
    case Nil{}:
      {==}
    case Con{hh, tt}:
      doc.pick(U32.is_eq(nn, 0), String.starts_with(hh, "#"), Doc.check.hash(tt, U32.sub(nn, 1)),
        Laws.doc.hash(tt, U32.sub(nn, 1)), doc.hash(tt, U32.sub(nn, 1)))

# the `#` line right above line nn, to the rule and to the law
law doc.above:
  for +lines: List<&2, String>
  for +nn: U32
  {Doc.check.above(lines, nn) == Bool.and(Bool.not(U32.is_eq(nn, 0)), Laws.doc.hash(lines, U32.sub(nn, 1))) : Bool}

def doc.above(lines, nn):
  hole.and(Bool.not(U32.is_eq(nn, 0)), Doc.check.hash(lines, U32.sub(nn, 1)), Laws.doc.hash(lines, U32.sub(nn, 1)),
    doc.hash(lines, U32.sub(nn, 1)))

# the kind, name and doc test, to the rule and to the law
law doc.needs:
  for kk: Outline.ItemKind
  for +name: String
  for +doc: String
  {Bool.and(Bool.and(Doc.needs(kk), Bool.not(Doc.exempt(name))), String.is_empty(doc))
    == Bool.and(Bool.and(Laws.doc.kind(kk), Bool.not(Laws.doc.free(name))), String.is_empty(doc)) : Bool}

def doc.needs(kk, _name, _doc):
  match kk:
    case Outline.IImport{}:
      {==}
    case Outline.IDef{}:
      {==}
    case Outline.ILaw{}:
      {==}
    case Outline.IType{}:
      {==}
    case Outline.ICtor{}:
      {==}
    case Outline.ILocal{}:
      {==}

# an item's hit, to the rule and to the law
law doc.hit:
  for +kk: Outline.ItemKind
  for +name: String
  for +line: U32
  for +doc: String
  for +lines: List<&2, String>
  {Lazy.and_then(Bool.and(Bool.and(Doc.needs(kk), Bool.not(Doc.exempt(name))), String.is_empty(doc)),
    _u => Bool.not(Doc.check.above(lines, line))) == Laws.doc.bare(kk, name, line, doc, lines) : Bool}

def doc.hit(kk, name, line, doc, lines):
  +ar = Bool.and(Bool.and(Doc.needs(kk), Bool.not(Doc.exempt(name))), String.is_empty(doc))
  +as = Bool.and(Bool.and(Laws.doc.kind(kk), Bool.not(Laws.doc.free(name))), String.is_empty(doc))
  +ns = Bool.not(Bool.and(Bool.not(U32.is_eq(line, 0)), Laws.doc.hash(lines, U32.sub(line, 1))))
  Equal.trans(Bool, Lazy.and_then(ar, _u => Bool.not(Doc.check.above(lines, line))), Bool.and(ar, ns),
    Bool.and(as, ns),
    hole.and(ar, Bool.not(Doc.check.above(lines, line)), ns,
      Equal.cong(Bool, Bool, z => Bool.not(z), Doc.check.above(lines, line),
        Bool.and(Bool.not(U32.is_eq(line, 0)), Laws.doc.hash(lines, U32.sub(line, 1))), doc.above(lines, line))),
    Equal.cong(Bool, Bool, z => Bool.and(z, ns), ar, as, doc.needs(kk, name, doc)))

# an item onto a rest the law holds for
law doc.item:
  for +kk: Outline.ItemKind
  for +name: String
  for +line: U32
  for sig: String
  for +doc: String
  for pp: String
  for +rest: List<&2, Outline.Item>
  for +path: String
  for +lines: List<&2, String>
  for ih: {List.length(&2, F.Finding, Doc.check.go(rest, path, lines)) == Laws.doc.count(rest, lines) : Nat}
  {List.length(&2, F.Finding, Doc.check.go(Outline.Item{kk, name, line, sig, doc, pp} <> rest, path, lines))
    == Laws.doc.count(Outline.Item{kk, name, line, sig, doc, pp} <> rest, lines) : Nat}

def doc.item(kk, name, line, _sig, doc, _pp, rest, path, lines, ih):
  +more = Doc.check.go(rest, path, lines)
  +m = Laws.doc.count(rest, lines)
  +x = {F.Finding{path, line, 0, 0, "doc", Doc.what(kk) ++ " " ++ name ++ " has no comment above it."} : F.Finding}
  +hr = Lazy.and_then(Bool.and(Bool.and(Doc.needs(kk), Bool.not(Doc.exempt(name))), String.is_empty(doc)),
    _u => Bool.not(Doc.check.above(lines, line)))
  +hs = Laws.doc.bare(kk, name, line, doc, lines)
  Equal.trans(Nat, List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, hr, x <> more, more)),
    List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, hs, x <> more, more)),
    Bool.pick(Nat, hs, 1n+m, m),
    Equal.cong(Bool, Nat, z => List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, z, x <> more, more)), hr, hs,
      doc.hit(kk, name, line, doc, lines)),
    nat.pick(hs, x, more, m, ih))

def Laws.doc_walk_counts(items, path, lines):
  match items:
    case Nil{}:
      {==}
    case Con{it, +rest}:
      match it:
        case Outline.Item{kk, name, line, sig, doc, pp}:
          doc.item(kk, name, line, sig, doc, pp, rest, path, lines, Laws.doc_walk_counts(rest, path, lines))

def Laws.doc_counts(path, text, _toks, _tree, _bound, items):
  param.stop(Bool.or(Paths.is_proof(path), Paths.is_test(path)), Doc.check.go(items, path, String.lines(text)),
    Laws.doc.count(items, String.lines(text)), Laws.doc_walk_counts(items, path, String.lines(text)))

# The binding rule, unused: the rule's foreign lines are the law's header
# lines, its kind test and use search are the law's, and each binder adds the
# finding the law counts.

# the lines of some tokens onto acc are those lines, then acc
law unused.lines:
  for ts: List<&2, Lex.Tok>
  for +acc: List<&2, U32>
  {Unused.lines(ts, acc) == List.append(&2, U32, Laws.unused.token_lines(ts), acc) : List<&2, U32>}

def unused.lines(ts, acc):
  match ts:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, t, +l, c}, rest}:
      Equal.cong(List<&2, U32>, List<&2, U32>, xs => l <> xs, Unused.lines(rest, acc),
        List.append(&2, U32, Laws.unused.token_lines(rest), acc), unused.lines(rest, acc))

# a foreign def's header lines onto the lines after it, to the rule and to
# the law
law unused.header:
  for +kids: Tree.Node
  for +rest: Tree.Node
  for ih: {Unused.foreign(rest) == Laws.unused.headers(rest) : List<&2, U32>}
  {Unused.lines(Tree.leaves(kids), Unused.foreign(rest))
    == List.append(&2, U32, Laws.unused.token_lines(Tree.leaves(kids)), Laws.unused.headers(rest)) : List<&2, U32>}

def unused.header(kids, rest, ih):
  Equal.trans(List<&2, U32>,
    Unused.lines(Tree.leaves(kids), Unused.foreign(rest)),
    List.append(&2, U32, Laws.unused.token_lines(Tree.leaves(kids)), Unused.foreign(rest)),
    List.append(&2, U32, Laws.unused.token_lines(Tree.leaves(kids)), Laws.unused.headers(rest)),
    unused.lines(Tree.leaves(kids), Unused.foreign(rest)),
    Equal.cong(List<&2, U32>, List<&2, U32>, xs => List.append(&2, U32, Laws.unused.token_lines(Tree.leaves(kids)), xs),
      Unused.foreign(rest), Laws.unused.headers(rest), ih))

# the rule's foreign lines are the law's header lines
law unused.foreign:
  for root: Tree.Node
  {Unused.foreign(root) == Laws.unused.headers(root) : List<&2, U32>}

def unused.foreign(root):
  match root:
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
          unused.foreign(rest)
        case Tree.Group{o, gk, cl}:
          unused.foreign(rest)
        case Tree.Stmt{kind, +kids, body}:
          match kind:
            case Tree.SDef{}:
              match body:
                case Tree.Leaf{tok}:
                  unused.foreign(rest)
                case Tree.Group{o, gk, cl}:
                  unused.foreign(rest)
                case Tree.Stmt{bk, bs, bb}:
                  unused.foreign(rest)
                case Tree.NNil{}:
                  unused.foreign(rest)
                case Tree.NCons{bh, more}:
                  match bh:
                    case Tree.Leaf{tok}:
                      unused.foreign(rest)
                    case Tree.Group{o, gk, cl}:
                      unused.foreign(rest)
                    case Tree.NNil{}:
                      unused.foreign(rest)
                    case Tree.NCons{nh, nt}:
                      unused.foreign(rest)
                    case Tree.Stmt{ik, ks, ib}:
                      match ik:
                        case Tree.SDef{}:
                          unused.foreign(rest)
                        case Tree.SType{}:
                          unused.foreign(rest)
                        case Tree.SLaw{}:
                          unused.foreign(rest)
                        case Tree.SImport{}:
                          unused.header(kids, rest, unused.foreign(rest))
                        case Tree.SCase{}:
                          unused.foreign(rest)
                        case Tree.SFor{}:
                          unused.foreign(rest)
                        case Tree.SLet{}:
                          unused.foreign(rest)
                        case Tree.STerm{}:
                          unused.foreign(rest)
            case Tree.SType{}:
              unused.foreign(rest)
            case Tree.SLaw{}:
              unused.foreign(rest)
            case Tree.SImport{}:
              unused.foreign(rest)
            case Tree.SCase{}:
              unused.foreign(rest)
            case Tree.SFor{}:
              unused.foreign(rest)
            case Tree.SLet{}:
              unused.foreign(rest)
            case Tree.STerm{}:
              unused.foreign(rest)
        case Tree.NNil{}:
          unused.foreign(rest)
        case Tree.NCons{nh, nt}:
          unused.foreign(rest)

# a stop at the first True is Bool.or
law unused.or:
  for a: Bool
  for -x: Bool
  for -y: Bool
  for ih: {x == y : Bool}
  {Lazy.or_else(a, _u => x) == Bool.or(a, y) : Bool}

def unused.or(a, _x, _y, ih):
  match a:
    case True{}:
      {==}
    case False{}:
      ih

# the rule's use search is the law's
law unused.used:
  for uses: List<&2, Bind.Use>
  for +line: U32
  for +col: U32
  {Unused.used(uses, line, col) == Laws.unused.seen(uses, line, col) : Bool}

def unused.used(uses, line, col):
  match uses:
    case Nil{}:
      {==}
    case Con{Bind.Use{n, l, c, tg}, +rest}:
      match tg:
        case Bind.TLocal{+tl, +tc}:
          unused.or(Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col)), Unused.used(rest, line, col),
            Laws.unused.seen(rest, line, col), unused.used(rest, line, col))
        case Bind.TItem{nm}:
          unused.used(rest, line, col)
        case Bind.TQual{a, nm}:
          unused.used(rest, line, col)
        case Bind.TFree{}:
          unused.used(rest, line, col)

# the rule's kind test is the law's
law unused.kind:
  for kk: Bind.BindKind
  for +note: String
  for +line: U32
  for +fl: List<&2, U32>
  {Unused.reportable(kk, note, line, fl) == Laws.unused.kept(kk, note, line, fl) : Bool}

def unused.kind(kk, _note, _line, _fl):
  match kk:
    case Bind.KItem{}:
      {==}
    case Bind.KCtor{}:
      {==}
    case Bind.KParam{}:
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

# the rule's finding test for a binder is the law's
law unused.hit:
  for +kk: Bind.BindKind
  for +name: String
  for +note: String
  for +line: U32
  for +col: U32
  for +uses: List<&2, Bind.Use>
  for +fl: List<&2, U32>
  {Bool.and(Bool.and(Unused.reportable(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
      Bool.not(Unused.used(uses, line, col)))
    == Bool.and(Bool.and(Laws.unused.kept(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
      Bool.not(Laws.unused.seen(uses, line, col))) : Bool}

def unused.hit(kk, name, note, line, col, uses, fl):
  Equal.trans(Bool,
    Bool.and(Bool.and(Unused.reportable(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
      Bool.not(Unused.used(uses, line, col))),
    Bool.and(Bool.and(Laws.unused.kept(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
      Bool.not(Unused.used(uses, line, col))),
    Bool.and(Bool.and(Laws.unused.kept(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
      Bool.not(Laws.unused.seen(uses, line, col))),
    Equal.cong(Bool, Bool,
      z => Bool.and(Bool.and(z, Bool.not(String.starts_with(name, "_"))), Bool.not(Unused.used(uses, line, col))),
      Unused.reportable(kk, note, line, fl), Laws.unused.kept(kk, note, line, fl), unused.kind(kk, note, line, fl)),
    Equal.cong(Bool, Bool,
      z => Bool.and(Bool.and(Laws.unused.kept(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
        Bool.not(z)),
      Unused.used(uses, line, col), Laws.unused.seen(uses, line, col), unused.used(uses, line, col)))

# over the binder list, the rule counts what the law counts
law unused.go:
  for binds: List<&2, Bind.Bind>
  for +uses: List<&2, Bind.Use>
  for +fl: List<&2, U32>
  for +path: String
  {List.length(&2, F.Finding, Unused.check.go(binds, uses, fl, path)) == Laws.unused.count(binds, uses, fl) : Nat}

def unused.go(binds, uses, fl, path):
  match binds:
    case Nil{}:
      {==}
    case Con{Bind.Bind{+name, +line, +col, +kk, +note}, +rest}:
      +m = Laws.unused.count(rest, uses, fl)
      +b = Bool.and(Bool.and(Unused.reportable(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
        Bool.not(Unused.used(uses, line, col)))
      Equal.trans(Nat,
        List.length(&2, F.Finding, Unused.check.go(Bind.Bind{name, line, col, kk, note} <> rest, uses, fl, path)),
        Bool.pick(Nat, b, 1n+m, m),
        Laws.unused.count(Bind.Bind{name, line, col, kk, note} <> rest, uses, fl),
        nat.pick(b, F.Finding{path, line, col, U32.from_nat(String.length(name)), "unused",
            Unused.what(kk) ++ " " ++ name ++ " is never used."},
          Unused.check.go(rest, uses, fl, path), m, unused.go(rest, uses, fl, path)),
        Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, 1n+m, m), b,
          Bool.and(Bool.and(Laws.unused.kept(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
            Bool.not(Laws.unused.seen(uses, line, col))),
          unused.hit(kk, name, note, line, col, uses, fl)))

def Laws.unused_counts(path, _text, _toks, tree, binds, uses, _scopes, _items):
  Equal.trans(Nat,
    List.length(&2, F.Finding, Unused.check.go(binds, uses, Unused.foreign(tree), path)),
    Laws.unused.count(binds, uses, Unused.foreign(tree)),
    Laws.unused.count(binds, uses, Laws.unused.headers(tree)),
    unused.go(binds, uses, Unused.foreign(tree), path),
    Equal.cong(List<&2, U32>, Nat, z => Laws.unused.count(binds, uses, z),
      Unused.foreign(tree), Laws.unused.headers(tree), unused.foreign(tree)))

# The recursion rule, index: its literal test is the law's, its fire test is
# the law's (a List.get held by a fixed table is exactly one `table`
# reports), each call adds what the law counts, and the def walk joins the
# per-def lists into their sum.

# the rule's literal test is the law's
law index.lit:
  for nn: Tree.Node
  {Index.literal(nn) == Laws.index.lit(nn) : Bool}

def index.lit(nn):
  match nn:
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
        case Tree.Group{o, gk, cl}:
          {==}
        case Tree.Stmt{kind, sk, sb}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{nh, nt}:
          {==}
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
              match rest:
                case Tree.Leaf{tok}:
                  {==}
                case Tree.Group{o, gk, cl}:
                  {==}
                case Tree.Stmt{sk, skids, sb}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{nh, nt}:
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

# table's literal test is the law's too
law index.tlit:
  for nn: Tree.Node
  {Table.literal(nn) == Laws.index.lit(nn) : Bool}

def index.tlit(nn):
  match nn:
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
        case Tree.Group{o, gk, cl}:
          {==}
        case Tree.Stmt{kind, sk, sb}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{nh, nt}:
          {==}
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
              match rest:
                case Tree.Leaf{tok}:
                  {==}
                case Tree.Group{o, gk, cl}:
                  {==}
                case Tree.Stmt{sk, skids, sb}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{nh, nt}:
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

# a List.get whose index is not a literal: index reports it exactly when its
# list is not a fixed table, which is exactly when table does not
law index.gate:
  for a: Bool
  for o: Bool
  for -x: F.Finding
  {Bool.and(Bool.not(a), Bool.not(o))
    == Bool.and(Bool.not(a),
      List.is_empty(&2, F.Finding, Bool.pick(List<&2, F.Finding>, Bool.and(Bool.not(a), o), [x], []))) : Bool}

def index.gate(a, o, _x):
  match a:
    case True{}:
      {==}
    case False{}:
      match o:
        case True{}:
          {==}
        case False{}:
          {==}

# a String.get's test, the held test dropped
law index.tail:
  for sb: Bool
  for a: Bool
  {Bool.and(sb, Bool.and(Bool.not(a), True{})) == Bool.and(sb, Bool.not(a)) : Bool}

def index.tail(sb, a):
  match sb:
    case False{}:
      {==}
    case True{}:
      match a:
        case True{}:
          {==}
        case False{}:
          {==}

# the rule's fire test for a call is the law's
law index.fire:
  for list: Bool
  for ob: Bool
  for +sb: Bool
  for +kids: Tree.Node
  for +fixed: List<&2, String>
  for +path: String
  for +l: U32
  for +c: U32
  {Bool.and(Bool.and(ob, Bool.or(list, sb)),
      Bool.and(Bool.not(Index.literal(Calls.arg(Calls.args(kids), Bool.pick(Nat, list, 3n, 1n)))),
        Bool.not(Index.held(list, Calls.arg(Calls.args(kids), 2n), fixed))))
    == Laws.index.fires(list, ob, sb, Calls.args(kids), Table.hit(ob, "List.get", kids, fixed, path, l, c)) : Bool}

def index.fire(list, ob, sb, kids, fixed, path, l, c):
  match list:
    case True{}:
      match ob:
        case False{}:
          {==}
        case True{}:
          +a3 = Calls.arg(Calls.args(kids), 3n)
          +own = Table.owns(Calls.arg(Calls.args(kids), 2n), fixed)
          +x = Table.cite(True{}, path, l, c, U32.from_nat(String.length("List.get")))
          Equal.trans(Bool,
            Bool.and(Bool.not(Index.literal(a3)), Bool.not(own)),
            Bool.and(Bool.not(Laws.index.lit(a3)), Bool.not(own)),
            Bool.and(Bool.not(Laws.index.lit(a3)), List.is_empty(&2, F.Finding,
              Bool.pick(List<&2, F.Finding>, Bool.and(Bool.not(Table.literal(a3)), own), [x], []))),
            Equal.cong(Bool, Bool, z => Bool.and(Bool.not(z), Bool.not(own)),
              Index.literal(a3), Laws.index.lit(a3), index.lit(a3)),
            Equal.trans(Bool,
              Bool.and(Bool.not(Laws.index.lit(a3)), Bool.not(own)),
              Bool.and(Bool.not(Laws.index.lit(a3)), List.is_empty(&2, F.Finding,
                Bool.pick(List<&2, F.Finding>, Bool.and(Bool.not(Laws.index.lit(a3)), own), [x], []))),
              Bool.and(Bool.not(Laws.index.lit(a3)), List.is_empty(&2, F.Finding,
                Bool.pick(List<&2, F.Finding>, Bool.and(Bool.not(Table.literal(a3)), own), [x], []))),
              index.gate(Laws.index.lit(a3), own, x),
              Equal.cong(Bool, Bool,
                z => Bool.and(Bool.not(Laws.index.lit(a3)), List.is_empty(&2, F.Finding,
                  Bool.pick(List<&2, F.Finding>, Bool.and(Bool.not(z), own), [x], []))),
                Laws.index.lit(a3), Table.literal(a3),
                Equal.sym(Bool, Table.literal(a3), Laws.index.lit(a3), index.tlit(a3)))))
    case False{}:
      match ob:
        case False{}:
          {==}
        case True{}:
          +a1 = Calls.arg(Calls.args(kids), 1n)
          Equal.trans(Bool,
            Bool.and(sb, Bool.and(Bool.not(Index.literal(a1)), True{})),
            Bool.and(sb, Bool.and(Bool.not(Laws.index.lit(a1)), True{})),
            Bool.and(sb, Bool.not(Laws.index.lit(a1))),
            Equal.cong(Bool, Bool, z => Bool.and(sb, Bool.and(Bool.not(z), True{})),
              Index.literal(a1), Laws.index.lit(a1), index.lit(a1)),
            index.tail(sb, Laws.index.lit(a1)))

# two lists joined count as the sum of their counts
law index.two:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for -x: Nat
  for -y: Nat
  for e1: {List.length(&2, F.Finding, a) == x : Nat}
  for e2: {List.length(&2, F.Finding, b) == y : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b])) == Nat.add(x, y) : Nat}

def index.two(a, b, x, y, e1, e2):
  Equal.trans(Nat,
    List.length(&2, F.Finding, List.append(&2, F.Finding, a, List.append(&2, F.Finding, b, []))),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, List.append(&2, F.Finding, b, []))),
    Nat.add(x, y),
    esc.app(a, List.append(&2, F.Finding, b, [])),
    esc.add(List.length(&2, F.Finding, a), x, List.length(&2, F.Finding, List.append(&2, F.Finding, b, [])), y, e1,
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, b, [])), List.length(&2, F.Finding, b), y,
        chars.nil(b), e2)))

# a count one higher when b holds is b's one or none, then the count
law index.one:
  for b: Bool
  for -m: Nat
  {Bool.pick(Nat, b, 1n+m, m) == Nat.add(Bool.pick(Nat, b, 1n, 0n), m) : Nat}

def index.one(b, _m):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a call onto the rest: its own finding, then its group's and the rest's
law index.call:
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +gk: Lex.TokKind
  for +o: String
  for +gl: U32
  for +gc: U32
  for +kids: Tree.Node
  for +cl: Maybe<&2, Lex.Tok>
  for +rr: Tree.Node
  for +path: String
  for +fixed: List<&2, String>
  for ih1: {List.length(&2, F.Finding, Index.walk(kids, path, fixed)) == Laws.index.count(kids, path, fixed) : Nat}
  for ih2: {List.length(&2, F.Finding, Index.walk(rr, path, fixed)) == Laws.index.count(rr, path, fixed) : Nat}
  {List.length(&2, F.Finding, Index.walk(Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}},
      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, kids, cl}, rr}}, path, fixed))
    == Laws.index.count(Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}},
      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, kids, cl}, rr}}, path, fixed) : Nat}

def index.call(_k, t, l, c, _gk, o, _gl, _gc, kids, _cl, rr, path, fixed, ih1, ih2):
  +list = String.eq(t, "List.get")
  +ob = String.eq(o, "(")
  +sb = String.eq(t, "String.get")
  +as = Calls.args(kids)
  +fire = Bool.and(Bool.and(ob, Bool.or(list, sb)),
    Bool.and(Bool.not(Index.literal(Calls.arg(as, Bool.pick(Nat, list, 3n, 1n)))),
      Bool.not(Index.held(list, Calls.arg(as, 2n), fixed))))
  +more = List.concat(&2, F.Finding, [Index.walk(kids, path, fixed), Index.walk(rr, path, fixed)])
  +m = Nat.add(Laws.index.count(kids, path, fixed), Laws.index.count(rr, path, fixed))
  +spec = Laws.index.fires(list, ob, sb, as, Table.hit(ob, "List.get", kids, fixed, path, l, c))
  +x = {F.Finding{path, l, c, U32.from_nat(String.length(t)), "index",
    t ++ " inside a recursive def walks the list again on each step, which is quadratic; walk the list itself."}
    : F.Finding}
  Equal.trans(Nat,
    List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, fire, x <> more, more)),
    Bool.pick(Nat, fire, 1n+m, m),
    Nat.add(Bool.pick(Nat, spec, 1n, 0n), m),
    nat.pick(fire, x, more, m, index.two(Index.walk(kids, path, fixed), Index.walk(rr, path, fixed),
      Laws.index.count(kids, path, fixed), Laws.index.count(rr, path, fixed), ih1, ih2)),
    Equal.trans(Nat,
      Bool.pick(Nat, fire, 1n+m, m),
      Nat.add(Bool.pick(Nat, fire, 1n, 0n), m),
      Nat.add(Bool.pick(Nat, spec, 1n, 0n), m),
      index.one(fire, m),
      Equal.cong(Bool, Nat, z => Nat.add(Bool.pick(Nat, z, 1n, 0n), m), fire, spec,
        index.fire(list, ob, sb, kids, fixed, path, l, c))))

# index's walk counts the calls the law counts
law index.walk:
  for nn: Tree.Node
  for +path: String
  for +fixed: List<&2, String>
  {List.length(&2, F.Finding, Index.walk(nn, path, fixed)) == Laws.index.count(nn, path, fixed) : Nat}

def index.walk(nn, path, fixed):
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
        case Tree.Leaf{Lex.Tok{k, t, l, c}}:
          match rest:
            case Tree.Leaf{tok}:
              {==}
            case Tree.Group{o, gk, cl}:
              {==}
            case Tree.Stmt{kind, sk, sb}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{rh, +rr}:
              match rh:
                case Tree.Group{Lex.Tok{gk, o, gl, gc}, +kids, cl}:
                  index.call(k, t, l, c, gk, o, gl, gc, kids, cl, rr, path, fixed,
                    index.walk(kids, path, fixed), index.walk(rr, path, fixed))
                case Tree.Leaf{tok}:
                  index.walk(rest, path, fixed)
                case Tree.Stmt{kind, sk, sb}:
                  index.walk(rest, path, fixed)
                case Tree.NNil{}:
                  index.walk(rest, path, fixed)
                case Tree.NCons{nh, nt}:
                  index.walk(rest, path, fixed)
        case Tree.Group{o, +kids, cl}:
          index.two(Index.walk(kids, path, fixed), Index.walk(rest, path, fixed),
            Laws.index.count(kids, path, fixed), Laws.index.count(rest, path, fixed),
            index.walk(kids, path, fixed), index.walk(rest, path, fixed))
        case Tree.Stmt{kind, +kids, +body}:
          chars.sum(Index.walk(kids, path, fixed), Index.walk(body, path, fixed), Index.walk(rest, path, fixed),
            Laws.index.count(kids, path, fixed), Laws.index.count(body, path, fixed),
            Laws.index.count(rest, path, fixed),
            index.walk(kids, path, fixed), index.walk(body, path, fixed), index.walk(rest, path, fixed))
        case Tree.NNil{}:
          index.walk(rest, path, fixed)
        case Tree.NCons{nh, nt}:
          index.walk(rest, path, fixed)

# the counts of gathered finding lists, the last gathered first
def index.sum(acc: List<&2, List<&2, F.Finding>>) -> Nat:
  match acc:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(index.sum(t), List.length(&2, F.Finding, h))

# adding is associative
law index.assoc:
  for a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def index.assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), index.assoc(p, b, c))

# reversing gathered lists onto others and joining them counts them all
law index.flat:
  for xs: List<&2, List<&2, F.Finding>>
  for +ys: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, List.reverse.go(&2, List<&2, F.Finding>, xs, ys)))
    == Nat.add(index.sum(xs), List.length(&2, F.Finding, List.concat(&2, F.Finding, ys))) : Nat}

def index.flat(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +cs = List.concat(&2, F.Finding, ys)
      Equal.trans(Nat,
        List.length(&2, F.Finding, List.concat(&2, F.Finding, List.reverse.go(&2, List<&2, F.Finding>, t, h <> ys))),
        Nat.add(index.sum(t), List.length(&2, F.Finding, List.append(&2, F.Finding, h, cs))),
        Nat.add(Nat.add(index.sum(t), List.length(&2, F.Finding, h)), List.length(&2, F.Finding, cs)),
        index.flat(t, h <> ys),
        Equal.trans(Nat,
          Nat.add(index.sum(t), List.length(&2, F.Finding, List.append(&2, F.Finding, h, cs))),
          Nat.add(index.sum(t), Nat.add(List.length(&2, F.Finding, h), List.length(&2, F.Finding, cs))),
          Nat.add(Nat.add(index.sum(t), List.length(&2, F.Finding, h)), List.length(&2, F.Finding, cs)),
          Equal.cong(Nat, Nat, z => Nat.add(index.sum(t), z),
            List.length(&2, F.Finding, List.append(&2, F.Finding, h, cs)),
            Nat.add(List.length(&2, F.Finding, h), List.length(&2, F.Finding, cs)), esc.app(h, cs)),
          Equal.sym(Nat,
            Nat.add(Nat.add(index.sum(t), List.length(&2, F.Finding, h)), List.length(&2, F.Finding, cs)),
            Nat.add(index.sum(t), Nat.add(List.length(&2, F.Finding, h), List.length(&2, F.Finding, cs))),
            index.assoc(index.sum(t), List.length(&2, F.Finding, h), List.length(&2, F.Finding, cs)))))

# a def that calls itself and is not exempt gathers its walk, any other
# nothing
law index.def:
  for g: Bool
  for +body: Tree.Node
  for +path: String
  for +fixed: List<&2, String>
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(g), [], _u => Index.walk(body, path, fixed)))
    == Bool.pick(Nat, g, Laws.index.count(body, path, fixed), 0n) : Nat}

def index.def(g, body, path, fixed):
  match g:
    case True{}:
      index.walk(body, path, fixed)
    case False{}:
      {==}

# over the defs, the rule's join counts what it gathered and what the law
# counts
law index.go:
  for ds: List<&2, Calls.Def>
  for +mods: List<&2, String>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Index.check.go(ds, mods, path, acc))
    == Nat.add(index.sum(acc), Laws.index.total(ds, mods, path)) : Nat}

def index.go(ds, mods, path, acc):
  match ds:
    case Nil{}:
      index.flat(acc, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +g = Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))
      +fixed = Table.scope(body, mods)
      +x = Lazy.stop(List<&2, F.Finding>, Bool.not(g), [], _u => Index.walk(body, path, fixed))
      +n = Bool.pick(Nat, g, Laws.index.count(body, path, fixed), 0n)
      +tot = Laws.index.total(rest, mods, path)
      Equal.trans(Nat,
        List.length(&2, F.Finding, Index.check.go(rest, mods, path, x <> acc)),
        Nat.add(Nat.add(index.sum(acc), List.length(&2, F.Finding, x)), tot),
        Nat.add(index.sum(acc), Nat.add(n, tot)),
        index.go(rest, mods, path, x <> acc),
        Equal.trans(Nat,
          Nat.add(Nat.add(index.sum(acc), List.length(&2, F.Finding, x)), tot),
          Nat.add(index.sum(acc), Nat.add(List.length(&2, F.Finding, x), tot)),
          Nat.add(index.sum(acc), Nat.add(n, tot)),
          index.assoc(index.sum(acc), List.length(&2, F.Finding, x), tot),
          Equal.cong(Nat, Nat, z => Nat.add(index.sum(acc), Nat.add(z, tot)), List.length(&2, F.Finding, x), n,
            index.def(g, body, path, fixed))))

def Laws.index_counts(path, _text, _toks, tree, _bound, _items):
  +ds = Calls.defs(tree)
  index.go(ds, Table.modules(ds, Nil{}), path, Nil{})

# concat (BOLT-RULE-U004). The walk joins each self-call's hits, its group's
# and what follows, so the count adds them; the hits and the def walk build
# their lists on an accumulator reversed at the end, so the count carries the
# accumulator's length (or the sum of its lists' lengths) along.

# a plus (1 plus b) is 1 plus (a plus b)
law concat.succ:
  for a: Nat
  for -b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def concat.succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 1n+b), 1n+Nat.add(p, b), concat.succ(p, b))

# a plus 0 is a
law concat.zero:
  for a: Nat
  {Nat.add(a, 0n) == a : Nat}

def concat.zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 0n), p, concat.zero(p))

# addition regroups
law concat.assoc:
  for a: Nat
  for -b: Nat
  for -c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def concat.assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), concat.assoc(p, b, c))

# the first two of three summands swap
law concat.swap:
  for a: Nat
  for +b: Nat
  for -c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}

def concat.swap(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, Nat.add(b, c)), 1n+Nat.add(b, Nat.add(p, c)), Nat.add(b, 1n+Nat.add(p, c)),
        Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, Nat.add(b, c)), Nat.add(b, Nat.add(p, c)), concat.swap(p, b, c)),
        Equal.sym(Nat, Nat.add(b, 1n+Nat.add(p, c)), 1n+Nat.add(b, Nat.add(p, c)), concat.succ(b, Nat.add(p, c))))

# a list reversed onto another is as long as both
law concat.rev:
  for xs: List<&2, F.Finding>
  for ys: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.reverse.go(&2, F.Finding, xs, ys))
    == Nat.add(List.length(&2, F.Finding, xs), List.length(&2, F.Finding, ys)) : Nat}

def concat.rev(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat, List.length(&2, F.Finding, List.reverse.go(&2, F.Finding, t, h <> ys)),
        Nat.add(List.length(&2, F.Finding, t), 1n+List.length(&2, F.Finding, ys)),
        1n+Nat.add(List.length(&2, F.Finding, t), List.length(&2, F.Finding, ys)),
        concat.rev(t, h <> ys), concat.succ(List.length(&2, F.Finding, t), List.length(&2, F.Finding, ys)))

# the lengths of a list of finding lists, summed
def concat.sum(xss: List<&2, List<&2, F.Finding>>) -> Nat:
  match xss:
    case Nil{}:
      0n
    case Con{+h, +t}:
      Nat.add(List.length(&2, F.Finding, h), concat.sum(t))

# a join is as long as its lists together
law concat.flat:
  for xss: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, xss)) == concat.sum(xss) : Nat}

def concat.flat(xss):
  match xss:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, h, List.concat(&2, F.Finding, t))),
        Nat.add(List.length(&2, F.Finding, h), List.length(&2, F.Finding, List.concat(&2, F.Finding, t))),
        Nat.add(List.length(&2, F.Finding, h), concat.sum(t)),
        esc.app(h, List.concat(&2, F.Finding, t)),
        Equal.cong(Nat, Nat, n => Nat.add(List.length(&2, F.Finding, h), n),
          List.length(&2, F.Finding, List.concat(&2, F.Finding, t)), concat.sum(t), concat.flat(t)))

# lists reversed onto others sum to both sums
law concat.rsum:
  for xss: List<&2, List<&2, F.Finding>>
  for yss: List<&2, List<&2, F.Finding>>
  {concat.sum(List.reverse.go(&2, List<&2, F.Finding>, xss, yss)) == Nat.add(concat.sum(xss), concat.sum(yss)) : Nat}

def concat.rsum(xss, yss):
  match xss:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat, concat.sum(List.reverse.go(&2, List<&2, F.Finding>, t, h <> yss)),
        Nat.add(concat.sum(t), Nat.add(List.length(&2, F.Finding, h), concat.sum(yss))),
        Nat.add(Nat.add(List.length(&2, F.Finding, h), concat.sum(t)), concat.sum(yss)),
        concat.rsum(t, h <> yss),
        Equal.trans(Nat, Nat.add(concat.sum(t), Nat.add(List.length(&2, F.Finding, h), concat.sum(yss))),
          Nat.add(List.length(&2, F.Finding, h), Nat.add(concat.sum(t), concat.sum(yss))),
          Nat.add(Nat.add(List.length(&2, F.Finding, h), concat.sum(t)), concat.sum(yss)),
          concat.swap(concat.sum(t), List.length(&2, F.Finding, h), concat.sum(yss)),
          Equal.sym(Nat, Nat.add(Nat.add(List.length(&2, F.Finding, h), concat.sum(t)), concat.sum(yss)),
            Nat.add(List.length(&2, F.Finding, h), Nat.add(concat.sum(t), concat.sum(yss))),
            concat.assoc(List.length(&2, F.Finding, h), concat.sum(t), concat.sum(yss)))))

# two lists joined count what each counts
law concat.two:
  for a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for -x: Nat
  for -y: Nat
  for ea: {List.length(&2, F.Finding, a) == x : Nat}
  for eb: {List.length(&2, F.Finding, b) == y : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b])) == Nat.add(x, y) : Nat}

def concat.two(a, b, x, y, ea, eb):
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b])),
    Nat.add(List.length(&2, F.Finding, a), Nat.add(List.length(&2, F.Finding, b), 0n)), Nat.add(x, y),
    concat.flat([a, b]),
    esc.add(List.length(&2, F.Finding, a), x, Nat.add(List.length(&2, F.Finding, b), 0n), y, ea,
      Equal.trans(Nat, Nat.add(List.length(&2, F.Finding, b), 0n), List.length(&2, F.Finding, b), y,
        concat.zero(List.length(&2, F.Finding, b)), eb)))

# three lists joined count what each counts
law concat.three:
  for a: List<&2, F.Finding>
  for b: List<&2, F.Finding>
  for +c: List<&2, F.Finding>
  for -x: Nat
  for -y: Nat
  for -z: Nat
  for ea: {List.length(&2, F.Finding, a) == x : Nat}
  for eb: {List.length(&2, F.Finding, b) == y : Nat}
  for ec: {List.length(&2, F.Finding, c) == z : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])) == Nat.add(x, Nat.add(y, z)) : Nat}

def concat.three(a, b, c, x, y, z, ea, eb, ec):
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])),
    Nat.add(List.length(&2, F.Finding, a),
      Nat.add(List.length(&2, F.Finding, b), Nat.add(List.length(&2, F.Finding, c), 0n))),
    Nat.add(x, Nat.add(y, z)),
    concat.flat([a, b, c]),
    esc.add(List.length(&2, F.Finding, a), x,
      Nat.add(List.length(&2, F.Finding, b), Nat.add(List.length(&2, F.Finding, c), 0n)), Nat.add(y, z), ea,
      esc.add(List.length(&2, F.Finding, b), y, Nat.add(List.length(&2, F.Finding, c), 0n), z, eb,
        Equal.trans(Nat, Nat.add(List.length(&2, F.Finding, c), 0n), List.length(&2, F.Finding, c), z,
          concat.zero(List.length(&2, F.Finding, c)), ec))))

# a stop on `not b` runs its thunk exactly when b holds
law concat.stop:
  for b: Bool
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(b), [], _u => more))
    == Bool.pick(Nat, b, m, 0n) : Nat}

def concat.stop(b, _more, _m, ih):
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# a finding in front when the flag holds, counted on either side of a sum
law concat.bump:
  for b: Bool
  for +l: Nat
  for +m: Nat
  {Nat.add(Bool.pick(Nat, b, 1n+l, l), m) == Nat.add(l, Bool.pick(Nat, b, 1n+m, m)) : Nat}

def concat.bump(b, l, m):
  match b:
    case True{}:
      Equal.sym(Nat, Nat.add(l, 1n+m), 1n+Nat.add(l, m), concat.succ(l, m))
    case False{}:
      {==}

# hit adds one finding exactly when the argument appends onto its slot
law concat.hit:
  for mm: Maybe<&2, Lex.Tok>
  for +slot: String
  for +path: String
  for +acc: List<&2, F.Finding>
  {List.length(&2, F.Finding, Concat.hit(mm, slot, path, acc))
    == Bool.pick(Nat, Laws.concat.is(mm, slot), 1n+List.length(&2, F.Finding, acc), List.length(&2, F.Finding, acc))
    : Nat}

def concat.hit(mm, slot, path, acc):
  match mm:
    case None{}:
      {==}
    case Some{Lex.Tok{k, +t, l, c}}:
      nat.pick(String.eq(t, slot), F.Finding{path, l, c, U32.from_nat(String.length(t)), "concat",
        t ++ " grows by appending on each step, which is quadratic; prepend and reverse once, or build with <>."},
        acc, List.length(&2, F.Finding, acc), {==})

# one argument's hit and the rest's, against its slot
law concat.arg:
  for +a: Tree.Node
  for +rest: List<&2, Tree.Node>
  for +slot: String
  for +ps: List<&2, String>
  for +path: String
  for +acc: List<&2, F.Finding>
  for ih: {List.length(&2, F.Finding, Concat.hits(rest, ps, path, Concat.hit(Concat.onto(a), slot, path, acc)))
    == Nat.add(List.length(&2, F.Finding, Concat.hit(Concat.onto(a), slot, path, acc)), Laws.concat.slots(rest, ps))
    : Nat}
  {List.length(&2, F.Finding, Concat.hits(rest, ps, path, Concat.hit(Concat.onto(a), slot, path, acc)))
    == Nat.add(List.length(&2, F.Finding, acc),
      Bool.pick(Nat, Laws.concat.is(Concat.onto(a), slot), 1n+Laws.concat.slots(rest, ps), Laws.concat.slots(rest, ps)))
    : Nat}

def concat.arg(a, rest, slot, ps, path, acc, ih):
  Equal.trans(Nat, List.length(&2, F.Finding, Concat.hits(rest, ps, path, Concat.hit(Concat.onto(a), slot, path, acc))),
    Nat.add(List.length(&2, F.Finding, Concat.hit(Concat.onto(a), slot, path, acc)), Laws.concat.slots(rest, ps)),
    Nat.add(List.length(&2, F.Finding, acc),
      Bool.pick(Nat, Laws.concat.is(Concat.onto(a), slot), 1n+Laws.concat.slots(rest, ps),
        Laws.concat.slots(rest, ps))),
    ih,
    Equal.trans(Nat,
      Nat.add(List.length(&2, F.Finding, Concat.hit(Concat.onto(a), slot, path, acc)), Laws.concat.slots(rest, ps)),
      Nat.add(Bool.pick(Nat, Laws.concat.is(Concat.onto(a), slot), 1n+List.length(&2, F.Finding, acc),
        List.length(&2, F.Finding, acc)), Laws.concat.slots(rest, ps)),
      Nat.add(List.length(&2, F.Finding, acc),
        Bool.pick(Nat, Laws.concat.is(Concat.onto(a), slot), 1n+Laws.concat.slots(rest, ps),
          Laws.concat.slots(rest, ps))),
      Equal.cong(Nat, Nat, n => Nat.add(n, Laws.concat.slots(rest, ps)),
        List.length(&2, F.Finding, Concat.hit(Concat.onto(a), slot, path, acc)),
        Bool.pick(Nat, Laws.concat.is(Concat.onto(a), slot), 1n+List.length(&2, F.Finding, acc),
          List.length(&2, F.Finding, acc)),
        concat.hit(Concat.onto(a), slot, path, acc)),
      concat.bump(Laws.concat.is(Concat.onto(a), slot), List.length(&2, F.Finding, acc), Laws.concat.slots(rest, ps))))

# hits adds to its accumulator one finding for each argument that appends
# onto its own slot
law concat.hits:
  for as: List<&2, Tree.Node>
  for +params: List<&2, String>
  for +path: String
  for +acc: List<&2, F.Finding>
  {List.length(&2, F.Finding, Concat.hits(as, params, path, acc))
    == Nat.add(List.length(&2, F.Finding, acc), Laws.concat.slots(as, params)) : Nat}

def concat.hits(as, params, path, acc):
  match as:
    case Nil{}:
      concat.rev(acc, Nil{})
    case Con{+a, +rest}:
      match params:
        case Nil{}:
          concat.arg(a, rest, "", Nil{}, path, acc,
            concat.hits(rest, Nil{}, path, Concat.hit(Concat.onto(a), "", path, acc)))
        case Con{+p, +ps}:
          concat.arg(a, rest, p, ps, path, acc,
            concat.hits(rest, ps, path, Concat.hit(Concat.onto(a), p, path, acc)))

# a def's count moves from the front of the sum past the accumulator's
law concat.move:
  for +x: Nat
  for -y: Nat
  for +s: Nat
  for +f: Nat
  for e: {x == y : Nat}
  {Nat.add(Nat.add(x, s), f) == Nat.add(s, Nat.add(y, f)) : Nat}

def concat.move(x, y, s, f, e):
  Equal.trans(Nat, Nat.add(Nat.add(x, s), f), Nat.add(s, Nat.add(x, f)), Nat.add(s, Nat.add(y, f)),
    Equal.trans(Nat, Nat.add(Nat.add(x, s), f), Nat.add(x, Nat.add(s, f)), Nat.add(s, Nat.add(x, f)),
      concat.assoc(x, s, f), concat.swap(x, s, f)),
    Equal.cong(Nat, Nat, n => Nat.add(s, Nat.add(n, f)), x, y, e))

# a leaf and a group: the self-call's hits, then the group's and the rest's
# counts, given the walk's law on the group's kids and on the rest
law concat.call:
  for tok: Lex.Tok
  for open: Lex.Tok
  for +kids: Tree.Node
  for cl: Maybe<&2, Lex.Tok>
  for +rest: Tree.Node
  for +name: String
  for +params: List<&2, String>
  for +path: String
  for ik: {List.length(&2, F.Finding, Concat.walk(kids, name, params, path))
    == Laws.concat.count(kids, name, params) : Nat}
  for ir: {List.length(&2, F.Finding, Concat.walk(rest, name, params, path))
    == Laws.concat.count(rest, name, params) : Nat}
  {List.length(&2, F.Finding,
    Concat.walk(Tree.NCons{Tree.Leaf{tok}, Tree.NCons{Tree.Group{open, kids, cl}, rest}}, name, params, path))
    == Laws.concat.count(Tree.NCons{Tree.Leaf{tok}, Tree.NCons{Tree.Group{open, kids, cl}, rest}}, name, params)
    : Nat}

def concat.call(tok, open, kids, _cl, rest, name, params, path, ik, ir):
  match tok open:
    case Lex.Tok{k, +t, l, c} Lex.Tok{ok, +o, ol, oc}:
      concat.three(
        Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(String.eq(o, "("), String.eq(t, name))), [],
          _u => Concat.hits(Calls.args(kids), params, path, [])),
        Concat.walk(kids, name, params, path), Concat.walk(rest, name, params, path),
        Bool.pick(Nat, Bool.and(String.eq(o, "("), String.eq(t, name)),
          Laws.concat.slots(Calls.args(kids), params), 0n),
        Laws.concat.count(kids, name, params), Laws.concat.count(rest, name, params),
        concat.stop(Bool.and(String.eq(o, "("), String.eq(t, name)),
          Concat.hits(Calls.args(kids), params, path, []),
          Laws.concat.slots(Calls.args(kids), params), concat.hits(Calls.args(kids), params, path, [])),
        ik, ir)

# walk finds what the law's count counts, node by node
law concat.walk:
  for nn: Tree.Node
  for +name: String
  for +params: List<&2, String>
  for +path: String
  {List.length(&2, F.Finding, Concat.walk(nn, name, params, path)) == Laws.concat.count(nn, name, params) : Nat}

def concat.walk(nn, name, params, path):
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{ok, o, ol, oc}, +kids, cl}, +rest}}:
      concat.call(Lex.Tok{k, t, l, c}, Lex.Tok{ok, o, ol, oc}, kids, cl, rest, name, params, path,
        concat.walk(kids, name, params, path), concat.walk(rest, name, params, path))
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.Leaf{x}, rest}}:
      concat.walk(Tree.NCons{Tree.Leaf{x}, rest}, name, params, path)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.Stmt{kind, kids, body}, rest}}:
      concat.walk(Tree.NCons{Tree.Stmt{kind, kids, body}, rest}, name, params, path)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.NNil{}, rest}}:
      concat.walk(Tree.NCons{Tree.NNil{}, rest}, name, params, path)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.NCons{a, b}, rest}}:
      concat.walk(Tree.NCons{Tree.NCons{a, b}, rest}, name, params, path)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.Leaf{x}}:
      {==}
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.Group{open, kids, close}}:
      {==}
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.Stmt{kind, kids, body}}:
      {==}
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NNil{}}:
      {==}
    case Tree.NCons{Tree.Group{open, +kids, close}, +rest}:
      concat.two(Concat.walk(kids, name, params, path), Concat.walk(rest, name, params, path),
        Laws.concat.count(kids, name, params), Laws.concat.count(rest, name, params),
        concat.walk(kids, name, params, path), concat.walk(rest, name, params, path))
    case Tree.NCons{Tree.Stmt{kind, +kids, +body}, +rest}:
      concat.three(Concat.walk(kids, name, params, path), Concat.walk(body, name, params, path),
        Concat.walk(rest, name, params, path),
        Laws.concat.count(kids, name, params), Laws.concat.count(body, name, params),
        Laws.concat.count(rest, name, params),
        concat.walk(kids, name, params, path), concat.walk(body, name, params, path),
        concat.walk(rest, name, params, path))
    case Tree.NCons{Tree.NNil{}, rest}:
      concat.walk(rest, name, params, path)
    case Tree.NCons{Tree.NCons{a, b}, rest}:
      concat.walk(rest, name, params, path)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# the def walk adds each def's count, none for an exempt def, to what its
# accumulator already holds
law concat.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Concat.check.go(ds, path, acc))
    == Nat.add(concat.sum(acc), Laws.concat.file(ds, path)) : Nat}

def concat.go(ds, path, acc):
  match ds:
    case Nil{}:
      Equal.trans(Nat,
        List.length(&2, F.Finding, List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))),
        concat.sum(List.reverse.go(&2, List<&2, F.Finding>, acc, Nil{})), Nat.add(concat.sum(acc), 0n),
        concat.flat(List.reverse(&2, List<&2, F.Finding>, acc)), concat.rsum(acc, Nil{}))
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      Equal.trans(Nat,
        List.length(&2, F.Finding, Concat.check.go(rest, path,
          Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
            _u => Concat.walk(body, name, Calls.names(sig), path)) <> acc)),
        Nat.add(Nat.add(List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
          _u => Concat.walk(body, name, Calls.names(sig), path))), concat.sum(acc)), Laws.concat.file(rest, path)),
        Nat.add(concat.sum(acc),
          Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n, Laws.concat.count(body, name, Calls.names(sig))),
            Laws.concat.file(rest, path))),
        concat.go(rest, path, Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
          _u => Concat.walk(body, name, Calls.names(sig), path)) <> acc),
        concat.move(List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
            _u => Concat.walk(body, name, Calls.names(sig), path))),
          Bool.pick(Nat, Calls.exempt(path, sig), 0n, Laws.concat.count(body, name, Calls.names(sig))),
          concat.sum(acc), Laws.concat.file(rest, path),
          param.stop(Calls.exempt(path, sig), Concat.walk(body, name, Calls.names(sig), path),
            Laws.concat.count(body, name, Calls.names(sig)), concat.walk(body, name, Calls.names(sig), path))))

def Laws.concat_counts(path, _text, _toks, tree, _bound, _items):
  concat.go(Calls.defs(tree), path, [])

# eager (BOLT-RULE-U003). The walk reports a hot call in front of its
# group's findings and the rest's, so the count adds one before adding
# them; the def walk is concat's, so concat's lemmas carry it.

# work finds what the law's count counts, node by node, in every state
law eager.work:
  for nn: Tree.Node
  for +ns: List<&2, String>
  for +self: String
  for +path: String
  for +hot: Bool
  for +seg: U32
  for +keep: Bool
  {List.length(&2, F.Finding, Eager.work(nn, ns, self, path, hot, seg, keep))
    == Laws.eager.count(nn, ns, self, hot, seg, keep) : Nat}

def eager.work(nn, ns, self, path, hot, seg, keep):
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, +t, +l, +c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, +rest}}:
      +now = Eager.work.hot(k, hot, seg, keep)
      +call = Bool.and(Eager.work.name(k), String.eq(o, "("))
      +is_pick = Bool.and(call, String.eq(t, "Bool.pick"))
      +mine = Bool.and(Bool.not(String.eq(t, self)), List.contains(~String, ~String.eq, ns, t))
      +inner = Bool.and(now, Bool.not(is_pick))
      nat.pick(Bool.and(now, Bool.and(call, mine)),
        F.Finding{path, l, c, U32.from_nat(String.length(t)), "eager",
          t ++ " runs in both branches of Bool.pick, so it runs whatever the condition; bind it above, or use Lazy.stop."},
        List.concat(&2, F.Finding,
          [Eager.work(kids, ns, self, path, inner, Bool.pick(U32, is_pick, 0, 9), inner),
            Eager.work(rest, ns, self, path, now, Eager.work.seg(k, seg), keep)]),
        Nat.add(Laws.eager.count(kids, ns, self, inner, Bool.pick(U32, is_pick, 0, 9), inner),
          Laws.eager.count(rest, ns, self, now, Eager.work.seg(k, seg), keep)),
        concat.two(Eager.work(kids, ns, self, path, inner, Bool.pick(U32, is_pick, 0, 9), inner),
          Eager.work(rest, ns, self, path, now, Eager.work.seg(k, seg), keep),
          Laws.eager.count(kids, ns, self, inner, Bool.pick(U32, is_pick, 0, 9), inner),
          Laws.eager.count(rest, ns, self, now, Eager.work.seg(k, seg), keep),
          eager.work(kids, ns, self, path, inner, Bool.pick(U32, is_pick, 0, 9), inner),
          eager.work(rest, ns, self, path, now, Eager.work.seg(k, seg), keep)))
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, t, l, c}}, Tree.NCons{Tree.Leaf{x}, rest}}:
      eager.work(Tree.NCons{Tree.Leaf{x}, rest}, ns, self, path, Eager.work.hot(k, hot, seg, keep),
        Eager.work.seg(k, seg), keep)
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, t, l, c}}, Tree.NCons{Tree.Stmt{kind, kids, body}, rest}}:
      eager.work(Tree.NCons{Tree.Stmt{kind, kids, body}, rest}, ns, self, path, Eager.work.hot(k, hot, seg, keep),
        Eager.work.seg(k, seg), keep)
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, t, l, c}}, Tree.NCons{Tree.NNil{}, rest}}:
      eager.work(Tree.NCons{Tree.NNil{}, rest}, ns, self, path, Eager.work.hot(k, hot, seg, keep),
        Eager.work.seg(k, seg), keep)
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, t, l, c}}, Tree.NCons{Tree.NCons{a, b}, rest}}:
      eager.work(Tree.NCons{Tree.NCons{a, b}, rest}, ns, self, path, Eager.work.hot(k, hot, seg, keep),
        Eager.work.seg(k, seg), keep)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.Leaf{x}}:
      {==}
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.Group{open, kids, close}}:
      {==}
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.Stmt{kind, kids, body}}:
      {==}
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NNil{}}:
      {==}
    case Tree.NCons{Tree.Group{open, +kids, close}, +rest}:
      concat.two(Eager.work(kids, ns, self, path, hot, 9, hot), Eager.work(rest, ns, self, path, hot, seg, keep),
        Laws.eager.count(kids, ns, self, hot, 9, hot), Laws.eager.count(rest, ns, self, hot, seg, keep),
        eager.work(kids, ns, self, path, hot, 9, hot), eager.work(rest, ns, self, path, hot, seg, keep))
    case Tree.NCons{Tree.Stmt{kind, +kids, +body}, +rest}:
      concat.three(Eager.work(kids, ns, self, path, False{}, 9, False{}),
        Eager.work(body, ns, self, path, False{}, 9, False{}), Eager.work(rest, ns, self, path, hot, seg, keep),
        Laws.eager.count(kids, ns, self, False{}, 9, False{}), Laws.eager.count(body, ns, self, False{}, 9, False{}),
        Laws.eager.count(rest, ns, self, hot, seg, keep),
        eager.work(kids, ns, self, path, False{}, 9, False{}), eager.work(body, ns, self, path, False{}, 9, False{}),
        eager.work(rest, ns, self, path, hot, seg, keep))
    case Tree.NCons{Tree.NNil{}, rest}:
      eager.work(rest, ns, self, path, hot, seg, keep)
    case Tree.NCons{Tree.NCons{a, b}, rest}:
      eager.work(rest, ns, self, path, hot, seg, keep)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# the def walk adds each def's count, none for an exempt def, to what its
# accumulator already holds
law eager.go:
  for ds: List<&2, Calls.Def>
  for +ns: List<&2, String>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Eager.check.go(ds, ns, path, acc))
    == Nat.add(concat.sum(acc), Laws.eager.file(ds, ns, path)) : Nat}

def eager.go(ds, ns, path, acc):
  match ds:
    case Nil{}:
      Equal.trans(Nat,
        List.length(&2, F.Finding, List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))),
        concat.sum(List.reverse.go(&2, List<&2, F.Finding>, acc, Nil{})), Nat.add(concat.sum(acc), 0n),
        concat.flat(List.reverse(&2, List<&2, F.Finding>, acc)), concat.rsum(acc, Nil{}))
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      Equal.trans(Nat,
        List.length(&2, F.Finding, Eager.check.go(rest, ns, path,
          Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
            _u => Eager.work(body, ns, name, path, False{}, 9, False{})) <> acc)),
        Nat.add(Nat.add(List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
          _u => Eager.work(body, ns, name, path, False{}, 9, False{}))), concat.sum(acc)),
          Laws.eager.file(rest, ns, path)),
        Nat.add(concat.sum(acc),
          Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n, Laws.eager.count(body, ns, name, False{}, 9, False{})),
            Laws.eager.file(rest, ns, path))),
        eager.go(rest, ns, path, Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
          _u => Eager.work(body, ns, name, path, False{}, 9, False{})) <> acc),
        concat.move(List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
            _u => Eager.work(body, ns, name, path, False{}, 9, False{}))),
          Bool.pick(Nat, Calls.exempt(path, sig), 0n, Laws.eager.count(body, ns, name, False{}, 9, False{})),
          concat.sum(acc), Laws.eager.file(rest, ns, path),
          param.stop(Calls.exempt(path, sig), Eager.work(body, ns, name, path, False{}, 9, False{}),
            Laws.eager.count(body, ns, name, False{}, 9, False{}),
            eager.work(body, ns, name, path, False{}, 9, False{}))))

def Laws.eager_counts(path, _text, _toks, tree, _bound, _items):
  eager.go(Calls.defs(tree), Eager.loops(Calls.defs(tree)), path, [])

def Laws.eager_lambda(_hot, _seg, _keep):
  {==}

def Laws.eager_comma(_hot, _keep):
  {==}

# Unit for False, Empty for True
def eager.false_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Unit
    case True{}:
      Empty

# False is never True
law eager.false_true:
  for e: {False{} == True{} : Bool}
  Empty

def eager.false_true(e):
  %e : eager.false_ty(_)
  Unit{}

def Laws.eager_plain(kk, hot, seg, keep, e):
  match kk:
    case Lex.TLam{}:
      Empty.absurd(
        {(Eager.work.hot(Lex.TLam{}, hot, seg, keep), Eager.work.seg(Lex.TLam{}, seg), Eager.work.name(Lex.TLam{}))
          == (hot, seg, True{}) : Bool & U32 & Bool}, eager.false_true(e))
    case Lex.TComma{}:
      Empty.absurd(
        {(Eager.work.hot(Lex.TComma{}, hot, seg, keep), Eager.work.seg(Lex.TComma{}, seg),
            Eager.work.name(Lex.TComma{}))
          == (hot, seg, True{}) : Bool & U32 & Bool}, eager.false_true(e))
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
    case Lex.TAll{}:
      {==}
    case Lex.TAmp{}:
      {==}
    case Lex.TOpen{}:
      {==}
    case Lex.TClose{}:
      {==}

# The table rules, table (BOLT-RULE-U008) and ring (BOLT-RULE-U010): a walk
# joins a site's own findings with its group's and the rest's, so its count
# is their sum; the def walk sums the defs the guard keeps (pick.sum).

# two joined lists that count m and n count m + n
law table.two:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for -m: Nat
  for -n: Nat
  for e1: {List.length(&2, F.Finding, a) == m : Nat}
  for e2: {List.length(&2, F.Finding, b) == n : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b])) == Nat.add(m, n) : Nat}

def table.two(a, b, m, n, e1, e2):
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b])),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, b)), Nat.add(m, n),
    tail.cat2(a, b), esc.add(List.length(&2, F.Finding, a), m, List.length(&2, F.Finding, b), n, e1, e2))

# three joined lists that count m, n and p count m + (n + p)
law table.three:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for +c: List<&2, F.Finding>
  for -m: Nat
  for -n: Nat
  for -p: Nat
  for e1: {List.length(&2, F.Finding, a) == m : Nat}
  for e2: {List.length(&2, F.Finding, b) == n : Nat}
  for e3: {List.length(&2, F.Finding, c) == p : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])) == Nat.add(m, Nat.add(n, p)) : Nat}

def table.three(a, b, c, m, n, p, e1, e2, e3):
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])),
    Nat.add(List.length(&2, F.Finding, a), Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c))),
    Nat.add(m, Nat.add(n, p)),
    tail.cat3(a, b, c),
    esc.add(List.length(&2, F.Finding, a), m,
      Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c)), Nat.add(n, p), e1,
      esc.add(List.length(&2, F.Finding, b), n, List.length(&2, F.Finding, c), p, e2, e3)))

# a call site's own finding: one exactly when the law's site test holds
law table.one:
  for +tt: String
  for +o: String
  for +kids: Tree.Node
  for +fixed: List<&2, String>
  for +path: String
  for +line: U32
  for +col: U32
  {List.length(&2, F.Finding, Table.hit(String.eq(o, "("), tt, kids, fixed, path, line, col))
    == Bool.pick(Nat, Laws.table.site(tt, o, kids, fixed), 1n, 0n) : Nat}

def table.one(tt, o, kids, fixed, path, line, col):
  chars.one(Laws.table.site(tt, o, kids, fixed),
    Table.cite(String.eq(tt, "List.get"), path, line, col, U32.from_nat(String.length(tt))))

def Laws.table_walk_counts(nn, path, fixed):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{Lex.Tok{k, +t, +l, +c}}:
          match rest:
            case Tree.NCons{h2, +r2}:
              match h2:
                case Tree.Group{Lex.Tok{k2, +o, l2, c2}, +kids, cl}:
                  table.three(Table.hit(String.eq(o, "("), t, kids, fixed, path, l, c), Table.walk(kids, path, fixed),
                    Table.walk(r2, path, fixed), Bool.pick(Nat, Laws.table.site(t, o, kids, fixed), 1n, 0n),
                    Laws.table.count(kids, fixed), Laws.table.count(r2, fixed),
                    table.one(t, o, kids, fixed, path, l, c),
                    Laws.table_walk_counts(kids, path, fixed), Laws.table_walk_counts(r2, path, fixed))
                case Tree.Leaf{x}:
                  Laws.table_walk_counts(rest, path, fixed)
                case Tree.Stmt{a, b, d}:
                  Laws.table_walk_counts(rest, path, fixed)
                case Tree.NNil{}:
                  Laws.table_walk_counts(rest, path, fixed)
                case Tree.NCons{a, b}:
                  Laws.table_walk_counts(rest, path, fixed)
            case Tree.Leaf{x}:
              Laws.table_walk_counts(rest, path, fixed)
            case Tree.Group{a, b, d}:
              Laws.table_walk_counts(rest, path, fixed)
            case Tree.Stmt{a, b, d}:
              Laws.table_walk_counts(rest, path, fixed)
            case Tree.NNil{}:
              Laws.table_walk_counts(rest, path, fixed)
        case Tree.Group{open, +kids, close}:
          table.two(Table.walk(kids, path, fixed), Table.walk(rest, path, fixed),
            Laws.table.count(kids, fixed), Laws.table.count(rest, fixed),
            Laws.table_walk_counts(kids, path, fixed), Laws.table_walk_counts(rest, path, fixed))
        case Tree.Stmt{kind, +kids, +body}:
          table.three(Table.walk(kids, path, fixed), Table.walk(body, path, fixed), Table.walk(rest, path, fixed),
            Laws.table.count(kids, fixed), Laws.table.count(body, fixed), Laws.table.count(rest, fixed),
            Laws.table_walk_counts(kids, path, fixed), Laws.table_walk_counts(body, path, fixed),
            Laws.table_walk_counts(rest, path, fixed))
        case Tree.NNil{}:
          Laws.table_walk_counts(rest, path, fixed)
        case Tree.NCons{a, b}:
          Laws.table_walk_counts(rest, path, fixed)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{a, b, d}:
      {==}
    case Tree.Stmt{a, b, d}:
      {==}
    case Tree.NNil{}:
      {==}

# one def's findings: walked when its guard keeps it, else none
law table.stop:
  for +b: Bool
  for +body: Tree.Node
  for +path: String
  for +fixed: List<&2, String>
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(b), [], _u => Table.walk(body, path, fixed)))
    == Bool.pick(Nat, b, Laws.table.count(body, fixed), 0n) : Nat}

def table.stop(b, body, path, fixed):
  match b:
    case True{}:
      Laws.table_walk_counts(body, path, fixed)
    case False{}:
      {==}

# table's def walk: the findings gathered so far, then each def's
law table.go:
  for ds: List<&2, Calls.Def>
  for +mods: List<&2, String>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Table.check.go(ds, mods, path, acc)) == pick.sum(acc, Laws.table.defs(ds, mods, path))
    : Nat}

def table.go(ds, mods, path, acc):
  match ds:
    case Nil{}:
      pick.rev(acc, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +keep = Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))
      +x = Lazy.stop(List<&2, F.Finding>, Bool.not(keep), [], _u => Table.walk(body, path, Table.scope(body, mods)))
      +cb = Bool.pick(Nat, keep, Laws.table.count(body, Table.scope(body, mods)), 0n)
      Equal.trans(Nat, List.length(&2, F.Finding, Table.check.go(rest, mods, path, x <> acc)),
        pick.sum(acc, Nat.add(List.length(&2, F.Finding, x), Laws.table.defs(rest, mods, path))),
        pick.sum(acc, Nat.add(cb, Laws.table.defs(rest, mods, path))),
        table.go(rest, mods, path, x <> acc),
        Equal.cong(Nat, Nat, n => pick.sum(acc, Nat.add(n, Laws.table.defs(rest, mods, path))),
          List.length(&2, F.Finding, x), cb, table.stop(keep, body, path, Table.scope(body, mods))))

def Laws.table_counts(path, _text, _toks, tree, _bound, _items):
  table.go(Calls.defs(tree), Table.modules(Calls.defs(tree), []), path, Nil{})

# a scan's finding counts one when it found a drop, else none
law ring.one:
  for mm: Maybe<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Ring.slide_at(mm, path)) == Laws.ring.hit(mm) : Nat}

def ring.one(mm, _path):
  match mm:
    case None{}:
      {==}
    case Some{Lex.Tok{k, t, l, c}}:
      {==}

# a self-call's arguments, each read against its own slot
law ring.slides:
  for as: List<&2, Tree.Node>
  for +params: List<&2, String>
  for +path: String
  for +wins: List<&2, String>
  {List.length(&2, F.Finding, Ring.slides(as, params, path, wins)) == Laws.ring.args(as, params, wins) : Nat}

def ring.slides(as, params, path, wins):
  match as:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      +scan = Ring.plus_scan(h, None{}, Ring.slot_wins(Maybe.default(&2, String, List.head(&2, String, params), ""),
        wins))
      +x = Ring.slide_at(scan, path)
      +more = Ring.slides(rest, List.tail(&2, String, params), path, wins)
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, x, more)),
        Nat.add(List.length(&2, F.Finding, x), List.length(&2, F.Finding, more)),
        Nat.add(Laws.ring.hit(scan), Laws.ring.args(rest, List.tail(&2, String, params), wins)),
        esc.app(x, more),
        esc.add(List.length(&2, F.Finding, x), Laws.ring.hit(scan), List.length(&2, F.Finding, more),
          Laws.ring.args(rest, List.tail(&2, String, params), wins), ring.one(scan, path),
          ring.slides(rest, List.tail(&2, String, params), path, wins)))

def Laws.ring_walk_counts(nn, self, params, path, wins):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{Lex.Tok{k, +t, l, c}}:
          match rest:
            case Tree.NCons{h2, +r2}:
              match h2:
                case Tree.Group{Lex.Tok{k2, +o, l2, c2}, +kids, cl}:
                  +me = Bool.and(String.eq(o, "("), String.eq(t, self))
                  table.three(
                    Lazy.stop(List<&2, F.Finding>, Bool.not(me), [], _u => Ring.slides(Calls.args(kids), params, path,
                      wins)),
                    Ring.walk(kids, self, params, path, wins), Ring.walk(r2, self, params, path, wins),
                    Bool.pick(Nat, me, Laws.ring.args(Calls.args(kids), params, wins), 0n),
                    Laws.ring.count(kids, self, params, wins), Laws.ring.count(r2, self, params, wins),
                    tail.stop(me, Ring.slides(Calls.args(kids), params, path, wins),
                      Laws.ring.args(Calls.args(kids), params, wins),
                      ring.slides(Calls.args(kids), params, path, wins)),
                    Laws.ring_walk_counts(kids, self, params, path, wins),
                    Laws.ring_walk_counts(r2, self, params, path, wins))
                case Tree.Leaf{x}:
                  Laws.ring_walk_counts(rest, self, params, path, wins)
                case Tree.Stmt{a, b, d}:
                  Laws.ring_walk_counts(rest, self, params, path, wins)
                case Tree.NNil{}:
                  Laws.ring_walk_counts(rest, self, params, path, wins)
                case Tree.NCons{a, b}:
                  Laws.ring_walk_counts(rest, self, params, path, wins)
            case Tree.Leaf{x}:
              Laws.ring_walk_counts(rest, self, params, path, wins)
            case Tree.Group{a, b, d}:
              Laws.ring_walk_counts(rest, self, params, path, wins)
            case Tree.Stmt{a, b, d}:
              Laws.ring_walk_counts(rest, self, params, path, wins)
            case Tree.NNil{}:
              Laws.ring_walk_counts(rest, self, params, path, wins)
        case Tree.Group{open, +kids, close}:
          table.two(Ring.walk(kids, self, params, path, wins), Ring.walk(rest, self, params, path, wins),
            Laws.ring.count(kids, self, params, wins), Laws.ring.count(rest, self, params, wins),
            Laws.ring_walk_counts(kids, self, params, path, wins),
            Laws.ring_walk_counts(rest, self, params, path, wins))
        case Tree.Stmt{kind, +kids, +body}:
          table.three(Ring.walk(kids, self, params, path, wins), Ring.walk(body, self, params, path, wins),
            Ring.walk(rest, self, params, path, wins), Laws.ring.count(kids, self, params, wins),
            Laws.ring.count(body, self, params, wins), Laws.ring.count(rest, self, params, wins),
            Laws.ring_walk_counts(kids, self, params, path, wins),
            Laws.ring_walk_counts(body, self, params, path, wins),
            Laws.ring_walk_counts(rest, self, params, path, wins))
        case Tree.NNil{}:
          Laws.ring_walk_counts(rest, self, params, path, wins)
        case Tree.NCons{a, b}:
          Laws.ring_walk_counts(rest, self, params, path, wins)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{a, b, d}:
      {==}
    case Tree.Stmt{a, b, d}:
      {==}
    case Tree.NNil{}:
      {==}

# one def's findings: walked when its guard keeps it, else none
law ring.stop:
  for +b: Bool
  for +body: Tree.Node
  for +self: String
  for +params: List<&2, String>
  for +path: String
  for +wins: List<&2, String>
  {List.length(&2, F.Finding,
    Lazy.stop(List<&2, F.Finding>, Bool.not(b), [], _u => Ring.walk(body, self, params, path, wins)))
    == Bool.pick(Nat, b, Laws.ring.count(body, self, params, wins), 0n) : Nat}

def ring.stop(b, body, self, params, path, wins):
  match b:
    case True{}:
      Laws.ring_walk_counts(body, self, params, path, wins)
    case False{}:
      {==}

# ring's def walk: the findings gathered so far, then each def's
law ring.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Ring.check.go(ds, path, acc)) == pick.sum(acc, Laws.ring.defs(ds, path)) : Nat}

def ring.go(ds, path, acc):
  match ds:
    case Nil{}:
      pick.rev(acc, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +keep = Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))
      +x = Lazy.stop(List<&2, F.Finding>, Bool.not(keep), [],
        _u => Ring.walk(body, name, Calls.names(sig), path, Ring.windows(sig, body)))
      +cb = Bool.pick(Nat, keep, Laws.ring.count(body, name, Calls.names(sig), Ring.windows(sig, body)), 0n)
      Equal.trans(Nat, List.length(&2, F.Finding, Ring.check.go(rest, path, x <> acc)),
        pick.sum(acc, Nat.add(List.length(&2, F.Finding, x), Laws.ring.defs(rest, path))),
        pick.sum(acc, Nat.add(cb, Laws.ring.defs(rest, path))),
        ring.go(rest, path, x <> acc),
        Equal.cong(Nat, Nat, n => pick.sum(acc, Nat.add(n, Laws.ring.defs(rest, path))),
          List.length(&2, F.Finding, x), cb,
          ring.stop(keep, body, name, Calls.names(sig), path, Ring.windows(sig, body))))

def Laws.ring_counts(path, _text, _toks, tree, _bound, _items):
  ring.go(Calls.defs(tree), path, Nil{})

# fuel (BOLT-RULE-U006): the rule's parameter scan is the law's, its call
# checks count the law's hits, and its walk the law's count.

# the rule's fuel parameters of one def are the law's
law fuel.of:
  for ps: List<&2, Tree.Node>
  for +name: String
  for +ii: Nat
  {FuelRule.fuels.params(ps, name, ii) == Laws.fuel.slots.of(ps, name, ii) : List<&2, FuelRule.Fuel>}

def fuel.of(ps, name, ii):
  match ps:
    case Nil{}:
      {==}
    case Con{p, rest}:
      Equal.cong(List<&2, FuelRule.Fuel>, List<&2, FuelRule.Fuel>,
        x => Bool.pick(List<&2, FuelRule.Fuel>, FuelRule.is_fuel(Calls.param_name(p)), FuelRule.Fuel{name, ii} <> x, x),
        FuelRule.fuels.params(rest, name, 1n+ii), Laws.fuel.slots.of(rest, name, 1n+ii), fuel.of(rest, name, 1n+ii))

def Laws.fuel_slots(ds):
  match ds:
    case Nil{}:
      {==}
    case Con{d, +rest}:
      match d:
        case Calls.Def{+name, +sig, body}:
          +aa = FuelRule.fuels.params(Calls.params(sig), name, 0n)
          +bb = Laws.fuel.slots.of(Calls.params(sig), name, 0n)
          Equal.trans(List<&2, FuelRule.Fuel>, List.append(&2, FuelRule.Fuel, aa, FuelRule.fuels(rest)),
            List.append(&2, FuelRule.Fuel, bb, FuelRule.fuels(rest)), List.append(&2, FuelRule.Fuel, bb,
              Laws.fuel.slots(rest)),
            Equal.cong(List<&2, FuelRule.Fuel>, List<&2, FuelRule.Fuel>, x => List.append(&2, FuelRule.Fuel, x,
              FuelRule.fuels(rest)),
              aa, bb, fuel.of(Calls.params(sig), name, 0n)),
            Equal.cong(List<&2, FuelRule.Fuel>, List<&2, FuelRule.Fuel>, x => List.append(&2, FuelRule.Fuel, bb, x),
              FuelRule.fuels(rest), Laws.fuel.slots(rest), Laws.fuel_slots(rest)))

# a lone Nat literal argument is one finding, anything else none
law fuel.lit:
  for aa: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, FuelRule.literal(aa, path)) == Bool.pick(Nat, Laws.fuel.lone(aa), 1n, 0n) : Nat}

def fuel.lit(aa, path):
  match aa:
    case Tree.NCons{h, r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, l, c}:
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
                  match r:
                    case Tree.Leaf{x}:
                      {==}
                    case Tree.Group{x, y, z}:
                      {==}
                    case Tree.Stmt{x, y, z}:
                      {==}
                    case Tree.NNil{}:
                      chars.one(T.nat_ok(String.to_list(t)), F.Finding{path, l, c, U32.from_nat(String.length(t)),
                        "fuel",
                        "Fuel is fixed at " ++ t ++ ", so input past it is cut short with no error; derive the fuel from the input size."})
                    case Tree.NCons{x, y}:
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
        case Tree.Group{x, y, z}:
          {==}
        case Tree.Stmt{x, y, z}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{x, y}:
          {==}
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{x, y, z}:
      {==}
    case Tree.Stmt{x, y, z}:
      {==}
    case Tree.NNil{}:
      {==}

# adding a one-or-none is picking between the successor and the Nat
law fuel.addpick:
  for l: Bool
  for -m: Nat
  {Nat.add(Bool.pick(Nat, l, 1n, 0n), m) == Bool.pick(Nat, l, 1n+m, m) : Nat}

def fuel.addpick(l, _m):
  match l:
    case True{}:
      {==}
    case False{}:
      {==}

# one fuel parameter's check onto the rest's: its literal's finding when the
# def's name is the call's
law fuel.stop:
  for b: Bool
  for +l: Bool
  for +lit: List<&2, F.Finding>
  for +more: List<&2, F.Finding>
  for -m: Nat
  for e1: {List.length(&2, F.Finding, lit) == Bool.pick(Nat, l, 1n, 0n) : Nat}
  for e2: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(b), more,
    _u => List.append(&2, F.Finding, lit, more))) == Bool.pick(Nat, Bool.and(b, l), 1n+m, m) : Nat}

def fuel.stop(b, l, lit, more, m, e1, e2):
  match b:
    case True{}:
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, lit, more)),
        Nat.add(Bool.pick(Nat, l, 1n, 0n), m), Bool.pick(Nat, l, 1n+m, m),
        pick.join(lit, more, Bool.pick(Nat, l, 1n, 0n), m, e1, e2), fuel.addpick(l, m))
    case False{}:
      e2

# a call's findings count the law's hits
law fuel.call:
  for fs: List<&2, FuelRule.Fuel>
  for +name: String
  for +as: List<&2, Tree.Node>
  for +path: String
  {List.length(&2, F.Finding, FuelRule.call(fs, name, as, path)) == Laws.fuel.hits(fs, name, as) : Nat}

def fuel.call(fs, name, as, path):
  match fs:
    case Nil{}:
      {==}
    case Con{f, +rest}:
      match f:
        case FuelRule.Fuel{+fn, +at}:
          fuel.stop(String.eq(fn, name), Laws.fuel.lone(Calls.arg(as, at)), FuelRule.literal(Calls.arg(as, at), path),
            FuelRule.call(rest, name, as, path), Laws.fuel.hits(rest, name, as), fuel.lit(Calls.arg(as, at), path),
            fuel.call(rest, name, as, path))

# a call site: the call's findings when it counts, onto the rest's
law fuel.site:
  for hit: Bool
  for +cl: List<&2, F.Finding>
  for +more: List<&2, F.Finding>
  for -hh: Nat
  for -m: Nat
  for e1: {List.length(&2, F.Finding, cl) == hh : Nat}
  for e2: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(hit), more,
    _u => List.append(&2, F.Finding, cl, more))) == Bool.pick(Nat, hit, Nat.add(hh, m), m) : Nat}

def fuel.site(hit, cl, more, hh, m, e1, e2):
  match hit:
    case True{}:
      pick.join(cl, more, hh, m, e1, e2)
    case False{}:
      e2

# two joined finding lists count the sum of theirs
law fuel.two:
  for a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for -ma: Nat
  for -mb: Nat
  for ea: {List.length(&2, F.Finding, a) == ma : Nat}
  for eb: {List.length(&2, F.Finding, b) == mb : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b])) == Nat.add(ma, mb) : Nat}

def fuel.two(a, b, ma, mb, ea, eb):
  pick.join(a, List.append(&2, F.Finding, b, Nil{}), ma, mb, ea, pick.last(b, mb, eb))

# three joined finding lists count the sum of theirs
law fuel.three:
  for a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for +c: List<&2, F.Finding>
  for -ma: Nat
  for -mb: Nat
  for -mc: Nat
  for ea: {List.length(&2, F.Finding, a) == ma : Nat}
  for eb: {List.length(&2, F.Finding, b) == mb : Nat}
  for ec: {List.length(&2, F.Finding, c) == mc : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])) == Nat.add(ma, Nat.add(mb, mc)) : Nat}

def fuel.three(a, b, c, ma, mb, mc, ea, eb, ec):
  pick.join(a, List.concat(&2, F.Finding, [b, c]), ma, Nat.add(mb, mc), ea, fuel.two(b, c, mb, mc, eb, ec))

def Laws.fuel_walk_counts(nn, fs, self, path):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, l, c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{open, +kids, close}:
                      match open:
                        case Lex.Tok{ok, +o, ol, oc}:
                          +hit = Bool.and(Bool.and(Lex.is_name(k), String.eq(o, "(")), Bool.not(String.eq(t, self)))
                          +more = List.concat(&2, F.Finding, [FuelRule.calls(kids, fs, self, path), FuelRule.calls(r2,
                            fs, self, path)])
                          +m = Nat.add(Laws.fuel.count(kids, fs, self), Laws.fuel.count(r2, fs, self))
                          fuel.site(hit, FuelRule.call(fs, t, Calls.args(kids), path), more, Laws.fuel.hits(fs, t,
                            Calls.args(kids)), m,
                            fuel.call(fs, t, Calls.args(kids), path),
                            fuel.two(FuelRule.calls(kids, fs, self, path), FuelRule.calls(r2, fs, self, path),
                              Laws.fuel.count(kids, fs, self), Laws.fuel.count(r2, fs, self),
                                Laws.fuel_walk_counts(kids, fs, self, path), Laws.fuel_walk_counts(r2, fs, self, path)))
                    case Tree.Leaf{x}:
                      Laws.fuel_walk_counts(rest, fs, self, path)
                    case Tree.Stmt{x, y, z}:
                      Laws.fuel_walk_counts(rest, fs, self, path)
                    case Tree.NNil{}:
                      Laws.fuel_walk_counts(rest, fs, self, path)
                    case Tree.NCons{x, y}:
                      Laws.fuel_walk_counts(rest, fs, self, path)
                case Tree.Leaf{x}:
                  Laws.fuel_walk_counts(rest, fs, self, path)
                case Tree.Group{x, y, z}:
                  Laws.fuel_walk_counts(rest, fs, self, path)
                case Tree.Stmt{x, y, z}:
                  Laws.fuel_walk_counts(rest, fs, self, path)
                case Tree.NNil{}:
                  Laws.fuel_walk_counts(rest, fs, self, path)
        case Tree.Group{open, +kids, close}:
          fuel.two(FuelRule.calls(kids, fs, self, path), FuelRule.calls(rest, fs, self, path), Laws.fuel.count(kids, fs,
            self), Laws.fuel.count(rest, fs, self), Laws.fuel_walk_counts(kids, fs, self, path),
              Laws.fuel_walk_counts(rest, fs, self, path))
        case Tree.Stmt{kind, +kids, +body}:
          fuel.three(FuelRule.calls(kids, fs, self, path), FuelRule.calls(body, fs, self, path), FuelRule.calls(rest,
            fs, self, path), Laws.fuel.count(kids, fs, self), Laws.fuel.count(body, fs, self), Laws.fuel.count(rest, fs,
              self),
            Laws.fuel_walk_counts(kids, fs, self, path), Laws.fuel_walk_counts(body, fs, self, path),
              Laws.fuel_walk_counts(rest, fs, self, path))
        case Tree.NNil{}:
          Laws.fuel_walk_counts(rest, fs, self, path)
        case Tree.NCons{x, y}:
          Laws.fuel_walk_counts(rest, fs, self, path)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{x, y, z}:
      {==}
    case Tree.Stmt{x, y, z}:
      {==}
    case Tree.NNil{}:
      {==}

# a statement's own name, to the rule and to the law
law fuel.own:
  for mm: Maybe<&2, String>
  {FuelRule.own(mm) == Laws.fuel.own(mm) : String}

def fuel.own(mm):
  match mm:
    case None{}:
      {==}
    case Some{nm}:
      {==}

# a chain walked with the rule's self counts the law's
law fuel.self:
  for +nn: Tree.Node
  for +fs: List<&2, FuelRule.Fuel>
  for +mm: Maybe<&2, String>
  for +path: String
  {List.length(&2, F.Finding, FuelRule.calls(nn, fs, FuelRule.own(mm), path))
    == Laws.fuel.count(nn, fs, Laws.fuel.own(mm)) : Nat}

def fuel.self(nn, fs, mm, path):
  Equal.trans(Nat, List.length(&2, F.Finding, FuelRule.calls(nn, fs, FuelRule.own(mm), path)),
    Laws.fuel.count(nn, fs, FuelRule.own(mm)), Laws.fuel.count(nn, fs, Laws.fuel.own(mm)),
    Laws.fuel_walk_counts(nn, fs, FuelRule.own(mm), path),
    Equal.cong(String, Nat, x => Laws.fuel.count(nn, fs, x), FuelRule.own(mm), Laws.fuel.own(mm), fuel.own(mm)))

# the rule's statement walk counts the law's total
law fuel.go:
  for root: Tree.Node
  for +fs: List<&2, FuelRule.Fuel>
  for +path: String
  {List.length(&2, F.Finding, FuelRule.check.go(root, fs, path)) == Laws.fuel.total(root, fs) : Nat}

def fuel.go(root, fs, path):
  match root:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{kind, +kids, +body}:
          +self = FuelRule.own(Bind.declared(kids))
          +me = Laws.fuel.own(Bind.declared(kids))
          fuel.three(FuelRule.calls(kids, fs, self, path), FuelRule.calls(body, fs, self, path),
            FuelRule.check.go(rest, fs, path), Laws.fuel.count(kids, fs, me), Laws.fuel.count(body, fs, me),
            Laws.fuel.total(rest, fs), fuel.self(kids, fs, Bind.declared(kids), path),
            fuel.self(body, fs, Bind.declared(kids), path), fuel.go(rest, fs, path))
        case Tree.Leaf{x}:
          fuel.go(rest, fs, path)
        case Tree.Group{x, y, z}:
          fuel.go(rest, fs, path)
        case Tree.NNil{}:
          fuel.go(rest, fs, path)
        case Tree.NCons{x, y}:
          fuel.go(rest, fs, path)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{x, y, z}:
      {==}
    case Tree.Stmt{x, y, z}:
      {==}
    case Tree.NNil{}:
      {==}

def Laws.fuel_counts(path, _text, _toks, tree, _bound, _items):
  +ds = Calls.defs(tree)
  Equal.trans(Nat, List.length(&2, F.Finding, FuelRule.check.go(tree, FuelRule.fuels(ds), path)),
    Laws.fuel.total(tree, FuelRule.fuels(ds)), Laws.fuel.total(tree, Laws.fuel.slots(ds)),
    fuel.go(tree, FuelRule.fuels(ds), path),
    Equal.cong(List<&2, FuelRule.Fuel>, Nat, x => Laws.fuel.total(tree, x), FuelRule.fuels(ds), Laws.fuel.slots(ds),
      Laws.fuel_slots(ds)))

# unit (BOLT-RULE-U012): the rule's literal, operator and call tests are the
# law's, read through whether a maybe holds a token (unit.has), and its walk
# counts the law's count.

# does the maybe hold a token?
def unit.has(mm: Maybe<&2, Lex.Tok>) -> Bool:
  match mm:
    case None{}:
      False{}
    case Some{tok}:
      True{}

# a finding on the maybe's token: one when it holds one
law unit.cite:
  for mm: Maybe<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, UnitRule.cite(mm, path)) == Bool.pick(Nat, unit.has(mm), 1n, 0n) : Nat}

def unit.cite(mm, _path):
  match mm:
    case None{}:
      {==}
    case Some{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}:
          {==}

# a pick between a token and none holds one exactly when it picks the token
law unit.hp:
  for b: Bool
  for -tok: Lex.Tok
  {unit.has(Bool.pick(Maybe<&2, Lex.Tok>, b, Some{tok}, None{})) == b : Bool}

def unit.hp(b, _tok):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the rule's literal one is the law's
law unit.one_is:
  for mm: Maybe<&2, Lex.Tok>
  {unit.has(UnitRule.one_of(mm)) == Laws.unit.one(mm) : Bool}

def unit.one_is(mm):
  match mm:
    case None{}:
      {==}
    case Some{tok}:
      match tok:
        case Lex.Tok{k, +t, l, c}:
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
              unit.hp(UnitRule.one_text(t), Lex.Tok{Lex.TNum{}, t, l, c})
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

# the first of two maybes that holds a token: one when either holds one
law unit.either:
  for xx: Maybe<&2, Lex.Tok>
  for -yy: Maybe<&2, Lex.Tok>
  {unit.has(UnitRule.either(xx, yy)) == Bool.or(unit.has(xx), unit.has(yy)) : Bool}

def unit.either(xx, _yy):
  match xx:
    case None{}:
      {==}
    case Some{tok}:
      {==}

# equal Bools give equal ors
law unit.or2:
  for -a: Bool
  for -b: Bool
  for -c: Bool
  for -d: Bool
  for e1: {a == b : Bool}
  for e2: {c == d : Bool}
  {Bool.or(a, c) == Bool.or(b, d) : Bool}

def unit.or2(a, b, c, d, e1, e2):
  Equal.trans(Bool, Bool.or(a, c), Bool.or(b, c), Bool.or(b, d), Equal.cong(Bool, Bool, x => Bool.or(x, c), a, b, e1),
    Equal.cong(Bool, Bool, x => Bool.or(b, x), c, d, e2))

# or commutes
law unit.comm:
  for a: Bool
  for b: Bool
  {Bool.or(a, b) == Bool.or(b, a) : Bool}

def unit.comm(a, b):
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

# the literal an operator's finding cites is there exactly when the law's
# operator is by one: `*` (s) with one after or before, `/` (d) with one after
law unit.which:
  for s: Bool
  for d: Bool
  for +pp: Maybe<&2, Lex.Tok>
  for +nn: Maybe<&2, Lex.Tok>
  {unit.has(Bool.pick(Maybe<&2, Lex.Tok>, s, UnitRule.either(UnitRule.one_of(nn), UnitRule.one_of(pp)),
    Bool.pick(Maybe<&2, Lex.Tok>, d, UnitRule.one_of(nn), None{})))
    == Bool.pick(Bool, s, Bool.or(Laws.unit.one(nn), Laws.unit.one(pp)), Bool.and(d, Laws.unit.one(nn))) : Bool}

def unit.which(s, d, pp, nn):
  match s:
    case True{}:
      Equal.trans(Bool, unit.has(UnitRule.either(UnitRule.one_of(nn), UnitRule.one_of(pp))),
        Bool.or(unit.has(UnitRule.one_of(nn)), unit.has(UnitRule.one_of(pp))),
        Bool.or(Laws.unit.one(nn), Laws.unit.one(pp)),
        unit.either(UnitRule.one_of(nn), UnitRule.one_of(pp)),
        unit.or2(unit.has(UnitRule.one_of(nn)), Laws.unit.one(nn), unit.has(UnitRule.one_of(pp)), Laws.unit.one(pp),
          unit.one_is(nn), unit.one_is(pp)))
    case False{}:
      match d:
        case True{}:
          unit.one_is(nn)
        case False{}:
          {==}

# the node after, to the rule and to the law
law unit.first_is:
  for nn: Tree.Node
  {UnitRule.first_tok(nn) == Laws.unit.first(nn) : Maybe<&2, Lex.Tok>}

def unit.first_is(nn):
  match nn:
    case Tree.NCons{h, r}:
      match h:
        case Tree.Leaf{tok}:
          {==}
        case Tree.Group{x, y, z}:
          {==}
        case Tree.Stmt{x, y, z}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{x, y}:
          {==}
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{x, y, z}:
      {==}
    case Tree.Stmt{x, y, z}:
      {==}
    case Tree.NNil{}:
      {==}

# an operator's finding: one exactly when it is by one
law unit.opx:
  for +t: String
  for +prev: Maybe<&2, Lex.Tok>
  for +rest: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path))
    == Bool.pick(Nat, Laws.unit.by_one(t, prev, Laws.unit.first(rest)), 1n, 0n) : Nat}

def unit.opx(t, prev, rest, path):
  +ft = UnitRule.first_tok(rest)
  +uf = Laws.unit.first(rest)
  +wh = UnitRule.which(t, prev, ft)
  Equal.trans(Nat, List.length(&2, F.Finding, UnitRule.cite(wh, path)), Bool.pick(Nat, unit.has(wh), 1n, 0n),
    Bool.pick(Nat, Laws.unit.by_one(t, prev, uf), 1n, 0n), unit.cite(wh, path),
    Equal.cong(Bool, Nat, b => Bool.pick(Nat, b, 1n, 0n), unit.has(wh), Laws.unit.by_one(t, prev, uf),
      Equal.trans(Bool, unit.has(wh), Laws.unit.by_one(t, prev, ft), Laws.unit.by_one(t, prev, uf),
        unit.which(String.eq(t, "*"), String.eq(t, "/"), prev, ft),
        Equal.cong(Maybe<&2, Lex.Tok>, Bool, m => Laws.unit.by_one(t, prev, m), ft, uf, unit.first_is(rest)))))

# an operator in a region as hot as hot: its finding when hot
law unit.on:
  for hot: Bool
  for -x: List<&2, F.Finding>
  for -b: Bool
  for e: {List.length(&2, F.Finding, x) == Bool.pick(Nat, b, 1n, 0n) : Nat}
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, Bool.and(hot, True{}), x, []))
    == Bool.pick(Nat, Bool.and(hot, b), 1n, 0n) : Nat}

def unit.on(hot, _x, _b, e):
  match hot:
    case True{}:
      e
    case False{}:
      {==}

# a leaf that is no operator: no finding
law unit.off:
  for hot: Bool
  for -x: List<&2, F.Finding>
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, Bool.and(hot, False{}), x, []))
    == Bool.pick(Nat, Bool.and(hot, False{}), 1n, 0n) : Nat}

def unit.off(hot, _x):
  match hot:
    case True{}:
      {==}
    case False{}:
      {==}

# a leaf's own finding onto the rest's
law unit.leaf:
  for +x: List<&2, F.Finding>
  for +more: List<&2, F.Finding>
  for +b: Bool
  for -m: Nat
  for ex: {List.length(&2, F.Finding, x) == Bool.pick(Nat, b, 1n, 0n) : Nat}
  for em: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, List.append(&2, F.Finding, x, more)) == Bool.pick(Nat, b, 1n+m, m) : Nat}

def unit.leaf(x, more, b, m, ex, em):
  Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, x, more)), Nat.add(Bool.pick(Nat, b, 1n, 0n),
    m),
    Bool.pick(Nat, b, 1n+m, m), pick.join(x, more, Bool.pick(Nat, b, 1n, 0n), m, ex, em), fuel.addpick(b, m))

# the rule's argument that is the literal one alone is the law's
law unit.arg_is:
  for aa: Tree.Node
  {unit.has(UnitRule.arg_one(aa)) == Laws.unit.lone(aa) : Bool}

def unit.arg_is(aa):
  match aa:
    case Tree.NCons{h, r}:
      match h:
        case Tree.Leaf{tok}:
          match r:
            case Tree.NNil{}:
              unit.one_is(Some{tok})
            case Tree.Leaf{x}:
              {==}
            case Tree.Group{x, y, z}:
              {==}
            case Tree.Stmt{x, y, z}:
              {==}
            case Tree.NCons{x, y}:
              {==}
        case Tree.Group{x, y, z}:
          {==}
        case Tree.Stmt{x, y, z}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{x, y}:
          {==}
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{x, y, z}:
      {==}
    case Tree.Stmt{x, y, z}:
      {==}
    case Tree.NNil{}:
      {==}

# the rule's some argument one is the law's
law unit.any_is:
  for as: List<&2, Tree.Node>
  {unit.has(UnitRule.any_one(as)) == Laws.unit.any(as) : Bool}

def unit.any_is(as):
  match as:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      Equal.trans(Bool, unit.has(UnitRule.either(UnitRule.any_one(rest), UnitRule.arg_one(h))),
        Bool.or(unit.has(UnitRule.any_one(rest)), unit.has(UnitRule.arg_one(h))),
        Bool.or(Laws.unit.lone(h), Laws.unit.any(rest)),
        unit.either(UnitRule.any_one(rest), UnitRule.arg_one(h)),
        Equal.trans(Bool, Bool.or(unit.has(UnitRule.any_one(rest)), unit.has(UnitRule.arg_one(h))),
          Bool.or(Laws.unit.any(rest), Laws.unit.lone(h)), Bool.or(Laws.unit.lone(h), Laws.unit.any(rest)),
          unit.or2(unit.has(UnitRule.any_one(rest)), Laws.unit.any(rest), unit.has(UnitRule.arg_one(h)),
            Laws.unit.lone(h), unit.any_is(rest), unit.arg_is(h)),
          unit.comm(Laws.unit.any(rest), Laws.unit.lone(h))))

# the rule's last argument one is the law's
law unit.last_is:
  for as: List<&2, Tree.Node>
  {unit.has(UnitRule.last_one(as)) == Laws.unit.last(as) : Bool}

def unit.last_is(as):
  match as:
    case Nil{}:
      {==}
    case Con{h, t}:
      match t:
        case Nil{}:
          unit.arg_is(h)
        case Con{x, y}:
          unit.last_is(t)

# a finding on what the maybe holds, as the law's Bool says
law unit.has_is:
  for +mm: Maybe<&2, Lex.Tok>
  for -b: Bool
  for +path: String
  for e: {unit.has(mm) == b : Bool}
  {List.length(&2, F.Finding, UnitRule.cite(mm, path)) == Bool.pick(Nat, b, 1n, 0n) : Nat}

def unit.has_is(mm, b, path, e):
  Equal.trans(Nat, List.length(&2, F.Finding, UnitRule.cite(mm, path)), Bool.pick(Nat, unit.has(mm), 1n, 0n),
    Bool.pick(Nat, b, 1n, 0n), unit.cite(mm, path), Equal.cong(Bool, Nat, x => Bool.pick(Nat, x, 1n, 0n), unit.has(mm),
      b, e))

# a divide's finding, when the call is a divide
law unit.div:
  for db: Bool
  for +as: List<&2, Tree.Node>
  for +path: String
  {List.length(&2, F.Finding, UnitRule.on_div_is(db, as, path)) == Bool.pick(Nat, Bool.and(db, Laws.unit.last(as)), 1n,
    0n)
    : Nat}

def unit.div(db, as, path):
  match db:
    case True{}:
      unit.has_is(UnitRule.last_one(as), Laws.unit.last(as), path, unit.last_is(as))
    case False{}:
      {==}

# a multiply's finding, else a divide's
law unit.opis:
  for mb: Bool
  for +tt: String
  for +as: List<&2, Tree.Node>
  for +path: String
  {List.length(&2, F.Finding, UnitRule.on_op_is(mb, tt, as, path))
    == Bool.pick(Nat, Bool.pick(Bool, mb, Laws.unit.any(as),
      Bool.and(List.contains(~String, ~String.eq, ["Nat.div", "U32.div", "F32.div"], tt),
        Laws.unit.last(as))), 1n, 0n)
    : Nat}

def unit.opis(mb, tt, as, path):
  match mb:
    case True{}:
      unit.has_is(UnitRule.any_one(as), Laws.unit.any(as), path, unit.any_is(as))
    case False{}:
      unit.div(List.contains(~String, ~String.eq, ["Nat.div", "U32.div", "F32.div"], tt), as, path)

# a group's own finding: a `(` call that multiplies or divides by one, when hot
law unit.own:
  for call: Bool
  for +tt: String
  for +kids: Tree.Node
  for +path: String
  for hot: Bool
  {List.length(&2, F.Finding, UnitRule.own_of(call, tt, kids, path, hot))
    == Bool.pick(Nat, Bool.and(call, Bool.and(hot, Laws.unit.call(tt, Calls.args(kids)))), 1n, 0n) : Nat}

def unit.own(call, tt, kids, path, hot):
  match call:
    case True{}:
      match hot:
        case True{}:
          unit.opis(List.contains(~String, ~String.eq, ["Nat.mul", "U32.mul", "F32.mul"], tt), tt,
            Calls.args(kids), path)
        case False{}:
          {==}
    case False{}:
      {==}

# the name a group calls, to the rule and to the law
law unit.callee:
  for mm: Maybe<&2, Lex.Tok>
  {UnitRule.callee(mm) == Laws.unit.name(mm) : String}

def unit.callee(mm):
  match mm:
    case None{}:
      {==}
    case Some{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}:
          {==}

def Laws.unit_walk_counts(nn, prev, self, path, hot):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, +l, +c}:
              match k:
                case Lex.TName{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TName{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TName{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TName{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TName{}, t, l, c}}, self, path, hot))
                case Lex.TUpper{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TUpper{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TUpper{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TUpper{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TUpper{}, t, l, c}}, self, path, hot))
                case Lex.TDotted{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TDotted{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TDotted{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TDotted{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TDotted{}, t, l, c}}, self, path, hot))
                case Lex.TWild{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TWild{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TWild{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TWild{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TWild{}, t, l, c}}, self, path, hot))
                case Lex.TKey{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TKey{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TKey{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TKey{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TKey{}, t, l, c}}, self, path, hot))
                case Lex.TNum{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TNum{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TNum{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TNum{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TNum{}, t, l, c}}, self, path, hot))
                case Lex.TStr{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TStr{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TStr{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TStr{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TStr{}, t, l, c}}, self, path, hot))
                case Lex.TChar{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TChar{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TChar{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TChar{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TChar{}, t, l, c}}, self, path, hot))
                case Lex.TComment{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TComment{}, t, l, c}, prev, UnitRule.first_tok(rest), path,
                    hot), UnitRule.walk(rest, Some{Lex.Tok{Lex.TComment{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TComment{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TComment{}, t, l, c}}, self, path, hot))
                case Lex.TSpace{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TSpace{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TSpace{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TSpace{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TSpace{}, t, l, c}}, self, path, hot))
                case Lex.TNewline{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TNewline{}, t, l, c}, prev, UnitRule.first_tok(rest), path,
                    hot), UnitRule.walk(rest, Some{Lex.Tok{Lex.TNewline{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TNewline{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TNewline{}, t, l, c}}, self, path, hot))
                case Lex.TOp{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TOp{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, None{}, self, path, hot),
                    Bool.and(hot, Laws.unit.by_one(t, prev, Laws.unit.first(rest))), Laws.unit.count(rest, None{}, self,
                      hot),
                    unit.on(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path),
                      Laws.unit.by_one(t, prev, Laws.unit.first(rest)), unit.opx(t, prev, rest, path)),
                    Laws.unit_walk_counts(rest, None{}, self, path, hot))
                case Lex.TColon{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TColon{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TColon{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TColon{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TColon{}, t, l, c}}, self, path, hot))
                case Lex.TEq{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TEq{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TEq{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TEq{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TEq{}, t, l, c}}, self, path, hot))
                case Lex.TBind{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TBind{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TBind{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TBind{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TBind{}, t, l, c}}, self, path, hot))
                case Lex.TArrow{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TArrow{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TArrow{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TArrow{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TArrow{}, t, l, c}}, self, path, hot))
                case Lex.TLam{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TLam{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TLam{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TLam{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TLam{}, t, l, c}}, self, path, hot))
                case Lex.TAll{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TAll{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TAll{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TAll{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TAll{}, t, l, c}}, self, path, hot))
                case Lex.TAmp{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TAmp{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TAmp{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TAmp{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TAmp{}, t, l, c}}, self, path, hot))
                case Lex.TOpen{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TOpen{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TOpen{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TOpen{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TOpen{}, t, l, c}}, self, path, hot))
                case Lex.TClose{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TClose{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TClose{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TClose{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TClose{}, t, l, c}}, self, path, hot))
                case Lex.TComma{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TComma{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TComma{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TComma{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TComma{}, t, l, c}}, self, path, hot))
        case Tree.Group{open, +kids, close}:
          match open:
            case Lex.Tok{ok, +o, ol, oc}:
              +call = String.eq(o, "(")
              +own = UnitRule.own_of(call, UnitRule.callee(prev), kids, path, hot)
              fuel.three(UnitRule.walk(kids, None{}, self, path, hot), own, UnitRule.walk(rest, None{}, self, path,
                hot),
                Laws.unit.count(kids, None{}, self, hot),
                Bool.pick(Nat, Bool.and(call, Bool.and(hot, Laws.unit.call(Laws.unit.name(prev), Calls.args(kids)))),
                  1n, 0n),
                Laws.unit.count(rest, None{}, self, hot), Laws.unit_walk_counts(kids, None{}, self, path, hot),
                Equal.trans(Nat, List.length(&2, F.Finding, own),
                  Bool.pick(Nat, Bool.and(call, Bool.and(hot, Laws.unit.call(UnitRule.callee(prev), Calls.args(kids)))),
                    1n, 0n),
                  Bool.pick(Nat, Bool.and(call, Bool.and(hot, Laws.unit.call(Laws.unit.name(prev), Calls.args(kids)))),
                    1n, 0n),
                  unit.own(call, UnitRule.callee(prev), kids, path, hot),
                  Equal.cong(String, Nat, x => Bool.pick(Nat, Bool.and(call, Bool.and(hot, Laws.unit.call(x,
                    Calls.args(kids)))), 1n,
                    0n), UnitRule.callee(prev), Laws.unit.name(prev), unit.callee(prev))),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SDef{}:
              fuel.three(UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(body, None{}, self, path, hot),
                UnitRule.walk(rest, None{}, self, path, hot), Laws.unit.count(kids, None{}, self, hot),
                Laws.unit.count(body, None{}, self, hot), Laws.unit.count(rest, None{}, self, hot),
                Laws.unit_walk_counts(kids, None{}, self, path, hot), Laws.unit_walk_counts(body, None{}, self, path,
                  hot),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
            case Tree.SType{}:
              fuel.three(UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(body, None{}, self, path, hot),
                UnitRule.walk(rest, None{}, self, path, hot), Laws.unit.count(kids, None{}, self, hot),
                Laws.unit.count(body, None{}, self, hot), Laws.unit.count(rest, None{}, self, hot),
                Laws.unit_walk_counts(kids, None{}, self, path, hot), Laws.unit_walk_counts(body, None{}, self, path,
                  hot),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
            case Tree.SLaw{}:
              fuel.three(UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(body, None{}, self, path, hot),
                UnitRule.walk(rest, None{}, self, path, hot), Laws.unit.count(kids, None{}, self, hot),
                Laws.unit.count(body, None{}, self, hot), Laws.unit.count(rest, None{}, self, hot),
                Laws.unit_walk_counts(kids, None{}, self, path, hot), Laws.unit_walk_counts(body, None{}, self, path,
                  hot),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
            case Tree.SImport{}:
              fuel.three(UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(body, None{}, self, path, hot),
                UnitRule.walk(rest, None{}, self, path, hot), Laws.unit.count(kids, None{}, self, hot),
                Laws.unit.count(body, None{}, self, hot), Laws.unit.count(rest, None{}, self, hot),
                Laws.unit_walk_counts(kids, None{}, self, path, hot), Laws.unit_walk_counts(body, None{}, self, path,
                  hot),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
            case Tree.SCase{}:
              fuel.three(UnitRule.walk(kids, None{}, self, path, False{}), UnitRule.walk(body, None{}, self, path,
                Bool.and(hot, Calls.calls(body, self))),
                UnitRule.walk(rest, None{}, self, path, hot), Laws.unit.count(kids, None{}, self, False{}),
                Laws.unit.count(body, None{}, self, Bool.and(hot, Calls.calls(body, self))), Laws.unit.count(rest,
                  None{}, self, hot),
                Laws.unit_walk_counts(kids, None{}, self, path, False{}), Laws.unit_walk_counts(body, None{}, self,
                  path, Bool.and(hot, Calls.calls(body, self))),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
            case Tree.SFor{}:
              fuel.three(UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(body, None{}, self, path, hot),
                UnitRule.walk(rest, None{}, self, path, hot), Laws.unit.count(kids, None{}, self, hot),
                Laws.unit.count(body, None{}, self, hot), Laws.unit.count(rest, None{}, self, hot),
                Laws.unit_walk_counts(kids, None{}, self, path, hot), Laws.unit_walk_counts(body, None{}, self, path,
                  hot),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
            case Tree.SLet{}:
              fuel.three(UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(body, None{}, self, path, hot),
                UnitRule.walk(rest, None{}, self, path, hot), Laws.unit.count(kids, None{}, self, hot),
                Laws.unit.count(body, None{}, self, hot), Laws.unit.count(rest, None{}, self, hot),
                Laws.unit_walk_counts(kids, None{}, self, path, hot), Laws.unit_walk_counts(body, None{}, self, path,
                  hot),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
            case Tree.STerm{}:
              fuel.three(UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(body, None{}, self, path, hot),
                UnitRule.walk(rest, None{}, self, path, hot), Laws.unit.count(kids, None{}, self, hot),
                Laws.unit.count(body, None{}, self, hot), Laws.unit.count(rest, None{}, self, hot),
                Laws.unit_walk_counts(kids, None{}, self, path, hot), Laws.unit_walk_counts(body, None{}, self, path,
                  hot),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
        case Tree.NNil{}:
          Laws.unit_walk_counts(rest, prev, self, path, hot)
        case Tree.NCons{x, y}:
          Laws.unit_walk_counts(rest, prev, self, path, hot)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{x, y, z}:
      {==}
    case Tree.Stmt{x, y, z}:
      {==}
    case Tree.NNil{}:
      {==}

# one def's findings: its walk when it calls itself and is not exempt
law unit.stop:
  for b: Bool
  for +body: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(b), [],
    _u => UnitRule.walk(body, None{}, name, path, True{})))
    == Bool.pick(Nat, b, Laws.unit.count(body, None{}, name, True{}), 0n) : Nat}

def unit.stop(b, body, name, path):
  match b:
    case True{}:
      Laws.unit_walk_counts(body, None{}, name, path, True{})
    case False{}:
      {==}

# unit's def walk: the findings gathered so far, then each def's
law unit.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, UnitRule.check.go(ds, path, acc)) == pick.sum(acc, Laws.unit.defs(ds, path)) : Nat}

def unit.go(ds, path, acc):
  match ds:
    case Nil{}:
      pick.rev(acc, Nil{})
    case Con{d, +rest}:
      match d:
        case Calls.Def{+name, +sig, +body}:
          +b = Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))
          +x = Lazy.stop(List<&2, F.Finding>, Bool.not(b), [], _u => UnitRule.walk(body, None{}, name, path, True{}))
          +cb = Bool.pick(Nat, b, Laws.unit.count(body, None{}, name, True{}), 0n)
          Equal.trans(Nat, List.length(&2, F.Finding, UnitRule.check.go(rest, path, x <> acc)),
            pick.sum(acc, Nat.add(List.length(&2, F.Finding, x), Laws.unit.defs(rest, path))),
            pick.sum(acc, Nat.add(cb, Laws.unit.defs(rest, path))),
            unit.go(rest, path, x <> acc),
            Equal.cong(Nat, Nat, n => pick.sum(acc, Nat.add(n, Laws.unit.defs(rest, path))),
              List.length(&2, F.Finding, x), cb, unit.stop(b, body, name, path)))

def Laws.unit_counts(path, _text, _toks, tree, _bound, _items):
  unit.go(Calls.defs(tree), path, Nil{})

# The header rule wrap (BOLT-RULE-S003). The width walk agrees with the
# spec's width from any state; the shape walk, read through wrap.of, takes
# each token the way the spec's read does, so the two agree on the whole
# header; the verdicts agree on what they read.

# a colon or not, and a colon or not later on: the walk from here is the spec's
law wrap.width_step:
  for c: Bool
  for h: Bool
  for +next: U32
  for +upto: U32
  for +seen: Bool
  for -uu: U32
  for -tt: U32
  for -x: U32
  for ih: {x == Bool.pick(U32, h, uu, Bool.pick(U32, Bool.or(c, seen), Bool.pick(U32, c, next, upto), tt)) : U32}
  {x == Bool.pick(U32, Bool.or(c, h), Bool.pick(U32, h, uu, next), Bool.pick(U32, seen, upto, tt)) : U32}

def wrap.width_step(c, h, _next, _upto, _seen, _uu, _tt, _x, ih):
  match c:
    case True{}:
      ih
    case False{}:
      match h:
        case True{}:
          ih
        case False{}:
          ih

# the width walk from any state: through the last `:` when the rest has one,
# else the `:` already seen, else the whole width
law wrap.width_go:
  for +toks: List<&2, Lex.Tok>
  for +acc: U32
  for +upto: U32
  for +seen: Bool
  {Wrap.check.width.go(toks, acc, upto, seen)
    == Bool.pick(U32, Laws.wrap.colons(toks), Laws.wrap.upto(toks, acc),
      Bool.pick(U32, seen, upto, Laws.wrap.total(toks, acc))) : U32}

def wrap.width_go(toks, acc, upto, seen):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+kk, +tx, _ln, _cl}, +rest}:
      +next = (acc + Space.width_of(kk, tx) : U32)
      +colon = Wrap.check.is_colon(kk)
      wrap.width_step(colon, Laws.wrap.colons(rest), next, upto, seen, Laws.wrap.upto(rest, next),
        Laws.wrap.total(rest, next),
        Wrap.check.width.go(rest, next, Bool.pick(U32, colon, next, upto), Bool.or(colon, seen)),
        wrap.width_go(rest, next, Bool.pick(U32, colon, next, upto), Bool.or(colon, seen)))

def Laws.wrap_width(toks):
  wrap.width_go(toks, 0, 0, False{})

# the `)`'s line
def wrap.line_of(sp: Wrap.Span) -> U32:
  Wrap.Span{line, _end, _col} = sp
  line

# the parameter being read, when one is
def wrap.cur_of(on: Bool, +pline: U32, +pend: U32, +pcol: U32) -> Maybe<&2, Wrap.Span>:
  Bool.pick(Maybe<&2, Wrap.Span>, on, Some{Wrap.Span{pline, pend, pcol}}, None{})

# the rule's walk as the spec's read
def wrap.of(wk: Wrap.Walk) -> Laws.wrap.Read:
  Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans} = wk
  Laws.wrap.Read{mode, paren, bracket, brace, angle, open, wrap.line_of(shut), wrap.cur_of(on, pline, pend, pcol),
    spans}

# before the list: the rule's seek is the spec's
law wrap.seek_open:
  for a: Bool
  for z: Bool
  for +r: Wrap.Act
  {Bool.pick(Wrap.Act, Bool.and(a, z), Wrap.AOpen{}, r) == Wrap.check.seek_open(a, z, r) : Wrap.Act}

def wrap.seek_open(a, z, _r):
  match a:
    case True{}:
      match z:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

# inside the list: the rule's edges are the spec's
law wrap.args_end:
  for c: Bool
  for +t: Bool
  for m: Bool
  for +r: Wrap.Act
  {Bool.pick(Wrap.Act, t, Bool.pick(Wrap.Act, c, Wrap.AEnd{}, Bool.pick(Wrap.Act, m, Wrap.AComma{}, r)), r)
    == Wrap.check.args_end(c, t, Wrap.check.args_comma(m, t, r)) : Wrap.Act}

def wrap.args_end(c, t, m, _r):
  match c:
    case True{}:
      match t:
        case True{}:
          {==}
        case False{}:
          match m:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      match t:
        case True{}:
          match m:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match m:
            case True{}:
              {==}
            case False{}:
              {==}

# the spec's motion of a token is the rule's
law wrap.motion:
  for at: Wrap.Phase
  for +kk: Lex.TokKind
  for +tx: String
  for +glued: Bool
  for +paren: U32
  for +bracket: U32
  for +brace: U32
  for +angle: U32
  {Laws.wrap.motion(at, kk, tx, glued, paren, bracket, brace, angle)
    == Wrap.check.act(at, kk, tx, glued, paren, angle, brace, bracket) : Wrap.Act}

def wrap.motion(at, kk, tx, glued, paren, bracket, brace, angle):
  match at:
    case Wrap.Seek{}:
      wrap.seek_open(Wrap.check.is_oparen(kk, tx), Wrap.check.zero(paren, angle, brace, bracket),
        Wrap.check.brackets(kk, tx, glued))
    case Wrap.Args{}:
      wrap.args_end(Wrap.check.is_cparen(kk, tx), Wrap.check.top(paren, angle, brace, bracket), Lex.is_comma(kk),
        Wrap.check.brackets(kk, tx, glued))
    case Wrap.Past{}:
      {==}
    case Wrap.Shut{}:
      {==}
    case Wrap.Loose{}:
      {==}

# a pick and an early exit that agree on both branches agree
law wrap.stop_pick:
  for c: Bool
  for +a: U32
  for -x: U32
  for -y: U32
  for e: {x == y : U32}
  {Bool.pick(U32, c, a, x) == Lazy.stop(U32, c, a, _u => y) : U32}

def wrap.stop_pick(c, _a, _x, _y, e):
  match c:
    case True{}:
      {==}
    case False{}:
      e

# the spec closes angles as the rule does
law wrap.lower:
  for n: Nat
  for +angle: U32
  {Laws.wrap.lower(n, angle) == Wrap.check.sub(n, angle) : U32}

def wrap.lower(n, angle):
  match n:
    case Zero{}:
      {==}
    case Succ{p}:
      wrap.stop_pick(U32.is_eq(angle, 0), angle, Laws.wrap.lower(p, (angle - 1 : U32)),
        Wrap.check.sub(p, (angle - 1 : U32)), wrap.lower(p, (angle - 1 : U32)))

# a token that moves only the depths: inside the list it joins the parameter
law wrap.joined:
  for mode: Wrap.Phase
  for on: Bool
  for +paren: U32
  for +bracket: U32
  for +brace: U32
  for +angle: U32
  for +shut: Wrap.Span
  for +open: U32
  for +pline: U32
  for +pend: U32
  for +pcol: U32
  for +spans: List<&2, Wrap.Span>
  for +kk: Lex.TokKind
  for +tx: String
  for +ln: U32
  for +cl: U32
  {wrap.of(Wrap.check.note_args(Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans},
    Lex.Tok{kk, tx, ln, cl}))
    == Laws.wrap.join(mode, paren, bracket, brace, angle, open, wrap.line_of(shut), wrap.cur_of(on, pline, pend, pcol),
      spans, ln, cl) : Laws.wrap.Read}

def wrap.joined(
  mode,
  on,
  _paren,
  _bracket,
  _brace,
  _angle,
  _shut,
  _open,
  _pline,
  _pend,
  _pcol,
  _spans,
  _kk,
  _tx,
  _ln,
  _cl
):
  match mode:
    case Wrap.Args{}:
      match on:
        case True{}:
          {==}
        case False{}:
          {==}
    case Wrap.Seek{}:
      {==}
    case Wrap.Past{}:
      {==}
    case Wrap.Shut{}:
      {==}
    case Wrap.Loose{}:
      {==}

# a `->` right after the `)`: past it, on the `)` line or not, nothing joins
law wrap.arrowed:
  for b: Bool
  for on: Bool
  for +paren: U32
  for +bracket: U32
  for +brace: U32
  for +angle: U32
  for +shut: Wrap.Span
  for +open: U32
  for +pline: U32
  for +pend: U32
  for +pcol: U32
  for +spans: List<&2, Wrap.Span>
  for +tok: Lex.Tok
  {wrap.of(Wrap.check.note_args(Wrap.Walk{Bool.pick(Wrap.Phase, b, Wrap.Past{}, Wrap.Loose{}), paren, bracket, brace,
    angle, shut, open, on, pline, pend, pcol, spans}, tok))
    == Laws.wrap.Read{Bool.pick(Wrap.Phase, b, Wrap.Past{}, Wrap.Loose{}), paren, bracket, brace, angle, open,
      wrap.line_of(shut), wrap.cur_of(on, pline, pend, pcol), spans} : Laws.wrap.Read}

def wrap.arrowed(b, _on, _paren, _bracket, _brace, _angle, _shut, _open, _pline, _pend, _pcol, _spans, _tok):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# any motion: the rule's walk after it is the spec's read after it
law wrap.moved:
  for m: Wrap.Act
  for mode: Wrap.Phase
  for on: Bool
  for +paren: U32
  for +bracket: U32
  for +brace: U32
  for +angle: U32
  for +shut: Wrap.Span
  for +open: U32
  for +pline: U32
  for +pend: U32
  for +pcol: U32
  for +spans: List<&2, Wrap.Span>
  for +kk: Lex.TokKind
  for +tx: String
  for +ln: U32
  for +cl: U32
  for +ticks: Nat
  {wrap.of(Wrap.check.maybe_note(Wrap.check.is_sep(m),
    Wrap.check.apply(m, Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans}, ln, cl,
      ticks), Lex.Tok{kk, tx, ln, cl}))
    == Laws.wrap.move(m, mode, paren, bracket, brace, angle, open, wrap.line_of(shut),
      wrap.cur_of(on, pline, pend, pcol), spans, ln, cl, ticks) : Laws.wrap.Read}

def wrap.moved(m, mode, on, paren, bracket, brace, angle, shut, open, pline, pend, pcol, spans, kk, tx, ln, cl, ticks):
  match m:
    case Wrap.AOpen{}:
      {==}
    case Wrap.AEnd{}:
      match on:
        case True{}:
          {==}
        case False{}:
          {==}
    case Wrap.AComma{}:
      match on:
        case True{}:
          {==}
        case False{}:
          {==}
    case Wrap.AArrow{}:
      match shut:
        case Wrap.Span{+line, +end, +col}:
          wrap.arrowed(U32.is_eq(ln, line), on, paren, bracket, brace, angle, Wrap.Span{line, end, col}, open, pline,
            pend, pcol, spans, Lex.Tok{kk, tx, ln, cl})
    case Wrap.AStray{}:
      {==}
    case Wrap.AParen{}:
      wrap.joined(mode, on, (paren + 1 : U32), bracket, brace, angle, shut,
        open, pline, pend, pcol, spans, kk, tx, ln, cl)
    case Wrap.AUnparen{}:
      wrap.joined(mode, on, Wrap.check.dec_u(paren), bracket, brace, angle, shut,
        open, pline, pend, pcol, spans, kk, tx, ln, cl)
    case Wrap.ABrack{}:
      wrap.joined(mode, on, paren, (bracket + 1 : U32), brace, angle, shut,
        open, pline, pend, pcol, spans, kk, tx, ln, cl)
    case Wrap.AUnbrack{}:
      wrap.joined(mode, on, paren, Wrap.check.dec_u(bracket), brace, angle, shut,
        open, pline, pend, pcol, spans, kk, tx, ln, cl)
    case Wrap.ABrace{}:
      wrap.joined(mode, on, paren, bracket, (brace + 1 : U32), angle, shut,
        open, pline, pend, pcol, spans, kk, tx, ln, cl)
    case Wrap.AUnbrace{}:
      wrap.joined(mode, on, paren, bracket, Wrap.check.dec_u(brace), angle, shut,
        open, pline, pend, pcol, spans, kk, tx, ln, cl)
    case Wrap.AAngle{}:
      wrap.joined(mode, on, paren, bracket, brace, (angle + 1 : U32), shut,
        open, pline, pend, pcol, spans, kk, tx, ln, cl)
    case Wrap.AUnangle{}:
      %wrap.lower(ticks, angle) : {wrap.of(Wrap.check.note_args(Wrap.Walk{mode, paren, bracket, brace, _, shut, open,
        on, pline, pend, pcol, spans}, Lex.Tok{kk, tx, ln, cl})) == Laws.wrap.join(mode, paren, bracket, brace,
        Laws.wrap.lower(ticks, angle), open, wrap.line_of(shut), wrap.cur_of(on, pline, pend, pcol), spans, ln, cl)
        : Laws.wrap.Read}
      wrap.joined(mode, on, paren, bracket, brace, Laws.wrap.lower(ticks, angle), shut,
        open, pline, pend, pcol, spans, kk, tx, ln, cl)
    case Wrap.ANone{}:
      wrap.joined(mode, on, paren, bracket, brace, angle, shut,
        open, pline, pend, pcol, spans, kk, tx, ln, cl)

# a significant token or not: the rule's step and the spec's agree when they
# agree on a significant one
law wrap.on_sig:
  for s: Bool
  for +tok: Lex.Tok
  for +wk: Wrap.Walk
  for +glued: Bool
  for -y: Laws.wrap.Read
  for e: {wrap.of(Wrap.check.step_hit(wk, tok, glued)) == y : Laws.wrap.Read}
  {wrap.of(Wrap.check.step_on(s, tok, wk, glued)) == Bool.pick(Laws.wrap.Read, s, y, wrap.of(wk)) : Laws.wrap.Read}

def wrap.on_sig(s, _tok, _wk, _glued, _y, e):
  match s:
    case True{}:
      e
    case False{}:
      {==}

# one token: the rule's walk after it is the spec's read after it
law wrap.stepped:
  for +tok: Lex.Tok
  for +wk: Wrap.Walk
  for +glued: Bool
  {wrap.of(Wrap.check.step(tok, wk, glued)) == Laws.wrap.step(tok, wrap.of(wk), glued) : Laws.wrap.Read}

def wrap.stepped(tok, wk, glued):
  match tok:
    case Lex.Tok{+kk, +tx, +ln, +cl}:
      match wk:
        case Wrap.Walk{+mode, +paren, +bracket, +brace, +angle, +shut, +open, +on, +pline, +pend, +pcol, +spans}:
          +ticks = Wrap.check.ticks_of(tx)
          +act = Wrap.check.act(mode, kk, tx, glued, paren, angle, brace, bracket)
          +spec = Laws.wrap.motion(mode, kk, tx, glued, paren, bracket, brace, angle)
          wrap.on_sig(Lex.significant(kk), Lex.Tok{kk, tx, ln, cl},
            Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans}, glued,
            Laws.wrap.move(spec, mode, paren, bracket, brace, angle, open, wrap.line_of(shut),
              wrap.cur_of(on, pline, pend, pcol), spans, ln, cl, ticks),
            Equal.trans(Laws.wrap.Read,
              wrap.of(Wrap.check.maybe_note(Wrap.check.is_sep(act),
                Wrap.check.apply(act, Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol,
                  spans}, ln, cl, ticks), Lex.Tok{kk, tx, ln, cl})),
              Laws.wrap.move(act, mode, paren, bracket, brace, angle, open, wrap.line_of(shut),
                wrap.cur_of(on, pline, pend, pcol), spans, ln, cl, ticks),
              Laws.wrap.move(spec, mode, paren, bracket, brace, angle, open, wrap.line_of(shut),
                wrap.cur_of(on, pline, pend, pcol), spans, ln, cl, ticks),
              wrap.moved(act, mode, on, paren, bracket, brace, angle, shut, open, pline, pend, pcol, spans, kk, tx, ln,
                cl, ticks),
              Equal.cong(Wrap.Act, Laws.wrap.Read,
                aa => Laws.wrap.move(aa, mode, paren, bracket, brace, angle, open, wrap.line_of(shut),
                  wrap.cur_of(on, pline, pend, pcol), spans, ln, cl, ticks),
                act, spec,
                Equal.sym(Wrap.Act, spec, act, wrap.motion(mode, kk, tx, glued, paren, bracket, brace, angle)))))

# the end of the header: the parameter still open is done
law wrap.sealed:
  for +wk: Wrap.Walk
  for +glued: Bool
  {wrap.of(Wrap.check.seal(wk)) == Laws.wrap.run([], wrap.of(wk), glued) : Laws.wrap.Read}

def wrap.sealed(wk, _glued):
  match wk:
    case Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans}:
      match on:
        case True{}:
          {==}
        case False{}:
          {==}

# the whole header: the rule's walk is the spec's read, from any state
law wrap.walked:
  for toks: List<&2, Lex.Tok>
  for +wk: Wrap.Walk
  for +glued: Bool
  {wrap.of(Wrap.check.walk(toks, wk, glued)) == Laws.wrap.run(toks, wrap.of(wk), glued) : Laws.wrap.Read}

def wrap.walked(toks, wk, glued):
  match toks:
    case Nil{}:
      wrap.sealed(wk, glued)
    case Con{Lex.Tok{+kk, +tx, +ln, +cl}, +rest}:
      +tok = {Lex.Tok{kk, tx, ln, cl} : Lex.Tok}
      Equal.trans(Laws.wrap.Read,
        wrap.of(Wrap.check.walk(rest, Wrap.check.step(tok, wk, glued), Lex.is_name(kk))),
        Laws.wrap.run(rest, wrap.of(Wrap.check.step(tok, wk, glued)), Lex.is_name(kk)),
        Laws.wrap.run(rest, Laws.wrap.step(tok, wrap.of(wk), glued), Lex.is_name(kk)),
        wrap.walked(rest, Wrap.check.step(tok, wk, glued), Lex.is_name(kk)),
        Equal.cong(Laws.wrap.Read, Laws.wrap.Read, rd => Laws.wrap.run(rest, rd, Lex.is_name(kk)),
          wrap.of(Wrap.check.step(tok, wk, glued)), Laws.wrap.step(tok, wrap.of(wk), glued),
          wrap.stepped(tok, wk, glued)))

# a Maybe that holds a value
def wrap.found(mm: Maybe<&2, Wrap.Span>) -> Bool:
  match mm:
    case None{}:
      False{}
    case Some{_sp}:
      True{}

# the rule's line test is the spec's
law wrap.shares:
  for ps: List<&2, Wrap.Span>
  for +ln: U32
  {Wrap.check.shares(ps, ln) == Laws.wrap.starts_on(ps, ln) : Bool}

def wrap.shares(ps, ln):
  match ps:
    case Nil{}:
      {==}
    case Con{Wrap.Span{+line, _end, _col}, +rest}:
      put.or(U32.is_eq(line, ln), Wrap.check.shares(rest, ln), Laws.wrap.starts_on(rest, ln), wrap.shares(rest, ln))

# the rule's misplaced parameter is the spec's
law wrap.bad:
  for +line: U32
  for +end: U32
  for +col: U32
  for +open: U32
  for +rest: List<&2, Wrap.Span>
  {Wrap.check.bad(Wrap.Span{line, end, col}, open, rest)
    == Bool.or(Bool.not(U32.is_eq(line, end)), Bool.or(U32.is_eq(line, open), Laws.wrap.starts_on(rest, line))) : Bool}

def wrap.bad(line, end, _col, open, rest):
  put.or(Bool.not(U32.is_eq(line, end)), Lazy.or_else(U32.is_eq(line, open), _u2 => Wrap.check.shares(rest, line)),
    Bool.or(U32.is_eq(line, open), Laws.wrap.starts_on(rest, line)),
    put.or(U32.is_eq(line, open), Wrap.check.shares(rest, line), Laws.wrap.starts_on(rest, line),
      wrap.shares(rest, line)))

# an early exit to a found value is found when it exits, else when the rest is
law wrap.stop_found:
  for b: Bool
  for -sp: Wrap.Span
  for -x: Maybe<&2, Wrap.Span>
  for -y: Bool
  for e: {wrap.found(x) == y : Bool}
  {wrap.found(Lazy.stop(Maybe<&2, Wrap.Span>, b, Some{sp}, _u => x)) == Bool.or(b, y) : Bool}

def wrap.stop_found(b, _sp, _x, _y, e):
  match b:
    case True{}:
      {==}
    case False{}:
      e

# equal disjuncts give equal ors
law wrap.or2:
  for -a: Bool
  for -b: Bool
  for -c: Bool
  for -d: Bool
  for e1: {a == c : Bool}
  for e2: {b == d : Bool}
  {Bool.or(a, b) == Bool.or(c, d) : Bool}

def wrap.or2(a, b, _c, d, e1, e2):
  %e1 : {Bool.or(a, b) == Bool.or(_, d) : Bool}
  %e2 : {Bool.or(a, b) == Bool.or(a, _) : Bool}
  {==}

# the rule finds a misplaced parameter exactly when the spec does
law wrap.judged:
  for ps: List<&2, Wrap.Span>
  for +open: U32
  {wrap.found(Wrap.check.judge(ps, open)) == Laws.wrap.misplaced(ps, open) : Bool}

def wrap.judged(ps, open):
  match ps:
    case Nil{}:
      {==}
    case Con{Wrap.Span{+line, +end, +col}, +rest}:
      Equal.trans(Bool,
        wrap.found(Lazy.stop(Maybe<&2, Wrap.Span>, Wrap.check.bad(Wrap.Span{line, end, col}, open, rest),
          Some{Wrap.Span{line, end, col}}, _u => Wrap.check.judge(rest, open))),
        Bool.or(Wrap.check.bad(Wrap.Span{line, end, col}, open, rest), Laws.wrap.misplaced(rest, open)),
        Laws.wrap.misplaced(Wrap.Span{line, end, col} <> rest, open),
        wrap.stop_found(Wrap.check.bad(Wrap.Span{line, end, col}, open, rest), Wrap.Span{line, end, col},
          Wrap.check.judge(rest, open), Laws.wrap.misplaced(rest, open), wrap.judged(rest, open)),
        wrap.or2(Wrap.check.bad(Wrap.Span{line, end, col}, open, rest), Laws.wrap.misplaced(rest, open),
          Bool.or(Bool.not(U32.is_eq(line, end)), Bool.or(U32.is_eq(line, open), Laws.wrap.starts_on(rest, line))),
          Laws.wrap.misplaced(rest, open), wrap.bad(line, end, col, open, rest), {==}))

# a pick between a found value and none is found when it picks the first
law wrap.pick_found:
  for t: Bool
  for -sp: Wrap.Span
  {wrap.found(Bool.pick(Maybe<&2, Wrap.Span>, t, Some{sp}, None{})) == t : Bool}

def wrap.pick_found(t, _sp):
  match t:
    case True{}:
      {==}
    case False{}:
      {==}

# the rule's last-line test is the spec's
law wrap.tight:
  for ps: List<&2, Wrap.Span>
  for +shut: U32
  {Wrap.check.tight(ps, shut) == Laws.wrap.tight(ps, shut) : Bool}

def wrap.tight(ps, _shut):
  match ps:
    case Nil{}:
      {==}
    case Con{Wrap.Span{line, end, col}, rest}:
      {==}

# a `)` on the line given is found cramped exactly when the spec's test says so
law wrap.tight_found:
  for +line: U32
  for +end: U32
  for +col: U32
  for +spans: List<&2, Wrap.Span>
  {wrap.found(Wrap.check.shut_at(Wrap.Span{line, end, col}, spans)) == Laws.wrap.tight(spans, line) : Bool}

def wrap.tight_found(line, end, col, spans):
  Equal.trans(Bool,
    wrap.found(Bool.pick(Maybe<&2, Wrap.Span>, Wrap.check.tight(spans, line), Some{Wrap.Span{line, end, col}},
      None{})),
    Wrap.check.tight(spans, line),
    Laws.wrap.tight(spans, line),
    wrap.pick_found(Wrap.check.tight(spans, line), Wrap.Span{line, end, col}),
    wrap.tight(spans, line))

# no parameter: found at the `(` line exactly when the spec says none
law wrap.none:
  for spans: List<&2, Wrap.Span>
  for +open: U32
  {wrap.found(Wrap.check.none_at(spans, open)) == Laws.wrap.none(spans) : Bool}

def wrap.none(spans, _open):
  match spans:
    case Nil{}:
      {==}
    case Con{sp, rest}:
      {==}

# the rule finds a cramped `)` exactly when the spec does
law wrap.shut:
  for mode: Wrap.Phase
  for +shut: Wrap.Span
  for +spans: List<&2, Wrap.Span>
  for -paren: U32
  for -bracket: U32
  for -brace: U32
  for -angle: U32
  for -open: U32
  for -on: Bool
  for -pline: U32
  for -pend: U32
  for -pcol: U32
  {wrap.found(Wrap.check.shut_span(Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol,
    spans}))
    == Laws.wrap.cramped(mode, wrap.line_of(shut), spans) : Bool}

def wrap.shut(mode, shut, spans, _paren, _bracket, _brace, _angle, _open, _on, _pline, _pend, _pcol):
  match mode:
    case Wrap.Past{}:
      match shut:
        case Wrap.Span{+line, +end, +col}:
          wrap.tight_found(line, end, col, spans)
    case Wrap.Shut{}:
      match shut:
        case Wrap.Span{+line, +end, +col}:
          wrap.tight_found(line, end, col, spans)
    case Wrap.Loose{}:
      match shut:
        case Wrap.Span{+line, +end, +col}:
          wrap.tight_found(line, end, col, spans)
    case Wrap.Seek{}:
      {==}
    case Wrap.Args{}:
      {==}

# the rule finds an empty list exactly when the spec does
law wrap.empty:
  for mode: Wrap.Phase
  for +spans: List<&2, Wrap.Span>
  for +open: U32
  for -paren: U32
  for -bracket: U32
  for -brace: U32
  for -angle: U32
  for -shut: Wrap.Span
  for -on: Bool
  for -pline: U32
  for -pend: U32
  for -pcol: U32
  {wrap.found(Wrap.check.empty_span(Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol,
    spans})) == Laws.wrap.empty(mode, spans) : Bool}

def wrap.empty(mode, spans, open, _paren, _bracket, _brace, _angle, _shut, _on, _pline, _pend, _pcol):
  match mode:
    case Wrap.Seek{}:
      {==}
    case Wrap.Args{}:
      wrap.none(spans, open)
    case Wrap.Past{}:
      wrap.none(spans, open)
    case Wrap.Shut{}:
      wrap.none(spans, open)
    case Wrap.Loose{}:
      wrap.none(spans, open)

# the rule finds a `)` with no `->` after it exactly when the spec does
law wrap.loose:
  for mode: Wrap.Phase
  for -spans: List<&2, Wrap.Span>
  for -open: U32
  for -paren: U32
  for -bracket: U32
  for -brace: U32
  for -angle: U32
  for -shut: Wrap.Span
  for -on: Bool
  for -pline: U32
  for -pend: U32
  for -pcol: U32
  {wrap.found(Wrap.check.loose_span(Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol,
    spans})) == Laws.wrap.loose(mode) : Bool}

def wrap.loose(mode, _spans, _open, _paren, _bracket, _brace, _angle, _shut, _on, _pline, _pend, _pcol):
  match mode:
    case Wrap.Seek{}:
      {==}
    case Wrap.Args{}:
      {==}
    case Wrap.Past{}:
      {==}
    case Wrap.Shut{}:
      {==}
    case Wrap.Loose{}:
      {==}

# the rule's four findings for a header read are the spec's verdict on it
law wrap.verdict:
  for +wk: Wrap.Walk
  {Bool.or(wrap.found(Wrap.check.jam_span(wk)), Bool.or(wrap.found(Wrap.check.empty_span(wk)),
    Bool.or(wrap.found(Wrap.check.shut_span(wk)), wrap.found(Wrap.check.loose_span(wk)))))
    == Laws.wrap.bad_shape(wrap.of(wk)) : Bool}

def wrap.verdict(wk):
  match wk:
    case Wrap.Walk{+mode, +paren, +bracket, +brace, +angle, +shut, +open, +on, +pline, +pend, +pcol, +spans}:
      +w = {Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans} : Wrap.Walk}
      wrap.or2(wrap.found(Wrap.check.judge(List.reverse(&2, Wrap.Span, spans), open)),
        Bool.or(wrap.found(Wrap.check.empty_span(w)),
          Bool.or(wrap.found(Wrap.check.shut_span(w)), wrap.found(Wrap.check.loose_span(w)))),
        Laws.wrap.misplaced(List.reverse(&2, Wrap.Span, spans), open),
        Bool.or(Laws.wrap.empty(mode, spans),
          Bool.or(Laws.wrap.cramped(mode, wrap.line_of(shut), spans), Laws.wrap.loose(mode))),
        wrap.judged(List.reverse(&2, Wrap.Span, spans), open),
        wrap.or2(wrap.found(Wrap.check.empty_span(w)),
          Bool.or(wrap.found(Wrap.check.shut_span(w)), wrap.found(Wrap.check.loose_span(w))),
          Laws.wrap.empty(mode, spans),
          Bool.or(Laws.wrap.cramped(mode, wrap.line_of(shut), spans), Laws.wrap.loose(mode)),
          wrap.empty(mode, spans, open, paren, bracket, brace, angle, shut, on, pline, pend, pcol),
          wrap.or2(wrap.found(Wrap.check.shut_span(w)), wrap.found(Wrap.check.loose_span(w)),
            Laws.wrap.cramped(mode, wrap.line_of(shut), spans), Laws.wrap.loose(mode),
            wrap.shut(mode, shut, spans, paren, bracket, brace, angle, open, on, pline, pend, pcol),
            wrap.loose(mode, spans, open, paren, bracket, brace, angle, shut, on, pline, pend, pcol))))

# the rule's four findings, first found first: one onto the rest when any
# is found, else the rest
law wrap.placed:
  for mm: Maybe<&2, Wrap.Span>
  for em: Maybe<&2, Wrap.Span>
  for sh: Maybe<&2, Wrap.Span>
  for lo: Maybe<&2, Wrap.Span>
  for +base: U32
  for +path: String
  for +more: List<&2, F.Finding>
  {List.length(&2, F.Finding, Wrap.check.place(mm, em, sh, lo, base, path, more))
    == Bool.pick(Nat, Bool.or(wrap.found(mm), Bool.or(wrap.found(em), Bool.or(wrap.found(sh), wrap.found(lo)))),
      1n+List.length(&2, F.Finding, more), List.length(&2, F.Finding, more)) : Nat}

def wrap.placed(mm, em, sh, lo, _base, _path, _more):
  match mm:
    case Some{Wrap.Span{line, end, col}}:
      {==}
    case None{}:
      match em:
        case Some{Wrap.Span{line, end, col}}:
          {==}
        case None{}:
          match sh:
            case Some{Wrap.Span{line, end, col}}:
              {==}
            case None{}:
              match lo:
                case Some{Wrap.Span{line, end, col}}:
                  {==}
                case None{}:
                  {==}

# a broken header: one finding onto the rest exactly when its shape is bad
law wrap.jammed:
  for +toks: List<&2, Lex.Tok>
  for +line: U32
  for +path: String
  for +more: List<&2, F.Finding>
  {List.length(&2, F.Finding, Wrap.check.jam(line, toks, path, more))
    == Bool.pick(Nat, Laws.wrap.shape(toks), 1n+List.length(&2, F.Finding, more), List.length(&2, F.Finding, more))
    : Nat}

def wrap.jammed(toks, line, path, more):
  +wk = Wrap.check.walk(toks, Wrap.check.start(), False{})
  +len = List.length(&2, F.Finding, more)
  +any = Bool.or(wrap.found(Wrap.check.jam_span(wk)), Bool.or(wrap.found(Wrap.check.empty_span(wk)),
    Bool.or(wrap.found(Wrap.check.shut_span(wk)), wrap.found(Wrap.check.loose_span(wk)))))
  Equal.trans(Nat,
    List.length(&2, F.Finding, Wrap.check.place(Wrap.check.jam_span(wk), Wrap.check.empty_span(wk),
      Wrap.check.shut_span(wk), Wrap.check.loose_span(wk), line, path, more)),
    Bool.pick(Nat, any, 1n+len, len),
    Bool.pick(Nat, Laws.wrap.shape(toks), 1n+len, len),
    wrap.placed(Wrap.check.jam_span(wk), Wrap.check.empty_span(wk), Wrap.check.shut_span(wk), Wrap.check.loose_span(wk),
      line, path, more),
    Equal.cong(Bool, Nat, bb => Bool.pick(Nat, bb, 1n+len, len), any, Laws.wrap.shape(toks),
      Equal.trans(Bool, any, Laws.wrap.bad_shape(wrap.of(wk)), Laws.wrap.shape(toks), wrap.verdict(wk),
        Equal.cong(Laws.wrap.Read, Bool, rd => Laws.wrap.bad_shape(rd), wrap.of(wk),
          Laws.wrap.run(toks, Laws.wrap.start(), False{}), wrap.walked(toks, Wrap.check.start(), False{})))))

def Laws.wrap_shape_counts(toks, line, path):
  wrap.jammed(toks, line, path, [])

# an early exit to one finding onto the rest, else the rest
law wrap.stop_len:
  for b: Bool
  for -x: F.Finding
  for +more: List<&2, F.Finding>
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, b, x <> more, _u => more))
    == Bool.pick(Nat, b, 1n+List.length(&2, F.Finding, more), List.length(&2, F.Finding, more)) : Nat}

def wrap.stop_len(b, _x, _more):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a one-line header: one finding onto the rest exactly when it is too wide
law wrap.wide:
  for +line: U32
  for +sig: String
  for +path: String
  for +more: List<&2, F.Finding>
  {List.length(&2, F.Finding, Wrap.check.wide(line, sig, path, more))
    == Bool.pick(Nat, U32.is_gt(Laws.wrap.width(Lex.tokens(sig)), 120), 1n+List.length(&2, F.Finding, more),
      List.length(&2, F.Finding, more)) : Nat}

def wrap.wide(line, sig, path, more):
  +len = List.length(&2, F.Finding, more)
  Equal.trans(Nat,
    List.length(&2, F.Finding, Wrap.check.wide(line, sig, path, more)),
    Bool.pick(Nat, U32.is_gt(Wrap.check.width(sig), 120), 1n+len, len),
    Bool.pick(Nat, U32.is_gt(Laws.wrap.width(Lex.tokens(sig)), 120), 1n+len, len),
    wrap.stop_len(U32.is_gt(Wrap.check.width(sig), 120),
      F.Finding{path, line, 120, 0, "wrap", "Def header exceeds the 120-character limit; wrap with one parameter per line."},
      more),
    Equal.cong(U32, Nat, ww => Bool.pick(Nat, U32.is_gt(ww, 120), 1n+len, len), Wrap.check.width(sig),
      Laws.wrap.width(Lex.tokens(sig)), Laws.wrap_width(Lex.tokens(sig))))

# a header, broken or not: one finding onto the rest exactly when it is bad
law wrap.headed:
  for multi: Bool
  for +line: U32
  for +sig: String
  for +path: String
  for +more: List<&2, F.Finding>
  {List.length(&2, F.Finding, Wrap.check.header(multi, line, sig, path, more))
    == Bool.pick(Nat, Bool.pick(Bool, multi, Laws.wrap.shape(Lex.tokens(sig)),
      U32.is_gt(Laws.wrap.width(Lex.tokens(sig)), 120)), 1n+List.length(&2, F.Finding, more),
      List.length(&2, F.Finding, more)) : Nat}

def wrap.headed(multi, line, sig, path, more):
  match multi:
    case True{}:
      wrap.jammed(Lex.tokens(sig), line, path, more)
    case False{}:
      wrap.wide(line, sig, path, more)

# an item: one finding onto the rest exactly when it is a bad def header
law wrap.one:
  for kk: Outline.ItemKind
  for +line: U32
  for +sig: String
  for +path: String
  for +more: List<&2, F.Finding>
  {List.length(&2, F.Finding, Wrap.check.one(kk, line, sig, path, more))
    == Bool.pick(Nat, Bool.and(Outline.is_def(kk), Laws.wrap.bad(sig)), 1n+List.length(&2, F.Finding, more),
      List.length(&2, F.Finding, more)) : Nat}

def wrap.one(kk, line, sig, path, more):
  match kk:
    case Outline.IImport{}:
      {==}
    case Outline.IDef{}:
      wrap.headed(String.contains(sig, "\n"), line, sig, path, more)
    case Outline.ILaw{}:
      {==}
    case Outline.IType{}:
      {==}
    case Outline.ICtor{}:
      {==}
    case Outline.ILocal{}:
      {==}

# the rule's walk over the items counts the bad def headers
law wrap.went:
  for items: List<&2, Outline.Item>
  for +path: String
  {List.length(&2, F.Finding, Wrap.check.go(items, path)) == Laws.wrap.count(items) : Nat}

def wrap.went(items, path):
  match items:
    case Nil{}:
      {==}
    case Con{Outline.Item{+kk, _name, +line, +sig, _doc, _pp}, +rest}:
      +more = Wrap.check.go(rest, path)
      +hit = Bool.and(Outline.is_def(kk), Laws.wrap.bad(sig))
      Equal.trans(Nat,
        List.length(&2, F.Finding, Wrap.check.one(kk, line, sig, path, more)),
        Bool.pick(Nat, hit, 1n+List.length(&2, F.Finding, more), List.length(&2, F.Finding, more)),
        Bool.pick(Nat, hit, 1n+Laws.wrap.count(rest), Laws.wrap.count(rest)),
        wrap.one(kk, line, sig, path, more),
        Equal.cong(Nat, Nat, nn => Bool.pick(Nat, hit, 1n+nn, nn), List.length(&2, F.Finding, more),
          Laws.wrap.count(rest), wrap.went(rest, path)))

def Laws.wrap_counts(path, _text, _toks, _tree, _bound, items):
  wrap.went(items, path)

# coverage (BOLT-LAW-1)

# an early-exit or is Bool.or
law coverage.or_else:
  for c: Bool
  for -x: Bool
  {Lazy.or_else(c, _u => x) == Bool.or(c, x) : Bool}

def coverage.or_else(c, _x):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# or is associative
law coverage.or_assoc:
  for a: Bool
  for -b: Bool
  for -c: Bool
  {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}

def coverage.or_assoc(a, _b, _c):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the rule's search of the uses is coverage.names
law coverage.has:
  for ms: List<&2, Digest.Mention>
  for +pp: String
  for +name: String
  {Coverage.has_item(ms, pp, name) == Laws.coverage.names(ms, pp, name) : Bool}

def coverage.has(ms, pp, name):
  match ms:
    case Nil{}:
      {==}
    case Con{Digest.Mention{+mp, +mn}, rest}:
      %coverage.has(rest, pp, name) :
        {Lazy.or_else(Bool.and(String.eq(mp, pp), String.eq(mn, name)), _u => Coverage.has_item(rest, pp, name))
          == Bool.or(Bool.and(String.eq(mp, pp), String.eq(mn, name)), _) : Bool}
      coverage.or_else(Bool.and(String.eq(mp, pp), String.eq(mn, name)), Coverage.has_item(rest, pp, name))

# two lists of uses name an item when either does
law coverage.app:
  for as: List<&2, Digest.Mention>
  for -bs: List<&2, Digest.Mention>
  for +pp: String
  for +name: String
  {Laws.coverage.names(List.append(&2, Digest.Mention, as, bs), pp, name)
    == Bool.or(Laws.coverage.names(as, pp, name), Laws.coverage.names(bs, pp, name)) : Bool}

def coverage.app(as, bs, pp, name):
  match as:
    case Nil{}:
      {==}
    case Con{Digest.Mention{+mp, +mn}, rest}:
      %Equal.sym(Bool, Bool.or(Bool.or(Bool.and(String.eq(mp, pp), String.eq(mn, name)),
          Laws.coverage.names(rest, pp, name)), Laws.coverage.names(bs, pp, name)),
        Bool.or(Bool.and(String.eq(mp, pp), String.eq(mn, name)),
          Bool.or(Laws.coverage.names(rest, pp, name), Laws.coverage.names(bs, pp, name))),
        coverage.or_assoc(Bool.and(String.eq(mp, pp), String.eq(mn, name)), Laws.coverage.names(rest, pp, name),
          Laws.coverage.names(bs, pp, name))) :
        {Bool.or(Bool.and(String.eq(mp, pp), String.eq(mn, name)),
          Laws.coverage.names(List.append(&2, Digest.Mention, rest, bs), pp, name)) == _ : Bool}
      Equal.cong(Bool, Bool, b => Bool.or(Bool.and(String.eq(mp, pp), String.eq(mn, name)), b),
        Laws.coverage.names(List.append(&2, Digest.Mention, rest, bs), pp, name),
        Bool.or(Laws.coverage.names(rest, pp, name), Laws.coverage.names(bs, pp, name)),
        coverage.app(rest, bs, pp, name))

# what the rule gathers names an item exactly when some LAWS.bend uses it
law coverage.named:
  for ds: List<&2, Digest.Digest>
  for +pp: String
  for +name: String
  {Laws.coverage.names(Coverage.named(ds), pp, name) == Laws.coverage.used(ds, pp, name) : Bool}

def coverage.named(ds, pp, name):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, +says, deps, unsafes, laws}, rest}:
      match is_laws:
        case True{}:
          %coverage.named(rest, pp, name) :
            {Laws.coverage.names(List.append(&2, Digest.Mention, says, Coverage.named(rest)), pp, name)
              == Bool.or(Laws.coverage.names(says, pp, name), _) : Bool}
          coverage.app(says, Coverage.named(rest), pp, name)
        case False{}:
          coverage.named(rest, pp, name)

# the rule's lookup is coverage.used
law coverage.item:
  for +ds: List<&2, Digest.Digest>
  for +pp: String
  for +name: String
  {Coverage.has_item(Coverage.named(ds), pp, name) == Laws.coverage.used(ds, pp, name) : Bool}

def coverage.item(ds, pp, name):
  Equal.trans(Bool, Coverage.has_item(Coverage.named(ds), pp, name), Laws.coverage.names(Coverage.named(ds), pp, name),
    Laws.coverage.used(ds, pp, name), coverage.has(Coverage.named(ds), pp, name), coverage.named(ds, pp, name))

# the rule's search of a type's constructors is coverage.any
law coverage.any:
  for ns: List<&2, String>
  for +all: List<&2, Digest.Digest>
  for +pp: String
  {Coverage.any_item(ns, Coverage.named(all), pp) == Laws.coverage.any(ns, all, pp) : Bool}

def coverage.any(ns, all, pp):
  match ns:
    case Nil{}:
      {==}
    case Con{+name, rest}:
      %coverage.item(all, pp, name) :
        {Lazy.or_else(Coverage.has_item(Coverage.named(all), pp, name),
          _u => Coverage.any_item(rest, Coverage.named(all), pp))
          == Bool.or(_, Laws.coverage.any(rest, all, pp)) : Bool}
      %coverage.any(rest, all, pp) :
        {Lazy.or_else(Coverage.has_item(Coverage.named(all), pp, name),
          _u => Coverage.any_item(rest, Coverage.named(all), pp))
          == Bool.or(Coverage.has_item(Coverage.named(all), pp, name), _) : Bool}
      coverage.or_else(Coverage.has_item(Coverage.named(all), pp, name),
        Coverage.any_item(rest, Coverage.named(all), pp))

# the rule's gaps are coverage.gaps
law coverage.gaps:
  for ts: List<&2, Digest.Top>
  for +all: List<&2, Digest.Digest>
  for +pp: String
  for +path: String
  {Coverage.gaps(ts, Coverage.named(all), pp, path) == Laws.coverage.gaps(ts, all, pp, path) : List<&2, F.Finding>}

def coverage.gaps(ts, all, pp, path):
  match ts:
    case Nil{}:
      {==}
    case Con{Digest.Top{Outline.IDef{}, +name, +line, cs}, rest}:
      %coverage.item(all, pp, name) :
        {Coverage.gaps(Digest.Top{Outline.IDef{}, name, line, cs} <> rest, Coverage.named(all), pp, path)
          == Bool.pick(List<&2, F.Finding>, Bool.or(String.contains(name, "."), _),
            Laws.coverage.gaps(rest, all, pp, path), F.Finding{path, line, 0, 0, "coverage", "Def " ++ name ++ " is named by no law."}
              <> Laws.coverage.gaps(rest, all, pp, path)) : List<&2, F.Finding>}
      %coverage.gaps(rest, all, pp, path) :
        {Coverage.gaps(Digest.Top{Outline.IDef{}, name, line, cs} <> rest, Coverage.named(all), pp, path)
          == Bool.pick(List<&2, F.Finding>,
            Bool.or(String.contains(name, "."), Coverage.has_item(Coverage.named(all), pp, name)), _,
            F.Finding{path, line, 0, 0, "coverage", "Def " ++ name ++ " is named by no law."} <> _) : List<&2, F.Finding>}
      {==}
    case Con{Digest.Top{Outline.IType{}, +name, +line, +cs}, rest}:
      %coverage.item(all, pp, name) :
        {Coverage.gaps(Digest.Top{Outline.IType{}, name, line, cs} <> rest, Coverage.named(all), pp, path)
          == Bool.pick(List<&2, F.Finding>, Bool.or(_, Laws.coverage.any(cs, all, pp)),
            Laws.coverage.gaps(rest, all, pp, path), F.Finding{path, line, 0, 0, "coverage", "Type " ++ name ++ " is named by no law, nor are its constructors."}
              <> Laws.coverage.gaps(rest, all, pp, path)) : List<&2, F.Finding>}
      %coverage.any(cs, all, pp) :
        {Coverage.gaps(Digest.Top{Outline.IType{}, name, line, cs} <> rest, Coverage.named(all), pp, path)
          == Bool.pick(List<&2, F.Finding>, Bool.or(Coverage.has_item(Coverage.named(all), pp, name), _),
            Laws.coverage.gaps(rest, all, pp, path), F.Finding{path, line, 0, 0, "coverage", "Type " ++ name ++ " is named by no law, nor are its constructors."}
              <> Laws.coverage.gaps(rest, all, pp, path)) : List<&2, F.Finding>}
      %coverage.gaps(rest, all, pp, path) :
        {Coverage.gaps(Digest.Top{Outline.IType{}, name, line, cs} <> rest, Coverage.named(all), pp, path)
          == Bool.pick(List<&2, F.Finding>,
            Bool.or(Coverage.has_item(Coverage.named(all), pp, name),
              Coverage.any_item(cs, Coverage.named(all), pp)), _,
            F.Finding{path, line, 0, 0, "coverage", "Type " ++ name ++ " is named by no law, nor are its constructors."}
              <> _) : List<&2, F.Finding>}
      Equal.cong(Bool, List<&2, F.Finding>,
        bb => Bool.pick(List<&2, F.Finding>, bb, Coverage.gaps(rest, Coverage.named(all), pp, path),
          F.Finding{path, line, 0, 0, "coverage", "Type " ++ name ++ " is named by no law, nor are its constructors."}
            <> Coverage.gaps(rest, Coverage.named(all), pp, path)),
        Lazy.or_else(Coverage.has_item(Coverage.named(all), pp, name),
          _u => Coverage.any_item(cs, Coverage.named(all), pp)),
        Bool.or(Coverage.has_item(Coverage.named(all), pp, name), Coverage.any_item(cs, Coverage.named(all), pp)),
        coverage.or_else(Coverage.has_item(Coverage.named(all), pp, name),
          Coverage.any_item(cs, Coverage.named(all), pp)))
    case Con{Digest.Top{Outline.IImport{}, name, line, cs}, rest}:
      coverage.gaps(rest, all, pp, path)
    case Con{Digest.Top{Outline.ILaw{}, name, line, cs}, rest}:
      coverage.gaps(rest, all, pp, path)
    case Con{Digest.Top{Outline.ICtor{}, name, line, cs}, rest}:
      coverage.gaps(rest, all, pp, path)
    case Con{Digest.Top{Outline.ILocal{}, name, line, cs}, rest}:
      coverage.gaps(rest, all, pp, path)

# the rule's walk over the files is coverage.files
law coverage.go:
  for fs: List<&2, Digest.Digest>
  for +all: List<&2, Digest.Digest>
  {Coverage.check.go(fs, Coverage.named(all)) == Laws.coverage.files(fs, all) : List<&2, F.Finding>}

def coverage.go(fs, all):
  match fs:
    case Nil{}:
      {==}
    case Con{Digest.Digest{+path, +norm, dir, is_laws, is_law_file, exempt, +tops, says, deps, unsafes, laws}, rest}:
      match exempt:
        case True{}:
          coverage.go(rest, all)
        case False{}:
          %coverage.go(rest, all) :
            {Coverage.check.go(Digest.Digest{path, norm, dir, is_laws, is_law_file, False{}, tops, says, deps, unsafes,
              laws} <> rest, Coverage.named(all))
              == List.append(&2, F.Finding, Laws.coverage.gaps(tops, all, norm, path), _) : List<&2, F.Finding>}
          %coverage.gaps(tops, all, norm, path) :
            {Coverage.check.go(Digest.Digest{path, norm, dir, is_laws, is_law_file, False{}, tops, says, deps, unsafes,
              laws} <> rest, Coverage.named(all))
              == List.append(&2, F.Finding, _, Coverage.check.go(rest, Coverage.named(all))) : List<&2, F.Finding>}
          {==}

# the rule runs the walk exactly when some digest is a LAWS.bend
law coverage.first:
  for +fs: List<&2, Digest.Digest>
  for ds: List<&2, Digest.Digest>
  {Coverage.check.first(fs, Coverage.law_dirs(ds))
    == Bool.pick(List<&2, F.Finding>, Laws.coverage.lawful(ds), Coverage.check.go(fs, Coverage.named(fs)), [])
    : List<&2, F.Finding>}

def coverage.first(fs, ds):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      match is_laws:
        case True{}:
          {==}
        case False{}:
          coverage.first(fs, rest)

def Laws.coverage_reports(ds):
  %coverage.go(ds, ds) :
    {Coverage.check(ds) == Bool.pick(List<&2, F.Finding>, Laws.coverage.lawful(ds), _, []) : List<&2, F.Finding>}
  coverage.first(ds, ds)

# unsafe (BOLT-LAW-3)

# the rule's search of the law files' closures is unsafe.origin
law unsafe.reacher:
  for ls: List<&2, Digest.Digest>
  for +all: List<&2, Digest.Digest>
  for +pp: String
  {Unsafe.reacher(Unsafe.reaches(ls, Digest.edges(all), Imports.paths(Digest.edges(all)),
    List.length(&2, Digest.Digest, all)), pp) == Laws.unsafe.origin(ls, all, pp) : Maybe<&2, String>}

def unsafe.reacher(ls, all, pp):
  match ls:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      match is_law_file:
        case True{}:
          %unsafe.reacher(rest, all, pp) :
            {Unsafe.reacher(Unsafe.Reach{path, Laws.unsafe.closure(all, norm)}
              <> Unsafe.reaches(rest, Digest.edges(all), Imports.paths(Digest.edges(all)),
                List.length(&2, Digest.Digest, all)), pp)
              == Bool.pick(Maybe<&2, String>, Imports.has(Laws.unsafe.closure(all, norm), pp), Some{path}, _)
              : Maybe<&2, String>}
          {==}
        case False{}:
          unsafe.reacher(rest, all, pp)

# the rule's report is unsafe.each
law unsafe.report:
  for us: List<&2, Digest.Unsafe>
  for +origin: String
  for +path: String
  {Unsafe.report(us, origin, path) == Laws.unsafe.each(us, origin, path) : List<&2, F.Finding>}

def unsafe.report(us, origin, path):
  match us:
    case Nil{}:
      {==}
    case Con{Digest.Unsafe{+n, +l, +c}, rest}:
      Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
        t => F.Finding{path, l, c, 7, "unsafe", "@unsafe def " ++ n ++ " is reached from " ++ origin
          ++ "; the checker only warns there and exits 0. Recurse on a shrinking argument or fuel."} <> t,
        Unsafe.report(rest, origin, path), Laws.unsafe.each(rest, origin, path), unsafe.report(rest, origin, path))

# the rule's found is unsafe.at
law unsafe.found:
  for mm: Maybe<&2, String>
  for us: List<&2, Digest.Unsafe>
  for +path: String
  {Unsafe.found(mm, us, path) == Laws.unsafe.at(mm, us, path) : List<&2, F.Finding>}

def unsafe.found(mm, us, path):
  match mm:
    case None{}:
      {==}
    case Some{origin}:
      unsafe.report(us, origin, path)

# the rule's walk over the files is unsafe.files
law unsafe.go:
  for fs: List<&2, Digest.Digest>
  for +all: List<&2, Digest.Digest>
  {Unsafe.check.go(fs, Unsafe.reaches(all, Digest.edges(all), Imports.paths(Digest.edges(all)),
    List.length(&2, Digest.Digest, all))) == Laws.unsafe.files(fs, all) : List<&2, F.Finding>}

def unsafe.go(fs, all):
  match fs:
    case Nil{}:
      {==}
    case Con{Digest.Digest{+path, +norm, dir, is_laws, is_law_file, exempt, tops, says, deps, +unsafes, laws}, rest}:
      %unsafe.go(rest, all) :
        {Unsafe.check.go(Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}
          <> rest, Unsafe.reaches(all, Digest.edges(all), Imports.paths(Digest.edges(all)),
            List.length(&2, Digest.Digest, all)))
          == List.append(&2, F.Finding, Laws.unsafe.at(Laws.unsafe.origin(all, all, norm), unsafes, path), _)
          : List<&2, F.Finding>}
      %unsafe.found(Laws.unsafe.origin(all, all, norm), unsafes, path) :
        {Unsafe.check.go(Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}
          <> rest, Unsafe.reaches(all, Digest.edges(all), Imports.paths(Digest.edges(all)),
            List.length(&2, Digest.Digest, all)))
          == List.append(&2, F.Finding, _, Unsafe.check.go(rest, Unsafe.reaches(all, Digest.edges(all),
            Imports.paths(Digest.edges(all)), List.length(&2, Digest.Digest, all)))) : List<&2, F.Finding>}
      %unsafe.reacher(all, all, norm) :
        {Unsafe.check.go(Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}
          <> rest, Unsafe.reaches(all, Digest.edges(all), Imports.paths(Digest.edges(all)),
            List.length(&2, Digest.Digest, all)))
          == List.append(&2, F.Finding, Unsafe.found(_, unsafes, path), Unsafe.check.go(rest, Unsafe.reaches(all,
            Digest.edges(all), Imports.paths(Digest.edges(all)), List.length(&2, Digest.Digest, all))))
          : List<&2, F.Finding>}
      {==}

def Laws.unsafe_reports(ds):
  unsafe.go(ds, ds)

# The recursion rule, hoist: each call adds the one the law's call test
# counts, each plain let the one its let test counts, the heat follows the
# same lambdas and case arms, and the def walk joins the per-def lists into
# their sum.

# a table found or not: one finding or none
law hoist.yes:
  for b: Bool
  for -aa: Tree.Node
  for -path: String
  {List.length(&2, F.Finding, Hoist.one_yes(b, aa, path)) == Bool.pick(Nat, b, 1n, 0n) : Nat}

def hoist.yes(b, _aa, _path):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a get or set's collection: one finding when the law's slot test holds
law hoist.slot:
  for ss: Hoist.Slot
  for +as: List<&2, Tree.Node>
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  {List.length(&2, F.Finding, Hoist.arg_table(ss, as, self, wides, carried, path))
    == Bool.pick(Nat, Laws.hoist.slot(ss, as, self, wides, carried), 1n, 0n) : Nat}

def hoist.slot(ss, as, self, wides, carried, path):
  match ss:
    case Hoist.Slot{on, at}:
      match on:
        case False{}:
          {==}
        case True{}:
          hoist.yes(Hoist.is_table(Calls.arg(as, at), self, wides, carried), Calls.arg(as, at), path)

# a call site: one finding when the law's call test holds
law hoist.call:
  for hot: Bool
  for open: Bool
  for +tt: String
  for +kids: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  {List.length(&2, F.Finding, Hoist.call_table(hot, open, tt, kids, self, wides, carried, path))
    == Bool.pick(Nat, Laws.hoist.call(hot, open, tt, kids, self, wides, carried), 1n, 0n) : Nat}

def hoist.call(hot, open, tt, kids, self, wides, carried, path):
  match hot:
    case False{}:
      {==}
    case True{}:
      match open:
        case False{}:
          {==}
        case True{}:
          hoist.slot(Hoist.slot_of(tt), Calls.args(kids), self, wides, carried, path)

# a let's table and use: one finding when both hold
law hoist.use:
  for a: Bool
  for b: Bool
  for -expr: Tree.Node
  for -path: String
  {List.length(&2, F.Finding, Hoist.let_use(a, b, expr, path)) == Bool.pick(Nat, Bool.and(a, b), 1n, 0n) : Nat}

def hoist.use(a, b, _expr, _path):
  match a:
    case False{}:
      {==}
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

# a let's left side read: one finding when the law's got test holds
law hoist.got:
  for mm: Maybe<&2, Hoist.Got>
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  {List.length(&2, F.Finding, Hoist.let_of(mm, body, rest, self, wides, carried, path))
    == Bool.pick(Nat, Laws.hoist.got(mm, body, rest, self, wides, carried), 1n, 0n) : Nat}

def hoist.got(mm, body, rest, self, wides, carried, path):
  match mm:
    case None{}:
      {==}
    case Some{Hoist.Got{+nm, +expr}}:
      hoist.use(Hoist.is_table(expr, self, wides, carried), Hoist.uses_or(body, rest, nm), expr, path)

# a statement: one finding when the law's let test holds
law hoist.let:
  for hot: Bool
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  {List.length(&2, F.Finding, Hoist.let_hit(hot, kids, body, rest, self, wides, carried, path))
    == Bool.pick(Nat, Laws.hoist.let(hot, kids, body, rest, self, wides, carried), 1n, 0n) : Nat}

def hoist.let(hot, kids, body, rest, self, wides, carried, path):
  match hot:
    case False{}:
      {==}
    case True{}:
      hoist.got(Hoist.eat(kids, False{}, False{}, ""), body, rest, self, wides, carried, path)

# a list joined before another counts as its own count plus the other's
law hoist.front:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for -x: Nat
  for -y: Nat
  for e1: {List.length(&2, F.Finding, a) == x : Nat}
  for e2: {List.length(&2, F.Finding, b) == y : Nat}
  {List.length(&2, F.Finding, List.append(&2, F.Finding, a, b)) == Nat.add(x, y) : Nat}

def hoist.front(a, b, x, y, e1, e2):
  Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, a, b)),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, b)), Nat.add(x, y),
    esc.app(a, b), esc.add(List.length(&2, F.Finding, a), x, List.length(&2, F.Finding, b), y, e1, e2))

# a name token, then a group: its own finding, then its group's and the
# rest's, all at the heat the token leaves
law hoist.site:
  for +k: Lex.TokKind
  for +t: String
  for +o: String
  for +kids: Tree.Node
  for +rr: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +hot: Bool
  for ih1: {List.length(&2, F.Finding, Hoist.walk(kids, self, wides, carried, path, Hoist.warm(hot, k)))
    == Laws.hoist.count(kids, self, wides, carried, Hoist.warm(hot, k)) : Nat}
  for ih2: {List.length(&2, F.Finding, Hoist.walk(rr, self, wides, carried, path, Hoist.warm(hot, k)))
    == Laws.hoist.count(rr, self, wides, carried, Hoist.warm(hot, k)) : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding,
      [Hoist.call_table(Hoist.warm(hot, k), String.eq(o, "("), t, kids, self, wides, carried, path),
        Hoist.walk(kids, self, wides, carried, path, Hoist.warm(hot, k)),
        Hoist.walk(rr, self, wides, carried, path, Hoist.warm(hot, k))]))
    == Nat.add(Bool.pick(Nat, Laws.hoist.call(Hoist.warm(hot, k), String.eq(o, "("), t, kids, self, wides, carried),
      1n, 0n), Nat.add(Laws.hoist.count(kids, self, wides, carried, Hoist.warm(hot, k)),
        Laws.hoist.count(rr, self, wides, carried, Hoist.warm(hot, k)))) : Nat}

def hoist.site(k, t, o, kids, rr, self, wides, carried, path, hot, ih1, ih2):
  +heat = Hoist.warm(hot, k)
  chars.sum(Hoist.call_table(heat, String.eq(o, "("), t, kids, self, wides, carried, path),
    Hoist.walk(kids, self, wides, carried, path, heat), Hoist.walk(rr, self, wides, carried, path, heat),
    Bool.pick(Nat, Laws.hoist.call(heat, String.eq(o, "("), t, kids, self, wides, carried), 1n, 0n),
    Laws.hoist.count(kids, self, wides, carried, heat), Laws.hoist.count(rr, self, wides, carried, heat),
    hoist.call(heat, String.eq(o, "("), t, kids, self, wides, carried, path), ih1, ih2)

# a case: its pattern cold, its arm hot when it calls the def, then the rest
law hoist.arm:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +hot: Bool
  for ih1: {List.length(&2, F.Finding, Hoist.walk(kids, self, wides, carried, path, False{}))
    == Laws.hoist.count(kids, self, wides, carried, False{}) : Nat}
  for ih2: {List.length(&2, F.Finding,
      Hoist.walk(body, self, wides, carried, path, Bool.and(hot, Calls.calls(body, self))))
    == Laws.hoist.count(body, self, wides, carried, Bool.and(hot, Calls.calls(body, self))) : Nat}
  for ih3: {List.length(&2, F.Finding, Hoist.walk(rest, self, wides, carried, path, hot))
    == Laws.hoist.count(rest, self, wides, carried, hot) : Nat}
  {List.length(&2, F.Finding, Hoist.walk(Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, body}, rest},
      self, wides, carried, path, hot))
    == Laws.hoist.count(Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, body}, rest}, self, wides, carried, hot) : Nat}

def hoist.arm(kids, body, rest, self, wides, carried, path, hot, ih1, ih2, ih3):
  +arm = Bool.and(hot, Calls.calls(body, self))
  chars.sum(Hoist.walk(kids, self, wides, carried, path, False{}), Hoist.walk(body, self, wides, carried, path, arm),
    Hoist.walk(rest, self, wides, carried, path, hot),
    Laws.hoist.count(kids, self, wides, carried, False{}), Laws.hoist.count(body, self, wides, carried, arm),
    Laws.hoist.count(rest, self, wides, carried, hot), ih1, ih2, ih3)

# any other statement: its own let finding, then its tokens', its block's
# and the rest's
law hoist.plain:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +hot: Bool
  for ih1: {List.length(&2, F.Finding, Hoist.walk(kids, self, wides, carried, path, hot))
    == Laws.hoist.count(kids, self, wides, carried, hot) : Nat}
  for ih2: {List.length(&2, F.Finding, Hoist.walk(body, self, wides, carried, path, hot))
    == Laws.hoist.count(body, self, wides, carried, hot) : Nat}
  for ih3: {List.length(&2, F.Finding, Hoist.walk(rest, self, wides, carried, path, hot))
    == Laws.hoist.count(rest, self, wides, carried, hot) : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding,
      [Hoist.let_hit(hot, kids, body, rest, self, wides, carried, path),
        Hoist.walk(kids, self, wides, carried, path, hot), Hoist.walk(body, self, wides, carried, path, hot),
        Hoist.walk(rest, self, wides, carried, path, hot)]))
    == Nat.add(Bool.pick(Nat, Laws.hoist.let(hot, kids, body, rest, self, wides, carried), 1n, 0n),
      Nat.add(Laws.hoist.count(kids, self, wides, carried, hot),
        Nat.add(Laws.hoist.count(body, self, wides, carried, hot), Laws.hoist.count(rest, self, wides, carried, hot))))
    : Nat}

def hoist.plain(kids, body, rest, self, wides, carried, path, hot, ih1, ih2, ih3):
  +own = Hoist.let_hit(hot, kids, body, rest, self, wides, carried, path)
  +wk = Hoist.walk(kids, self, wides, carried, path, hot)
  +wb = Hoist.walk(body, self, wides, carried, path, hot)
  +wr = Hoist.walk(rest, self, wides, carried, path, hot)
  +ck = Laws.hoist.count(kids, self, wides, carried, hot)
  +cb = Laws.hoist.count(body, self, wides, carried, hot)
  +cr = Laws.hoist.count(rest, self, wides, carried, hot)
  hoist.front(own, List.concat(&2, F.Finding, [wk, wb, wr]),
    Bool.pick(Nat, Laws.hoist.let(hot, kids, body, rest, self, wides, carried), 1n, 0n),
    Nat.add(ck, Nat.add(cb, cr)),
    hoist.let(hot, kids, body, rest, self, wides, carried, path),
    chars.sum(wk, wb, wr, ck, cb, cr, ih1, ih2, ih3))

# hoist's walk counts the calls and lets the law counts, at every heat
law hoist.walk:
  for nn: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +hot: Bool
  {List.length(&2, F.Finding, Hoist.walk(nn, self, wides, carried, path, hot))
    == Laws.hoist.count(nn, self, wides, carried, hot) : Nat}

def hoist.walk(nn, self, wides, carried, path, hot):
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
        case Tree.Leaf{Lex.Tok{+k, +t, l, c}}:
          match rest:
            case Tree.Leaf{tok}:
              {==}
            case Tree.Group{o, gk, cl}:
              {==}
            case Tree.Stmt{kind, sk, sb}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{rh, +rr}:
              match rh:
                case Tree.Group{Lex.Tok{gk, +o, gl, gc}, +kids, cl}:
                  hoist.site(k, t, o, kids, rr, self, wides, carried, path, hot,
                    hoist.walk(kids, self, wides, carried, path, Hoist.warm(hot, k)),
                    hoist.walk(rr, self, wides, carried, path, Hoist.warm(hot, k)))
                case Tree.Leaf{tok}:
                  hoist.walk(rest, self, wides, carried, path, Hoist.warm(hot, k))
                case Tree.Stmt{kind, sk, sb}:
                  hoist.walk(rest, self, wides, carried, path, Hoist.warm(hot, k))
                case Tree.NNil{}:
                  hoist.walk(rest, self, wides, carried, path, Hoist.warm(hot, k))
                case Tree.NCons{nh, nt}:
                  hoist.walk(rest, self, wides, carried, path, Hoist.warm(hot, k))
        case Tree.Group{o, +kids, cl}:
          index.two(Hoist.walk(kids, self, wides, carried, path, hot),
            Hoist.walk(rest, self, wides, carried, path, hot),
            Laws.hoist.count(kids, self, wides, carried, hot), Laws.hoist.count(rest, self, wides, carried, hot),
            hoist.walk(kids, self, wides, carried, path, hot), hoist.walk(rest, self, wides, carried, path, hot))
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SCase{}:
              hoist.arm(kids, body, rest, self, wides, carried, path, hot,
                hoist.walk(kids, self, wides, carried, path, False{}),
                hoist.walk(body, self, wides, carried, path, Bool.and(hot, Calls.calls(body, self))),
                hoist.walk(rest, self, wides, carried, path, hot))
            case Tree.SDef{}:
              hoist.plain(kids, body, rest, self, wides, carried, path, hot,
                hoist.walk(kids, self, wides, carried, path, hot),
                hoist.walk(body, self, wides, carried, path, hot), hoist.walk(rest, self, wides, carried, path, hot))
            case Tree.SType{}:
              hoist.plain(kids, body, rest, self, wides, carried, path, hot,
                hoist.walk(kids, self, wides, carried, path, hot),
                hoist.walk(body, self, wides, carried, path, hot), hoist.walk(rest, self, wides, carried, path, hot))
            case Tree.SLaw{}:
              hoist.plain(kids, body, rest, self, wides, carried, path, hot,
                hoist.walk(kids, self, wides, carried, path, hot),
                hoist.walk(body, self, wides, carried, path, hot), hoist.walk(rest, self, wides, carried, path, hot))
            case Tree.SImport{}:
              hoist.plain(kids, body, rest, self, wides, carried, path, hot,
                hoist.walk(kids, self, wides, carried, path, hot),
                hoist.walk(body, self, wides, carried, path, hot), hoist.walk(rest, self, wides, carried, path, hot))
            case Tree.SFor{}:
              hoist.plain(kids, body, rest, self, wides, carried, path, hot,
                hoist.walk(kids, self, wides, carried, path, hot),
                hoist.walk(body, self, wides, carried, path, hot), hoist.walk(rest, self, wides, carried, path, hot))
            case Tree.SLet{}:
              hoist.plain(kids, body, rest, self, wides, carried, path, hot,
                hoist.walk(kids, self, wides, carried, path, hot),
                hoist.walk(body, self, wides, carried, path, hot), hoist.walk(rest, self, wides, carried, path, hot))
            case Tree.STerm{}:
              hoist.plain(kids, body, rest, self, wides, carried, path, hot,
                hoist.walk(kids, self, wides, carried, path, hot),
                hoist.walk(body, self, wides, carried, path, hot), hoist.walk(rest, self, wides, carried, path, hot))
        case Tree.NNil{}:
          hoist.walk(rest, self, wides, carried, path, hot)
        case Tree.NCons{nh, nt}:
          hoist.walk(rest, self, wides, carried, path, hot)

# a def that calls itself and is not exempt gathers its walk, entered hot,
# any other nothing
law hoist.def:
  for g: Bool
  for +body: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  {List.length(&2, F.Finding,
      Lazy.stop(List<&2, F.Finding>, Bool.not(g), [], _u => Hoist.walk(body, self, wides, carried, path, True{})))
    == Bool.pick(Nat, g, Laws.hoist.count(body, self, wides, carried, True{}), 0n) : Nat}

def hoist.def(g, body, self, wides, carried, path):
  match g:
    case True{}:
      hoist.walk(body, self, wides, carried, path, True{})
    case False{}:
      {==}

# over the defs, the rule's join counts what it gathered and what the law
# counts
law hoist.go:
  for ds: List<&2, Calls.Def>
  for +wides: List<&2, String>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Hoist.check.go(ds, wides, path, acc))
    == Nat.add(index.sum(acc), Laws.hoist.total(ds, wides, path)) : Nat}

def hoist.go(ds, wides, path, acc):
  match ds:
    case Nil{}:
      index.flat(acc, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +g = Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))
      +carried = Hoist.carried(sig, body, name)
      +x = Lazy.stop(List<&2, F.Finding>, Bool.not(g), [], _u => Hoist.walk(body, name, wides, carried, path, True{}))
      +n = Bool.pick(Nat, g, Laws.hoist.count(body, name, wides, carried, True{}), 0n)
      +tot = Laws.hoist.total(rest, wides, path)
      Equal.trans(Nat,
        List.length(&2, F.Finding, Hoist.check.go(rest, wides, path, x <> acc)),
        Nat.add(Nat.add(index.sum(acc), List.length(&2, F.Finding, x)), tot),
        Nat.add(index.sum(acc), Nat.add(n, tot)),
        hoist.go(rest, wides, path, x <> acc),
        Equal.trans(Nat,
          Nat.add(Nat.add(index.sum(acc), List.length(&2, F.Finding, x)), tot),
          Nat.add(index.sum(acc), Nat.add(List.length(&2, F.Finding, x), tot)),
          Nat.add(index.sum(acc), Nat.add(n, tot)),
          index.assoc(index.sum(acc), List.length(&2, F.Finding, x), tot),
          Equal.cong(Nat, Nat, z => Nat.add(index.sum(acc), Nat.add(z, tot)), List.length(&2, F.Finding, x), n,
            hoist.def(g, body, name, wides, carried, path))))

def Laws.hoist_counts(path, _text, _toks, tree, _bound, _items):
  +ds = Calls.defs(tree)
  hoist.go(ds, Hoist.wide_defs(ds, Nil{}), path, Nil{})

# the rule's names are the law's
law rewalk.names_eq:
  for nn: Tree.Node
  for +acc: List<&2, String>
  {Rewalk.names(nn, acc) == Laws.rewalk.names(nn, acc) : List<&2, String>}

def rewalk.names_eq(nn, acc):
  match nn:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}:
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
    case Tree.Group{open, kids, close}:
      rewalk.names_eq(kids, acc)
    case Tree.Stmt{kind, +kids, body}:
      %rewalk.names_eq(kids, acc) : {Rewalk.names(body, Rewalk.names(kids, acc)) == Laws.rewalk.names(body, _)
        : List<&2, String>}
      rewalk.names_eq(body, Rewalk.names(kids, acc))
    case Tree.NCons{+h, rest}:
      %rewalk.names_eq(h, acc) : {Rewalk.names(rest, Rewalk.names(h, acc)) == Laws.rewalk.names(rest, _)
        : List<&2, String>}
      rewalk.names_eq(rest, Rewalk.names(h, acc))
    case Tree.NNil{}:
      {==}

# the rule's let names are the law's
law rewalk.lhs_eq:
  for nn: Tree.Node
  for +acc: List<&2, String>
  {Rewalk.lhs_names(nn, acc) == Laws.rewalk.lhs(nn, acc) : List<&2, String>}

def rewalk.lhs_eq(nn, acc):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}:
                  rewalk.lhs_eq(rest, t <> acc)
                case Lex.TUpper{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TDotted{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TWild{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TKey{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TNum{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TStr{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TChar{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TComment{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TSpace{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TNewline{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TOp{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TColon{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TEq{}:
                  {==}
                case Lex.TBind{}:
                  {==}
                case Lex.TArrow{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TLam{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TAll{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TAmp{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TOpen{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TClose{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TComma{}:
                  rewalk.lhs_eq(rest, acc)
        case Tree.Group{open, +kids, close}:
          %rewalk.names_eq(kids, acc) : {Rewalk.lhs_names(rest, Rewalk.names(kids, acc))
            == Laws.rewalk.lhs(rest, _) : List<&2, String>}
          rewalk.lhs_eq(rest, Rewalk.names(kids, acc))
        case Tree.Stmt{kind, kids, body}:
          rewalk.lhs_eq(rest, acc)
        case Tree.NNil{}:
          rewalk.lhs_eq(rest, acc)
        case Tree.NCons{x, y}:
          rewalk.lhs_eq(rest, acc)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# the rule's lets of a piece are the law's
law rewalk.binds_eq:
  for nn: Tree.Node
  for +acc: List<&2, Rewalk.Bind>
  {Rewalk.binds(nn, acc) == Laws.rewalk.binds(nn, acc) : List<&2, Rewalk.Bind>}

def rewalk.binds_eq(nn, acc):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SDef{}:
              %rewalk.binds_eq(body, acc) : {Rewalk.binds(rest, Rewalk.binds(body, acc)) == Laws.rewalk.binds(rest,
                _) : List<&2, Rewalk.Bind>}
              rewalk.binds_eq(rest, Rewalk.binds(body, acc))
            case Tree.SType{}:
              %rewalk.binds_eq(body, acc) : {Rewalk.binds(rest, Rewalk.binds(body, acc)) == Laws.rewalk.binds(rest,
                _) : List<&2, Rewalk.Bind>}
              rewalk.binds_eq(rest, Rewalk.binds(body, acc))
            case Tree.SLaw{}:
              %rewalk.binds_eq(body, acc) : {Rewalk.binds(rest, Rewalk.binds(body, acc)) == Laws.rewalk.binds(rest,
                _) : List<&2, Rewalk.Bind>}
              rewalk.binds_eq(rest, Rewalk.binds(body, acc))
            case Tree.SImport{}:
              %rewalk.binds_eq(body, acc) : {Rewalk.binds(rest, Rewalk.binds(body, acc)) == Laws.rewalk.binds(rest,
                _) : List<&2, Rewalk.Bind>}
              rewalk.binds_eq(rest, Rewalk.binds(body, acc))
            case Tree.SCase{}:
              rewalk.binds_eq(rest, acc)
            case Tree.SFor{}:
              %rewalk.binds_eq(body, acc) : {Rewalk.binds(rest, Rewalk.binds(body, acc)) == Laws.rewalk.binds(rest,
                _) : List<&2, Rewalk.Bind>}
              rewalk.binds_eq(rest, Rewalk.binds(body, acc))
            case Tree.SLet{}:
              +pp = Rewalk.last_pos(Tree.leaves.go(body, Tree.leaves.go(kids, [])))
              %rewalk.lhs_eq(kids, []) : {Rewalk.binds(rest, Rewalk.binds(body, Rewalk.bind_at(Rewalk.lhs_names(kids,
                []), pp, acc))) == Laws.rewalk.binds(rest, Laws.rewalk.binds(body, Rewalk.bind_at(_, pp,
                  acc))) : List<&2, Rewalk.Bind>}
              +x = Rewalk.bind_at(Rewalk.lhs_names(kids, []), pp, acc)
              %rewalk.binds_eq(body, x) : {Rewalk.binds(rest, Rewalk.binds(body, x)) == Laws.rewalk.binds(rest,
                _) : List<&2, Rewalk.Bind>}
              rewalk.binds_eq(rest, Rewalk.binds(body, x))
            case Tree.STerm{}:
              %rewalk.binds_eq(body, acc) : {Rewalk.binds(rest, Rewalk.binds(body, acc)) == Laws.rewalk.binds(rest,
                _) : List<&2, Rewalk.Bind>}
              rewalk.binds_eq(rest, Rewalk.binds(body, acc))
        case Tree.Leaf{tok}:
          rewalk.binds_eq(rest, acc)
        case Tree.Group{open, kids, close}:
          rewalk.binds_eq(rest, acc)
        case Tree.NNil{}:
          rewalk.binds_eq(rest, acc)
        case Tree.NCons{x, y}:
          rewalk.binds_eq(rest, acc)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# the rule's let count is the law's
law rewalk.lets_eq:
  for bs: List<&2, Rewalk.Bind>
  for +name: String
  for +line: U32
  for +col: U32
  {Rewalk.count(bs, name, line, col) == Laws.rewalk.lets(bs, name, line, col) : U32}

def rewalk.lets_eq(bs, name, line, col):
  match bs:
    case Nil{}:
      {==}
    case Con{b, rest}:
      match b:
        case Rewalk.Bind{+nm, +l, +c}:
          Equal.cong(U32, U32, m => Bool.pick(U32, Bool.and(String.eq(nm, name), Rewalk.before(l, c, line, col)),
            (m + 1 : U32), m), Rewalk.count(rest, name, line, col), Laws.rewalk.lets(rest, name, line, col),
            rewalk.lets_eq(rest, name, line, col))

# the rule's stamp is the law's
law rewalk.stamp_eq:
  for ns: List<&2, String>
  for +bs: List<&2, Rewalk.Bind>
  for +line: U32
  for +col: U32
  {Rewalk.stamp(ns, bs, line, col) == Laws.rewalk.stamp(ns, bs, line, col) : String}

def rewalk.stamp_eq(ns, bs, line, col):
  match ns:
    case Nil{}:
      {==}
    case Con{+nm, rest}:
      %rewalk.lets_eq(bs, nm, line, col) : {Rewalk.stamp(nm <> rest, bs, line, col)
        == "|" ++ nm ++ "=" ++ U32.show(_) ++ Laws.rewalk.stamp(rest, bs, line, col) : String}
      %rewalk.stamp_eq(rest, bs, line, col) : {Rewalk.stamp(nm <> rest, bs, line, col)
        == "|" ++ nm ++ "=" ++ U32.show(Rewalk.count(bs, nm, line, col)) ++ _ : String}
      {==}

# two lists joined, each equal to its counterpart
law rewalk.cat2:
  for -A: Data
  for -a1: List<&2, A>
  for -a2: List<&2, A>
  for -b1: List<&2, A>
  for -b2: List<&2, A>
  for ea: {a1 == a2 : List<&2, A>}
  for eb: {b1 == b2 : List<&2, A>}
  {List.concat(&2, A, [a1, b1]) == List.concat(&2, A, [a2, b2]) : List<&2, A>}

def rewalk.cat2(A, a1, _a2, b1, b2, ea, eb):
  %ea : {List.concat(&2, A, [a1, b1]) == List.concat(&2, A, [_, b2]) : List<&2, A>}
  %eb : {List.concat(&2, A, [a1, b1]) == List.concat(&2, A, [a1, _]) : List<&2, A>}
  {==}

# three lists joined, each equal to its counterpart
law rewalk.cat3:
  for -A: Data
  for -a1: List<&2, A>
  for -a2: List<&2, A>
  for -b1: List<&2, A>
  for -b2: List<&2, A>
  for -c1: List<&2, A>
  for -c2: List<&2, A>
  for ea: {a1 == a2 : List<&2, A>}
  for eb: {b1 == b2 : List<&2, A>}
  for ec: {c1 == c2 : List<&2, A>}
  {List.concat(&2, A, [a1, b1, c1]) == List.concat(&2, A, [a2, b2, c2]) : List<&2, A>}

def rewalk.cat3(A, a1, _a2, b1, b2, c1, c2, ea, eb, ec):
  %ea : {List.concat(&2, A, [a1, b1, c1]) == List.concat(&2, A, [_, b2, c2]) : List<&2, A>}
  %eb : {List.concat(&2, A, [a1, b1, c1]) == List.concat(&2, A, [a1, _, c2]) : List<&2, A>}
  %ec : {List.concat(&2, A, [a1, b1, c1]) == List.concat(&2, A, [a1, b1, _]) : List<&2, A>}
  {==}

# a call's argument key, to the rule and to the law
law rewalk.args_eq:
  for +kids: Tree.Node
  for +bs: List<&2, Rewalk.Bind>
  for +l: U32
  for +c: U32
  {Tree.show(kids) ++ Rewalk.stamp(Rewalk.names(kids, []), bs, l, c)
    == Tree.show(kids) ++ Laws.rewalk.stamp(Laws.rewalk.names(kids, []), bs, l, c) : String}

def rewalk.args_eq(kids, bs, l, c):
  %rewalk.names_eq(kids, []) : {Tree.show(kids) ++ Rewalk.stamp(Rewalk.names(kids, []), bs, l, c)
    == Tree.show(kids) ++ Laws.rewalk.stamp(_, bs, l, c) : String}
  %rewalk.stamp_eq(Rewalk.names(kids, []), bs, l, c) : {Tree.show(kids) ++ Rewalk.stamp(Rewalk.names(kids, []), bs, l,
    c) == Tree.show(kids) ++ _ : String}
  {==}

# the rule's sites are the law's
law rewalk.gather_eq:
  for nn: Tree.Node
  for +self: String
  for +lp: List<&2, String>
  for +bs: List<&2, Rewalk.Bind>
  {Rewalk.gather(nn, self, lp, bs) == Laws.rewalk.gather(nn, self, lp, bs) : List<&2, Rewalk.Site>}

# a call's own site, to the rule and to the law
law rewalk.here_eq:
  for +o: String
  for +r2: Tree.Node
  for +t: String
  for +kids: Tree.Node
  for +bs: List<&2, Rewalk.Bind>
  for +l: U32
  for +c: U32
  for +self: String
  for +lp: List<&2, String>
  {Rewalk.open_site(String.eq(o, "("), Rewalk.indexed(r2), t, Tree.show(kids) ++ Rewalk.stamp(Rewalk.names(kids, []),
    bs, l, c), l, c, U32.from_nat(String.length(t)), self, lp)
    == Rewalk.open_site(String.eq(o, "("), Rewalk.indexed(r2), t, Tree.show(kids)
      ++ Laws.rewalk.stamp(Laws.rewalk.names(kids, []), bs, l, c), l, c, U32.from_nat(String.length(t)), self, lp)
    : List<&2, Rewalk.Site>}

def rewalk.here_eq(o, r2, t, kids, bs, l, c, self, lp):
  Equal.cong(String, List<&2, Rewalk.Site>, a => Rewalk.open_site(String.eq(o, "("), Rewalk.indexed(r2), t, a, l, c,
    U32.from_nat(String.length(t)), self, lp), Tree.show(kids) ++ Rewalk.stamp(Rewalk.names(kids, []), bs, l, c),
    Tree.show(kids) ++ Laws.rewalk.stamp(Laws.rewalk.names(kids, []), bs, l, c), rewalk.args_eq(kids, bs, l, c))

# a statement's sites: its own tokens, its body, then what follows
law rewalk.gather_stmt:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +lp: List<&2, String>
  for +bs: List<&2, Rewalk.Bind>
  for ek: {Rewalk.gather(kids, self, lp, bs) == Laws.rewalk.gather(kids, self, lp, bs) : List<&2, Rewalk.Site>}
  for eb: {Rewalk.gather(body, self, lp, bs) == Laws.rewalk.gather(body, self, lp, bs) : List<&2, Rewalk.Site>}
  for er: {Rewalk.gather(rest, self, lp, bs) == Laws.rewalk.gather(rest, self, lp, bs) : List<&2, Rewalk.Site>}
  {List.concat(&2, Rewalk.Site, [Rewalk.gather(kids, self, lp, bs), Rewalk.gather(body, self, lp, bs),
    Rewalk.gather(rest, self, lp, bs)]) == List.concat(&2, Rewalk.Site, [Laws.rewalk.gather(kids, self, lp, bs),
    Laws.rewalk.gather(body, self, lp, bs), Laws.rewalk.gather(rest, self, lp, bs)]) : List<&2, Rewalk.Site>}

def rewalk.gather_stmt(kids, body, rest, self, lp, bs, ek, eb, er):
  rewalk.cat3(Rewalk.Site, Rewalk.gather(kids, self, lp, bs), Laws.rewalk.gather(kids, self, lp, bs),
    Rewalk.gather(body, self, lp, bs), Laws.rewalk.gather(body, self, lp, bs), Rewalk.gather(rest, self, lp, bs),
    Laws.rewalk.gather(rest, self, lp, bs), ek, eb, er)

def rewalk.gather_eq(nn, self, lp, bs):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{open, +kids, close}:
                      match open:
                        case Lex.Tok{ok, +o, ol, oc}:
                          rewalk.cat3(Rewalk.Site,
                            Rewalk.open_site(String.eq(o, "("), Rewalk.indexed(r2), t, Tree.show(kids)
                              ++ Rewalk.stamp(Rewalk.names(kids, []), bs, l, c), l, c, U32.from_nat(String.length(t)),
                              self, lp),
                            Rewalk.open_site(String.eq(o, "("), Rewalk.indexed(r2), t, Tree.show(kids)
                              ++ Laws.rewalk.stamp(Laws.rewalk.names(kids, []), bs, l, c), l, c,
                              U32.from_nat(String.length(t)), self, lp),
                            Rewalk.gather(kids, self, lp, bs), Laws.rewalk.gather(kids, self, lp, bs),
                            Rewalk.gather(r2, self, lp, bs), Laws.rewalk.gather(r2, self, lp, bs),
                            rewalk.here_eq(o, r2, t, kids, bs, l, c, self, lp),
                            rewalk.gather_eq(kids, self, lp, bs), rewalk.gather_eq(r2, self, lp, bs))
                    case Tree.Leaf{x}:
                      rewalk.gather_eq(rest, self, lp, bs)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.gather_eq(rest, self, lp, bs)
                    case Tree.NNil{}:
                      rewalk.gather_eq(rest, self, lp, bs)
                    case Tree.NCons{x, y}:
                      rewalk.gather_eq(rest, self, lp, bs)
                case Tree.Leaf{x}:
                  rewalk.gather_eq(rest, self, lp, bs)
                case Tree.Group{open, kids, close}:
                  rewalk.gather_eq(rest, self, lp, bs)
                case Tree.Stmt{kind, kids, body}:
                  rewalk.gather_eq(rest, self, lp, bs)
                case Tree.NNil{}:
                  rewalk.gather_eq(rest, self, lp, bs)
        case Tree.Group{open, +kids, close}:
          rewalk.cat2(Rewalk.Site, Rewalk.gather(kids, self, lp, bs), Laws.rewalk.gather(kids, self, lp, bs),
            Rewalk.gather(rest, self, lp, bs), Laws.rewalk.gather(rest, self, lp, bs),
            rewalk.gather_eq(kids, self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SDef{}:
              rewalk.gather_stmt(kids, body, rest, self, lp, bs, rewalk.gather_eq(kids, self, lp, bs),
                rewalk.gather_eq(body, self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
            case Tree.SType{}:
              rewalk.gather_stmt(kids, body, rest, self, lp, bs, rewalk.gather_eq(kids, self, lp, bs),
                rewalk.gather_eq(body, self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
            case Tree.SLaw{}:
              rewalk.gather_stmt(kids, body, rest, self, lp, bs, rewalk.gather_eq(kids, self, lp, bs),
                rewalk.gather_eq(body, self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
            case Tree.SImport{}:
              rewalk.gather_stmt(kids, body, rest, self, lp, bs, rewalk.gather_eq(kids, self, lp, bs),
                rewalk.gather_eq(body, self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
            case Tree.SCase{}:
              rewalk.cat2(Rewalk.Site, Rewalk.gather(kids, self, lp, bs), Laws.rewalk.gather(kids, self, lp, bs),
                Rewalk.gather(rest, self, lp, bs), Laws.rewalk.gather(rest, self, lp, bs), rewalk.gather_eq(kids,
                  self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
            case Tree.SFor{}:
              rewalk.gather_stmt(kids, body, rest, self, lp, bs, rewalk.gather_eq(kids, self, lp, bs),
                rewalk.gather_eq(body, self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
            case Tree.SLet{}:
              rewalk.gather_stmt(kids, body, rest, self, lp, bs, rewalk.gather_eq(kids, self, lp, bs),
                rewalk.gather_eq(body, self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
            case Tree.STerm{}:
              rewalk.gather_stmt(kids, body, rest, self, lp, bs, rewalk.gather_eq(kids, self, lp, bs),
                rewalk.gather_eq(body, self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
        case Tree.NNil{}:
          rewalk.gather_eq(rest, self, lp, bs)
        case Tree.NCons{x, y}:
          rewalk.gather_eq(rest, self, lp, bs)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# two steps, each the rule's and the law's alike, from equal starts
law rewalk.then:
  for -A: Type
  for -f1: A -> A
  for -g1: A -> A
  for -f2: A -> A
  for -g2: A -> A
  for -x: A
  for -y: A
  for e0: {x == y : A}
  for e1: {f1(x) == g1(x) : A}
  for e2: {f2(f1(x)) == g2(f1(x)) : A}
  {f2(f1(x)) == g2(g1(y)) : A}

def rewalk.then(A, f1, g1, f2, g2, x, _y, e0, e1, e2):
  %e0 : {f2(f1(x)) == g2(g1(_)) : A}
  %e1 : {f2(f1(x)) == g2(_) : A}
  e2

# the rule's retag is the law's
law rewalk.retag_eq:
  for sites: List<&2, Rewalk.Site>
  for +note: Rewalk.Note
  {Rewalk.retag(sites, note) == Laws.rewalk.retag(sites, note) : List<&2, Rewalk.Site>}

def rewalk.retag_eq(sites, note):
  match sites:
    case Nil{}:
      {==}
    case Con{s, rest}:
      match s:
        case Rewalk.Site{+name, +args, +line, +col, +len, how}:
          +hd = Rewalk.retag_one(Bool.and(U32.is_eq(line, Rewalk.note_line(note)), U32.is_eq(col,
            Rewalk.note_col(note))), how, Rewalk.note_how_of(note), name, args, line, col, len)
          Equal.cong(List<&2, Rewalk.Site>, List<&2, Rewalk.Site>, tl => hd <> tl, Rewalk.retag(rest, note),
            Laws.rewalk.retag(rest, note), rewalk.retag_eq(rest, note))

# a let's note retags alike
law rewalk.relet_eq:
  for mm: Maybe<&2, Rewalk.Note>
  for sites: List<&2, Rewalk.Site>
  {Rewalk.retag_may(mm, sites) == Laws.rewalk.relet(mm, sites) : List<&2, Rewalk.Site>}

def rewalk.relet_eq(mm, sites):
  match mm:
    case None{}:
      {==}
    case Some{note}:
      rewalk.retag_eq(sites, note)

# the rule's apply is the law's
law rewalk.apply_eq:
  for nn: Tree.Node
  for +sites: List<&2, Rewalk.Site>
  {Rewalk.apply(nn, sites) == Laws.rewalk.apply(nn, sites) : List<&2, Rewalk.Site>}

# a statement retags its own call, then its body's, then what follows
law rewalk.apply_stmt:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +sites: List<&2, Rewalk.Site>
  for eb: {Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites))
    == Laws.rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites)) : List<&2, Rewalk.Site>}
  for er: {Rewalk.apply(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites)))
    == Laws.rewalk.apply(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites)))
    : List<&2, Rewalk.Site>}
  {Rewalk.apply(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites)))
    == Laws.rewalk.apply(rest, Laws.rewalk.apply(body, Laws.rewalk.relet(Rewalk.note_st(kids), sites)))
    : List<&2, Rewalk.Site>}

def rewalk.apply_stmt(kids, body, rest, sites, eb, er):
  rewalk.then(List<&2, Rewalk.Site>, ss => Rewalk.apply(body, ss), ss => Laws.rewalk.apply(body, ss),
    ss => Rewalk.apply(rest, ss), ss => Laws.rewalk.apply(rest, ss), Rewalk.retag_may(Rewalk.note_st(kids), sites),
    Laws.rewalk.relet(Rewalk.note_st(kids), sites), rewalk.relet_eq(Rewalk.note_st(kids), sites), eb, er)

def rewalk.apply_eq(nn, sites):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SDef{}:
              rewalk.apply_stmt(kids, body, rest, sites, rewalk.apply_eq(body, Rewalk.retag_may(Rewalk.note_st(kids),
                sites)), rewalk.apply_eq(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites))))
            case Tree.SType{}:
              rewalk.apply_stmt(kids, body, rest, sites, rewalk.apply_eq(body, Rewalk.retag_may(Rewalk.note_st(kids),
                sites)), rewalk.apply_eq(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites))))
            case Tree.SLaw{}:
              rewalk.apply_stmt(kids, body, rest, sites, rewalk.apply_eq(body, Rewalk.retag_may(Rewalk.note_st(kids),
                sites)), rewalk.apply_eq(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites))))
            case Tree.SImport{}:
              rewalk.apply_stmt(kids, body, rest, sites, rewalk.apply_eq(body, Rewalk.retag_may(Rewalk.note_st(kids),
                sites)), rewalk.apply_eq(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites))))
            case Tree.SCase{}:
              rewalk.apply_eq(rest, sites)
            case Tree.SFor{}:
              rewalk.apply_stmt(kids, body, rest, sites, rewalk.apply_eq(body, Rewalk.retag_may(Rewalk.note_st(kids),
                sites)), rewalk.apply_eq(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites))))
            case Tree.SLet{}:
              rewalk.apply_stmt(kids, body, rest, sites, rewalk.apply_eq(body, Rewalk.retag_may(Rewalk.note_st(kids),
                sites)), rewalk.apply_eq(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites))))
            case Tree.STerm{}:
              rewalk.apply_stmt(kids, body, rest, sites, rewalk.apply_eq(body, Rewalk.retag_may(Rewalk.note_st(kids),
                sites)), rewalk.apply_eq(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites))))
        case Tree.Group{open, +kids, close}:
          rewalk.then(List<&2, Rewalk.Site>, ss => Rewalk.apply(kids, ss), ss => Laws.rewalk.apply(kids, ss),
            ss => Rewalk.apply(rest, ss), ss => Laws.rewalk.apply(rest, ss), sites, sites, {==},
            rewalk.apply_eq(kids, sites), rewalk.apply_eq(rest, Rewalk.apply(kids, sites)))
        case Tree.Leaf{tok}:
          rewalk.apply_eq(rest, sites)
        case Tree.NNil{}:
          rewalk.apply_eq(rest, sites)
        case Tree.NCons{x, y}:
          rewalk.apply_eq(rest, sites)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# an accessor's mark, taken lazily by the rule and outright by the law
law rewalk.mark_here:
  for b: Bool
  for +t: String
  for +kids: Tree.Node
  {Lazy.stop(List<&2, Rewalk.Pos>, Bool.not(b), [], _u => Rewalk.mark_slot(Rewalk.slot_of(t), Calls.args(kids)))
    == Bool.pick(List<&2, Rewalk.Pos>, b, Rewalk.mark_slot(Rewalk.slot_of(t), Calls.args(kids)), [])
    : List<&2, Rewalk.Pos>}

def rewalk.mark_here(b, _t, _kids):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the rule's marks are the law's
law rewalk.marks_eq:
  for nn: Tree.Node
  {Rewalk.mark(nn) == Laws.rewalk.marks(nn) : List<&2, Rewalk.Pos>}

# a statement's marks: its own tokens, its body, then what follows
law rewalk.marks_stmt:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for ek: {Rewalk.mark(kids) == Laws.rewalk.marks(kids) : List<&2, Rewalk.Pos>}
  for eb: {Rewalk.mark(body) == Laws.rewalk.marks(body) : List<&2, Rewalk.Pos>}
  for er: {Rewalk.mark(rest) == Laws.rewalk.marks(rest) : List<&2, Rewalk.Pos>}
  {List.concat(&2, Rewalk.Pos, [Rewalk.mark(kids), Rewalk.mark(body), Rewalk.mark(rest)])
    == List.concat(&2, Rewalk.Pos, [Laws.rewalk.marks(kids), Laws.rewalk.marks(body), Laws.rewalk.marks(rest)])
    : List<&2, Rewalk.Pos>}

def rewalk.marks_stmt(kids, body, rest, ek, eb, er):
  rewalk.cat3(Rewalk.Pos, Rewalk.mark(kids), Laws.rewalk.marks(kids), Rewalk.mark(body), Laws.rewalk.marks(body),
    Rewalk.mark(rest), Laws.rewalk.marks(rest), ek, eb, er)

# two chains' marks, joined
law rewalk.marks_two:
  for +kids: Tree.Node
  for +rest: Tree.Node
  for ek: {Rewalk.mark(kids) == Laws.rewalk.marks(kids) : List<&2, Rewalk.Pos>}
  for er: {Rewalk.mark(rest) == Laws.rewalk.marks(rest) : List<&2, Rewalk.Pos>}
  {List.concat(&2, Rewalk.Pos, [Rewalk.mark(kids), Rewalk.mark(rest)])
    == List.concat(&2, Rewalk.Pos, [Laws.rewalk.marks(kids), Laws.rewalk.marks(rest)]) : List<&2, Rewalk.Pos>}

def rewalk.marks_two(kids, rest, ek, er):
  rewalk.cat2(Rewalk.Pos, Rewalk.mark(kids), Laws.rewalk.marks(kids), Rewalk.mark(rest), Laws.rewalk.marks(rest), ek,
    er)

def rewalk.marks_eq(nn):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, l, c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{open, +kids, close}:
                      match open:
                        case Lex.Tok{ok, +o, ol, oc}:
                          rewalk.cat3(Rewalk.Pos,
                            Lazy.stop(List<&2, Rewalk.Pos>, Bool.not(String.eq(o, "(")), [],
                              _u => Rewalk.mark_slot(Rewalk.slot_of(t), Calls.args(kids))),
                            Bool.pick(List<&2, Rewalk.Pos>, String.eq(o, "("),
                              Rewalk.mark_slot(Rewalk.slot_of(t), Calls.args(kids)), []),
                            Rewalk.mark(kids), Laws.rewalk.marks(kids), Rewalk.mark(r2), Laws.rewalk.marks(r2),
                            rewalk.mark_here(String.eq(o, "("), t, kids), rewalk.marks_eq(kids), rewalk.marks_eq(r2))
                    case Tree.Leaf{x}:
                      rewalk.marks_eq(rest)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.marks_eq(rest)
                    case Tree.NNil{}:
                      rewalk.marks_eq(rest)
                    case Tree.NCons{x, y}:
                      rewalk.marks_eq(rest)
                case Tree.Leaf{x}:
                  rewalk.marks_eq(rest)
                case Tree.Group{open, kids, close}:
                  rewalk.marks_eq(rest)
                case Tree.Stmt{kind, kids, body}:
                  rewalk.marks_eq(rest)
                case Tree.NNil{}:
                  rewalk.marks_eq(rest)
        case Tree.Group{open, +kids, close}:
          rewalk.marks_two(kids, rest, rewalk.marks_eq(kids), rewalk.marks_eq(rest))
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SDef{}:
              rewalk.marks_stmt(kids, body, rest, rewalk.marks_eq(kids), rewalk.marks_eq(body), rewalk.marks_eq(rest))
            case Tree.SType{}:
              rewalk.marks_stmt(kids, body, rest, rewalk.marks_eq(kids), rewalk.marks_eq(body), rewalk.marks_eq(rest))
            case Tree.SLaw{}:
              rewalk.marks_stmt(kids, body, rest, rewalk.marks_eq(kids), rewalk.marks_eq(body), rewalk.marks_eq(rest))
            case Tree.SImport{}:
              rewalk.marks_stmt(kids, body, rest, rewalk.marks_eq(kids), rewalk.marks_eq(body), rewalk.marks_eq(rest))
            case Tree.SCase{}:
              rewalk.marks_two(kids, rest, rewalk.marks_eq(kids), rewalk.marks_eq(rest))
            case Tree.SFor{}:
              rewalk.marks_stmt(kids, body, rest, rewalk.marks_eq(kids), rewalk.marks_eq(body), rewalk.marks_eq(rest))
            case Tree.SLet{}:
              rewalk.marks_stmt(kids, body, rest, rewalk.marks_eq(kids), rewalk.marks_eq(body), rewalk.marks_eq(rest))
            case Tree.STerm{}:
              rewalk.marks_stmt(kids, body, rest, rewalk.marks_eq(kids), rewalk.marks_eq(body), rewalk.marks_eq(rest))
        case Tree.NNil{}:
          rewalk.marks_eq(rest)
        case Tree.NCons{x, y}:
          rewalk.marks_eq(rest)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# the rule's pinned is the law's
law rewalk.pinned_eq:
  for +line: U32
  for +col: U32
  for ps: List<&2, Rewalk.Pos>
  {Rewalk.pinned(line, col, ps) == Laws.rewalk.pinned(line, col, ps) : Bool}

def rewalk.pinned_eq(line, col, ps):
  match ps:
    case Nil{}:
      {==}
    case Con{p, rest}:
      match p:
        case Rewalk.Pos{+l, +c}:
          Equal.cong(Bool, Bool, m => Bool.or(Bool.and(U32.is_eq(l, line), U32.is_eq(c, col)), m),
            Rewalk.pinned(line, col, rest), Laws.rewalk.pinned(line, col, rest), rewalk.pinned_eq(line, col, rest))

# the rule's pin is the law's
law rewalk.pin_eq:
  for +ps: List<&2, Rewalk.Pos>
  for sites: List<&2, Rewalk.Site>
  {Rewalk.pin(ps, sites) == Laws.rewalk.pin(ps, sites) : List<&2, Rewalk.Site>}

def rewalk.pin_eq(ps, sites):
  match sites:
    case Nil{}:
      {==}
    case Con{s, rest}:
      match s:
        case Rewalk.Site{+name, +args, +line, +col, +len, +how}:
          %rewalk.pinned_eq(line, col, ps) : {Rewalk.pin(ps, Rewalk.Site{name, args, line, col, len, how} <> rest)
            == Rewalk.pin_how(_, how, name, args, line, col, len) <> Laws.rewalk.pin(ps, rest)
            : List<&2, Rewalk.Site>}
          %rewalk.pin_eq(ps, rest) : {Rewalk.pin(ps, Rewalk.Site{name, args, line, col, len, how} <> rest)
            == Rewalk.pin_how(Rewalk.pinned(line, col, ps), how, name, args, line, col, len) <> _
            : List<&2, Rewalk.Site>}
          {==}

# two joined reads, each the rule's and the law's alike
law rewalk.either2:
  for -a1: Rewalk.Hit
  for -a2: Rewalk.Hit
  for -b1: Rewalk.Hit
  for -b2: Rewalk.Hit
  for ea: {a1 == a2 : Rewalk.Hit}
  for eb: {b1 == b2 : Rewalk.Hit}
  {Rewalk.either(a1, b1) == Rewalk.either(a2, b2) : Rewalk.Hit}

def rewalk.either2(a1, _a2, b1, b2, ea, eb):
  %ea : {Rewalk.either(a1, b1) == Rewalk.either(_, b2) : Rewalk.Hit}
  %eb : {Rewalk.either(a1, b1) == Rewalk.either(a1, _) : Rewalk.Hit}
  {==}

# the rule's reads are the law's
law rewalk.reads_eq:
  for nn: Tree.Node
  for +name: String
  for +hot: Bool
  for +left: Nat
  for +live: Bool
  for +skip: Bool
  {Rewalk.hits(nn, name, hot, left, live, skip) == Laws.rewalk.reads(nn, name, hot, left, live, skip) : Rewalk.Hit}

# a mention of a name, then the rest of the chain
law rewalk.reads_name:
  for +t: String
  for +rest: Tree.Node
  for +name: String
  for +hot: Bool
  for +left: Nat
  for +live: Bool
  for +skip: Bool
  for ih: {Rewalk.hits(rest, name, hot, left, live, skip) == Laws.rewalk.reads(rest, name, hot, left, live, skip)
    : Rewalk.Hit}
  {Rewalk.either(Rewalk.hit_keep(skip, Rewalk.name_hit(String.eq(t, name), hot)),
    Rewalk.hits(rest, name, hot, left, live, skip))
    == Rewalk.either(Rewalk.hit_keep(skip, Rewalk.name_hit(String.eq(t, name), hot)),
      Laws.rewalk.reads(rest, name, hot, left, live, skip)) : Rewalk.Hit}

def rewalk.reads_name(t, rest, name, hot, left, live, skip, ih):
  +h = Rewalk.hit_keep(skip, Rewalk.name_hit(String.eq(t, name), hot))
  rewalk.either2(h, h, Rewalk.hits(rest, name, hot, left, live, skip),
    Laws.rewalk.reads(rest, name, hot, left, live, skip), {==}, ih)

# a callee or an indexed name, its group, then the rest of the chain
law rewalk.reads_call:
  for +o: String
  for +t: String
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +name: String
  for +hot: Bool
  for +left: Nat
  for +live: Bool
  for +skip: Bool
  for ik: {Rewalk.hits(kids, name, Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot),
    Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t),
    Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t), skip)
    == Laws.rewalk.reads(kids, name, Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot),
    Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t),
    Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t), skip) : Rewalk.Hit}
  for ir: {Rewalk.hits(r2, name, hot, left, live, skip) == Laws.rewalk.reads(r2, name, hot, left, live, skip)
    : Rewalk.Hit}
  {Rewalk.either(Rewalk.hit_keep(skip, Rewalk.here_hit(String.eq(o, "["), String.eq(o, "("), t, name, hot)),
    Rewalk.either(Rewalk.hits(kids, name, Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot),
      Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t),
      Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t), skip),
      Rewalk.hits(r2, name, hot, left, live, skip)))
    == Rewalk.either(Rewalk.hit_keep(skip, Rewalk.here_hit(String.eq(o, "["), String.eq(o, "("), t, name, hot)),
      Rewalk.either(Laws.rewalk.reads(kids, name, Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot),
        Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t),
        Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t), skip),
        Laws.rewalk.reads(r2, name, hot, left, live, skip))) : Rewalk.Hit}

def rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, ik, ir):
  +h = Rewalk.hit_keep(skip, Rewalk.here_hit(String.eq(o, "["), String.eq(o, "("), t, name, hot))
  +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
  +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
  +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
  rewalk.either2(h, h, Rewalk.either(Rewalk.hits(kids, name, hk, lk, vk, skip), Rewalk.hits(r2, name, hot, left, live,
    skip)), Rewalk.either(Laws.rewalk.reads(kids, name, hk, lk, vk, skip), Laws.rewalk.reads(r2, name, hot, left, live,
    skip)), {==}, rewalk.either2(Rewalk.hits(kids, name, hk, lk, vk, skip), Laws.rewalk.reads(kids, name, hk, lk, vk,
    skip), Rewalk.hits(r2, name, hot, left, live, skip), Laws.rewalk.reads(r2, name, hot, left, live, skip), ik, ir))

# a bare group, then the rest of the chain
law rewalk.reads_group:
  for +kids: Tree.Node
  for +rest: Tree.Node
  for +name: String
  for +hot: Bool
  for +left: Nat
  for +live: Bool
  for +skip: Bool
  for ik: {Rewalk.hits(kids, name, hot, 0n, False{}, skip) == Laws.rewalk.reads(kids, name, hot, 0n, False{}, skip)
    : Rewalk.Hit}
  for ir: {Rewalk.hits(rest, name, hot, left, live, skip) == Laws.rewalk.reads(rest, name, hot, left, live, skip)
    : Rewalk.Hit}
  {Rewalk.either(Rewalk.hits(kids, name, hot, 0n, False{}, skip), Rewalk.hits(rest, name, hot, left, live, skip))
    == Rewalk.either(Laws.rewalk.reads(kids, name, hot, 0n, False{}, skip),
      Laws.rewalk.reads(rest, name, hot, left, live, skip)) : Rewalk.Hit}

def rewalk.reads_group(kids, rest, name, hot, left, live, skip, ik, ir):
  rewalk.either2(Rewalk.hits(kids, name, hot, 0n, False{}, skip), Laws.rewalk.reads(kids, name, hot, 0n, False{}, skip),
    Rewalk.hits(rest, name, hot, left, live, skip), Laws.rewalk.reads(rest, name, hot, left, live, skip), ik, ir)

# a statement: its own tokens (the left of a let skipped), its body, then the
# rest of the chain
law rewalk.reads_stmt:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +name: String
  for +hot: Bool
  for +left: Nat
  for +live: Bool
  for +skip: Bool
  for ik: {Rewalk.hits(kids, name, False{}, 0n, False{}, Rewalk.has_eq(kids))
    == Laws.rewalk.reads(kids, name, False{}, 0n, False{}, Rewalk.has_eq(kids)) : Rewalk.Hit}
  for ib: {Rewalk.hits(body, name, False{}, 0n, False{}, False{})
    == Laws.rewalk.reads(body, name, False{}, 0n, False{}, False{}) : Rewalk.Hit}
  for ir: {Rewalk.hits(rest, name, hot, left, live, skip) == Laws.rewalk.reads(rest, name, hot, left, live, skip)
    : Rewalk.Hit}
  {Rewalk.either(Rewalk.hits(kids, name, False{}, 0n, False{}, Rewalk.has_eq(kids)),
    Rewalk.either(Rewalk.hits(body, name, False{}, 0n, False{}, False{}), Rewalk.hits(rest, name, hot, left, live,
      skip)))
    == Rewalk.either(Laws.rewalk.reads(kids, name, False{}, 0n, False{}, Rewalk.has_eq(kids)),
      Rewalk.either(Laws.rewalk.reads(body, name, False{}, 0n, False{}, False{}),
        Laws.rewalk.reads(rest, name, hot, left, live, skip))) : Rewalk.Hit}

def rewalk.reads_stmt(kids, body, rest, name, hot, left, live, skip, ik, ib, ir):
  +k1 = Rewalk.hits(kids, name, False{}, 0n, False{}, Rewalk.has_eq(kids))
  +k2 = Laws.rewalk.reads(kids, name, False{}, 0n, False{}, Rewalk.has_eq(kids))
  +b1 = Rewalk.hits(body, name, False{}, 0n, False{}, False{})
  +b2 = Laws.rewalk.reads(body, name, False{}, 0n, False{}, False{})
  +r1 = Rewalk.hits(rest, name, hot, left, live, skip)
  +r2 = Laws.rewalk.reads(rest, name, hot, left, live, skip)
  rewalk.either2(k1, k2, Rewalk.either(b1, r1), Rewalk.either(b2, r2), ik, rewalk.either2(b1, b2, r1, r2, ib, ir))

def rewalk.reads_eq(nn, name, hot, left, live, skip):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, l, c}:
              match k:
                case Lex.TName{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_name(t, rest, name, hot, left, live, skip, rewalk.reads_eq(rest, name, hot,
                            left, live, skip))
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_name(t, rest, name, hot, left, live, skip, rewalk.reads_eq(rest, name, hot,
                            left, live, skip))
                        case Tree.NNil{}:
                          rewalk.reads_name(t, rest, name, hot, left, live, skip, rewalk.reads_eq(rest, name, hot,
                            left, live, skip))
                        case Tree.NCons{x, y}:
                          rewalk.reads_name(t, rest, name, hot, left, live, skip, rewalk.reads_eq(rest, name, hot,
                            left, live, skip))
                    case Tree.Leaf{x}:
                      rewalk.reads_name(t, rest, name, hot, left, live, skip, rewalk.reads_eq(rest, name, hot, left,
                        live, skip))
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_name(t, rest, name, hot, left, live, skip, rewalk.reads_eq(rest, name, hot, left,
                        live, skip))
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_name(t, rest, name, hot, left, live, skip, rewalk.reads_eq(rest, name, hot, left,
                        live, skip))
                    case Tree.NNil{}:
                      rewalk.reads_name(t, rest, name, hot, left, live, skip, rewalk.reads_eq(rest, name, hot, left,
                        live, skip))
                case Lex.TUpper{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TDotted{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TWild{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TKey{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TNum{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TStr{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TChar{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TComment{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TSpace{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TNewline{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TOp{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TColon{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TEq{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              rewalk.reads_eq(rest, name, hot, left, live, False{})
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, False{})
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, False{})
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, False{})
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, False{})
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, False{})
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, False{})
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, False{})
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, False{})
                case Lex.TBind{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TArrow{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TLam{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TAll{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TAmp{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TOpen{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TClose{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TComma{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left,
                                live), live, skip)
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left, live),
                            live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left, live),
                            live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left, live),
                            live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left, live),
                            live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left, live),
                        live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left, live),
                        live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left, live),
                        live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left, live),
                        live, skip)
        case Tree.Group{open, +kids, close}:
          rewalk.reads_group(kids, rest, name, hot, left, live, skip, rewalk.reads_eq(kids, name, hot, 0n, False{},
            skip),
            rewalk.reads_eq(rest, name, hot, left, live, skip))
        case Tree.Stmt{kind, +kids, +body}:
          rewalk.reads_stmt(kids, body, rest, name, hot, left, live, skip,
            rewalk.reads_eq(kids, name, False{}, 0n, False{}, Rewalk.has_eq(kids)),
            rewalk.reads_eq(body, name, False{}, 0n, False{}, False{}), rewalk.reads_eq(rest, name, hot, left, live,
              skip))
        case Tree.NNil{}:
          rewalk.reads_eq(rest, name, hot, left, live, skip)
        case Tree.NCons{x, y}:
          rewalk.reads_eq(rest, name, hot, left, live, skip)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# the rule's narrow is the law's single
law rewalk.single_eq:
  for hh: Rewalk.How
  for +piece: Tree.Node
  {Rewalk.narrow(hh, piece) == Laws.rewalk.single(hh, piece) : Bool}

def rewalk.single_eq(hh, piece):
  match hh:
    case Rewalk.HWide{}:
      {==}
    case Rewalk.HSlot{}:
      {==}
    case Rewalk.HField{}:
      {==}
    case Rewalk.HLet{+binder}:
      Equal.cong(Rewalk.Hit, Bool, x => Rewalk.narrow_let(x), Rewalk.hits(piece, binder, False{}, 0n, False{}, False{}),
        Laws.rewalk.reads(piece, binder, False{}, 0n, False{}, False{}),
        rewalk.reads_eq(piece, binder, False{}, 0n, False{}, False{}))

# a twin keeps its whole result, to the rule and to the law
law rewalk.full_eq:
  for b: Bool
  for +hh: Rewalk.How
  for +piece: Tree.Node
  {Rewalk.other_full(b, hh, piece) == Bool.and(b, Bool.not(Laws.rewalk.single(hh, piece))) : Bool}

def rewalk.full_eq(b, hh, piece):
  match b:
    case False{}:
      {==}
    case True{}:
      Equal.cong(Bool, Bool, x => Bool.not(x), Rewalk.narrow(hh, piece), Laws.rewalk.single(hh, piece),
        rewalk.single_eq(hh, piece))

# a twin is read for a single value, to the rule and to the law
law rewalk.nar_eq:
  for b: Bool
  for +hh: Rewalk.How
  for +piece: Tree.Node
  {Rewalk.earlier_nar(b, hh, piece) == Bool.and(b, Laws.rewalk.single(hh, piece)) : Bool}

def rewalk.nar_eq(b, hh, piece):
  match b:
    case False{}:
      {==}
    case True{}:
      rewalk.single_eq(hh, piece)

# the rule's other_go is the law's whole
law rewalk.whole_eq:
  for sites: List<&2, Rewalk.Site>
  for +name: String
  for +args: String
  for +line: U32
  for +col: U32
  for +piece: Tree.Node
  {Rewalk.other_go(sites, name, args, line, col, piece) == Laws.rewalk.whole(sites, name, args, line, col, piece)
    : Bool}

def rewalk.whole_eq(sites, name, args, line, col, piece):
  match sites:
    case Nil{}:
      {==}
    case Con{s, rest}:
      match s:
        case Rewalk.Site{+nm, +as, +l, +c, len, +how}:
          +tw = Laws.rewalk.twin(nm, as, l, c, name, args, line, col)
          %rewalk.full_eq(tw, how, piece) : {Rewalk.other_go(Rewalk.Site{nm, as, l, c, len, how} <> rest, name, args,
            line, col, piece) == Bool.or(_, Laws.rewalk.whole(rest, name, args, line, col, piece)) : Bool}
          %rewalk.whole_eq(rest, name, args, line, col, piece) : {Rewalk.other_go(Rewalk.Site{nm, as, l, c, len, how}
            <> rest, name, args, line, col, piece) == Bool.or(Rewalk.other_full(tw, how, piece), _) : Bool}
          {==}

# the rule's earlier is the law's prior
law rewalk.prior_eq:
  for seen: List<&2, Rewalk.Site>
  for +name: String
  for +args: String
  for +line: U32
  for +col: U32
  for +piece: Tree.Node
  {Rewalk.earlier(seen, name, args, line, col, piece) == Laws.rewalk.prior(seen, name, args, line, col, piece) : Bool}

def rewalk.prior_eq(seen, name, args, line, col, piece):
  match seen:
    case Nil{}:
      {==}
    case Con{s, rest}:
      match s:
        case Rewalk.Site{+nm, +as, +l, +c, len, +how}:
          +tw = Laws.rewalk.twin(nm, as, l, c, name, args, line, col)
          %rewalk.nar_eq(tw, how, piece) : {Rewalk.earlier(Rewalk.Site{nm, as, l, c, len, how} <> rest, name, args,
            line, col, piece) == Bool.or(_, Laws.rewalk.prior(rest, name, args, line, col, piece)) : Bool}
          %rewalk.prior_eq(rest, name, args, line, col, piece) : {Rewalk.earlier(Rewalk.Site{nm, as, l, c, len, how}
            <> rest, name, args, line, col, piece) == Bool.or(Rewalk.earlier_nar(tw, how, piece), _) : Bool}
          {==}

# a narrow site with no narrow twin before it: one finding
law rewalk.nar_len:
  for n: Bool
  for p: Bool
  for +name: String
  for +line: U32
  for +col: U32
  for +len: U32
  for +path: String
  {List.length(&2, F.Finding, Rewalk.report_nar(n, p, name, line, col, len, path))
    == Bool.pick(Nat, Bool.and(n, Bool.not(p)), 1n, 0n) : Nat}

def rewalk.nar_len(n, p, _name, _line, _col, _len, _path):
  match n p:
    case False{} p:
      {==}
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}

# a site with a whole twin, read narrow, and no narrow twin before it: one
# finding
law rewalk.dup_len:
  for d: Bool
  for +how: Rewalk.How
  for +name: String
  for +args: String
  for +line: U32
  for +col: U32
  for +len: U32
  for +body: Tree.Node
  for +path: String
  for +seen: List<&2, Rewalk.Site>
  {List.length(&2, F.Finding, Rewalk.report_dup(d, how, name, args, line, col, len, body, path, seen))
    == Bool.pick(Nat, Bool.and(d, Bool.and(Rewalk.narrow(how, body), Bool.not(Rewalk.earlier(seen, name, args, line,
      col, body)))), 1n, 0n) : Nat}

def rewalk.dup_len(d, how, name, args, line, col, len, body, path, seen):
  match d:
    case False{}:
      {==}
    case True{}:
      rewalk.nar_len(Rewalk.narrow(how, body), Rewalk.earlier(seen, name, args, line, col, body), name, line, col, len,
        path)

# one site: one finding when the law flags it, none otherwise
law rewalk.one_len:
  for s: Rewalk.Site
  for +all: List<&2, Rewalk.Site>
  for +body: Tree.Node
  for +path: String
  for +seen: List<&2, Rewalk.Site>
  {List.length(&2, F.Finding, Rewalk.report_one(s, all, body, path, seen))
    == Bool.pick(Nat, Laws.rewalk.flag(s, all, body, seen), 1n, 0n) : Nat}

def rewalk.one_len(s, all, body, path, seen):
  match s:
    case Rewalk.Site{+name, +args, +line, +col, +len, +how}:
      +lhs = List.length(&2, F.Finding, Rewalk.report_one(Rewalk.Site{name, args, line, col, len, how}, all, body, path,
        seen))
      %rewalk.whole_eq(all, name, args, line, col, body) : {lhs == Bool.pick(Nat, Bool.and(_,
        Bool.and(Laws.rewalk.single(how, body), Bool.not(Laws.rewalk.prior(seen, name, args, line, col, body)))), 1n,
          0n)
        : Nat}
      %rewalk.single_eq(how, body) : {lhs == Bool.pick(Nat, Bool.and(Rewalk.other_go(all, name, args, line, col, body),
        Bool.and(_, Bool.not(Laws.rewalk.prior(seen, name, args, line, col, body)))), 1n, 0n) : Nat}
      %rewalk.prior_eq(seen, name, args, line, col, body) : {lhs == Bool.pick(Nat, Bool.and(Rewalk.other_go(all, name,
        args, line, col, body), Bool.and(Rewalk.narrow(how, body), Bool.not(_))), 1n, 0n) : Nat}
      rewalk.dup_len(Rewalk.other_go(all, name, args, line, col, body), how, name, args, line, col, len, body, path,
        seen)

# a flag's one or none, onto the rest's count
law rewalk.add_pick:
  for f: Bool
  for m: Nat
  {Nat.add(Bool.pick(Nat, f, 1n, 0n), m) == Bool.pick(Nat, f, 1n+m, m) : Nat}

def rewalk.add_pick(f, _m):
  match f:
    case True{}:
      {==}
    case False{}:
      {==}

# the rule's report counts what the law counts
law rewalk.report_len:
  for sites: List<&2, Rewalk.Site>
  for +all: List<&2, Rewalk.Site>
  for +body: Tree.Node
  for +path: String
  for +seen: List<&2, Rewalk.Site>
  {List.length(&2, F.Finding, Rewalk.report(sites, all, body, path, seen))
    == Laws.rewalk.count(sites, all, body, seen) : Nat}

def rewalk.report_len(sites, all, body, path, seen):
  match sites:
    case Nil{}:
      {==}
    case Con{+s, +rest}:
      +one = Rewalk.report_one(s, all, body, path, seen)
      +tl = Rewalk.report(rest, all, body, path, s <> seen)
      +f = Laws.rewalk.flag(s, all, body, seen)
      +m = Laws.rewalk.count(rest, all, body, s <> seen)
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, one, tl)),
        Nat.add(List.length(&2, F.Finding, one), List.length(&2, F.Finding, tl)), Bool.pick(Nat, f, 1n+m, m),
        esc.app(one, tl),
        Equal.trans(Nat, Nat.add(List.length(&2, F.Finding, one), List.length(&2, F.Finding, tl)),
          Nat.add(Bool.pick(Nat, f, 1n, 0n), m), Bool.pick(Nat, f, 1n+m, m),
          esc.add(List.length(&2, F.Finding, one), Bool.pick(Nat, f, 1n, 0n), List.length(&2, F.Finding, tl), m,
            rewalk.one_len(s, all, body, path, seen), rewalk.report_len(rest, all, body, path, s <> seen)),
          rewalk.add_pick(f, m)))

# the rule's sites of a piece are the law's
law rewalk.sites_eq:
  for +nn: Tree.Node
  for +self: String
  for +lp: List<&2, String>
  {Rewalk.pin(Rewalk.mark(nn), Rewalk.apply(nn, Rewalk.gather(nn, self, lp, Rewalk.binds(nn, []))))
    == Laws.rewalk.sites(nn, self, lp) : List<&2, Rewalk.Site>}

def rewalk.sites_eq(nn, self, lp):
  +lhs = Rewalk.pin(Rewalk.mark(nn), Rewalk.apply(nn, Rewalk.gather(nn, self, lp, Rewalk.binds(nn, []))))
  %rewalk.binds_eq(nn, []) : {lhs == Laws.rewalk.pin(Laws.rewalk.marks(nn), Laws.rewalk.apply(nn,
    Laws.rewalk.gather(nn, self, lp, _))) : List<&2, Rewalk.Site>}
  %rewalk.gather_eq(nn, self, lp, Rewalk.binds(nn, [])) : {lhs == Laws.rewalk.pin(Laws.rewalk.marks(nn),
    Laws.rewalk.apply(nn, _)) : List<&2, Rewalk.Site>}
  %rewalk.apply_eq(nn, Rewalk.gather(nn, self, lp, Rewalk.binds(nn, []))) : {lhs
    == Laws.rewalk.pin(Laws.rewalk.marks(nn), _) : List<&2, Rewalk.Site>}
  %rewalk.marks_eq(nn) : {lhs == Laws.rewalk.pin(_, Rewalk.apply(nn, Rewalk.gather(nn, self, lp, Rewalk.binds(nn,
    [])))) : List<&2, Rewalk.Site>}
  rewalk.pin_eq(Rewalk.mark(nn), Rewalk.apply(nn, Rewalk.gather(nn, self, lp, Rewalk.binds(nn, []))))

def Laws.rewalk_local_counts(nn, self, lp, path):
  +ss = Rewalk.pin(Rewalk.mark(nn), Rewalk.apply(nn, Rewalk.gather(nn, self, lp, Rewalk.binds(nn, []))))
  %rewalk.sites_eq(nn, self, lp) : {List.length(&2, F.Finding, Rewalk.report(ss, ss, nn, path, []))
    == Laws.rewalk.count(_, _, nn, []) : Nat}
  rewalk.report_len(ss, ss, nn, path, [])

# two finding lists joined: the counts added
law rewalk.two_len:
  for a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for -ma: Nat
  for -mb: Nat
  for ea: {List.length(&2, F.Finding, a) == ma : Nat}
  for eb: {List.length(&2, F.Finding, b) == mb : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b])) == Nat.add(ma, mb) : Nat}

def rewalk.two_len(a, b, ma, mb, ea, eb):
  pick.join(a, List.append(&2, F.Finding, b, Nil{}), ma, mb, ea, pick.last(b, mb, eb))

# three finding lists joined: the counts added
law rewalk.three_len:
  for a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for +c: List<&2, F.Finding>
  for -ma: Nat
  for -mb: Nat
  for -mc: Nat
  for ea: {List.length(&2, F.Finding, a) == ma : Nat}
  for eb: {List.length(&2, F.Finding, b) == mb : Nat}
  for ec: {List.length(&2, F.Finding, c) == mc : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])) == Nat.add(ma, Nat.add(mb, mc)) : Nat}

def rewalk.three_len(a, b, c, ma, mb, mc, ea, eb, ec):
  pick.join(a, List.append(&2, F.Finding, b, List.append(&2, F.Finding, c, Nil{})), ma, Nat.add(mb, mc), ea,
    pick.join(b, List.append(&2, F.Finding, c, Nil{}), mb, mc, eb, pick.last(c, mc, ec)))

# a statement's case-arm findings: its own tokens, its body, then what follows
law rewalk.visit_stmt:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +lp: List<&2, String>
  for +path: String
  for ek: {List.length(&2, F.Finding, Rewalk.visit(kids, self, lp, path)) == Laws.rewalk.arms(kids, self, lp) : Nat}
  for eb: {List.length(&2, F.Finding, Rewalk.visit(body, self, lp, path)) == Laws.rewalk.arms(body, self, lp) : Nat}
  for er: {List.length(&2, F.Finding, Rewalk.visit(rest, self, lp, path)) == Laws.rewalk.arms(rest, self, lp) : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [Rewalk.visit(kids, self, lp, path),
    Rewalk.visit(body, self, lp, path), Rewalk.visit(rest, self, lp, path)]))
    == Nat.add(Laws.rewalk.arms(kids, self, lp), Nat.add(Laws.rewalk.arms(body, self, lp),
      Laws.rewalk.arms(rest, self, lp))) : Nat}

def rewalk.visit_stmt(kids, body, rest, self, lp, path, ek, eb, er):
  rewalk.three_len(Rewalk.visit(kids, self, lp, path), Rewalk.visit(body, self, lp, path), Rewalk.visit(rest, self, lp,
    path), Laws.rewalk.arms(kids, self, lp), Laws.rewalk.arms(body, self, lp), Laws.rewalk.arms(rest, self, lp), ek,
    eb, er)

# a case arm: its own piece, the arms in it, then what follows
law rewalk.visit_case:
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +lp: List<&2, String>
  for +path: String
  for eb: {List.length(&2, F.Finding, Rewalk.visit(body, self, lp, path)) == Laws.rewalk.arms(body, self, lp) : Nat}
  for er: {List.length(&2, F.Finding, Rewalk.visit(rest, self, lp, path)) == Laws.rewalk.arms(rest, self, lp) : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [Rewalk.local(body, self, lp, path),
    Rewalk.visit(body, self, lp, path), Rewalk.visit(rest, self, lp, path)]))
    == Nat.add(Laws.rewalk.piece(body, self, lp), Nat.add(Laws.rewalk.arms(body, self, lp),
      Laws.rewalk.arms(rest, self, lp))) : Nat}

def rewalk.visit_case(body, rest, self, lp, path, eb, er):
  rewalk.three_len(Rewalk.local(body, self, lp, path), Rewalk.visit(body, self, lp, path), Rewalk.visit(rest, self, lp,
    path), Laws.rewalk.piece(body, self, lp), Laws.rewalk.arms(body, self, lp), Laws.rewalk.arms(rest, self, lp),
    Laws.rewalk_local_counts(body, self, lp, path), eb, er)

def Laws.rewalk_visit_counts(nn, self, lp, path):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SDef{}:
              rewalk.visit_stmt(kids, body, rest, self, lp, path, Laws.rewalk_visit_counts(kids, self, lp, path),
                Laws.rewalk_visit_counts(body, self, lp, path), Laws.rewalk_visit_counts(rest, self, lp, path))
            case Tree.SType{}:
              rewalk.visit_stmt(kids, body, rest, self, lp, path, Laws.rewalk_visit_counts(kids, self, lp, path),
                Laws.rewalk_visit_counts(body, self, lp, path), Laws.rewalk_visit_counts(rest, self, lp, path))
            case Tree.SLaw{}:
              rewalk.visit_stmt(kids, body, rest, self, lp, path, Laws.rewalk_visit_counts(kids, self, lp, path),
                Laws.rewalk_visit_counts(body, self, lp, path), Laws.rewalk_visit_counts(rest, self, lp, path))
            case Tree.SImport{}:
              rewalk.visit_stmt(kids, body, rest, self, lp, path, Laws.rewalk_visit_counts(kids, self, lp, path),
                Laws.rewalk_visit_counts(body, self, lp, path), Laws.rewalk_visit_counts(rest, self, lp, path))
            case Tree.SCase{}:
              rewalk.visit_case(body, rest, self, lp, path, Laws.rewalk_visit_counts(body, self, lp, path),
                Laws.rewalk_visit_counts(rest, self, lp, path))
            case Tree.SFor{}:
              rewalk.visit_stmt(kids, body, rest, self, lp, path, Laws.rewalk_visit_counts(kids, self, lp, path),
                Laws.rewalk_visit_counts(body, self, lp, path), Laws.rewalk_visit_counts(rest, self, lp, path))
            case Tree.SLet{}:
              rewalk.visit_stmt(kids, body, rest, self, lp, path, Laws.rewalk_visit_counts(kids, self, lp, path),
                Laws.rewalk_visit_counts(body, self, lp, path), Laws.rewalk_visit_counts(rest, self, lp, path))
            case Tree.STerm{}:
              rewalk.visit_stmt(kids, body, rest, self, lp, path, Laws.rewalk_visit_counts(kids, self, lp, path),
                Laws.rewalk_visit_counts(body, self, lp, path), Laws.rewalk_visit_counts(rest, self, lp, path))
        case Tree.Group{open, +kids, close}:
          rewalk.two_len(Rewalk.visit(kids, self, lp, path), Rewalk.visit(rest, self, lp, path),
            Laws.rewalk.arms(kids, self, lp), Laws.rewalk.arms(rest, self, lp),
            Laws.rewalk_visit_counts(kids, self, lp, path), Laws.rewalk_visit_counts(rest, self, lp, path))
        case Tree.Leaf{tok}:
          Laws.rewalk_visit_counts(rest, self, lp, path)
        case Tree.NNil{}:
          Laws.rewalk_visit_counts(rest, self, lp, path)
        case Tree.NCons{x, y}:
          Laws.rewalk_visit_counts(rest, self, lp, path)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# the rule's called names are the law's
law rewalk.called_eq:
  for nn: Tree.Node
  {Rewalk.called(nn) == Laws.rewalk.called(nn) : List<&2, String>}

# a callee, then what its group and the rest call
law rewalk.called_call:
  for +o: String
  for +t: String
  for +kids: Tree.Node
  for +r2: Tree.Node
  for ek: {Rewalk.called(kids) == Laws.rewalk.called(kids) : List<&2, String>}
  for er: {Rewalk.called(r2) == Laws.rewalk.called(r2) : List<&2, String>}
  {Bool.pick(List<&2, String>, String.eq(o, "("), t <> List.concat(&2, String, [Rewalk.called(kids),
    Rewalk.called(r2)]), List.concat(&2, String, [Rewalk.called(kids), Rewalk.called(r2)]))
    == Bool.pick(List<&2, String>, String.eq(o, "("), t <> List.concat(&2, String, [Laws.rewalk.called(kids),
      Laws.rewalk.called(r2)]), List.concat(&2, String, [Laws.rewalk.called(kids), Laws.rewalk.called(r2)]))
    : List<&2, String>}

def rewalk.called_call(o, t, kids, r2, ek, er):
  Equal.cong(List<&2, String>, List<&2, String>, m => Bool.pick(List<&2, String>, String.eq(o, "("), t <> m, m),
    List.concat(&2, String, [Rewalk.called(kids), Rewalk.called(r2)]),
    List.concat(&2, String, [Laws.rewalk.called(kids), Laws.rewalk.called(r2)]),
    rewalk.cat2(String, Rewalk.called(kids), Laws.rewalk.called(kids), Rewalk.called(r2), Laws.rewalk.called(r2), ek,
      er))

def rewalk.called_eq(nn):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, l, c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{open, +kids, close}:
                      match open:
                        case Lex.Tok{ok, +o, ol, oc}:
                          rewalk.called_call(o, t, kids, r2, rewalk.called_eq(kids), rewalk.called_eq(r2))
                    case Tree.Leaf{x}:
                      rewalk.called_eq(rest)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.called_eq(rest)
                    case Tree.NNil{}:
                      rewalk.called_eq(rest)
                    case Tree.NCons{x, y}:
                      rewalk.called_eq(rest)
                case Tree.Leaf{x}:
                  rewalk.called_eq(rest)
                case Tree.Group{open, kids, close}:
                  rewalk.called_eq(rest)
                case Tree.Stmt{kind, kids, body}:
                  rewalk.called_eq(rest)
                case Tree.NNil{}:
                  rewalk.called_eq(rest)
        case Tree.Group{open, +kids, close}:
          rewalk.cat2(String, Rewalk.called(kids), Laws.rewalk.called(kids), Rewalk.called(rest),
            Laws.rewalk.called(rest), rewalk.called_eq(kids), rewalk.called_eq(rest))
        case Tree.Stmt{kind, +kids, +body}:
          rewalk.cat3(String, Rewalk.called(kids), Laws.rewalk.called(kids), Rewalk.called(body),
            Laws.rewalk.called(body), Rewalk.called(rest), Laws.rewalk.called(rest), rewalk.called_eq(kids),
            rewalk.called_eq(body), rewalk.called_eq(rest))
        case Tree.NNil{}:
          rewalk.called_eq(rest)
        case Tree.NCons{x, y}:
          rewalk.called_eq(rest)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# a lazy or is the plain or
law rewalk.or_else:
  for b: Bool
  for t: List<&2, String>
  for +set: List<&2, String>
  for ih: {Rewalk.any_of(t, set) == Laws.rewalk.any(t, set) : Bool}
  {Lazy.or_else(b, _u => Rewalk.any_of(t, set)) == Bool.or(b, Laws.rewalk.any(t, set)) : Bool}

def rewalk.or_else(b, _t, _set, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# the rule's any_of is the law's any
law rewalk.any_eq:
  for cs: List<&2, String>
  for +set: List<&2, String>
  {Rewalk.any_of(cs, set) == Laws.rewalk.any(cs, set) : Bool}

def rewalk.any_eq(cs, set):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      rewalk.or_else(List.contains(~String, ~String.eq, set, c), t, set, rewalk.any_eq(t, set))

# the rule's looping defs are the law's
law rewalk.loops_eq:
  for ds: List<&2, Calls.Def>
  for +acc: List<&2, String>
  {Rewalk.loops.go(ds, acc) == Laws.rewalk.loops(ds, acc) : List<&2, String>}

def rewalk.loops_eq(ds, acc):
  match ds:
    case Nil{}:
      {==}
    case Con{d, +rest}:
      match d:
        case Calls.Def{+name, sig, +body}:
          +lhs = Rewalk.loops.go(Calls.Def{name, sig, body} <> rest, acc)
          %rewalk.called_eq(body) : {lhs == Laws.rewalk.loops(rest, Bool.pick(List<&2, String>,
            Bool.or(List.contains(~String, ~String.eq, _, name), Laws.rewalk.any(_, acc)), name <> acc, acc))
            : List<&2, String>}
          %rewalk.any_eq(Rewalk.called(body), acc) : {lhs == Laws.rewalk.loops(rest, Bool.pick(List<&2, String>,
            Bool.or(List.contains(~String, ~String.eq, Rewalk.called(body), name), _), name <> acc, acc))
            : List<&2, String>}
          rewalk.loops_eq(rest, Bool.pick(List<&2, String>, Bool.or(List.contains(~String, ~String.eq,
            Rewalk.called(body), name), Rewalk.any_of(Rewalk.called(body), acc)), name <> acc, acc))

# one def's findings, exempt or its piece and its arms
law rewalk.stop:
  for b: Bool
  for +body: Tree.Node
  for +name: String
  for +lp: List<&2, String>
  for +path: String
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, b, [], _u => List.concat(&2, F.Finding,
    [Rewalk.local(body, name, lp, path), Rewalk.visit(body, name, lp, path)])))
    == Bool.pick(Nat, b, 0n, Nat.add(Laws.rewalk.piece(body, name, lp), Laws.rewalk.arms(body, name, lp))) : Nat}

def rewalk.stop(b, body, name, lp, path):
  match b:
    case True{}:
      {==}
    case False{}:
      rewalk.two_len(Rewalk.local(body, name, lp, path), Rewalk.visit(body, name, lp, path),
        Laws.rewalk.piece(body, name, lp), Laws.rewalk.arms(body, name, lp),
        Laws.rewalk_local_counts(body, name, lp, path), Laws.rewalk_visit_counts(body, name, lp, path))

# rewalk's def walk: the findings gathered so far, then each def's
law rewalk.go:
  for ds: List<&2, Calls.Def>
  for +lp: List<&2, String>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Rewalk.check.go(ds, lp, path, acc)) == pick.sum(acc, Laws.rewalk.total(ds, lp, path))
    : Nat}

def rewalk.go(ds, lp, path, acc):
  match ds:
    case Nil{}:
      pick.rev(acc, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +x = Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [], _u => List.concat(&2, F.Finding,
        [Rewalk.local(body, name, lp, path), Rewalk.visit(body, name, lp, path)]))
      +n = Bool.pick(Nat, Calls.exempt(path, sig), 0n, Nat.add(Laws.rewalk.piece(body, name, lp),
        Laws.rewalk.arms(body, name, lp)))
      Equal.trans(Nat, List.length(&2, F.Finding, Rewalk.check.go(rest, lp, path, x <> acc)),
        pick.sum(acc, Nat.add(List.length(&2, F.Finding, x), Laws.rewalk.total(rest, lp, path))),
        pick.sum(acc, Nat.add(n, Laws.rewalk.total(rest, lp, path))),
        rewalk.go(rest, lp, path, x <> acc),
        Equal.cong(Nat, Nat, m => pick.sum(acc, Nat.add(m, Laws.rewalk.total(rest, lp, path))),
          List.length(&2, F.Finding, x), n, rewalk.stop(Calls.exempt(path, sig), body, name, lp, path)))

def Laws.rewalk_counts(path, _text, _toks, tree, _bound, _items):
  +ds = Calls.defs(tree)
  %rewalk.loops_eq(ds, []) : {List.length(&2, F.Finding, Rewalk.check.go(ds, Rewalk.loops.go(ds, []), path, []))
    == Laws.rewalk.total(ds, _, path) : Nat}
  rewalk.go(ds, Rewalk.loops.go(ds, []), path, [])

# trace
# -----

# the cells a Cells state ends with, once the pieces still to come are cut
def trace.closed(ps: List<&2, List<&2, Char>>, pp: List<&2, Char>) -> List<&2, String>:
  match ps:
    case Nil{}:
      [String.from_list(pp)]
    case Con{qq, rest}:
      String.trim(String.from_list(pp)) <> trace.closed(rest, qq)

# what cells.go returns from a state, given the pieces the rest of the line cuts into
def trace.close(cut: Laws.trace.Cut, st: Trace.Cells) -> List<&2, String>:
  match cut st:
    case Laws.trace.Cut{hh, tl} Trace.Cells{cur, done}:
      List.reverse.go(&2, String, done, trace.closed(tl, List.reverse.go(&2, Char, cur, hh)))

# one char onto the state is one piece onto the cut
law trace.at:
  for bar: Bool
  for cc: Char
  for cut: Laws.trace.Cut
  for st: Trace.Cells
  {trace.close(cut, Trace.cells.at(bar, cc, st)) == trace.close(Laws.trace.piece(bar, cc, cut), st)
    : List<&2, String>}

def trace.at(bar, _cc, cut, st):
  match bar cut st:
    case True{} Laws.trace.Cut{hh, tl} Trace.Cells{cur, done}:
      {==}
    case False{} Laws.trace.Cut{hh, tl} Trace.Cells{cur, done}:
      {==}

# the rule's walk over a line is the spec's cut of it, closed
law trace.go:
  for cs: List<&2, Char>
  for +esc: Bool
  for +st: Trace.Cells
  {Trace.cells.go(cs, esc, st) == trace.close(Laws.trace.split(cs, esc), st) : List<&2, String>}

def trace.go(cs, esc, st):
  match cs:
    case Nil{}:
      match st:
        case Trace.Cells{cur, done}:
          {==}
    case Con{+cc, +t}:
      Equal.trans(List<&2, String>,
        Trace.cells.go(t, Char.is_eq(cc, '\\'), Trace.cells.at(Bool.and(Char.is_eq(cc, '|'), Bool.not(esc)), cc, st)),
        trace.close(Laws.trace.split(t, Char.is_eq(cc, '\\')),
          Trace.cells.at(Bool.and(Char.is_eq(cc, '|'), Bool.not(esc)), cc, st)),
        trace.close(Laws.trace.piece(Bool.and(Char.is_eq(cc, '|'), Bool.not(esc)), cc,
          Laws.trace.split(t, Char.is_eq(cc, '\\'))), st),
        trace.go(t, Char.is_eq(cc, '\\'), Trace.cells.at(Bool.and(Char.is_eq(cc, '|'), Bool.not(esc)), cc, st)),
        trace.at(Bool.and(Char.is_eq(cc, '|'), Bool.not(esc)), cc, Laws.trace.split(t, Char.is_eq(cc, '\\')), st))

# taking nothing away from a Nat leaves it
law trace.sub0:
  for nn: Nat
  {Nat.sub(nn, 0n) == nn : Nat}

def trace.sub0(nn):
  match nn:
    case 0n:
      {==}
    case 1n+pp:
      {==}

# every closed piece but the last is the spec's middle
law trace.mid:
  for ps: List<&2, List<&2, Char>>
  for +pp: List<&2, Char>
  {List.take(&2, String, trace.closed(ps, pp), Nat.sub(List.length(&2, String, trace.closed(ps, pp)), 1n))
    == Laws.trace.mid(ps, pp) : List<&2, String>}

def trace.mid(ps, pp):
  match ps:
    case Nil{}:
      {==}
    case Con{+qq, +rest}:
      match rest:
        case Nil{}:
          {==}
        case Con{+aa, +bb}:
          %trace.sub0(List.length(&2, String, trace.closed(bb, aa))) :
            {String.trim(String.from_list(pp)) <> List.take(&2, String,
              String.trim(String.from_list(qq)) <> trace.closed(bb, aa),
              _) == String.trim(String.from_list(pp)) <> Laws.trace.mid(Con{aa, bb}, qq) : List<&2, String>}
          Equal.cong(List<&2, String>, List<&2, String>, xs => String.trim(String.from_list(pp)) <> xs,
            List.take(&2, String, trace.closed(Con{aa, bb}, qq),
              Nat.sub(List.length(&2, String, trace.closed(Con{aa, bb}, qq)), 1n)),
            Laws.trace.mid(Con{aa, bb}, qq), trace.mid(Con{aa, bb}, qq))

# the cells between the outer bars of the closed pieces are the spec's inner ones
law trace.inner:
  for cut: Laws.trace.Cut
  {List.take(&2, String, List.drop(&2, String, trace.close(cut, Trace.Cells{[], []}), 1n),
    Nat.sub(List.length(&2, String, trace.close(cut, Trace.Cells{[], []})), 2n)) == Laws.trace.inner(cut)
    : List<&2, String>}

def trace.inner(cut):
  match cut:
    case Laws.trace.Cut{hh, Nil{}}:
      {==}
    case Laws.trace.Cut{hh, Con{+qq, rest}}:
      match rest:
        case Nil{}:
          trace.mid(Nil{}, qq)
        case Con{+aa, +bb}:
          trace.mid(Con{aa, bb}, qq)

# the rule's cells of a line are the spec's
law trace.cells:
  for +line: String
  {Trace.cells(line) == Laws.trace.cells(line) : List<&2, String>}

def trace.cells(line):
  %Equal.sym(List<&2, String>, Trace.cells.go(String.to_list(String.trim(line)), False{}, Trace.Cells{[], []}),
    trace.close(Laws.trace.split(String.to_list(String.trim(line)), False{}), Trace.Cells{[], []}),
    trace.go(String.to_list(String.trim(line)), False{}, Trace.Cells{[], []})) :
    {List.take(&2, String, List.drop(&2, String, _, 1n), Nat.sub(List.length(&2, String, _), 2n))
      == Laws.trace.cells(line) : List<&2, String>}
  trace.inner(Laws.trace.split(String.to_list(String.trim(line)), False{}))

# the rule's Law entries of a cell are the spec's
law trace.entries:
  for ss: List<&2, String>
  {Trace.entries.go(ss) == Laws.trace.laws(ss) : List<&2, String>}

def trace.entries(ss):
  match ss:
    case Nil{}:
      {==}
    case Con{+s1, +rest}:
      Equal.cong(List<&2, String>, List<&2, String>,
        xs => Bool.pick(List<&2, String>, String.is_empty(String.trim(s1)), xs, String.trim(s1) <> xs),
        Trace.entries.go(rest), Laws.trace.laws(rest), trace.entries(rest))

# reversing a joined list onto an accumulator reverses each part in turn
law trace.rev_app:
  for -A: Data
  for ys: List<&2, A>
  for xs: List<&2, A>
  for acc: List<&2, A>
  {List.reverse.go(&2, A, List.append(&2, A, ys, xs), acc)
    == List.reverse.go(&2, A, xs, List.reverse.go(&2, A, ys, acc)) : List<&2, A>}

def trace.rev_app(A, ys, xs, acc):
  match ys:
    case Nil{}:
      {==}
    case Con{hh, tl}:
      trace.rev_app(A, tl, xs, hh <> acc)

# the malformed-row mark a requirement table line of these cells adds
def trace.bad5(+cs: List<&2, String>, +nn: U32) -> List<&2, Trace.Mark>:
  Bool.pick(List<&2, Trace.Mark>, Nat.is_eq(List.length(&2, String, cs), 5n), [],
    [Trace.Mark{"a requirement row has five cells", nn}])

# the malformed-row mark a trust table line of these cells adds
def trace.bad3(+cs: List<&2, String>, +nn: U32) -> List<&2, Trace.Mark>:
  Bool.pick(List<&2, Trace.Mark>, Nat.is_eq(List.length(&2, String, cs), 3n), [],
    [Trace.Mark{"a trust row has three cells", nn}])

# a requirement table line of any cells adds the spec's row, or a mark
law trace.five:
  for +cs: List<&2, String>
  for +nn: U32
  for +mm: Trace.Mode
  for +rr: List<&2, Trace.Row>
  for +tt: List<&2, Trace.Mark>
  for +bb: List<&2, Trace.Mark>
  {Lazy.stop(Trace.Spec, Bool.not(Nat.is_eq(List.length(&2, String, cs), 5n)),
    Trace.Spec{mm, rr, tt, Trace.Mark{"a requirement row has five cells", nn} <> bb},
    _u => Trace.Spec{mm, Trace.Row{Trace.cell(cs, 0n), Trace.cell(cs, 2n), Trace.cell(cs, 3n),
      Trace.entries(Trace.cell(cs, 4n)), nn} <> rr, tt, bb})
    == Trace.Spec{mm, List.reverse.go(&2, Trace.Row, Laws.trace.req_row(cs, nn), rr), tt,
      List.reverse.go(&2, Trace.Mark, trace.bad5(cs, nn), bb)} : Trace.Spec}

def trace.five(cs, nn, mm, rr, tt, bb):
  match cs:
    case Nil{}:
      {==}
    case Con{+c0, +r1}:
      match r1:
        case Nil{}:
          {==}
        case Con{+c1, +r2}:
          match r2:
            case Nil{}:
              {==}
            case Con{+c2, +r3}:
              match r3:
                case Nil{}:
                  {==}
                case Con{+c3, +r4}:
                  match r4:
                    case Nil{}:
                      {==}
                    case Con{+c4, +r5}:
                      match r5:
                        case Nil{}:
                          Equal.cong(List<&2, String>, Trace.Spec,
                            es => Trace.Spec{mm, Trace.Row{c0, c2, c3, es, nn} <> rr, tt, bb},
                            Trace.entries(c4), Laws.trace.laws(String.split(c4, ';')),
                            trace.entries(String.split(c4, ';')))
                        case Con{+c5, +r6}:
                          {==}

# a trust table line of any cells adds the spec's row, or a mark
law trace.three:
  for +cs: List<&2, String>
  for +nn: U32
  for +mm: Trace.Mode
  for +rr: List<&2, Trace.Row>
  for +tt: List<&2, Trace.Mark>
  for +bb: List<&2, Trace.Mark>
  {Bool.pick(Trace.Spec, Nat.is_eq(List.length(&2, String, cs), 3n),
    Trace.Spec{mm, rr, Trace.Mark{Trace.cell(cs, 0n), nn} <> tt, bb},
    Trace.Spec{mm, rr, tt, Trace.Mark{"a trust row has three cells", nn} <> bb})
    == Trace.Spec{mm, rr, List.reverse.go(&2, Trace.Mark, Laws.trace.trust_row(cs, nn), tt),
      List.reverse.go(&2, Trace.Mark, trace.bad3(cs, nn), bb)} : Trace.Spec}

def trace.three(cs, _nn, _mm, _rr, _tt, _bb):
  match cs:
    case Nil{}:
      {==}
    case Con{+c0, +r1}:
      match r1:
        case Nil{}:
          {==}
        case Con{+c1, +r2}:
          match r2:
            case Nil{}:
              {==}
            case Con{+c2, +r3}:
              match r3:
                case Nil{}:
                  {==}
                case Con{+c3, +r4}:
                  {==}

# the malformed-row mark a table line adds in place mm
def trace.bad_in(mm: Trace.Mode, +tt: String, +nn: U32) -> List<&2, Trace.Mark>:
  match mm:
    case Trace.Reqs{}:
      trace.bad5(Laws.trace.cells(tt), nn)
    case Trace.Trusts{}:
      trace.bad3(Laws.trace.cells(tt), nn)
    case _other:
      Nil{}

# the malformed-row mark a line of kind kk adds in place mm
def trace.bad_at(kk: Laws.trace.Line, mm: Trace.Mode, +tt: String, +nn: U32) -> List<&2, Trace.Mark>:
  match kk:
    case Laws.trace.Bar{}:
      trace.bad_in(mm, tt, nn)
    case _other:
      Nil{}

# a table line inside a table adds what the spec reads of it
law trace.table:
  for +mm: Trace.Mode
  for +tt: String
  for +nn: U32
  for +rr: List<&2, Trace.Row>
  for +ts: List<&2, Trace.Mark>
  for +bb: List<&2, Trace.Mark>
  {Trace.in_table(mm, tt, nn, Trace.Spec{mm, rr, ts, bb})
    == Trace.Spec{Laws.trace.on_bar(mm), List.reverse.go(&2, Trace.Row, Laws.trace.req_in(mm, tt, nn), rr),
      List.reverse.go(&2, Trace.Mark, Laws.trace.trust_in(mm, tt, nn), ts),
      List.reverse.go(&2, Trace.Mark, trace.bad_in(mm, tt, nn), bb)} : Trace.Spec}

def trace.table(mm, tt, nn, rr, ts, bb):
  match mm:
    case Trace.Out{}:
      {==}
    case Trace.ReqHead{}:
      {==}
    case Trace.Reqs{}:
      Equal.trans(Trace.Spec, Trace.in_table(Trace.Reqs{}, tt, nn, Trace.Spec{Trace.Reqs{}, rr, ts, bb}),
        Trace.Spec{Trace.Reqs{}, List.reverse.go(&2, Trace.Row, Laws.trace.req_row(Trace.cells(tt), nn), rr), ts,
          List.reverse.go(&2, Trace.Mark, trace.bad5(Trace.cells(tt), nn), bb)},
        Trace.Spec{Trace.Reqs{}, List.reverse.go(&2, Trace.Row, Laws.trace.req_row(Laws.trace.cells(tt), nn), rr), ts,
          List.reverse.go(&2, Trace.Mark, trace.bad5(Laws.trace.cells(tt), nn), bb)},
        trace.five(Trace.cells(tt), nn, Trace.Reqs{}, rr, ts, bb),
        Equal.cong(List<&2, String>, Trace.Spec,
          cs => Trace.Spec{Trace.Reqs{}, List.reverse.go(&2, Trace.Row, Laws.trace.req_row(cs, nn), rr), ts,
            List.reverse.go(&2, Trace.Mark, trace.bad5(cs, nn), bb)},
          Trace.cells(tt), Laws.trace.cells(tt), trace.cells(tt)))
    case Trace.TrustHead{}:
      {==}
    case Trace.Trusts{}:
      Equal.trans(Trace.Spec, Trace.in_table(Trace.Trusts{}, tt, nn, Trace.Spec{Trace.Trusts{}, rr, ts, bb}),
        Trace.Spec{Trace.Trusts{}, rr, List.reverse.go(&2, Trace.Mark, Laws.trace.trust_row(Trace.cells(tt), nn), ts),
          List.reverse.go(&2, Trace.Mark, trace.bad3(Trace.cells(tt), nn), bb)},
        Trace.Spec{Trace.Trusts{}, rr, List.reverse.go(&2, Trace.Mark, Laws.trace.trust_row(Laws.trace.cells(tt),
          nn), ts),
          List.reverse.go(&2, Trace.Mark, trace.bad3(Laws.trace.cells(tt), nn), bb)},
        trace.three(Trace.cells(tt), nn, Trace.Trusts{}, rr, ts, bb),
        Equal.cong(List<&2, String>, Trace.Spec,
          cs => Trace.Spec{Trace.Trusts{}, rr, List.reverse.go(&2, Trace.Mark, Laws.trace.trust_row(cs, nn), ts),
            List.reverse.go(&2, Trace.Mark, trace.bad3(cs, nn), bb)},
          Trace.cells(tt), Laws.trace.cells(tt), trace.cells(tt)))

# what the spec reads of a line of kind kk in place mm, onto what was read
def trace.onto(
  kk: Laws.trace.Line,
  +mm: Trace.Mode,
  +tt: String,
  +nn: U32,
  rr: List<&2, Trace.Row>,
  ts: List<&2, Trace.Mark>,
  bb: List<&2, Trace.Mark>
) -> Trace.Spec:
  match kk:
    case Laws.trace.ReqHeader{}:
      Trace.Spec{Trace.ReqHead{}, rr, ts, bb}
    case Laws.trace.TrustHeader{}:
      Trace.Spec{Trace.TrustHead{}, rr, ts, bb}
    case Laws.trace.Bar{}:
      Trace.Spec{Laws.trace.on_bar(mm), List.reverse.go(&2, Trace.Row, Laws.trace.req_in(mm, tt, nn), rr),
        List.reverse.go(&2, Trace.Mark, Laws.trace.trust_in(mm, tt, nn), ts),
        List.reverse.go(&2, Trace.Mark, trace.bad_in(mm, tt, nn), bb)}
    case Laws.trace.Prose{}:
      Trace.Spec{Trace.Out{}, rr, ts, bb}

# the rule's step, whatever the three tests on the line say, is the spec's reading
law trace.bools:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for +tt: String
  for +nn: U32
  for +mm: Trace.Mode
  for +rr: List<&2, Trace.Row>
  for +ts: List<&2, Trace.Mark>
  for +bb: List<&2, Trace.Mark>
  {Bool.pick(Trace.Spec, b1, Trace.moved(Trace.Spec{mm, rr, ts, bb}, Trace.ReqHead{}),
    Bool.pick(Trace.Spec, b2, Trace.moved(Trace.Spec{mm, rr, ts, bb}, Trace.TrustHead{}),
      Lazy.stop(Trace.Spec, Bool.not(b3), Trace.moved(Trace.Spec{mm, rr, ts, bb}, Trace.Out{}),
        _u => Trace.in_table(Trace.mode_of(Trace.Spec{mm, rr, ts, bb}), tt, nn, Trace.Spec{mm, rr, ts, bb}))))
    == trace.onto(Bool.pick(Laws.trace.Line, b1, Laws.trace.ReqHeader{},
      Bool.pick(Laws.trace.Line, b2, Laws.trace.TrustHeader{},
        Bool.pick(Laws.trace.Line, b3, Laws.trace.Bar{}, Laws.trace.Prose{}))), mm, tt, nn, rr, ts, bb) : Trace.Spec}

def trace.bools(b1, b2, b3, tt, nn, mm, rr, ts, bb):
  match b1 b2 b3:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      trace.table(mm, tt, nn, rr, ts, bb)
    case False{} False{} False{}:
      {==}

# the spec's reading written out
def trace.read(
  +kk: Laws.trace.Line,
  +mm: Trace.Mode,
  +tt: String,
  +nn: U32,
  rr: List<&2, Trace.Row>,
  ts: List<&2, Trace.Mark>,
  bb: List<&2, Trace.Mark>
) -> Trace.Spec:
  Trace.Spec{Laws.trace.after(kk, mm), List.reverse.go(&2, Trace.Row, Laws.trace.req_at(kk, mm, tt, nn), rr),
    List.reverse.go(&2, Trace.Mark, Laws.trace.trust_at(kk, mm, tt, nn), ts),
    List.reverse.go(&2, Trace.Mark, trace.bad_at(kk, mm, tt, nn), bb)}

# the reading by kind is the reading written out
law trace.kind:
  for +kk: Laws.trace.Line
  for +mm: Trace.Mode
  for +tt: String
  for +nn: U32
  for rr: List<&2, Trace.Row>
  for ts: List<&2, Trace.Mark>
  for bb: List<&2, Trace.Mark>
  {trace.onto(kk, mm, tt, nn, rr, ts, bb) == trace.read(kk, mm, tt, nn, rr, ts, bb) : Trace.Spec}

def trace.kind(kk, _mm, _tt, _nn, _rr, _ts, _bb):
  match kk:
    case Laws.trace.ReqHeader{}:
      {==}
    case Laws.trace.TrustHeader{}:
      {==}
    case Laws.trace.Bar{}:
      {==}
    case Laws.trace.Prose{}:
      {==}

# one line onto what was read is the spec's reading of it
law trace.step:
  for +ll: String
  for +nn: U32
  for +mm: Trace.Mode
  for +rr: List<&2, Trace.Row>
  for +ts: List<&2, Trace.Mark>
  for +bb: List<&2, Trace.Mark>
  {Trace.step(ll, nn, Trace.Spec{mm, rr, ts, bb})
    == trace.read(Laws.trace.line(String.trim(ll)), mm, String.trim(ll), nn, rr, ts, bb) : Trace.Spec}

def trace.step(ll, nn, mm, rr, ts, bb):
  Equal.trans(Trace.Spec, Trace.step(ll, nn, Trace.Spec{mm, rr, ts, bb}),
    trace.onto(Laws.trace.line(String.trim(ll)), mm, String.trim(ll), nn, rr, ts, bb),
    trace.read(Laws.trace.line(String.trim(ll)), mm, String.trim(ll), nn, rr, ts, bb),
    trace.bools(String.eq(String.trim(ll), "| ID | Requirement | Level | Status | Law |"),
      String.eq(String.trim(ll), "| ID | Assumption | Why it is trusted |"), String.starts_with(String.trim(ll), "|"),
      String.trim(ll), nn, mm, rr, ts, bb),
    trace.kind(Laws.trace.line(String.trim(ll)), mm, String.trim(ll), nn, rr, ts, bb))

# the place the spec's reading ends in
def trace.last(ls: List<&2, String>, +mm: Trace.Mode) -> Trace.Mode:
  match ls:
    case Nil{}:
      mm
    case Con{ll, rest}:
      trace.last(rest, Laws.trace.after(Laws.trace.line(String.trim(ll)), mm))

# the malformed-row marks of the lines, in file order
def trace.bads(ls: List<&2, String>, +nn: U32, +mm: Trace.Mode) -> List<&2, Trace.Mark>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{ll, rest}:
      +tt = String.trim(ll)
      +kk = Laws.trace.line(tt)
      List.append(&2, Trace.Mark, trace.bad_at(kk, mm, tt, nn), trace.bads(rest, (nn + 1 : U32),
        Laws.trace.after(kk, mm)))

# two readings with equal lists are equal
law trace.fields:
  for -mm: Trace.Mode
  for -r1: List<&2, Trace.Row>
  for -r2: List<&2, Trace.Row>
  for -t1: List<&2, Trace.Mark>
  for -t2: List<&2, Trace.Mark>
  for -b1: List<&2, Trace.Mark>
  for -b2: List<&2, Trace.Mark>
  for er: {r1 == r2 : List<&2, Trace.Row>}
  for et: {t1 == t2 : List<&2, Trace.Mark>}
  for eb: {b1 == b2 : List<&2, Trace.Mark>}
  {Trace.Spec{mm, r1, t1, b1} == Trace.Spec{mm, r2, t2, b2} : Trace.Spec}

def trace.fields(mm, r1, r2, t1, t2, b1, b2, er, et, eb):
  Equal.trans(Trace.Spec, Trace.Spec{mm, r1, t1, b1}, Trace.Spec{mm, r2, t1, b1}, Trace.Spec{mm, r2, t2, b2},
    Equal.cong(List<&2, Trace.Row>, Trace.Spec, xs => Trace.Spec{mm, xs, t1, b1}, r1, r2, er),
    Equal.trans(Trace.Spec, Trace.Spec{mm, r2, t1, b1}, Trace.Spec{mm, r2, t2, b1}, Trace.Spec{mm, r2, t2, b2},
      Equal.cong(List<&2, Trace.Mark>, Trace.Spec, xs => Trace.Spec{mm, r2, xs, b1}, t1, t2, et),
      Equal.cong(List<&2, Trace.Mark>, Trace.Spec, xs => Trace.Spec{mm, r2, t2, xs}, b1, b2, eb)))

# the rule's reading of the lines is the spec's, each list reversed onto what was read
law trace.parse:
  for ls: List<&2, String>
  for +nn: U32
  for +mm: Trace.Mode
  for +rr: List<&2, Trace.Row>
  for +ts: List<&2, Trace.Mark>
  for +bb: List<&2, Trace.Mark>
  {Trace.parse.go(ls, nn, Trace.Spec{mm, rr, ts, bb})
    == Trace.Spec{trace.last(ls, mm), List.reverse.go(&2, Trace.Row, Laws.trace.reqs(ls, nn, mm), rr),
      List.reverse.go(&2, Trace.Mark, Laws.trace.trusts(ls, nn, mm), ts),
      List.reverse.go(&2, Trace.Mark, trace.bads(ls, nn, mm), bb)} : Trace.Spec}

def trace.parse(ls, nn, mm, rr, ts, bb):
  match ls:
    case Nil{}:
      {==}
    case Con{+ll, +rest}:
      +tt = String.trim(ll)
      +kk = Laws.trace.line(tt)
      +m2 = Laws.trace.after(kk, mm)
      +n2 = (nn + 1 : U32)
      +r2 = List.reverse.go(&2, Trace.Row, Laws.trace.req_at(kk, mm, tt, nn), rr)
      +t2 = List.reverse.go(&2, Trace.Mark, Laws.trace.trust_at(kk, mm, tt, nn), ts)
      +b2 = List.reverse.go(&2, Trace.Mark, trace.bad_at(kk, mm, tt, nn), bb)
      Equal.trans(Trace.Spec, Trace.parse.go(rest, n2, Trace.step(ll, nn, Trace.Spec{mm, rr, ts, bb})),
        Trace.parse.go(rest, n2, Trace.Spec{m2, r2, t2, b2}),
        Trace.Spec{trace.last(rest, m2), List.reverse.go(&2, Trace.Row, Laws.trace.reqs(ll <> rest, nn, mm), rr),
          List.reverse.go(&2, Trace.Mark, Laws.trace.trusts(ll <> rest, nn, mm), ts),
          List.reverse.go(&2, Trace.Mark, trace.bads(ll <> rest, nn, mm), bb)},
        Equal.cong(Trace.Spec, Trace.Spec, sp => Trace.parse.go(rest, n2, sp),
          Trace.step(ll, nn, Trace.Spec{mm, rr, ts, bb}), Trace.Spec{m2, r2, t2, b2}, trace.step(ll, nn, mm, rr,
            ts, bb)),
        Equal.trans(Trace.Spec, Trace.parse.go(rest, n2, Trace.Spec{m2, r2, t2, b2}),
          Trace.Spec{trace.last(rest, m2), List.reverse.go(&2, Trace.Row, Laws.trace.reqs(rest, n2, m2), r2),
            List.reverse.go(&2, Trace.Mark, Laws.trace.trusts(rest, n2, m2), t2),
            List.reverse.go(&2, Trace.Mark, trace.bads(rest, n2, m2), b2)},
          Trace.Spec{trace.last(rest, m2), List.reverse.go(&2, Trace.Row, Laws.trace.reqs(ll <> rest, nn, mm), rr),
            List.reverse.go(&2, Trace.Mark, Laws.trace.trusts(ll <> rest, nn, mm), ts),
            List.reverse.go(&2, Trace.Mark, trace.bads(ll <> rest, nn, mm), bb)},
          trace.parse(rest, n2, m2, r2, t2, b2),
          trace.fields(trace.last(rest, m2),
            List.reverse.go(&2, Trace.Row, Laws.trace.reqs(rest, n2, m2), r2),
            List.reverse.go(&2, Trace.Row, Laws.trace.reqs(ll <> rest, nn, mm), rr),
            List.reverse.go(&2, Trace.Mark, Laws.trace.trusts(rest, n2, m2), t2),
            List.reverse.go(&2, Trace.Mark, Laws.trace.trusts(ll <> rest, nn, mm), ts),
            List.reverse.go(&2, Trace.Mark, trace.bads(rest, n2, m2), b2),
            List.reverse.go(&2, Trace.Mark, trace.bads(ll <> rest, nn, mm), bb),
            Equal.sym(List<&2, Trace.Row>, List.reverse.go(&2, Trace.Row, Laws.trace.reqs(ll <> rest, nn, mm), rr),
              List.reverse.go(&2, Trace.Row, Laws.trace.reqs(rest, n2, m2), r2),
              trace.rev_app(Trace.Row, Laws.trace.req_at(kk, mm, tt, nn), Laws.trace.reqs(rest, n2, m2), rr)),
            Equal.sym(List<&2, Trace.Mark>, List.reverse.go(&2, Trace.Mark, Laws.trace.trusts(ll <> rest, nn, mm), ts),
              List.reverse.go(&2, Trace.Mark, Laws.trace.trusts(rest, n2, m2), t2),
              trace.rev_app(Trace.Mark, Laws.trace.trust_at(kk, mm, tt, nn), Laws.trace.trusts(rest, n2, m2), ts)),
            Equal.sym(List<&2, Trace.Mark>, List.reverse.go(&2, Trace.Mark, trace.bads(ll <> rest, nn, mm), bb),
              List.reverse.go(&2, Trace.Mark, trace.bads(rest, n2, m2), b2),
              trace.rev_app(Trace.Mark, trace.bad_at(kk, mm, tt, nn), trace.bads(rest, n2, m2), bb)))))

# the text up to the first `-`
def trace.first(ss: String) -> String:
  match ss:
    case SNil{}:
      SNil{}
    case SCon{+cc, tl}:
      Bool.pick(String, Char.is_eq(cc, '-'), SNil{}, SCon{cc, trace.first(tl)})

# the segments after the first `-`
def trace.after(ss: String) -> List<&2, String>:
  match ss:
    case SNil{}:
      Nil{}
    case SCon{+cc, +tl}:
      Bool.pick(List<&2, String>, Char.is_eq(cc, '-'), trace.first(tl) <> trace.after(tl), trace.after(tl))

# a split's first segment and the rest, whatever the char says
law trace.cut:
  for dd: Bool
  for +cc: Char
  for +tl: String
  {String.split.fin(cc, trace.first(tl) <> trace.after(tl), dd)
    == Bool.pick(String, dd, SNil{}, SCon{cc, trace.first(tl)})
      <> Bool.pick(List<&2, String>, dd, trace.first(tl) <> trace.after(tl), trace.after(tl)) : List<&2, String>}

def trace.cut(dd, _cc, _tl):
  match dd:
    case True{}:
      {==}
    case False{}:
      {==}

# a split at `-` is the first segment, then the rest
law trace.dash:
  for ss: String
  {String.split(ss, '-') == trace.first(ss) <> trace.after(ss) : List<&2, String>}

def trace.dash(ss):
  match ss:
    case SNil{}:
      {==}
    case SCon{+cc, +tl}:
      Equal.trans(List<&2, String>, String.split.fin(cc, String.split(tl, '-'), Char.is_eq(cc, '-')),
        String.split.fin(cc, trace.first(tl) <> trace.after(tl), Char.is_eq(cc, '-')),
        trace.first(SCon{cc, tl}) <> trace.after(SCon{cc, tl}),
        Equal.cong(List<&2, String>, List<&2, String>, xs => String.split.fin(cc, xs, Char.is_eq(cc, '-')),
          String.split(tl, '-'), trace.first(tl) <> trace.after(tl), trace.dash(tl)),
        trace.cut(Char.is_eq(cc, '-'), cc, tl))

# what the rule asks of the segments p, ps, read so far to a `-` (dashed) or
# not, with the first segment known to hold a char (not empty) or not
def trace.segs(+pp: String, +ps: List<&2, String>, dashed: Bool, empty: Bool) -> Bool:
  Bool.and(Bool.or(dashed, Bool.not(List.is_empty(&2, String, ps))),
    Bool.and(Bool.pick(Bool, empty, Trace.segment(pp), Trace.id_chars(String.to_list(pp))), Trace.segments(ps)))

# the empty text ends an ID as the rule says
law trace.run_nil:
  for dashed: Bool
  for empty: Bool
  {Laws.trace.run(SNil{}, dashed, empty) == trace.segs(SNil{}, Nil{}, dashed, empty) : Bool}

def trace.run_nil(dashed, empty):
  match dashed empty:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a `-` at the head: the segment it ends must hold a char
law trace.run_dash:
  for aa: Bool
  for bb: Bool
  for +rs: List<&2, String>
  for dashed: Bool
  for empty: Bool
  {Bool.and(Bool.not(empty), Bool.and(Bool.or(True{}, Bool.not(List.is_empty(&2, String, rs))),
    Bool.and(aa, bb)))
    == Bool.and(Bool.or(dashed, Bool.not(False{})),
      Bool.and(Bool.pick(Bool, empty, False{}, True{}), Lazy.and_then(aa, _u => bb))) : Bool}

def trace.run_dash(aa, _bb, _rs, dashed, empty):
  match aa dashed empty:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# any other char at the head: it must be an uppercase letter or a digit
law trace.run_char:
  for aa: Bool
  for oo: Bool
  for xx: Bool
  for yy: Bool
  {Bool.and(aa, Bool.and(oo, Bool.and(xx, yy))) == Bool.and(oo, Bool.and(Lazy.and_then(aa, _u => xx), yy)) : Bool}

def trace.run_char(aa, oo, _xx, _yy):
  match aa oo:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# one char at the head, whatever Char.is_eq says of it
law trace.run_head:
  for dd: Bool
  for +cc: Char
  for +tl: String
  for +dashed: Bool
  for +empty: Bool
  for ih: {Laws.trace.run(tl, Bool.or(dd, dashed), dd)
    == trace.segs(trace.first(tl), trace.after(tl), Bool.or(dd, dashed), dd) : Bool}
  {Bool.and(Bool.pick(Bool, dd, Bool.not(empty), Laws.trace.alnum(cc)), Laws.trace.run(tl, Bool.or(dd, dashed), dd))
    == trace.segs(Bool.pick(String, dd, SNil{}, SCon{cc, trace.first(tl)}),
      Bool.pick(List<&2, String>, dd, trace.first(tl) <> trace.after(tl), trace.after(tl)), dashed, empty) : Bool}

def trace.run_head(dd, cc, tl, dashed, empty, ih):
  match dd empty:
    case True{} True{}:
      %Equal.sym(Bool, Laws.trace.run(tl, True{}, True{}),
        trace.segs(trace.first(tl), trace.after(tl), True{}, True{}), ih) :
        {Bool.and(Bool.not(True{}), _) == trace.segs(SNil{}, trace.first(tl) <> trace.after(tl), dashed, True{}) : Bool}
      trace.run_dash(Trace.segment(trace.first(tl)), Trace.segments(trace.after(tl)), trace.after(tl), dashed, True{})
    case True{} False{}:
      %Equal.sym(Bool, Laws.trace.run(tl, True{}, True{}),
        trace.segs(trace.first(tl), trace.after(tl), True{}, True{}), ih) :
        {Bool.and(Bool.not(False{}), _) == trace.segs(SNil{}, trace.first(tl) <> trace.after(tl), dashed,
          False{}) : Bool}
      trace.run_dash(Trace.segment(trace.first(tl)), Trace.segments(trace.after(tl)), trace.after(tl), dashed, False{})
    case False{} True{}:
      %Equal.sym(Bool, Laws.trace.run(tl, dashed, False{}),
        trace.segs(trace.first(tl), trace.after(tl), dashed, False{}), ih) :
        {Bool.and(Laws.trace.alnum(cc), _) == trace.segs(SCon{cc, trace.first(tl)}, trace.after(tl), dashed, True{})
          : Bool}
      trace.run_char(Laws.trace.alnum(cc), Bool.or(dashed, Bool.not(List.is_empty(&2, String, trace.after(tl)))),
        Trace.id_chars(String.to_list(trace.first(tl))), Trace.segments(trace.after(tl)))
    case False{} False{}:
      %Equal.sym(Bool, Laws.trace.run(tl, dashed, False{}),
        trace.segs(trace.first(tl), trace.after(tl), dashed, False{}), ih) :
        {Bool.and(Laws.trace.alnum(cc), _) == trace.segs(SCon{cc, trace.first(tl)}, trace.after(tl), dashed, False{})
          : Bool}
      trace.run_char(Laws.trace.alnum(cc), Bool.or(dashed, Bool.not(List.is_empty(&2, String, trace.after(tl)))),
        Trace.id_chars(String.to_list(trace.first(tl))), Trace.segments(trace.after(tl)))

# the spec's reading of an ID's segments is the rule's split
law trace.run:
  for ss: String
  for +dashed: Bool
  for +empty: Bool
  {Laws.trace.run(ss, dashed, empty) == trace.segs(trace.first(ss), trace.after(ss), dashed, empty) : Bool}

def trace.run(ss, dashed, empty):
  match ss:
    case SNil{}:
      trace.run_nil(dashed, empty)
    case SCon{+cc, +tl}:
      trace.run_head(Char.is_eq(cc, '-'), cc, tl, dashed, empty,
        trace.run(tl, Bool.or(Char.is_eq(cc, '-'), dashed), Char.is_eq(cc, '-')))

# any Nat is at least zero
law trace.ge0:
  for nn: Nat
  {Cmp.is_ge(Nat.cmp(nn, 0n)) == True{} : Bool}

def trace.ge0(nn):
  match nn:
    case 0n:
      {==}
    case 1n+pp:
      {==}

# two or more segments, each well formed, as the rule tests them
law trace.id_top:
  for rs: List<&2, String>
  for aa: Bool
  for -bb: Bool
  for -ll: Bool
  {Bool.and(Bool.and(Nat.is_ge(1n+List.length(&2, String, rs), 2n), Lazy.and_then(aa, _u => bb)), ll)
    == Bool.and(Bool.and(Bool.not(List.is_empty(&2, String, rs)), Bool.and(aa, bb)), ll) : Bool}

def trace.id_top(rs, aa, bb, ll):
  match rs aa:
    case Nil{} _:
      {==}
    case Con{hh, tl} True{}:
      %Equal.sym(Bool, Cmp.is_ge(Nat.cmp(List.length(&2, String, tl), 0n)), True{},
        trace.ge0(List.length(&2, String, tl))) :
        {Bool.and(Bool.and(_, bb), ll) == Bool.and(Bool.and(True{}, bb), ll) : Bool}
      {==}
    case Con{hh, tl} False{}:
      %Equal.sym(Bool, Cmp.is_ge(Nat.cmp(List.length(&2, String, tl), 0n)), True{},
        trace.ge0(List.length(&2, String, tl))) :
        {Bool.and(Bool.and(_, False{}), ll) == Bool.and(Bool.and(True{}, False{}), ll) : Bool}
      {==}

# the rule's first letter is the spec's
law trace.lead:
  for +ss: String
  {Trace.lettered(ss) == Laws.trace.lead(ss) : Bool}

def trace.lead(ss):
  match ss:
    case SNil{}:
      {==}
    case SCon{cc, tl}:
      {==}

# the rule's ID test is the spec's
law trace.is_id:
  for +ss: String
  {Trace.is_id(ss) == Laws.trace.is_id(ss) : Bool}

def trace.is_id(ss):
  +fs = trace.first(ss)
  +rs = trace.after(ss)
  +a1 = Bool.and(Bool.and(Nat.is_ge(List.length(&2, String, fs <> rs), 2n), Trace.segments(fs <> rs)),
    Trace.lettered(ss))
  +a2 = Bool.and(Bool.and(Bool.not(List.is_empty(&2, String, rs)), Bool.and(Trace.segment(fs), Trace.segments(rs))),
    Laws.trace.lead(ss))
  Equal.trans(Bool, Trace.is_id(ss), a1, Laws.trace.is_id(ss),
    Equal.cong(List<&2, String>, Bool,
      xs => Bool.and(Bool.and(Nat.is_ge(List.length(&2, String, xs), 2n), Trace.segments(xs)), Trace.lettered(ss)),
      String.split(ss, '-'), fs <> rs, trace.dash(ss)),
    Equal.trans(Bool, a1, a2, Laws.trace.is_id(ss),
      Equal.trans(Bool, a1,
        Bool.and(Bool.and(Bool.not(List.is_empty(&2, String, rs)), Bool.and(Trace.segment(fs), Trace.segments(rs))),
          Trace.lettered(ss)), a2,
        trace.id_top(rs, Trace.segment(fs), Trace.segments(rs), Trace.lettered(ss)),
        Equal.cong(Bool, Bool,
          ll => Bool.and(Bool.and(Bool.not(List.is_empty(&2, String, rs)), Bool.and(Trace.segment(fs),
            Trace.segments(rs))),
            ll), Trace.lettered(ss), Laws.trace.lead(ss), trace.lead(ss))),
      Equal.sym(Bool, Laws.trace.is_id(ss), a2,
        Equal.cong(Bool, Bool, xx => Bool.and(xx, Laws.trace.lead(ss)), Laws.trace.run(ss, False{}, True{}),
          trace.segs(fs, rs, False{}, True{}), trace.run(ss, False{}, True{})))))

# the rule's count of rows with an ID is the spec's
law trace.many:
  for rs: List<&2, Trace.Row>
  for +id: String
  {Trace.rows_with(rs, id) == Laws.trace.many(rs, id) : Nat}

def trace.many(rs, id):
  match rs:
    case Nil{}:
      {==}
    case Con{Trace.Row{+ii, lv, st, ls, nn}, +rest}:
      Equal.cong(Nat, Nat, mm => Bool.pick(Nat, String.eq(ii, id), 1n+mm, mm), Trace.rows_with(rest, id),
        Laws.trace.many(rest, id), trace.many(rest, id))

# the rule's count of trust rows with an ID is the spec's
law trace.marks:
  for ms: List<&2, Trace.Mark>
  for +id: String
  {Trace.marks_with(ms, id) == Laws.trace.marks(ms, id) : Nat}

def trace.marks(ms, id):
  match ms:
    case Nil{}:
      {==}
    case Con{Trace.Mark{+ii, nn}, +rest}:
      Equal.cong(Nat, Nat, mm => Bool.pick(Nat, String.eq(ii, id), 1n+mm, mm), Trace.marks_with(rest, id),
        Laws.trace.marks(rest, id), trace.marks(rest, id))

# the three shape messages: some message exactly when some test holds
law trace.why:
  for xx: Bool
  for yy: Bool
  for zz: Bool
  {Bool.not(String.is_empty(Bool.pick(String, xx,
    "the level is Proved or Trusted, the status proved or pending for Proved and empty for Trusted",
    Bool.pick(String, yy, "a proved row names its law", Bool.pick(String, zz, "a Trusted row names no law", "")))))
    == Bool.or(xx, Bool.or(yy, zz)) : Bool}

def trace.why(xx, yy, zz):
  match xx yy zz:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# the rule finds a shape wrong exactly when the spec does
law trace.shape:
  for +lv: String
  for +st: String
  for +ls: List<&2, String>
  {Bool.not(String.is_empty(Trace.shape(lv, st, ls))) == Laws.trace.misshapen(lv, st, ls) : Bool}

def trace.shape(lv, st, ls):
  +trusted = Bool.and(String.eq(lv, "Trusted"), String.is_empty(st))
  +none = List.is_empty(&2, String, ls)
  trace.why(Bool.not(Bool.or(Laws.trace.claim(lv, st), trusted)),
    Bool.and(Bool.and(String.eq(lv, "Proved"), String.eq(st, "proved")), none), Bool.and(trusted, Bool.not(none)))

# a finding when a test fails counts one exactly when it fails
law trace.flip:
  for cc: Bool
  for -xx: F.Finding
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, cc, [], [xx])) == Laws.trace.one(Bool.not(cc)) : Nat}

def trace.flip(cc, _xx):
  match cc:
    case True{}:
      {==}
    case False{}:
      {==}

# the lazy stop is the eager pick, when the thunk ignores its argument
law trace.stop:
  for -A: Data
  for cc: Bool
  for -aa: A
  for -xx: A
  for -yy: A
  for ih: {xx == yy : A}
  {Lazy.stop(A, cc, aa, _u => xx) == Bool.pick(A, cc, aa, yy) : A}

def trace.stop(_A, cc, _aa, _xx, _yy, ih):
  match cc:
    case True{}:
      {==}
    case False{}:
      ih

# the rule's law lookup is the spec's
law trace.law:
  for ls: List<&2, Digest.Law>
  for +name: String
  {Trace.law_named(ls, name) == Laws.trace.law(ls, name) : Maybe<&2, Digest.Law>}

def trace.law(ls, name):
  match ls:
    case Nil{}:
      {==}
    case Con{Digest.Law{+nn, +ll, +bb, +dd}, +rest}:
      trace.stop(Maybe<&2, Digest.Law>, String.eq(nn, name), Some{Digest.Law{nn, ll, bb, dd}},
        Trace.law_named(rest, name),
        Laws.trace.law(rest, name), trace.law(rest, name))

# the rule's file lookup is the spec's
law trace.file:
  for ds: List<&2, Digest.Digest>
  for +pp: String
  {Trace.laws_file(ds, pp) == Laws.trace.file(ds, pp) : Maybe<&2, List<&2, Digest.Law>>}

def trace.file(ds, pp):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, +norm, dir, +is_laws, lf, ex, tops, says, deps, uns, +laws}, +rest}:
      trace.stop(Maybe<&2, List<&2, Digest.Law>>, Bool.and(is_laws, String.eq(norm, pp)), Some{laws},
        Trace.laws_file(rest, pp), Laws.trace.file(rest, pp), trace.file(rest, pp))

# the rule's tag test is the spec's
law trace.tagged:
  for doc: List<&2, String>
  for +id: String
  {Trace.tagged(doc, id) == Laws.trace.tagged(doc, id) : Bool}

def trace.tagged(doc, id):
  match doc:
    case Nil{}:
      {==}
    case Con{+dd, +rest}:
      put.or(String.eq(String.trim(dd), id), Trace.tagged(rest, id), Laws.trace.tagged(rest, id),
        trace.tagged(rest, id))

# the findings on a law an entry names are the spec's defects of it
law trace.judge_law:
  for mm: Maybe<&2, Digest.Law>
  for +id: String
  for +entry: String
  for +nn: U32
  {List.length(&2, F.Finding, Trace.judge_law(mm, id, entry, nn)) == Laws.trace.law_at(mm, id) : Nat}

def trace.judge_law(mm, id, entry, nn):
  match mm:
    case None{}:
      {==}
    case Some{Digest.Law{na, li, +bb, +dd}}:
      +xb = Trace.at(nn, id ++ " names " ++ entry ++ ", which has no for or exs.")
      +xt = Trace.at(nn, id ++ " names " ++ entry ++ ", which is not tagged # " ++ id ++ ".")
      Equal.trans(Nat,
        List.length(&2, F.Finding, List.append(&2, F.Finding, Bool.pick(List<&2, F.Finding>, bb, [], [xb]),
          Bool.pick(List<&2, F.Finding>, Trace.tagged(dd, id), [], [xt]))),
        Nat.add(List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, bb, [], [xb])),
          List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, Trace.tagged(dd, id), [], [xt]))),
        Laws.trace.law_at(Some{Digest.Law{na, li, bb, dd}}, id),
        esc.app(Bool.pick(List<&2, F.Finding>, bb, [], [xb]), Bool.pick(List<&2, F.Finding>, Trace.tagged(dd, id),
          [], [xt])),
        esc.add(List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, bb, [], [xb])),
          Laws.trace.one(Bool.not(bb)),
          List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, Trace.tagged(dd, id), [], [xt])),
          Laws.trace.one(Bool.not(Laws.trace.tagged(dd, id))),
          trace.flip(bb, xb),
          Equal.trans(Nat, List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, Trace.tagged(dd, id), [], [xt])),
            Laws.trace.one(Bool.not(Trace.tagged(dd, id))), Laws.trace.one(Bool.not(Laws.trace.tagged(dd, id))),
            trace.flip(Trace.tagged(dd, id), xt),
            Equal.cong(Bool, Nat, bx => Laws.trace.one(Bool.not(bx)), Trace.tagged(dd, id), Laws.trace.tagged(dd, id),
              trace.tagged(dd, id)))))

# the findings on an entry's file are the spec's defects of it
law trace.judge_file:
  for mm: Maybe<&2, List<&2, Digest.Law>>
  for +name: String
  for +id: String
  for +entry: String
  for +nn: U32
  {List.length(&2, F.Finding, Trace.judge_file(mm, name, id, entry, nn)) == Laws.trace.file_at(mm, name, id) : Nat}

def trace.judge_file(mm, name, id, entry, nn):
  match mm:
    case None{}:
      {==}
    case Some{+ls}:
      Equal.trans(Nat, List.length(&2, F.Finding, Trace.judge_law(Trace.law_named(ls, name), id, entry, nn)),
        List.length(&2, F.Finding, Trace.judge_law(Laws.trace.law(ls, name), id, entry, nn)),
        Laws.trace.law_at(Laws.trace.law(ls, name), id),
        Equal.cong(Maybe<&2, Digest.Law>, Nat, ml => List.length(&2, F.Finding, Trace.judge_law(ml, id, entry, nn)),
          Trace.law_named(ls, name), Laws.trace.law(ls, name), trace.law(ls, name)),
        trace.judge_law(Laws.trace.law(ls, name), id, entry, nn))

# the findings on an entry, as its words, are the spec's defects of it
law trace.words:
  for +ws: List<&2, String>
  for +ds: List<&2, Digest.Digest>
  for +id: String
  for +entry: String
  for +nn: U32
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(Nat.is_eq(List.length(&2, String, ws), 2n)),
    [Trace.at(nn, id ++ ": a Law entry is <path> <law>, not " ++ entry ++ ".")],
    _u => Trace.judge_file(Trace.laws_file(ds, Imports.norm(Trace.cell(ws, 0n))), Trace.cell(ws, 1n), id, entry, nn)))
    == Laws.trace.entry(ws, ds, id) : Nat}

def trace.words(ws, ds, id, entry, nn):
  match ws:
    case Nil{}:
      {==}
    case Con{+w0, +r1}:
      match r1:
        case Nil{}:
          {==}
        case Con{+w1, +r2}:
          match r2:
            case Nil{}:
              Equal.trans(Nat,
                List.length(&2, F.Finding, Trace.judge_file(Trace.laws_file(ds, Imports.norm(w0)), w1, id, entry, nn)),
                List.length(&2, F.Finding, Trace.judge_file(Laws.trace.file(ds, Imports.norm(w0)), w1, id, entry, nn)),
                Laws.trace.file_at(Laws.trace.file(ds, Imports.norm(w0)), w1, id),
                Equal.cong(Maybe<&2, List<&2, Digest.Law>>, Nat,
                  mf => List.length(&2, F.Finding, Trace.judge_file(mf, w1, id, entry, nn)),
                  Trace.laws_file(ds, Imports.norm(w0)), Laws.trace.file(ds, Imports.norm(w0)),
                  trace.file(ds, Imports.norm(w0))),
                trace.judge_file(Laws.trace.file(ds, Imports.norm(w0)), w1, id, entry, nn))
            case Con{+w2, +r3}:
              {==}

# the findings on a row's Law entries are the spec's defects of them
law trace.judge_entries:
  for es: List<&2, String>
  for +ds: List<&2, Digest.Digest>
  for +id: String
  for +nn: U32
  {List.length(&2, F.Finding, Trace.judge_entries(es, ds, id, nn)) == Laws.trace.entries(es, ds, id) : Nat}

def trace.judge_entries(es, ds, id, nn):
  match es:
    case Nil{}:
      {==}
    case Con{+ee, +rest}:
      Equal.trans(Nat, List.length(&2, F.Finding, Trace.judge_entries(ee <> rest, ds, id, nn)),
        Nat.add(List.length(&2, F.Finding, Trace.judge_entry(ds, id, ee, nn)),
          List.length(&2, F.Finding, Trace.judge_entries(rest, ds, id, nn))),
        Laws.trace.entries(ee <> rest, ds, id),
        esc.app(Trace.judge_entry(ds, id, ee, nn), Trace.judge_entries(rest, ds, id, nn)),
        esc.add(List.length(&2, F.Finding, Trace.judge_entry(ds, id, ee, nn)),
          Laws.trace.entry(String.split(ee, ' '), ds, id),
          List.length(&2, F.Finding, Trace.judge_entries(rest, ds, id, nn)), Laws.trace.entries(rest, ds, id),
          trace.words(String.split(ee, ' '), ds, id, ee, nn), trace.judge_entries(rest, ds, id, nn)))

# adding zero leaves a Nat
law trace.add0:
  for nn: Nat
  {Nat.add(nn, 0n) == nn : Nat}

def trace.add0(nn):
  match nn:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 0n), pp, trace.add0(pp))

# five finding lists joined count the sum of their counts
law trace.len5:
  for +p1: List<&2, F.Finding>
  for +p2: List<&2, F.Finding>
  for +p3: List<&2, F.Finding>
  for +p4: List<&2, F.Finding>
  for +p5: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [p1, p2, p3, p4, p5]))
    == Nat.add(List.length(&2, F.Finding, p1), Nat.add(List.length(&2, F.Finding, p2),
      Nat.add(List.length(&2, F.Finding, p3), Nat.add(List.length(&2, F.Finding, p4), List.length(&2, F.Finding, p5)))))
    : Nat}

def trace.len5(p1, p2, p3, p4, p5):
  +l5 = List.length(&2, F.Finding, List.append(&2, F.Finding, p5, []))
  +e5 = Equal.trans(Nat, l5, Nat.add(List.length(&2, F.Finding, p5), 0n), List.length(&2, F.Finding, p5),
    esc.app(p5, []), trace.add0(List.length(&2, F.Finding, p5)))
  +q4 = List.append(&2, F.Finding, p4, List.append(&2, F.Finding, p5, []))
  +e4 = Equal.trans(Nat, List.length(&2, F.Finding, q4), Nat.add(List.length(&2, F.Finding, p4), l5),
    Nat.add(List.length(&2, F.Finding, p4), List.length(&2, F.Finding, p5)),
    esc.app(p4, List.append(&2, F.Finding, p5, [])),
    Equal.cong(Nat, Nat, xx => Nat.add(List.length(&2, F.Finding, p4), xx), l5, List.length(&2, F.Finding, p5), e5))
  +s4 = Nat.add(List.length(&2, F.Finding, p4), List.length(&2, F.Finding, p5))
  +q3 = List.append(&2, F.Finding, p3, q4)
  +e3 = Equal.trans(Nat, List.length(&2, F.Finding, q3), Nat.add(List.length(&2, F.Finding, p3), List.length(&2,
    F.Finding, q4)),
    Nat.add(List.length(&2, F.Finding, p3), s4), esc.app(p3, q4),
    Equal.cong(Nat, Nat, xx => Nat.add(List.length(&2, F.Finding, p3), xx), List.length(&2, F.Finding, q4), s4, e4))
  +s3 = Nat.add(List.length(&2, F.Finding, p3), s4)
  +q2 = List.append(&2, F.Finding, p2, q3)
  +e2 = Equal.trans(Nat, List.length(&2, F.Finding, q2), Nat.add(List.length(&2, F.Finding, p2), List.length(&2,
    F.Finding, q3)),
    Nat.add(List.length(&2, F.Finding, p2), s3), esc.app(p2, q3),
    Equal.cong(Nat, Nat, xx => Nat.add(List.length(&2, F.Finding, p2), xx), List.length(&2, F.Finding, q3), s3, e3))
  +s2 = Nat.add(List.length(&2, F.Finding, p2), s3)
  Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, p1, q2)),
    Nat.add(List.length(&2, F.Finding, p1), List.length(&2, F.Finding, q2)),
    Nat.add(List.length(&2, F.Finding, p1), s2), esc.app(p1, q2),
    Equal.cong(Nat, Nat, xx => Nat.add(List.length(&2, F.Finding, p1), xx), List.length(&2, F.Finding, q2), s2, e2))

# equal summands give equal sums of five
law trace.add5:
  for -a1: Nat
  for -a2: Nat
  for -a3: Nat
  for -a4: Nat
  for -a5: Nat
  for -b1: Nat
  for -b2: Nat
  for -b3: Nat
  for -b4: Nat
  for -b5: Nat
  for e1: {a1 == b1 : Nat}
  for e2: {a2 == b2 : Nat}
  for e3: {a3 == b3 : Nat}
  for e4: {a4 == b4 : Nat}
  for e5: {a5 == b5 : Nat}
  {Nat.add(a1, Nat.add(a2, Nat.add(a3, Nat.add(a4, a5)))) == Nat.add(b1, Nat.add(b2, Nat.add(b3, Nat.add(b4, b5))))
    : Nat}

def trace.add5(a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, e1, e2, e3, e4, e5):
  esc.add(a1, b1, Nat.add(a2, Nat.add(a3, Nat.add(a4, a5))), Nat.add(b2, Nat.add(b3, Nat.add(b4, b5))), e1,
    esc.add(a2, b2, Nat.add(a3, Nat.add(a4, a5)), Nat.add(b3, Nat.add(b4, b5)), e2,
      esc.add(a3, b3, Nat.add(a4, a5), Nat.add(b4, b5), e3, esc.add(a4, b4, a5, b5, e4, e5))))

# a pick on a negated test is the pick the other way round
law trace.unpick:
  for cc: Bool
  for -mm: Nat
  {Bool.pick(Nat, Bool.not(cc), 0n, mm) == Bool.pick(Nat, cc, mm, 0n) : Nat}

def trace.unpick(cc, _mm):
  match cc:
    case True{}:
      {==}
    case False{}:
      {==}

# the rule's findings on one requirement row are the spec's defects of it
law trace.row:
  for +id: String
  for +lv: String
  for +st: String
  for +ls: List<&2, String>
  for +nn: U32
  for +mo: Trace.Mode
  for +rs: List<&2, Trace.Row>
  for +ts: List<&2, Trace.Mark>
  for +bs: List<&2, Trace.Mark>
  for +ds: List<&2, Digest.Digest>
  {List.length(&2, F.Finding, Trace.judge_row(Trace.Row{id, lv, st, ls, nn}, Trace.Spec{mo, rs, ts, bs}, ds))
    == Laws.trace.row(Trace.Row{id, lv, st, ls, nn}, rs, ts, ds) : Nat}

def trace.row(id, lv, st, ls, nn, _mo, rs, ts, _bs, ds):
  +why = Trace.shape(lv, st, ls)
  +x1 = Trace.at(nn, id ++ " is not an ID: [A-Z][A-Z0-9]*(-[A-Z0-9]+)+.")
  +x2 = Trace.at(nn, id ++ " is listed twice.")
  +x3 = Trace.at(nn, id ++ ": " ++ why ++ ".")
  +x4 = Trace.at(nn, id ++ " is Trusted and has no row in the trust boundary table.")
  +p1 = Bool.pick(List<&2, F.Finding>, Trace.is_id(id), [], [x1])
  +p2 = Bool.pick(List<&2, F.Finding>, Nat.is_gt(Trace.rows_with(rs, id), 1n), [x2], [])
  +p3 = Bool.pick(List<&2, F.Finding>, String.is_empty(why), [], [x3])
  +p4 = Bool.pick(List<&2, F.Finding>, Bool.and(String.eq(lv, "Trusted"), Nat.is_eq(Trace.marks_with(ts, id), 0n)), [x4], [])
  +p5 = Lazy.stop(List<&2, F.Finding>, Bool.not(Trace.claims(lv, st)), [], _u => Trace.judge_entries(ls, ds, id, nn))
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [p1, p2, p3, p4, p5])),
    Nat.add(List.length(&2, F.Finding, p1), Nat.add(List.length(&2, F.Finding, p2),
      Nat.add(List.length(&2, F.Finding, p3), Nat.add(List.length(&2, F.Finding, p4), List.length(&2, F.Finding,
        p5))))),
    Laws.trace.row(Trace.Row{id, lv, st, ls, nn}, rs, ts, ds),
    trace.len5(p1, p2, p3, p4, p5),
    trace.add5(List.length(&2, F.Finding, p1), List.length(&2, F.Finding, p2), List.length(&2, F.Finding, p3),
      List.length(&2, F.Finding, p4), List.length(&2, F.Finding, p5),
      Laws.trace.one(Bool.not(Laws.trace.is_id(id))), Laws.trace.one(Nat.is_gt(Laws.trace.many(rs, id), 1n)),
      Laws.trace.one(Laws.trace.misshapen(lv, st, ls)),
      Laws.trace.one(Bool.and(String.eq(lv, "Trusted"), Nat.is_eq(Laws.trace.marks(ts, id), 0n))),
      Bool.pick(Nat, Laws.trace.claim(lv, st), Laws.trace.entries(ls, ds, id), 0n),
      Equal.trans(Nat, List.length(&2, F.Finding, p1), Laws.trace.one(Bool.not(Trace.is_id(id))),
        Laws.trace.one(Bool.not(Laws.trace.is_id(id))), trace.flip(Trace.is_id(id), x1),
        Equal.cong(Bool, Nat, bx => Laws.trace.one(Bool.not(bx)), Trace.is_id(id), Laws.trace.is_id(id),
          trace.is_id(id))),
      Equal.trans(Nat, List.length(&2, F.Finding, p2), Laws.trace.one(Nat.is_gt(Trace.rows_with(rs, id), 1n)),
        Laws.trace.one(Nat.is_gt(Laws.trace.many(rs, id), 1n)), chars.one(Nat.is_gt(Trace.rows_with(rs, id), 1n), x2),
        Equal.cong(Nat, Nat, nx => Laws.trace.one(Nat.is_gt(nx, 1n)), Trace.rows_with(rs, id), Laws.trace.many(rs, id),
          trace.many(rs, id))),
      Equal.trans(Nat, List.length(&2, F.Finding, p3), Laws.trace.one(Bool.not(String.is_empty(why))),
        Laws.trace.one(Laws.trace.misshapen(lv, st, ls)), trace.flip(String.is_empty(why), x3),
        Equal.cong(Bool, Nat, bx => Laws.trace.one(bx), Bool.not(String.is_empty(why)), Laws.trace.misshapen(lv,
          st, ls),
          trace.shape(lv, st, ls))),
      Equal.trans(Nat, List.length(&2, F.Finding, p4),
        Laws.trace.one(Bool.and(String.eq(lv, "Trusted"), Nat.is_eq(Trace.marks_with(ts, id), 0n))),
        Laws.trace.one(Bool.and(String.eq(lv, "Trusted"), Nat.is_eq(Laws.trace.marks(ts, id), 0n))),
        chars.one(Bool.and(String.eq(lv, "Trusted"), Nat.is_eq(Trace.marks_with(ts, id), 0n)), x4),
        Equal.cong(Nat, Nat, nx => Laws.trace.one(Bool.and(String.eq(lv, "Trusted"), Nat.is_eq(nx, 0n))),
          Trace.marks_with(ts, id), Laws.trace.marks(ts, id), trace.marks(ts, id))),
      Equal.trans(Nat, List.length(&2, F.Finding, p5),
        Bool.pick(Nat, Bool.not(Laws.trace.claim(lv, st)), 0n, Laws.trace.entries(ls, ds, id)),
        Bool.pick(Nat, Laws.trace.claim(lv, st), Laws.trace.entries(ls, ds, id), 0n),
        put.stop(Bool.not(Laws.trace.claim(lv, st)), Trace.judge_entries(ls, ds, id, nn), Laws.trace.entries(ls,
          ds, id),
          trace.judge_entries(ls, ds, id, nn)),
        trace.unpick(Laws.trace.claim(lv, st), Laws.trace.entries(ls, ds, id)))))

# the rule's findings on the requirement rows are the spec's defects of them
law trace.rows:
  for xs: List<&2, Trace.Row>
  for +mo: Trace.Mode
  for +rs: List<&2, Trace.Row>
  for +ts: List<&2, Trace.Mark>
  for +bs: List<&2, Trace.Mark>
  for +ds: List<&2, Digest.Digest>
  {List.length(&2, F.Finding, Trace.judge_rows(xs, Trace.Spec{mo, rs, ts, bs}, ds)) == Laws.trace.rows(xs, rs, ts, ds)
    : Nat}

def trace.rows(xs, mo, rs, ts, bs, ds):
  match xs:
    case Nil{}:
      {==}
    case Con{Trace.Row{+id, +lv, +st, +ls, +nn}, +rest}:
      +sp = {Trace.Spec{mo, rs, ts, bs} : Trace.Spec}
      +rw = {Trace.Row{id, lv, st, ls, nn} : Trace.Row}
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, Trace.judge_row(rw, sp, ds),
        Trace.judge_rows(rest, sp, ds))),
        Nat.add(List.length(&2, F.Finding, Trace.judge_row(rw, sp, ds)),
          List.length(&2, F.Finding, Trace.judge_rows(rest, sp, ds))),
        Laws.trace.rows(rw <> rest, rs, ts, ds),
        esc.app(Trace.judge_row(rw, sp, ds), Trace.judge_rows(rest, sp, ds)),
        esc.add(List.length(&2, F.Finding, Trace.judge_row(rw, sp, ds)), Laws.trace.row(rw, rs, ts, ds),
          List.length(&2, F.Finding, Trace.judge_rows(rest, sp, ds)), Laws.trace.rows(rest, rs, ts, ds),
          trace.row(id, lv, st, ls, nn, mo, rs, ts, bs, ds), trace.rows(rest, mo, rs, ts, bs, ds)))

# a trust row's findings, whatever its two tests say
law trace.twin:
  for aa: Bool
  for bb: Bool
  for -x1: F.Finding
  for -x2: F.Finding
  for -more: List<&2, F.Finding>
  for -mm: Nat
  for ih: {List.length(&2, F.Finding, more) == mm : Nat}
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, aa, Bool.pick(List<&2, F.Finding>, bb, x2 <> more, more),
    x1 <> Bool.pick(List<&2, F.Finding>, bb, x2 <> more, more)))
    == Nat.add(Nat.add(Laws.trace.one(Bool.not(aa)), Laws.trace.one(bb)), mm) : Nat}

def trace.twin(aa, bb, _x1, _x2, more, mm, ih):
  match aa bb:
    case True{} True{}:
      Equal.cong(Nat, Nat, nx => 1n+nx, List.length(&2, F.Finding, more), mm, ih)
    case True{} False{}:
      ih
    case False{} True{}:
      Equal.cong(Nat, Nat, nx => 2n+nx, List.length(&2, F.Finding, more), mm, ih)
    case False{} False{}:
      Equal.cong(Nat, Nat, nx => 1n+nx, List.length(&2, F.Finding, more), mm, ih)

# the rule's findings on the trust rows are the spec's defects of them
law trace.twins:
  for ms: List<&2, Trace.Mark>
  for +all: List<&2, Trace.Mark>
  {List.length(&2, F.Finding, Trace.twins(ms, all)) == Laws.trace.trust(ms, all) : Nat}

def trace.twins(ms, all):
  match ms:
    case Nil{}:
      {==}
    case Con{Trace.Mark{+id, +nn}, +rest}:
      +x1 = Trace.at(nn, id ++ " is not an ID: [A-Z][A-Z0-9]*(-[A-Z0-9]+)+.")
      +x2 = Trace.at(nn, id ++ " is listed twice.")
      +mm = Laws.trace.trust(rest, all)
      Equal.trans(Nat, List.length(&2, F.Finding, Trace.twins(Trace.Mark{id, nn} <> rest, all)),
        Nat.add(Nat.add(Laws.trace.one(Bool.not(Trace.is_id(id))),
          Laws.trace.one(Nat.is_gt(Trace.marks_with(all, id), 1n))), mm),
        Laws.trace.trust(Trace.Mark{id, nn} <> rest, all),
        trace.twin(Trace.is_id(id), Nat.is_gt(Trace.marks_with(all, id), 1n), x1, x2, Trace.twins(rest, all), mm,
          trace.twins(rest, all)),
        Equal.trans(Nat,
          Nat.add(Nat.add(Laws.trace.one(Bool.not(Trace.is_id(id))),
            Laws.trace.one(Nat.is_gt(Trace.marks_with(all, id), 1n))), mm),
          Nat.add(Nat.add(Laws.trace.one(Bool.not(Laws.trace.is_id(id))),
            Laws.trace.one(Nat.is_gt(Trace.marks_with(all, id), 1n))), mm),
          Laws.trace.trust(Trace.Mark{id, nn} <> rest, all),
          Equal.cong(Bool, Nat,
            bx => Nat.add(Nat.add(Laws.trace.one(Bool.not(bx)), Laws.trace.one(Nat.is_gt(Trace.marks_with(all, id),
              1n))),
              mm), Trace.is_id(id), Laws.trace.is_id(id), trace.is_id(id)),
          Equal.cong(Nat, Nat,
            nx => Nat.add(Nat.add(Laws.trace.one(Bool.not(Laws.trace.is_id(id))), Laws.trace.one(Nat.is_gt(nx,
              1n))), mm),
            Trace.marks_with(all, id), Laws.trace.marks(all, id), trace.marks(all, id))))

# the rule's claim lookup is the spec's
law trace.claimed:
  for rs: List<&2, Trace.Row>
  for +id: String
  {Trace.claimed(rs, id) == Laws.trace.claimed(rs, id) : Bool}

def trace.claimed(rs, id):
  match rs:
    case Nil{}:
      {==}
    case Con{Trace.Row{+ii, +lv, +st, ls, nn}, +rest}:
      put.or(Bool.and(Trace.claims(lv, st), String.eq(ii, id)), Trace.claimed(rest, id), Laws.trace.claimed(rest, id),
        trace.claimed(rest, id))

# a tag line's finding, whatever its two tests say
law trace.loose:
  for aa: Bool
  for cc: Bool
  for -xx: F.Finding
  for -more: List<&2, F.Finding>
  for -mm: Nat
  for ih: {List.length(&2, F.Finding, more) == mm : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Lazy.or_else(Bool.not(aa), _u => cc), more,
    _u => xx <> more)) == Bool.pick(Nat, Bool.and(aa, Bool.not(cc)), 1n+mm, mm) : Nat}

def trace.loose(aa, cc, _xx, more, mm, ih):
  match aa cc:
    case True{} True{}:
      ih
    case True{} False{}:
      Equal.cong(Nat, Nat, nx => 1n+nx, List.length(&2, F.Finding, more), mm, ih)
    case False{} _:
      ih

# the rule's stray tags of a comment block are the spec's
law trace.stray:
  for doc: List<&2, String>
  for +rs: List<&2, Trace.Row>
  for +path: String
  for +name: String
  for +ll: U32
  {List.length(&2, F.Finding, Trace.stray(doc, rs, path, name, ll)) == Laws.trace.stray(doc, rs) : Nat}

def trace.stray(doc, rs, path, name, ll):
  match doc:
    case Nil{}:
      {==}
    case Con{+dd, +rest}:
      +tt = String.trim(dd)
      +mm = Laws.trace.stray(rest, rs)
      +xx = {F.Finding{path, ll, 0, 0, "trace",
        "Law " ++ name ++ " is tagged " ++ tt ++ ", which SPEC.md does not list as Proved, proved or pending."} : F.Finding}
      Equal.trans(Nat, List.length(&2, F.Finding, Trace.stray(dd <> rest, rs, path, name, ll)),
        Bool.pick(Nat, Bool.and(Trace.is_id(tt), Bool.not(Trace.claimed(rs, tt))), 1n+mm, mm),
        Laws.trace.stray(dd <> rest, rs),
        trace.loose(Trace.is_id(tt), Trace.claimed(rs, tt), xx, Trace.stray(rest, rs, path, name, ll), mm,
          trace.stray(rest, rs, path, name, ll)),
        Equal.trans(Nat, Bool.pick(Nat, Bool.and(Trace.is_id(tt), Bool.not(Trace.claimed(rs, tt))), 1n+mm, mm),
          Bool.pick(Nat, Bool.and(Laws.trace.is_id(tt), Bool.not(Trace.claimed(rs, tt))), 1n+mm, mm),
          Laws.trace.stray(dd <> rest, rs),
          Equal.cong(Bool, Nat, bx => Bool.pick(Nat, Bool.and(bx, Bool.not(Trace.claimed(rs, tt))), 1n+mm, mm),
            Trace.is_id(tt), Laws.trace.is_id(tt), trace.is_id(tt)),
          Equal.cong(Bool, Nat, bx => Bool.pick(Nat, Bool.and(Laws.trace.is_id(tt), Bool.not(bx)), 1n+mm, mm),
            Trace.claimed(rs, tt), Laws.trace.claimed(rs, tt), trace.claimed(rs, tt))))

# the rule's stray tags of each law are the spec's
law trace.stray_laws:
  for ls: List<&2, Digest.Law>
  for +rs: List<&2, Trace.Row>
  for +path: String
  {List.length(&2, F.Finding, Trace.strays.laws(ls, rs, path)) == Laws.trace.stray_laws(ls, rs) : Nat}

def trace.stray_laws(ls, rs, path):
  match ls:
    case Nil{}:
      {==}
    case Con{Digest.Law{+nn, +ll, bb, +dd}, +rest}:
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, Trace.stray(dd, rs, path, nn, ll),
        Trace.strays.laws(rest, rs, path))),
        Nat.add(List.length(&2, F.Finding, Trace.stray(dd, rs, path, nn, ll)),
          List.length(&2, F.Finding, Trace.strays.laws(rest, rs, path))),
        Nat.add(Laws.trace.stray(dd, rs), Laws.trace.stray_laws(rest, rs)),
        esc.app(Trace.stray(dd, rs, path, nn, ll), Trace.strays.laws(rest, rs, path)),
        esc.add(List.length(&2, F.Finding, Trace.stray(dd, rs, path, nn, ll)), Laws.trace.stray(dd, rs),
          List.length(&2, F.Finding, Trace.strays.laws(rest, rs, path)), Laws.trace.stray_laws(rest, rs),
          trace.stray(dd, rs, path, nn, ll), trace.stray_laws(rest, rs, path)))

# the rule's stray tags of each file are the spec's
law trace.strays:
  for ds: List<&2, Digest.Digest>
  for +rs: List<&2, Trace.Row>
  {List.length(&2, F.Finding, Trace.strays(ds, rs)) == Laws.trace.strays(ds, rs) : Nat}

def trace.strays(ds, rs):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{+path, norm, dir, il, lf, ex, tops, says, deps, uns, +laws}, +rest}:
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, Trace.strays.laws(laws, rs, path),
        Trace.strays(rest, rs))),
        Nat.add(List.length(&2, F.Finding, Trace.strays.laws(laws, rs, path)),
          List.length(&2, F.Finding, Trace.strays(rest, rs))),
        Nat.add(Laws.trace.stray_laws(laws, rs), Laws.trace.strays(rest, rs)),
        esc.app(Trace.strays.laws(laws, rs, path), Trace.strays(rest, rs)),
        esc.add(List.length(&2, F.Finding, Trace.strays.laws(laws, rs, path)), Laws.trace.stray_laws(laws, rs),
          List.length(&2, F.Finding, Trace.strays(rest, rs)), Laws.trace.strays(rest, rs),
          trace.stray_laws(laws, rs, path), trace.strays(rest, rs)))

# one more on the right is one more in the sum
law trace.adds:
  for aa: Nat
  for -bb: Nat
  {Nat.add(aa, 1n+bb) == 1n+Nat.add(aa, bb) : Nat}

def trace.adds(aa, bb):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, nx => 1n+nx, Nat.add(pp, 1n+bb), 1n+Nat.add(pp, bb), trace.adds(pp, bb))

# a count that picks one more moves across a sum
law trace.swap:
  for cc: Bool
  for +m1: Nat
  for +m2: Nat
  {Nat.add(m1, Bool.pick(Nat, cc, 1n+m2, m2)) == Nat.add(Bool.pick(Nat, cc, 1n+m1, m1), m2) : Nat}

def trace.swap(cc, m1, m2):
  match cc:
    case True{}:
      trace.adds(m1, m2)
    case False{}:
      {==}

# the spec's count of rows with an ID, over a list reversed onto another
law trace.many_rev:
  for xs: List<&2, Trace.Row>
  for +acc: List<&2, Trace.Row>
  for +id: String
  {Laws.trace.many(List.reverse.go(&2, Trace.Row, xs, acc), id)
    == Nat.add(Laws.trace.many(xs, id), Laws.trace.many(acc, id)) : Nat}

def trace.many_rev(xs, acc, id):
  match xs:
    case Nil{}:
      {==}
    case Con{Trace.Row{+ii, +lv, +st, +ls, +nn}, +rest}:
      Equal.trans(Nat, Laws.trace.many(List.reverse.go(&2, Trace.Row, rest, Trace.Row{ii, lv, st, ls, nn} <> acc), id),
        Nat.add(Laws.trace.many(rest, id), Laws.trace.many(Trace.Row{ii, lv, st, ls, nn} <> acc, id)),
        Nat.add(Laws.trace.many(Trace.Row{ii, lv, st, ls, nn} <> rest, id), Laws.trace.many(acc, id)),
        trace.many_rev(rest, Trace.Row{ii, lv, st, ls, nn} <> acc, id),
        trace.swap(String.eq(ii, id), Laws.trace.many(rest, id), Laws.trace.many(acc, id)))

# the spec's count of trust rows with an ID, over a list reversed onto another
law trace.marks_rev:
  for xs: List<&2, Trace.Mark>
  for +acc: List<&2, Trace.Mark>
  for +id: String
  {Laws.trace.marks(List.reverse.go(&2, Trace.Mark, xs, acc), id)
    == Nat.add(Laws.trace.marks(xs, id), Laws.trace.marks(acc, id)) : Nat}

def trace.marks_rev(xs, acc, id):
  match xs:
    case Nil{}:
      {==}
    case Con{Trace.Mark{+ii, +nn}, +rest}:
      Equal.trans(Nat, Laws.trace.marks(List.reverse.go(&2, Trace.Mark, rest, Trace.Mark{ii, nn} <> acc), id),
        Nat.add(Laws.trace.marks(rest, id), Laws.trace.marks(Trace.Mark{ii, nn} <> acc, id)),
        Nat.add(Laws.trace.marks(Trace.Mark{ii, nn} <> rest, id), Laws.trace.marks(acc, id)),
        trace.marks_rev(rest, Trace.Mark{ii, nn} <> acc, id),
        trace.swap(String.eq(ii, id), Laws.trace.marks(rest, id), Laws.trace.marks(acc, id)))

# or moves across a join
law trace.or3:
  for bb: Bool
  for c1: Bool
  for -c2: Bool
  {Bool.or(c1, Bool.or(bb, c2)) == Bool.or(Bool.or(bb, c1), c2) : Bool}

def trace.or3(bb, c1, _c2):
  match bb c1:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# or with false leaves a Bool
law trace.or0:
  for bb: Bool
  {Bool.or(bb, False{}) == bb : Bool}

def trace.or0(bb):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# the spec's claim lookup, over a list reversed onto another
law trace.claimed_rev:
  for xs: List<&2, Trace.Row>
  for +acc: List<&2, Trace.Row>
  for +id: String
  {Laws.trace.claimed(List.reverse.go(&2, Trace.Row, xs, acc), id)
    == Bool.or(Laws.trace.claimed(xs, id), Laws.trace.claimed(acc, id)) : Bool}

def trace.claimed_rev(xs, acc, id):
  match xs:
    case Nil{}:
      {==}
    case Con{Trace.Row{+ii, +lv, +st, +ls, +nn}, +rest}:
      Equal.trans(Bool,
        Laws.trace.claimed(List.reverse.go(&2, Trace.Row, rest, Trace.Row{ii, lv, st, ls, nn} <> acc), id),
        Bool.or(Laws.trace.claimed(rest, id), Laws.trace.claimed(Trace.Row{ii, lv, st, ls, nn} <> acc, id)),
        Bool.or(Laws.trace.claimed(Trace.Row{ii, lv, st, ls, nn} <> rest, id), Laws.trace.claimed(acc, id)),
        trace.claimed_rev(rest, Trace.Row{ii, lv, st, ls, nn} <> acc, id),
        trace.or3(Bool.and(Laws.trace.claim(lv, st), String.eq(ii, id)), Laws.trace.claimed(rest, id),
          Laws.trace.claimed(acc, id)))

# a row's defects are the same against the rows reversed
law trace.row_rev:
  for xx: Trace.Row
  for +rs: List<&2, Trace.Row>
  for +ts: List<&2, Trace.Mark>
  for +ds: List<&2, Digest.Digest>
  {Laws.trace.row(xx, List.reverse(&2, Trace.Row, rs), List.reverse(&2, Trace.Mark, ts), ds)
    == Laws.trace.row(xx, rs, ts, ds) : Nat}

def trace.row_rev(xx, rs, ts, ds):
  match xx:
    case Trace.Row{+id, +lv, +st, +es, +nn}:
      +a1 = Laws.trace.one(Bool.not(Laws.trace.is_id(id)))
      +a3 = Laws.trace.one(Laws.trace.misshapen(lv, st, es))
      +a5 = Bool.pick(Nat, Laws.trace.claim(lv, st), Laws.trace.entries(es, ds, id), 0n)
      Equal.trans(Nat, Laws.trace.row(Trace.Row{id, lv, st, es, nn}, List.reverse(&2, Trace.Row, rs),
        List.reverse(&2, Trace.Mark, ts), ds),
        Nat.add(a1, Nat.add(Laws.trace.one(Nat.is_gt(Laws.trace.many(rs, id), 1n)), Nat.add(a3,
          Nat.add(Laws.trace.one(Bool.and(String.eq(lv, "Trusted"),
            Nat.is_eq(Laws.trace.marks(List.reverse(&2, Trace.Mark, ts), id), 0n))), a5)))),
        Laws.trace.row(Trace.Row{id, lv, st, es, nn}, rs, ts, ds),
        Equal.cong(Nat, Nat, nx => Nat.add(a1, Nat.add(Laws.trace.one(Nat.is_gt(nx, 1n)), Nat.add(a3,
          Nat.add(Laws.trace.one(Bool.and(String.eq(lv, "Trusted"),
            Nat.is_eq(Laws.trace.marks(List.reverse(&2, Trace.Mark, ts), id), 0n))), a5)))),
          Laws.trace.many(List.reverse(&2, Trace.Row, rs), id), Laws.trace.many(rs, id),
          Equal.trans(Nat, Laws.trace.many(List.reverse(&2, Trace.Row, rs), id), Nat.add(Laws.trace.many(rs, id), 0n),
            Laws.trace.many(rs, id), trace.many_rev(rs, [], id), trace.add0(Laws.trace.many(rs, id)))),
        Equal.cong(Nat, Nat, nx => Nat.add(a1, Nat.add(Laws.trace.one(Nat.is_gt(Laws.trace.many(rs, id), 1n)),
          Nat.add(a3,
          Nat.add(Laws.trace.one(Bool.and(String.eq(lv, "Trusted"), Nat.is_eq(nx, 0n))), a5)))),
          Laws.trace.marks(List.reverse(&2, Trace.Mark, ts), id), Laws.trace.marks(ts, id),
          Equal.trans(Nat, Laws.trace.marks(List.reverse(&2, Trace.Mark, ts), id), Nat.add(Laws.trace.marks(ts,
            id), 0n),
            Laws.trace.marks(ts, id), trace.marks_rev(ts, [], id), trace.add0(Laws.trace.marks(ts, id)))))

# the rows' defects are the same against the rows reversed
law trace.rows_rev:
  for xs: List<&2, Trace.Row>
  for +rs: List<&2, Trace.Row>
  for +ts: List<&2, Trace.Mark>
  for +ds: List<&2, Digest.Digest>
  {Laws.trace.rows(xs, List.reverse(&2, Trace.Row, rs), List.reverse(&2, Trace.Mark, ts), ds)
    == Laws.trace.rows(xs, rs, ts, ds) : Nat}

def trace.rows_rev(xs, rs, ts, ds):
  match xs:
    case Nil{}:
      {==}
    case Con{+xx, +rest}:
      esc.add(Laws.trace.row(xx, List.reverse(&2, Trace.Row, rs), List.reverse(&2, Trace.Mark, ts), ds),
        Laws.trace.row(xx, rs, ts, ds),
        Laws.trace.rows(rest, List.reverse(&2, Trace.Row, rs), List.reverse(&2, Trace.Mark, ts), ds),
        Laws.trace.rows(rest, rs, ts, ds), trace.row_rev(xx, rs, ts, ds), trace.rows_rev(rest, rs, ts, ds))

# the trust rows' defects are the same against the trust rows reversed
law trace.trust_rev:
  for ms: List<&2, Trace.Mark>
  for +all: List<&2, Trace.Mark>
  {Laws.trace.trust(ms, List.reverse(&2, Trace.Mark, all)) == Laws.trace.trust(ms, all) : Nat}

def trace.trust_rev(ms, all):
  match ms:
    case Nil{}:
      {==}
    case Con{Trace.Mark{+id, +nn}, +rest}:
      +a1 = Laws.trace.one(Bool.not(Laws.trace.is_id(id)))
      esc.add(Nat.add(a1, Laws.trace.one(Nat.is_gt(Laws.trace.marks(List.reverse(&2, Trace.Mark, all), id), 1n))),
        Nat.add(a1, Laws.trace.one(Nat.is_gt(Laws.trace.marks(all, id), 1n))),
        Laws.trace.trust(rest, List.reverse(&2, Trace.Mark, all)), Laws.trace.trust(rest, all),
        Equal.cong(Nat, Nat, nx => Nat.add(a1, Laws.trace.one(Nat.is_gt(nx, 1n))),
          Laws.trace.marks(List.reverse(&2, Trace.Mark, all), id), Laws.trace.marks(all, id),
          Equal.trans(Nat, Laws.trace.marks(List.reverse(&2, Trace.Mark, all), id), Nat.add(Laws.trace.marks(all,
            id), 0n),
            Laws.trace.marks(all, id), trace.marks_rev(all, [], id), trace.add0(Laws.trace.marks(all, id)))),
        trace.trust_rev(rest, all))

# a comment block's stray tags are the same against the rows reversed
law trace.stray_rev:
  for doc: List<&2, String>
  for +rs: List<&2, Trace.Row>
  {Laws.trace.stray(doc, List.reverse(&2, Trace.Row, rs)) == Laws.trace.stray(doc, rs) : Nat}

def trace.stray_rev(doc, rs):
  match doc:
    case Nil{}:
      {==}
    case Con{+dd, +rest}:
      +tt = String.trim(dd)
      Equal.trans(Nat, Laws.trace.stray(dd <> rest, List.reverse(&2, Trace.Row, rs)),
        Bool.pick(Nat, Bool.and(Laws.trace.is_id(tt), Bool.not(Laws.trace.claimed(rs, tt))),
          1n+Laws.trace.stray(rest, List.reverse(&2, Trace.Row, rs)), Laws.trace.stray(rest, List.reverse(&2,
            Trace.Row, rs))),
        Laws.trace.stray(dd <> rest, rs),
        Equal.cong(Bool, Nat, bx => Bool.pick(Nat, Bool.and(Laws.trace.is_id(tt), Bool.not(bx)),
          1n+Laws.trace.stray(rest, List.reverse(&2, Trace.Row, rs)), Laws.trace.stray(rest, List.reverse(&2,
            Trace.Row, rs))),
          Laws.trace.claimed(List.reverse(&2, Trace.Row, rs), tt), Laws.trace.claimed(rs, tt),
          Equal.trans(Bool, Laws.trace.claimed(List.reverse(&2, Trace.Row, rs), tt),
            Bool.or(Laws.trace.claimed(rs, tt), False{}), Laws.trace.claimed(rs, tt),
            trace.claimed_rev(rs, [], tt), trace.or0(Laws.trace.claimed(rs, tt)))),
        Equal.cong(Nat, Nat, nx => Bool.pick(Nat, Bool.and(Laws.trace.is_id(tt), Bool.not(Laws.trace.claimed(rs, tt))),
          1n+nx, nx), Laws.trace.stray(rest, List.reverse(&2, Trace.Row, rs)), Laws.trace.stray(rest, rs),
          trace.stray_rev(rest, rs)))

# each law's stray tags are the same against the rows reversed
law trace.stray_laws_rev:
  for ls: List<&2, Digest.Law>
  for +rs: List<&2, Trace.Row>
  {Laws.trace.stray_laws(ls, List.reverse(&2, Trace.Row, rs)) == Laws.trace.stray_laws(ls, rs) : Nat}

def trace.stray_laws_rev(ls, rs):
  match ls:
    case Nil{}:
      {==}
    case Con{Digest.Law{nn, ll, bb, +dd}, +rest}:
      esc.add(Laws.trace.stray(dd, List.reverse(&2, Trace.Row, rs)), Laws.trace.stray(dd, rs),
        Laws.trace.stray_laws(rest, List.reverse(&2, Trace.Row, rs)), Laws.trace.stray_laws(rest, rs),
        trace.stray_rev(dd, rs), trace.stray_laws_rev(rest, rs))

# each file's stray tags are the same against the rows reversed
law trace.strays_rev:
  for ds: List<&2, Digest.Digest>
  for +rs: List<&2, Trace.Row>
  {Laws.trace.strays(ds, List.reverse(&2, Trace.Row, rs)) == Laws.trace.strays(ds, rs) : Nat}

def trace.strays_rev(ds, rs):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, norm, dir, il, lf, ex, tops, says, deps, uns, +laws}, +rest}:
      esc.add(Laws.trace.stray_laws(laws, List.reverse(&2, Trace.Row, rs)), Laws.trace.stray_laws(laws, rs),
        Laws.trace.strays(rest, List.reverse(&2, Trace.Row, rs)), Laws.trace.strays(rest, rs),
        trace.stray_laws_rev(laws, rs), trace.strays_rev(rest, rs))

# a mark when a test fails counts one exactly when it fails
law trace.mark:
  for cc: Bool
  for -xx: Trace.Mark
  {List.length(&2, Trace.Mark, Bool.pick(List<&2, Trace.Mark>, cc, [], [xx])) == Bool.pick(Nat, cc, 0n, 1n) : Nat}

def trace.mark(cc, _xx):
  match cc:
    case True{}:
      {==}
    case False{}:
      {==}

# the marks a line adds are the spec's count of it
law trace.bad_len:
  for kk: Laws.trace.Line
  for mm: Trace.Mode
  for +tt: String
  for +nn: U32
  {List.length(&2, Trace.Mark, trace.bad_at(kk, mm, tt, nn)) == Laws.trace.bad_at(kk, mm, tt) : Nat}

def trace.bad_len(kk, mm, tt, nn):
  match kk mm:
    case Laws.trace.Bar{} Trace.Reqs{}:
      trace.mark(Nat.is_eq(List.length(&2, String, Laws.trace.cells(tt)), 5n),
        Trace.Mark{"a requirement row has five cells", nn})
    case Laws.trace.Bar{} Trace.Trusts{}:
      trace.mark(Nat.is_eq(List.length(&2, String, Laws.trace.cells(tt)), 3n), Trace.Mark{"a trust row has three cells", nn})
    case Laws.trace.Bar{} Trace.Out{}:
      {==}
    case Laws.trace.Bar{} Trace.ReqHead{}:
      {==}
    case Laws.trace.Bar{} Trace.TrustHead{}:
      {==}
    case Laws.trace.ReqHeader{} _:
      {==}
    case Laws.trace.TrustHeader{} _:
      {==}
    case Laws.trace.Prose{} _:
      {==}

# the length of two lists joined is the sum of theirs
law trace.len_app:
  for -A: Data
  for xs: List<&2, A>
  for -ys: List<&2, A>
  {List.length(&2, A, List.append(&2, A, xs, ys)) == Nat.add(List.length(&2, A, xs), List.length(&2, A, ys)) : Nat}

def trace.len_app(A, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{hh, tl}:
      Equal.cong(Nat, Nat, nx => 1n+nx, List.length(&2, A, List.append(&2, A, tl, ys)),
        Nat.add(List.length(&2, A, tl), List.length(&2, A, ys)), trace.len_app(A, tl, ys))

# the marks of the lines are the spec's count of rows with the wrong number of cells
law trace.bads_len:
  for ls: List<&2, String>
  for +nn: U32
  for +mm: Trace.Mode
  {List.length(&2, Trace.Mark, trace.bads(ls, nn, mm)) == Laws.trace.bad(ls, mm) : Nat}

def trace.bads_len(ls, nn, mm):
  match ls:
    case Nil{}:
      {==}
    case Con{+ll, +rest}:
      +tt = String.trim(ll)
      +kk = Laws.trace.line(tt)
      Equal.trans(Nat, List.length(&2, Trace.Mark, trace.bads(ll <> rest, nn, mm)),
        Nat.add(List.length(&2, Trace.Mark, trace.bad_at(kk, mm, tt, nn)),
          List.length(&2, Trace.Mark, trace.bads(rest, (nn + 1 : U32), Laws.trace.after(kk, mm)))),
        Laws.trace.bad(ll <> rest, mm),
        trace.len_app(Trace.Mark, trace.bad_at(kk, mm, tt, nn), trace.bads(rest, (nn + 1 : U32),
          Laws.trace.after(kk, mm))),
        esc.add(List.length(&2, Trace.Mark, trace.bad_at(kk, mm, tt, nn)), Laws.trace.bad_at(kk, mm, tt),
          List.length(&2, Trace.Mark, trace.bads(rest, (nn + 1 : U32), Laws.trace.after(kk, mm))),
          Laws.trace.bad(rest, Laws.trace.after(kk, mm)), trace.bad_len(kk, mm, tt, nn),
          trace.bads_len(rest, (nn + 1 : U32), Laws.trace.after(kk, mm))))

# a list joined with nothing is itself
law trace.app_nil:
  for -A: Data
  for xs: List<&2, A>
  {List.append(&2, A, xs, []) == xs : List<&2, A>}

def trace.app_nil(A, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{hh, tl}:
      Equal.cong(List<&2, A>, List<&2, A>, ys => hh <> ys, List.append(&2, A, tl, []), tl, trace.app_nil(A, tl))

# reversing a list reversed onto an accumulator
law trace.rev_rev_go:
  for -A: Data
  for xs: List<&2, A>
  for acc: List<&2, A>
  for ys: List<&2, A>
  {List.reverse.go(&2, A, List.reverse.go(&2, A, xs, acc), ys) == List.reverse.go(&2, A, acc, List.append(&2, A,
    xs, ys))
    : List<&2, A>}

def trace.rev_rev_go(A, xs, acc, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{hh, tl}:
      trace.rev_rev_go(A, tl, hh <> acc, ys)

# a list reversed twice is itself
law trace.rev_rev:
  for -A: Data
  for +xs: List<&2, A>
  {List.reverse(&2, A, List.reverse(&2, A, xs)) == xs : List<&2, A>}

def trace.rev_rev(A, xs):
  Equal.trans(List<&2, A>, List.reverse(&2, A, List.reverse(&2, A, xs)), List.append(&2, A, xs, []), xs,
    trace.rev_rev_go(A, xs, [], []), trace.app_nil(A, xs))

# one finding for each malformed row
law trace.malformed:
  for ms: List<&2, Trace.Mark>
  {List.length(&2, F.Finding, Trace.malformed(ms)) == List.length(&2, Trace.Mark, ms) : Nat}

def trace.malformed(ms):
  match ms:
    case Nil{}:
      {==}
    case Con{Trace.Mark{why, nn}, rest}:
      Equal.cong(Nat, Nat, nx => 1n+nx, List.length(&2, F.Finding, Trace.malformed(rest)),
        List.length(&2, Trace.Mark, rest), trace.malformed(rest))

# four finding lists joined count the sum of their counts
law trace.len4:
  for +p1: List<&2, F.Finding>
  for +p2: List<&2, F.Finding>
  for +p3: List<&2, F.Finding>
  for +p4: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [p1, p2, p3, p4]))
    == Nat.add(List.length(&2, F.Finding, p1), Nat.add(List.length(&2, F.Finding, p2),
      Nat.add(List.length(&2, F.Finding, p3), List.length(&2, F.Finding, p4)))) : Nat}

def trace.len4(p1, p2, p3, p4):
  +l1 = List.length(&2, F.Finding, p1)
  +l2 = List.length(&2, F.Finding, p2)
  +l3 = List.length(&2, F.Finding, p3)
  +l4 = List.length(&2, F.Finding, p4)
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [p1, p2, p3, p4, []])),
    Nat.add(l1, Nat.add(l2, Nat.add(l3, Nat.add(l4, 0n)))), Nat.add(l1, Nat.add(l2, Nat.add(l3, l4))),
    trace.len5(p1, p2, p3, p4, []),
    Equal.cong(Nat, Nat, nx => Nat.add(l1, Nat.add(l2, Nat.add(l3, nx))), Nat.add(l4, 0n), l4, trace.add0(l4)))

def Laws.trace_named(_mm, _ds):
  {==}

def Laws.trace_unread(_ds):
  {==}

def Laws.trace_counts(text, ds):
  +ls = String.lines(text)
  +rs = Laws.trace.reqs(ls, 0, Trace.Out{})
  +ts = Laws.trace.trusts(ls, 0, Trace.Out{})
  +bs = trace.bads(ls, 0, Trace.Out{})
  +r0 = List.reverse(&2, Trace.Row, rs)
  +t0 = List.reverse(&2, Trace.Mark, ts)
  +b0 = List.reverse(&2, Trace.Mark, bs)
  +sp = {Trace.Spec{trace.last(ls, Trace.Out{}), r0, t0, b0} : Trace.Spec}
  +p1 = Trace.malformed(List.reverse(&2, Trace.Mark, b0))
  +p2 = Trace.judge_rows(List.reverse(&2, Trace.Row, r0), sp, ds)
  +p3 = Trace.twins(List.reverse(&2, Trace.Mark, t0), t0)
  +p4 = Trace.strays(ds, r0)
  +ea = Equal.trans(Nat, List.length(&2, F.Finding, p1), List.length(&2, Trace.Mark, List.reverse(&2, Trace.Mark, b0)),
    Laws.trace.bad(ls, Trace.Out{}), trace.malformed(List.reverse(&2, Trace.Mark, b0)),
    Equal.trans(Nat, List.length(&2, Trace.Mark, List.reverse(&2, Trace.Mark, b0)), List.length(&2, Trace.Mark, bs),
      Laws.trace.bad(ls, Trace.Out{}),
      Equal.cong(List<&2, Trace.Mark>, Nat, xs => List.length(&2, Trace.Mark, xs), List.reverse(&2, Trace.Mark, b0), bs,
        trace.rev_rev(Trace.Mark, bs)),
      trace.bads_len(ls, 0, Trace.Out{})))
  +eb = Equal.trans(Nat, List.length(&2, F.Finding, p2), List.length(&2, F.Finding, Trace.judge_rows(rs, sp, ds)),
    Laws.trace.rows(rs, rs, ts, ds),
    Equal.cong(List<&2, Trace.Row>, Nat, xs => List.length(&2, F.Finding, Trace.judge_rows(xs, sp, ds)),
      List.reverse(&2, Trace.Row, r0), rs, trace.rev_rev(Trace.Row, rs)),
    Equal.trans(Nat, List.length(&2, F.Finding, Trace.judge_rows(rs, sp, ds)), Laws.trace.rows(rs, r0, t0, ds),
      Laws.trace.rows(rs, rs, ts, ds), trace.rows(rs, trace.last(ls, Trace.Out{}), r0, t0, b0, ds),
      trace.rows_rev(rs, rs, ts, ds)))
  +ec = Equal.trans(Nat, List.length(&2, F.Finding, p3), List.length(&2, F.Finding, Trace.twins(ts, t0)),
    Laws.trace.trust(ts, ts),
    Equal.cong(List<&2, Trace.Mark>, Nat, xs => List.length(&2, F.Finding, Trace.twins(xs, t0)),
      List.reverse(&2, Trace.Mark, t0), ts, trace.rev_rev(Trace.Mark, ts)),
    Equal.trans(Nat, List.length(&2, F.Finding, Trace.twins(ts, t0)), Laws.trace.trust(ts, t0),
      Laws.trace.trust(ts, ts),
      trace.twins(ts, t0), trace.trust_rev(ts, ts)))
  +ed = Equal.trans(Nat, List.length(&2, F.Finding, p4), Laws.trace.strays(ds, r0), Laws.trace.strays(ds, rs),
    trace.strays(ds, r0), trace.strays_rev(ds, rs))
  Equal.trans(Nat, List.length(&2, F.Finding, Trace.check(True{}, Some{text}, ds)),
    List.length(&2, F.Finding, Trace.check.spec(sp, ds)), Laws.trace.count(ls, ds),
    Equal.cong(Trace.Spec, Nat, sx => List.length(&2, F.Finding, Trace.check.spec(sx, ds)),
      Trace.parse.go(ls, 0, Trace.Spec{Trace.Out{}, [], [], []}), sp, trace.parse(ls, 0, Trace.Out{}, [], [], [])),
    Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [p1, p2, p3, p4])),
      Nat.add(List.length(&2, F.Finding, p1), Nat.add(List.length(&2, F.Finding, p2),
        Nat.add(List.length(&2, F.Finding, p3), List.length(&2, F.Finding, p4)))),
      Laws.trace.count(ls, ds), trace.len4(p1, p2, p3, p4),
      esc.add(List.length(&2, F.Finding, p1), Laws.trace.bad(ls, Trace.Out{}),
        Nat.add(List.length(&2, F.Finding, p2), Nat.add(List.length(&2, F.Finding, p3), List.length(&2, F.Finding,
          p4))),
        Nat.add(Laws.trace.rows(rs, rs, ts, ds), Nat.add(Laws.trace.trust(ts, ts), Laws.trace.strays(ds, rs))), ea,
        esc.add(List.length(&2, F.Finding, p2), Laws.trace.rows(rs, rs, ts, ds),
          Nat.add(List.length(&2, F.Finding, p3), List.length(&2, F.Finding, p4)),
          Nat.add(Laws.trace.trust(ts, ts), Laws.trace.strays(ds, rs)), eb,
          esc.add(List.length(&2, F.Finding, p3), Laws.trace.trust(ts, ts), List.length(&2, F.Finding, p4),
            Laws.trace.strays(ds, rs), ec, ed)))))
