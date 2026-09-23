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
          Bool.not(Bool.or(z, Bool.or(Bool.not(String.contains(T.code(note), ":")),
            String.ends_with(T.code(note), ": Quant"))))),
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
        "Parameter " ++ nm ++ " is too short; use at least 2 characters."},
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
        F.Finding{path, l, c, 7, "put", "Map.put does not compare keys, so a new key can overwrite an existing entry; use Map.set."},
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
          F.Finding{path, l, c, Hole.check.width(rest, l, c), "hole", "This ?TODO hole is still unfilled."},
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
      nat.pick(U32.is_gt(acc, 120), F.Finding{path, nn, 120, 0, "space", "Line is longer than 120 characters."},
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
      nat.pick(U32.is_gt(acc, 120), F.Finding{path, nn, 120, 0, "space", "Line is longer than 120 characters."},
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
  %s : {Bool.or(_, Calls.proof(sig)) == True{} : Bool}
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

def Laws.doc_exempt(path, text, toks, _tree, _bound, items, e):
  ex.stop(Bool.or(Paths.is_proof(path), Paths.is_test(path)), e,
    _u => Doc.check.go(items, path, Doc.lines(text, toks)))

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

# an or whose second side ends in a true or holds whatever the rest is
law ex.or_true:
  for a: Bool
  for b: Bool
  {Bool.or(a, Bool.or(b, True{})) == True{} : Bool}

def ex.or_true(a, b):
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def Laws.untyped_exempt(path, sig, e):
  %Equal.sym(Bool, Calls.typed(sig), False{}, e) :
    {Bool.or(Paths.is_law_file(path), Bool.or(Calls.returns_proof(sig), Bool.not(_))) == True{} : Bool}
  ex.or_true(Paths.is_law_file(path), Calls.returns_proof(sig))

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
        "This match has " ++ U32.show(n) ++ " character-literal cases, over the limit of 8, which blows up compile time"
        ++ " and memory; compare Char.to_u32(c) instead."})),
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
    "This match has " ++ U32.show(nn) ++ " string-literal cases totalling " ++ U32.show(ch)
    ++ " characters, over the limit of 64, which blows up compile time and memory;"
    ++ " map the string to a sum type once and match on that."})

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
      "This call to " ++ name ++ " is not a tail call, so a long list or string overflows the stack on the JS lane; carry an accumulator."},
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
            "Unreachable: the case " ++ text ++ " above already matches everything from " ++ U32.show(j)
              ++ "n up; put narrower arms first."}, more, m, ih)
        case Arms.ALit{+j, +l, +c, +n}:
          nat.pick(U32.is_ge(j, k), F.Finding{path, l, c, n, "arms",
            "Unreachable: the case " ++ text ++ " above already matches " ++ U32.show(j)
              ++ "n; put narrower arms first."}, more, m, ih)
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
        "This literal appears twice in one list pattern, which makes the checker hang; match one element per step."},
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
                          name ++ " calls itself in both branches of Bool.pick, which evaluates both, so both calls run; bind the call once above the pick."},
                        F.Finding{path, l, c, 9, "pick",
                          name ++ " calls itself in one branch of Bool.pick, which evaluates both, so the call always runs and never exits early; use Lazy.stop."},
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
      name ++ " calls itself inside Bool.and or Bool.or, which evaluate both sides, so there is no short-circuit; match on the Bool in a helper."},
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
      ++ " has no `for` or `exs` binder, so it checks a single case; quantify it or delete it."} : F.Finding}
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

# the kind and name test, to the rule and to the law
law doc.needs:
  for kk: Outline.ItemKind
  for +name: String
  {Bool.and(Doc.needs(kk), Bool.not(Doc.exempt(name))) == Bool.and(Laws.doc.kind(kk), Bool.not(Laws.doc.free(name)))
    : Bool}

def doc.needs(kk, _name):
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
  {Lazy.and_then(Bool.and(Doc.needs(kk), Bool.not(Doc.exempt(name))), _u => Bool.not(Doc.check.above(lines, line)))
    == Laws.doc.bare(kk, name, line, doc, lines) : Bool}

def doc.hit(kk, name, line, _doc, lines):
  +ar = Bool.and(Doc.needs(kk), Bool.not(Doc.exempt(name)))
  +as = Bool.and(Laws.doc.kind(kk), Bool.not(Laws.doc.free(name)))
  +ns = Bool.not(Bool.and(Bool.not(U32.is_eq(line, 0)), Laws.doc.hash(lines, U32.sub(line, 1))))
  Equal.trans(Bool, Lazy.and_then(ar, _u => Bool.not(Doc.check.above(lines, line))), Bool.and(ar, ns),
    Bool.and(as, ns),
    hole.and(ar, Bool.not(Doc.check.above(lines, line)), ns,
      Equal.cong(Bool, Bool, z => Bool.not(z), Doc.check.above(lines, line),
        Bool.and(Bool.not(U32.is_eq(line, 0)), Laws.doc.hash(lines, U32.sub(line, 1))), doc.above(lines, line))),
    Equal.cong(Bool, Bool, z => Bool.and(z, ns), ar, as, doc.needs(kk, name)))

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
  +hr = Lazy.and_then(Bool.and(Doc.needs(kk), Bool.not(Doc.exempt(name))), _u => Bool.not(Doc.check.above(lines, line)))
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

def Laws.doc_counts(path, text, toks, _tree, _bound, items):
  param.stop(Bool.or(Paths.is_proof(path), Paths.is_test(path)), Doc.check.go(items, path, Doc.lines(text, toks)),
    Laws.doc.count(items, Doc.lines(text, toks)), Laws.doc_walk_counts(items, path, Doc.lines(text, toks)))

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
    t ++ " in a recursive def walks the list from its head on every step, which is quadratic; recurse over the list itself."}
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
        t ++ " is appended to on every step, which copies it each time and makes the loop quadratic; prepend and reverse once at the end, or build with <>."},
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
          t ++ " is called in a branch of Bool.pick, which evaluates both branches, so it runs whatever the condition; bind it above the pick, or use Lazy.stop."},
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
                        "The fuel is fixed at " ++ t ++ ", so longer input is silently cut short; derive the fuel from the input size."})
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
      F.Finding{path, line, 120, 0, "wrap", "This def header is longer than 120 characters; wrap it with one parameter per line."},
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
            Laws.coverage.gaps(rest, all, pp, path), F.Finding{path, line, 0, 0, "coverage", "No quantified law names def " ++ name ++ "."}
              <> Laws.coverage.gaps(rest, all, pp, path)) : List<&2, F.Finding>}
      %coverage.gaps(rest, all, pp, path) :
        {Coverage.gaps(Digest.Top{Outline.IDef{}, name, line, cs} <> rest, Coverage.named(all), pp, path)
          == Bool.pick(List<&2, F.Finding>,
            Bool.or(String.contains(name, "."), Coverage.has_item(Coverage.named(all), pp, name)), _,
            F.Finding{path, line, 0, 0, "coverage", "No quantified law names def " ++ name ++ "."} <> _) : List<&2, F.Finding>}
      {==}
    case Con{Digest.Top{Outline.IType{}, +name, +line, +cs}, rest}:
      %coverage.item(all, pp, name) :
        {Coverage.gaps(Digest.Top{Outline.IType{}, name, line, cs} <> rest, Coverage.named(all), pp, path)
          == Bool.pick(List<&2, F.Finding>, Bool.or(_, Laws.coverage.any(cs, all, pp)),
            Laws.coverage.gaps(rest, all, pp, path), F.Finding{path, line, 0, 0, "coverage", "No quantified law names type " ++ name ++ " or any of its constructors."}
              <> Laws.coverage.gaps(rest, all, pp, path)) : List<&2, F.Finding>}
      %coverage.any(cs, all, pp) :
        {Coverage.gaps(Digest.Top{Outline.IType{}, name, line, cs} <> rest, Coverage.named(all), pp, path)
          == Bool.pick(List<&2, F.Finding>, Bool.or(Coverage.has_item(Coverage.named(all), pp, name), _),
            Laws.coverage.gaps(rest, all, pp, path), F.Finding{path, line, 0, 0, "coverage", "No quantified law names type " ++ name ++ " or any of its constructors."}
              <> Laws.coverage.gaps(rest, all, pp, path)) : List<&2, F.Finding>}
      %coverage.gaps(rest, all, pp, path) :
        {Coverage.gaps(Digest.Top{Outline.IType{}, name, line, cs} <> rest, Coverage.named(all), pp, path)
          == Bool.pick(List<&2, F.Finding>,
            Bool.or(Coverage.has_item(Coverage.named(all), pp, name),
              Coverage.any_item(cs, Coverage.named(all), pp)), _,
            F.Finding{path, line, 0, 0, "coverage", "No quantified law names type " ++ name ++ " or any of its constructors."}
              <> _) : List<&2, F.Finding>}
      Equal.cong(Bool, List<&2, F.Finding>,
        bb => Bool.pick(List<&2, F.Finding>, bb, Coverage.gaps(rest, Coverage.named(all), pp, path),
          F.Finding{path, line, 0, 0, "coverage", "No quantified law names type " ++ name ++ " or any of its constructors."}
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
        t => F.Finding{path, l, c, 7, "unsafe", "@unsafe def " ++ n ++ " is reachable from " ++ origin
          ++ ", where the checker skips its termination check and still exits 0; recurse on a shrinking argument or on fuel, and drop @unsafe."} <> t,
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

def Laws.scope_digest_exempt(_path, _text, _toks, _tree, _bound, _items, _text2, _toks2, _tree2, _bound2, _items2):
  {==}

# two finding lists that are both empty are equal
law scope.same:
  for -a: List<&2, F.Finding>
  for -b: List<&2, F.Finding>
  for ea: {a == Nil{} : List<&2, F.Finding>}
  for eb: {b == Nil{} : List<&2, F.Finding>}
  {a == b : List<&2, F.Finding>}

def scope.same(a, b, ea, eb):
  Equal.trans(List<&2, F.Finding>, a, Nil{}, b, ea, Equal.sym(List<&2, F.Finding>, b, Nil{}, eb))

def Laws.scope_hole(path, text, toks, tree, bound, items, text2, toks2, tree2, bound2, items2, e):
  scope.same(Hole.check(Src.Src{path, text, toks, tree, bound, items}),
    Hole.check(Src.Src{path, text2, toks2, tree2, bound2, items2}),
    Laws.hole_exempt(path, text, toks, tree, bound, items, e),
    Laws.hole_exempt(path, text2, toks2, tree2, bound2, items2, e))

def Laws.scope_doc(path, text, toks, tree, bound, items, text2, toks2, tree2, bound2, items2, e):
  scope.same(Doc.check(Src.Src{path, text, toks, tree, bound, items}),
    Doc.check(Src.Src{path, text2, toks2, tree2, bound2, items2}),
    Laws.doc_exempt(path, text, toks, tree, bound, items, e),
    Laws.doc_exempt(path, text2, toks2, tree2, bound2, items2, e))

def Laws.scope_param(path, text, toks, tree, bound, items, text2, toks2, tree2, bound2, items2, e):
  scope.same(Param.check(Src.Src{path, text, toks, tree, bound, items}),
    Param.check(Src.Src{path, text2, toks2, tree2, bound2, items2}),
    Laws.param_exempt(path, text, toks, tree, bound, items, e),
    Laws.param_exempt(path, text2, toks2, tree2, bound2, items2, e))

# two empty heads onto equal tails make equal lists
law scope.con:
  for -x: List<&2, F.Finding>
  for -y: List<&2, F.Finding>
  for ex: {x == Nil{} : List<&2, F.Finding>}
  for ey: {y == Nil{} : List<&2, F.Finding>}
  for -xs: List<&2, List<&2, F.Finding>>
  for -ys: List<&2, List<&2, F.Finding>>
  for ih: {xs == ys : List<&2, List<&2, F.Finding>>}
  {x <> xs == y <> ys : List<&2, List<&2, F.Finding>>}

def scope.con(x, y, ex, ey, xs, ys, ih):
  sx = Equal.sym(List<&2, F.Finding>, x, Nil{}, ex)
  sy = Equal.sym(List<&2, F.Finding>, y, Nil{}, ey)
  %sx : {_ <> xs == y <> ys : List<&2, List<&2, F.Finding>>}
  %sy : {Nil{} <> xs == _ <> ys : List<&2, List<&2, F.Finding>>}
  %ih : {Nil{} <> xs == Nil{} <> _ : List<&2, List<&2, F.Finding>>}
  {==}

def Laws.scope_law_file(path, text, toks, tree, bound, items, text2, toks2, tree2, bound2, items2, e):
  +s = {Src.Src{path, text, toks, tree, bound, items} : Src.Src}
  +t = {Src.Src{path, text2, toks2, tree2, bound2, items2} : Src.Src}
  scope.con(Pick.check(s), Pick.check(t),
    Laws.pick_exempt(path, text, toks, tree, bound, items, e),
    Laws.pick_exempt(path, text2, toks2, tree2, bound2, items2, e),
    [Tail.check(s), Concat.check(s), Eager.check(s), Rewalk.check(s), Strict.check(s),
      Hoist.check(s), Index.check(s), Ring.check(s), Table.check(s), UnitRule.check(s)],
    [Tail.check(t), Concat.check(t), Eager.check(t), Rewalk.check(t), Strict.check(t),
      Hoist.check(t), Index.check(t), Ring.check(t), Table.check(t), UnitRule.check(t)],
  scope.con(Tail.check(s), Tail.check(t),
    Laws.tail_exempt(path, text, toks, tree, bound, items, e),
    Laws.tail_exempt(path, text2, toks2, tree2, bound2, items2, e),
    [Concat.check(s), Eager.check(s), Rewalk.check(s), Strict.check(s), Hoist.check(s),
      Index.check(s), Ring.check(s), Table.check(s), UnitRule.check(s)],
    [Concat.check(t), Eager.check(t), Rewalk.check(t), Strict.check(t), Hoist.check(t),
      Index.check(t), Ring.check(t), Table.check(t), UnitRule.check(t)],
  scope.con(Concat.check(s), Concat.check(t),
    Laws.concat_exempt(path, text, toks, tree, bound, items, e),
    Laws.concat_exempt(path, text2, toks2, tree2, bound2, items2, e),
    [Eager.check(s), Rewalk.check(s), Strict.check(s), Hoist.check(s), Index.check(s),
      Ring.check(s), Table.check(s), UnitRule.check(s)],
    [Eager.check(t), Rewalk.check(t), Strict.check(t), Hoist.check(t), Index.check(t),
      Ring.check(t), Table.check(t), UnitRule.check(t)],
  scope.con(Eager.check(s), Eager.check(t),
    Laws.eager_exempt(path, text, toks, tree, bound, items, e),
    Laws.eager_exempt(path, text2, toks2, tree2, bound2, items2, e),
    [Rewalk.check(s), Strict.check(s), Hoist.check(s), Index.check(s), Ring.check(s),
      Table.check(s), UnitRule.check(s)],
    [Rewalk.check(t), Strict.check(t), Hoist.check(t), Index.check(t), Ring.check(t),
      Table.check(t), UnitRule.check(t)],
  scope.con(Rewalk.check(s), Rewalk.check(t),
    Laws.rewalk_exempt(path, text, toks, tree, bound, items, e),
    Laws.rewalk_exempt(path, text2, toks2, tree2, bound2, items2, e),
    [Strict.check(s), Hoist.check(s), Index.check(s), Ring.check(s), Table.check(s),
      UnitRule.check(s)],
    [Strict.check(t), Hoist.check(t), Index.check(t), Ring.check(t), Table.check(t),
      UnitRule.check(t)],
  scope.con(Strict.check(s), Strict.check(t),
    Laws.strict_exempt(path, text, toks, tree, bound, items, e),
    Laws.strict_exempt(path, text2, toks2, tree2, bound2, items2, e),
    [Hoist.check(s), Index.check(s), Ring.check(s), Table.check(s), UnitRule.check(s)],
    [Hoist.check(t), Index.check(t), Ring.check(t), Table.check(t), UnitRule.check(t)],
  scope.con(Hoist.check(s), Hoist.check(t),
    Laws.hoist_exempt(path, text, toks, tree, bound, items, e),
    Laws.hoist_exempt(path, text2, toks2, tree2, bound2, items2, e),
    [Index.check(s), Ring.check(s), Table.check(s), UnitRule.check(s)],
    [Index.check(t), Ring.check(t), Table.check(t), UnitRule.check(t)],
  scope.con(Index.check(s), Index.check(t),
    Laws.index_exempt(path, text, toks, tree, bound, items, e),
    Laws.index_exempt(path, text2, toks2, tree2, bound2, items2, e),
    [Ring.check(s), Table.check(s), UnitRule.check(s)],
    [Ring.check(t), Table.check(t), UnitRule.check(t)],
  scope.con(Ring.check(s), Ring.check(t),
    Laws.ring_exempt(path, text, toks, tree, bound, items, e),
    Laws.ring_exempt(path, text2, toks2, tree2, bound2, items2, e),
    [Table.check(s), UnitRule.check(s)],
    [Table.check(t), UnitRule.check(t)],
  scope.con(Table.check(s), Table.check(t),
    Laws.table_exempt(path, text, toks, tree, bound, items, e),
    Laws.table_exempt(path, text2, toks2, tree2, bound2, items2, e),
    [UnitRule.check(s)],
    [UnitRule.check(t)],
  scope.con(UnitRule.check(s), UnitRule.check(t),
    Laws.unit_exempt(path, text, toks, tree, bound, items, e),
    Laws.unit_exempt(path, text2, toks2, tree2, bound2, items2, e),
    Nil{},
    Nil{},
  {==})))))))))))

# closed reports nothing outside a LAWS.bend
law scope.closed:
  for +path: String
  for tree: Tree.Node
  for e: {Paths.is_laws(path) == False{} : Bool}
  {Lazy.stop(List<&2, F.Finding>, Bool.not(Paths.is_laws(path)), [], _u => Closed.check.go(tree, path))
    == Nil{} : List<&2, F.Finding>}

def scope.closed(path, tree, e):
  s = Equal.sym(Bool, Paths.is_laws(path), False{}, e)
  %s : {Lazy.stop(List<&2, F.Finding>, Bool.not(_), [], _u => Closed.check.go(tree, path))
    == Nil{} : List<&2, F.Finding>}
  {==}

def Laws.scope_closed(path, text, toks, tree, bound, items, text2, toks2, tree2, bound2, items2, e):
  scope.same(Closed.check(Src.Src{path, text, toks, tree, bound, items}),
    Closed.check(Src.Src{path, text2, toks2, tree2, bound2, items2}),
    scope.closed(path, tree, e), scope.closed(path, tree2, e))

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
    [Trace.Mark{"a requirement row must have five cells", nn}])

# the malformed-row mark a trust table line of these cells adds
def trace.bad3(+cs: List<&2, String>, +nn: U32) -> List<&2, Trace.Mark>:
  Bool.pick(List<&2, Trace.Mark>, Nat.is_eq(List.length(&2, String, cs), 3n), [],
    [Trace.Mark{"a trust row must have three cells", nn}])

# a requirement table line of any cells adds the spec's row, or a mark
law trace.five:
  for +cs: List<&2, String>
  for +nn: U32
  for +mm: Trace.Mode
  for +rr: List<&2, Trace.Row>
  for +tt: List<&2, Trace.Mark>
  for +bb: List<&2, Trace.Mark>
  {Lazy.stop(Trace.Spec, Bool.not(Nat.is_eq(List.length(&2, String, cs), 5n)),
    Trace.Spec{mm, rr, tt, Trace.Mark{"a requirement row must have five cells", nn} <> bb},
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
    Trace.Spec{mm, rr, tt, Trace.Mark{"a trust row must have three cells", nn} <> bb})
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
    "the level must be Proved or Trusted, and the status proved or pending for Proved, empty for Trusted",
    Bool.pick(String, yy, "a proved row must name its law", Bool.pick(String, zz, "a Trusted row must not name a law", "")))))
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
      +xb = Trace.at(nn, id ++ " names " ++ entry ++ ", a law with no `for` or `exs` binder.")
      +xt = Trace.at(nn, id ++ " names " ++ entry ++ ", but that law is not tagged # " ++ id ++ ".")
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
    [Trace.at(nn, id ++ ": a Law entry must be <path> <law>, not " ++ entry ++ ".")],
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
  +x1 = Trace.at(nn, id ++ " is not a valid ID; an ID matches [A-Z][A-Z0-9]*(-[A-Z0-9]+)+.")
  +x2 = Trace.at(nn, id ++ " is listed twice.")
  +x3 = Trace.at(nn, id ++ ": " ++ why ++ ".")
  +x4 = Trace.at(nn, id ++ " is Trusted but has no row in the trust boundary table.")
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
      +x1 = Trace.at(nn, id ++ " is not a valid ID; an ID matches [A-Z][A-Z0-9]*(-[A-Z0-9]+)+.")
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
        "Law " ++ name ++ " is tagged " ++ tt ++ ", which is not a Proved row in SPEC.md with status proved or pending."} : F.Finding}
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
        Trace.Mark{"a requirement row must have five cells", nn})
    case Laws.trace.Bar{} Trace.Trusts{}:
      trace.mark(Nat.is_eq(List.length(&2, String, Laws.trace.cells(tt)), 3n), Trace.Mark{"a trust row must have three cells", nn})
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

# coverage's reading of a file (BOLT-LAW-1)

# the digest's constructors of a type are coverage.ctors_of
law coverage.d_ctors:
  for items: List<&2, Outline.Item>
  {Digest.ctors(items) == Laws.coverage.ctors_of(items) : List<&2, String>}

def coverage.d_ctors(items):
  match items:
    case Nil{}:
      {==}
    case Con{Outline.Item{kk, +name, +line, sig, doc, path}, +rest}:
      match kk:
        case Outline.ICtor{}:
          Equal.cong(List<&2, String>, List<&2, String>, xs => name <> xs, Digest.ctors(rest),
            Laws.coverage.ctors_of(rest), coverage.d_ctors(rest))
        case Outline.IImport{}:
          {==}
        case Outline.IDef{}:
          {==}
        case Outline.ILaw{}:
          {==}
        case Outline.IType{}:
          {==}
        case Outline.ILocal{}:
          {==}

# the digest's defs and types are coverage.tops
law coverage.d_tops:
  for items: List<&2, Outline.Item>
  {Digest.top_items(items) == Laws.coverage.tops(items) : List<&2, Digest.Top>}

def coverage.d_tops(items):
  match items:
    case Nil{}:
      {==}
    case Con{Outline.Item{kk, +name, +line, sig, doc, path}, +rest}:
      match kk:
        case Outline.IDef{}:
          Equal.cong(List<&2, Digest.Top>, List<&2, Digest.Top>, xs => Digest.Top{Outline.IDef{}, name, line, []} <> xs,
            Digest.top_items(rest), Laws.coverage.tops(rest), coverage.d_tops(rest))
        case Outline.IType{}:
          %coverage.d_ctors(rest) :
            {Digest.Top{Outline.IType{}, name, line, Digest.ctors(rest)} <> Digest.top_items(rest)
              == Digest.Top{Outline.IType{}, name, line, _} <> Laws.coverage.tops(rest)
              : List<&2, Digest.Top>}
          Equal.cong(List<&2, Digest.Top>, List<&2, Digest.Top>,
            xs => Digest.Top{Outline.IType{}, name, line, Digest.ctors(rest)} <> xs,
            Digest.top_items(rest), Laws.coverage.tops(rest), coverage.d_tops(rest))
        case Outline.IImport{}:
          coverage.d_tops(rest)
        case Outline.ILaw{}:
          coverage.d_tops(rest)
        case Outline.ICtor{}:
          coverage.d_tops(rest)
        case Outline.ILocal{}:
          coverage.d_tops(rest)

# the digest's alias lookup is coverage.alias
law coverage.d_alias:
  for items: List<&2, Outline.Item>
  for +name: String
  for +from: String
  {Digest.alias_path(Digest.aliases(items, from), name) == Laws.coverage.alias(items, name, from) : Maybe<&2, String>}

def coverage.d_alias(items, name, from):
  match items:
    case Nil{}:
      {==}
    case Con{Outline.Item{kk, +nm, line, sig, doc, +path}, +rest}:
      match kk:
        case Outline.IImport{}:
          Equal.cong(Maybe<&2, String>, Maybe<&2, String>,
            mm => Bool.pick(Maybe<&2, String>, String.eq(nm, name), Some{Imports.resolve(from, path)}, mm),
            Digest.alias_path(Digest.aliases(rest, from), name), Laws.coverage.alias(rest, name, from),
            coverage.d_alias(rest, name, from))
        case Outline.IDef{}:
          coverage.d_alias(rest, name, from)
        case Outline.ILaw{}:
          coverage.d_alias(rest, name, from)
        case Outline.IType{}:
          coverage.d_alias(rest, name, from)
        case Outline.ICtor{}:
          coverage.d_alias(rest, name, from)
        case Outline.ILocal{}:
          coverage.d_alias(rest, name, from)

# an item behind an alias, onto the others, is coverage.behind onto them
law coverage.d_aliased:
  for mm: Maybe<&2, String>
  for -name: String
  for -more: List<&2, Digest.Mention>
  {Digest.aliased(mm, name, more) == List.append(&2, Digest.Mention, Laws.coverage.behind(mm, name), more)
    : List<&2, Digest.Mention>}

def coverage.d_aliased(mm, _name, _more):
  match mm:
    case None{}:
      {==}
    case Some{_pp}:
      {==}

# what the digest makes of a use's target is coverage.target, onto the others
law coverage.d_target:
  for tt: Bind.Target
  for +items: List<&2, Outline.Item>
  for +file: String
  for +more: List<&2, Digest.Mention>
  {Digest.target(tt, Digest.aliases(items, file), file, more)
    == List.append(&2, Digest.Mention, Laws.coverage.target(tt, items, file), more) : List<&2, Digest.Mention>}

def coverage.d_target(tt, items, file, more):
  match tt:
    case Bind.TLocal{_l, _c}:
      {==}
    case Bind.TItem{_n}:
      {==}
    case Bind.TQual{+al, +name}:
      %Equal.sym(Maybe<&2, String>, Digest.alias_path(Digest.aliases(items, file), al),
          Laws.coverage.alias(items, al, file), coverage.d_alias(items, al, file)) :
        {Digest.aliased(_, name, more)
          == List.append(&2, Digest.Mention, Laws.coverage.behind(Laws.coverage.alias(items, al, file), name), more)
          : List<&2, Digest.Mention>}
      coverage.d_aliased(Laws.coverage.alias(items, al, file), name, more)
    case Bind.TFree{}:
      {==}

# a law's span, when the law binds, then the rest: the line is in one of them
# exactly when it is in the span of a binding law or in the rest
law coverage.d_span:
  for bb: Bool
  for +from: U32
  for +upto: U32
  for +rest: List<&2, Digest.Span>
  for +ln: U32
  {Digest.within(Bool.pick(List<&2, Digest.Span>, bb, Digest.Span{from, upto} <> rest, rest), ln)
    == Bool.or(Bool.and(bb, Bool.and(U32.is_le(from, ln), U32.is_le(ln, upto))), Digest.within(rest, ln)) : Bool}

def coverage.d_span(bb, from, upto, rest, ln):
  match bb:
    case True{}:
      coverage.or_else(Bool.and(U32.is_le(from, ln), U32.is_le(ln, upto)), Digest.within(rest, ln))
    case False{}:
      {==}

# the digest's test of a line against the spans is coverage.in_law
law coverage.d_within:
  for root: Tree.Node
  for +ln: U32
  {Digest.within(Digest.spans(root), ln) == Laws.coverage.in_law(root, ln) : Bool}

def coverage.d_within(root, ln):
  match root:
    case Tree.NCons{hd, +rest}:
      match hd:
        case Tree.Stmt{kk, +kids, +body}:
          match kk:
            case Tree.SLaw{}:
              +last = Tree.line.of(List.head(&2, Lex.Tok, Tree.leaves.go(body, [])))
              Equal.trans(Bool,
                Digest.within(Bool.pick(List<&2, Digest.Span>, Closed.binds(body),
                  Digest.Span{Tree.line(kids), last} <> Digest.spans(rest), Digest.spans(rest)), ln),
                Bool.or(Bool.and(Closed.binds(body), Bool.and(U32.is_le(Tree.line(kids), ln), U32.is_le(ln, last))),
                  Digest.within(Digest.spans(rest), ln)),
                Bool.or(Bool.and(Closed.binds(body), Bool.and(U32.is_le(Tree.line(kids), ln), U32.is_le(ln, last))),
                  Laws.coverage.in_law(rest, ln)),
                coverage.d_span(Closed.binds(body), Tree.line(kids), last, Digest.spans(rest), ln),
                Equal.cong(Bool, Bool,
                  b => Bool.or(Bool.and(Closed.binds(body),
                    Bool.and(U32.is_le(Tree.line(kids), ln), U32.is_le(ln, last))), b),
                  Digest.within(Digest.spans(rest), ln), Laws.coverage.in_law(rest, ln), coverage.d_within(rest, ln)))
            case Tree.SDef{}:
              coverage.d_within(rest, ln)
            case Tree.SType{}:
              coverage.d_within(rest, ln)
            case Tree.SImport{}:
              coverage.d_within(rest, ln)
            case Tree.SCase{}:
              coverage.d_within(rest, ln)
            case Tree.SFor{}:
              coverage.d_within(rest, ln)
            case Tree.SLet{}:
              coverage.d_within(rest, ln)
            case Tree.STerm{}:
              coverage.d_within(rest, ln)
        case Tree.Leaf{_tok}:
          coverage.d_within(rest, ln)
        case Tree.Group{_open, _kids, _close}:
          coverage.d_within(rest, ln)
        case Tree.NNil{}:
          coverage.d_within(rest, ln)
        case Tree.NCons{_h, _t}:
          coverage.d_within(rest, ln)
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_open, _kids, _close}:
      {==}
    case Tree.Stmt{_kk, _kids, _body}:
      {==}
    case Tree.NNil{}:
      {==}

# stopping on a negated test is picking on the test
law coverage.d_stop:
  for bb: Bool
  for -x: List<&2, Digest.Mention>
  for -y: List<&2, Digest.Mention>
  {Lazy.stop(List<&2, Digest.Mention>, Bool.not(bb), y, _u => x) == Bool.pick(List<&2, Digest.Mention>, bb, x, y)
    : List<&2, Digest.Mention>}

def coverage.d_stop(bb, _x, _y):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# the digest's mentions of the uses are coverage.said
law coverage.d_mentions:
  for us: List<&2, Bind.Use>
  for +root: Tree.Node
  for +items: List<&2, Outline.Item>
  for +file: String
  {Digest.mentions(us, Digest.spans(root), Digest.aliases(items, file), file)
    == Laws.coverage.said(us, root, items, file) : List<&2, Digest.Mention>}

def coverage.d_mentions(us, root, items, file):
  match us:
    case Nil{}:
      {==}
    case Con{Bind.Use{+nn, +ln, +cc, +tt}, +rest}:
      +mm = Digest.mentions(rest, Digest.spans(root), Digest.aliases(items, file), file)
      %coverage.d_mentions(rest, root, items, file) :
        {Digest.mentions(Bind.Use{nn, ln, cc, tt} <> rest, Digest.spans(root), Digest.aliases(items, file), file)
          == Bool.pick(List<&2, Digest.Mention>, Laws.coverage.in_law(root, ln),
            List.append(&2, Digest.Mention, Laws.coverage.target(tt, items, file), _), _) : List<&2, Digest.Mention>}
      %coverage.d_target(tt, items, file, mm) :
        {Digest.mentions(Bind.Use{nn, ln, cc, tt} <> rest, Digest.spans(root), Digest.aliases(items, file), file)
          == Bool.pick(List<&2, Digest.Mention>, Laws.coverage.in_law(root, ln), _, mm) : List<&2, Digest.Mention>}
      %coverage.d_within(root, ln) :
        {Digest.mentions(Bind.Use{nn, ln, cc, tt} <> rest, Digest.spans(root), Digest.aliases(items, file), file)
          == Bool.pick(List<&2, Digest.Mention>, _, Digest.target(tt, Digest.aliases(items, file), file, mm), mm)
          : List<&2, Digest.Mention>}
      coverage.d_stop(Digest.within(Digest.spans(root), ln), Digest.target(tt, Digest.aliases(items, file), file, mm),
        mm)

# what a file's laws name, in the digest, is coverage.said when it is a
# LAWS.bend, else nothing
law coverage.d_stated:
  for bb: Bool
  for +tree: Tree.Node
  for bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +file: String
  {Digest.stated(bb, tree, bound, Digest.aliases(items, file), file)
    == Bool.pick(List<&2, Digest.Mention>, bb, Laws.coverage.said(Laws.coverage.uses(bound), tree, items, file), [])
    : List<&2, Digest.Mention>}

def coverage.d_stated(bb, tree, bound, items, file):
  match bb:
    case True{}:
      match bound:
        case Bind.Bound{_bs, us, _scs}:
          coverage.d_mentions(us, tree, items, file)
    case False{}:
      {==}

def Laws.coverage_digest(path, text, toks, tree, bound, items):
  +pp = Imports.norm(path)
  %coverage.d_tops(items) :
    {Laws.coverage.view(Digest.of(Src.Src{path, text, toks, tree, bound, items}))
      == Laws.CoverageView{pp, Paths.is_laws(path), Bool.or(Paths.is_law_file(pp), Paths.is_test(pp)), _,
        Bool.pick(List<&2, Digest.Mention>, Paths.is_laws(path),
          Laws.coverage.said(Laws.coverage.uses(bound), tree, items, pp), [])} : Laws.CoverageView}
  %coverage.d_stated(Paths.is_laws(path), tree, bound, items, pp) :
    {Laws.coverage.view(Digest.of(Src.Src{path, text, toks, tree, bound, items}))
      == Laws.CoverageView{pp, Paths.is_laws(path), Bool.or(Paths.is_law_file(pp), Paths.is_test(pp)),
        Digest.top_items(items), _} : Laws.CoverageView}
  {==}

def Laws.coverage_binder(path, text):
  Laws.coverage_digest(path, text, Lex.tokens(text), Tree.parse(text),
    Bind.of_tree(Tree.parse(text), String.lines(text)), Outline.of_tokens(text, Lex.tokens(text)))

# unsafe (BOLT-LAW-3), the reach. Paths compare with String.eq, so the
# proofs need it sound and reflexive, down to the words a U32 is made of, as
# bolt/PROOF.bend's cfg4.seq does.

# Unit for False, Empty for True
def unsafe.false_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Unit
    case True{}:
      Empty

# False is never True
law unsafe.false_true:
  for e: {False{} == True{} : Bool}
  Empty

def unsafe.false_true(e):
  %e : unsafe.false_ty(_)
  Unit{}

# words that compare equal, bit by bit past the first: the rest equal, the
# first bits the same
law unsafe.weq.arm:
  for -p: Nat
  for -at: Word(p)
  for -bt: Word(p)
  for c: Cmp
  for ec: {Word.cmp(p, at, bt) == c : Cmp}
  for ih: {Cmp.is_eq(Word.cmp(p, at, bt)) == True{} : Bool} -> {at == bt : Word(p)}
  for ab: Bool
  for bb: Bool
  for e: {Cmp.is_eq(Word.cmp.fin(ab, bb, c)) == True{} : Bool}
  {WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}

def unsafe.weq.arm(p, at, bt, c, ec, ih, ab, bb, e):
  match c:
    case LT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, unsafe.false_true(e))
    case GT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, unsafe.false_true(e))
    case EQ{}:
      match ab bb:
        case False{} False{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{False{}, w}, at, bt,
            ih(Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, at, bt), EQ{}, ec)))
        case True{} True{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{True{}, w}, at, bt,
            ih(Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, at, bt), EQ{}, ec)))
        case False{} True{}:
          Empty.absurd({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, unsafe.false_true(e))
        case True{} False{}:
          Empty.absurd({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, unsafe.false_true(e))

# words that compare equal are equal
law unsafe.weq:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for e: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}
  {a == b : Word(n)}

def unsafe.weq(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          unsafe.weq.arm(p, at, bt, Word.cmp(p, at, bt), {==}, x => unsafe.weq(p, at, bt, x), ab, bb, e)

# U32s that compare equal are equal
law unsafe.ueq:
  for a: U32
  for b: U32
  for e: {U32.is_eq(a, b) == True{} : Bool}
  {a == b : U32}

def unsafe.ueq(a, b, e):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, unsafe.weq(32n, x, y, e))

# a compare that went on past equal first characters answers as the rest's
law unsafe.rec:
  for -h1: Char
  for -h2: Char
  for rr: (String & String) & Cmp
  {String.eq.fin(String.cmp.rec(h1, h2, rr)) == String.eq.fin(rr) : Bool}

def unsafe.rec(_h1, _h2, rr):
  ((_a, _b), _c) = rr
  {==}

# strings whose first characters compare as c and whose compare comes out
# equal: when c is equal and the rest are equal, they are equal
law unsafe.seq.arm:
  for +x: U32
  for +y: U32
  for +t1: String
  for +t2: String
  for c: Cmp
  for ec: {U32.cmp(x, y) == c : Cmp}
  for ih: {String.eq(t1, t2) == True{} : Bool} -> {t1 == t2 : String}
  for e: {String.eq.fin(String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), c))) == True{} : Bool}
  {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}

def unsafe.seq.arm(x, y, t1, t2, c, ec, ih, e):
  match c:
    case LT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, unsafe.false_true(e))
    case GT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, unsafe.false_true(e))
    case EQ{}:
      r = unsafe.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))
      et = ih(Equal.trans(Bool, String.eq(t1, t2), String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))),
        True{}, Equal.sym(Bool, String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))),
          String.eq(t1, t2), r), e))
      ex = unsafe.ueq(x, y, Equal.cong(Cmp, Bool, z => Cmp.is_eq(z), U32.cmp(x, y), EQ{}, ec))
      %ex : {SCon{Chr{x}, t1} == SCon{Chr{_}, t2} : String}
      %et : {SCon{Chr{x}, t1} == SCon{Chr{x}, _} : String}
      {==}

# strings that compare equal are equal
law unsafe.seq:
  for a: String
  for b: String
  for e: {String.eq(a, b) == True{} : Bool}
  {a == b : String}

def unsafe.seq(a, b, e):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      Empty.absurd({SNil{} == SCon{h, t} : String}, unsafe.false_true(e))
    case SCon{h, t} SNil{}:
      Empty.absurd({SCon{h, t} == SNil{} : String}, unsafe.false_true(e))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      unsafe.seq.arm(x, y, t1, t2, U32.cmp(x, y), {==}, z => unsafe.seq(t1, t2, z), e)

# a word compares equal to itself
law unsafe.wrefl:
  for n: Nat
  for +a: Word(n)
  {Word.cmp(n, a, a) == EQ{} : Cmp}

def unsafe.wrefl(n, a):
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      match a:
        case WCon{False{}, +at}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, unsafe.wrefl(p, at)) :
            {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
          {==}
        case WCon{True{}, +at}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, unsafe.wrefl(p, at)) :
            {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
          {==}

# a string is String.eq to itself
law unsafe.srefl:
  for +s: String
  {String.eq(s, s) == True{} : Bool}

def unsafe.srefl(s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{U32{+w}}, +t}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, unsafe.wrefl(32n, w)) :
        {String.eq.fin(String.cmp.fin(t, t, ((Chr{U32{w}}, Chr{U32{w}}), _))) == True{} : Bool}
      %Equal.sym(Bool, String.eq.fin(String.cmp.rec(Chr{U32{w}}, Chr{U32{w}}, String.cmp(t, t))),
          String.eq.fin(String.cmp(t, t)), unsafe.rec(Chr{U32{w}}, Chr{U32{w}}, String.cmp(t, t))) :
        {_ == True{} : Bool}
      unsafe.srefl(t)

# Bool facts the reach proofs lean on

# or with True on the right is True
law unsafe.or_true:
  for a: Bool
  {Bool.or(a, True{}) == True{} : Bool}

def unsafe.or_true(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# or with False on the right is the left
law unsafe.or_false:
  for a: Bool
  {Bool.or(a, False{}) == a : Bool}

def unsafe.or_false(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# or groups either way
law unsafe.or_assoc:
  for a: Bool
  for b: Bool
  for c: Bool
  {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}

def unsafe.or_assoc(a, _b, _c):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# or's first two arguments trade places
law unsafe.or_swap:
  for a: Bool
  for b: Bool
  for c: Bool
  {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}

def unsafe.or_swap(a, b, _c):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# or is True when its left is
law unsafe.or_l:
  for a: Bool
  for -b: Bool
  for e: {a == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def unsafe.or_l(a, b, e):
  %Equal.sym(Bool, a, True{}, e) : {Bool.or(_, b) == True{} : Bool}
  {==}

# or is True when its right is
law unsafe.or_r:
  for a: Bool
  for -b: Bool
  for e: {b == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def unsafe.or_r(a, _b, e):
  match a:
    case False{}:
      e
    case True{}:
      {==}

# a True and holds its left
law unsafe.and_l:
  for a: Bool
  for -b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def unsafe.and_l(a, _b, e):
  match a:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, unsafe.false_true(e))
    case True{}:
      {==}

# a True and holds its right
law unsafe.and_r:
  for a: Bool
  for -b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def unsafe.and_r(a, b, e):
  match a:
    case False{}:
      Empty.absurd({b == True{} : Bool}, unsafe.false_true(e))
    case True{}:
      e

# and of two Trues is True
law unsafe.and_true:
  for a: Bool
  for -b: Bool
  for ea: {a == True{} : Bool}
  for eb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def unsafe.and_true(a, b, ea, eb):
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# membership, as Imports.has reads it

# has over an append is has over either part
law unsafe.has_app:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  for +x: String
  {Imports.has(List.append(&2, String, xs, ys), x) == Bool.or(Imports.has(xs, x), Imports.has(ys, x)) : Bool}

def unsafe.has_app(xs, ys, x):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, Imports.has(List.append(&2, String, t, ys), x), Bool.or(Imports.has(t, x), Imports.has(ys, x)),
          unsafe.has_app(t, ys, x)) :
        {Bool.or(String.eq(h, x), _) == Bool.or(Bool.or(String.eq(h, x), Imports.has(t, x)), Imports.has(ys, x)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(String.eq(h, x), Imports.has(t, x)), Imports.has(ys, x)),
        Bool.or(String.eq(h, x), Bool.or(Imports.has(t, x), Imports.has(ys, x))),
        unsafe.or_assoc(String.eq(h, x), Imports.has(t, x), Imports.has(ys, x)))

# has over a reversal onto acc is has over either
law unsafe.has_rgo:
  for xs: List<&2, String>
  for +acc: List<&2, String>
  for +x: String
  {Imports.has(List.reverse.go(&2, String, xs, acc), x) == Bool.or(Imports.has(xs, x), Imports.has(acc, x)) : Bool}

def unsafe.has_rgo(xs, acc, x):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, Imports.has(List.reverse.go(&2, String, t, h <> acc), x),
          Bool.or(Imports.has(t, x), Bool.or(String.eq(h, x), Imports.has(acc, x))),
          unsafe.has_rgo(t, h <> acc, x)) :
        {_ == Bool.or(Bool.or(String.eq(h, x), Imports.has(t, x)), Imports.has(acc, x)) : Bool}
      %Equal.sym(Bool, Bool.or(Bool.or(String.eq(h, x), Imports.has(t, x)), Imports.has(acc, x)),
          Bool.or(String.eq(h, x), Bool.or(Imports.has(t, x), Imports.has(acc, x))),
          unsafe.or_assoc(String.eq(h, x), Imports.has(t, x), Imports.has(acc, x))) :
        {Bool.or(Imports.has(t, x), Bool.or(String.eq(h, x), Imports.has(acc, x))) == _ : Bool}
      unsafe.or_swap(Imports.has(t, x), String.eq(h, x), Imports.has(acc, x))

# has over a reversal is has
law unsafe.has_rev:
  for +xs: List<&2, String>
  for +x: String
  {Imports.has(List.reverse(&2, String, xs), x) == Imports.has(xs, x) : Bool}

def unsafe.has_rev(xs, x):
  Equal.trans(Bool, Imports.has(List.reverse(&2, String, xs), x), Bool.or(Imports.has(xs, x), False{}),
    Imports.has(xs, x), unsafe.has_rgo(xs, [], x), unsafe.or_false(Imports.has(xs, x)))

# every path of xs is held by ss
def unsafe.all_in(+ss: List<&2, String>, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      +more = unsafe.all_in(ss, rest)
      Bool.and(Imports.has(ss, x), more)

# the path h, String.eq to x or not, carried to has: when it is, ss has x
# because it has h
law unsafe.has_sub.at:
  for +ss: List<&2, String>
  for +h: String
  for -t: List<&2, String>
  for +x: String
  for b: Bool
  for eb: {String.eq(h, x) == b : Bool}
  for hh: {Imports.has(ss, h) == True{} : Bool}
  for hx: {Bool.or(b, Imports.has(t, x)) == True{} : Bool}
  for ih: {Imports.has(t, x) == True{} : Bool} -> {Imports.has(ss, x) == True{} : Bool}
  {Imports.has(ss, x) == True{} : Bool}

def unsafe.has_sub.at(ss, h, _t, x, b, eb, hh, hx, ih):
  match b:
    case True{}:
      %unsafe.seq(h, x, eb) : {Imports.has(ss, _) == True{} : Bool}
      hh
    case False{}:
      ih(hx)

# a path xs has is one ss has, when ss holds every path of xs
law unsafe.has_sub:
  for +ss: List<&2, String>
  for xs: List<&2, String>
  for +x: String
  for +ha: {unsafe.all_in(ss, xs) == True{} : Bool}
  for hx: {Imports.has(xs, x) == True{} : Bool}
  {Imports.has(ss, x) == True{} : Bool}

def unsafe.has_sub(ss, xs, x, ha, hx):
  match xs:
    case Nil{}:
      Empty.absurd({Imports.has(ss, x) == True{} : Bool}, unsafe.false_true(hx))
    case Con{+h, +t}:
      unsafe.has_sub.at(ss, h, t, x, String.eq(h, x), {==}, unsafe.and_l(Imports.has(ss, h), unsafe.all_in(ss, t), ha),
        hx, z => unsafe.has_sub(ss, t, x, unsafe.and_r(Imports.has(ss, h), unsafe.all_in(ss, t), ha), z))

# a list that holds xs, with more in front, still holds it
law unsafe.in_pre:
  for +aa: List<&2, String>
  for +ss: List<&2, String>
  for xs: List<&2, String>
  for +h: {unsafe.all_in(ss, xs) == True{} : Bool}
  {unsafe.all_in(List.append(&2, String, aa, ss), xs) == True{} : Bool}

def unsafe.in_pre(aa, ss, xs, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      unsafe.and_true(Imports.has(List.append(&2, String, aa, ss), x),
        unsafe.all_in(List.append(&2, String, aa, ss), t),
        Equal.trans(Bool, Imports.has(List.append(&2, String, aa, ss), x),
          Bool.or(Imports.has(aa, x), Imports.has(ss, x)), True{}, unsafe.has_app(aa, ss, x),
          unsafe.or_r(Imports.has(aa, x), Imports.has(ss, x), unsafe.and_l(Imports.has(ss, x), unsafe.all_in(ss, t),
            h))),
        unsafe.in_pre(aa, ss, t, unsafe.and_r(Imports.has(ss, x), unsafe.all_in(ss, t), h)))

# a list that holds xs, with more behind, still holds it
law unsafe.in_suf:
  for +ss: List<&2, String>
  for +bb: List<&2, String>
  for xs: List<&2, String>
  for +h: {unsafe.all_in(ss, xs) == True{} : Bool}
  {unsafe.all_in(List.append(&2, String, ss, bb), xs) == True{} : Bool}

def unsafe.in_suf(ss, bb, xs, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      unsafe.and_true(Imports.has(List.append(&2, String, ss, bb), x),
        unsafe.all_in(List.append(&2, String, ss, bb), t),
        Equal.trans(Bool, Imports.has(List.append(&2, String, ss, bb), x),
          Bool.or(Imports.has(ss, x), Imports.has(bb, x)), True{}, unsafe.has_app(ss, bb, x),
          unsafe.or_l(Imports.has(ss, x), Imports.has(bb, x), unsafe.and_l(Imports.has(ss, x), unsafe.all_in(ss, t),
            h))),
        unsafe.in_suf(ss, bb, t, unsafe.and_r(Imports.has(ss, x), unsafe.all_in(ss, t), h)))

# a list holds itself
law unsafe.in_refl:
  for xs: List<&2, String>
  {unsafe.all_in(xs, xs) == True{} : Bool}

def unsafe.in_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      unsafe.and_true(Imports.has(h <> t, h), unsafe.all_in(h <> t, t),
        unsafe.or_l(String.eq(h, h), Imports.has(t, h), unsafe.srefl(h)), unsafe.in_pre([h], t, t, unsafe.in_refl(t)))

# a list that holds two lists holds them appended
law unsafe.in_app:
  for +ss: List<&2, String>
  for aa: List<&2, String>
  for +bb: List<&2, String>
  for +ha: {unsafe.all_in(ss, aa) == True{} : Bool}
  for hb: {unsafe.all_in(ss, bb) == True{} : Bool}
  {unsafe.all_in(ss, List.append(&2, String, aa, bb)) == True{} : Bool}

def unsafe.in_app(ss, aa, bb, ha, hb):
  match aa:
    case Nil{}:
      hb
    case Con{+x, +t}:
      unsafe.and_true(Imports.has(ss, x), unsafe.all_in(ss, List.append(&2, String, t, bb)),
        unsafe.and_l(Imports.has(ss, x), unsafe.all_in(ss, t), ha),
        unsafe.in_app(ss, t, bb, unsafe.and_r(Imports.has(ss, x), unsafe.all_in(ss, t), ha), hb))

# a list that holds xs and acc holds xs reversed onto acc
law unsafe.in_rgo:
  for +ss: List<&2, String>
  for xs: List<&2, String>
  for +acc: List<&2, String>
  for +hx: {unsafe.all_in(ss, xs) == True{} : Bool}
  for hacc: {unsafe.all_in(ss, acc) == True{} : Bool}
  {unsafe.all_in(ss, List.reverse.go(&2, String, xs, acc)) == True{} : Bool}

def unsafe.in_rgo(ss, xs, acc, hx, hacc):
  match xs:
    case Nil{}:
      hacc
    case Con{+x, +t}:
      unsafe.in_rgo(ss, t, x <> acc, unsafe.and_r(Imports.has(ss, x), unsafe.all_in(ss, t), hx),
        unsafe.and_true(Imports.has(ss, x), unsafe.all_in(ss, acc), unsafe.and_l(Imports.has(ss, x),
          unsafe.all_in(ss, t),
          hx), hacc))

# a list that holds xs holds it reversed
law unsafe.in_rev:
  for +ss: List<&2, String>
  for xs: List<&2, String>
  for h: {unsafe.all_in(ss, xs) == True{} : Bool}
  {unsafe.all_in(ss, List.reverse(&2, String, xs)) == True{} : Bool}

def unsafe.in_rev(ss, xs, h):
  unsafe.in_rgo(ss, xs, [], h, {==})

# a list reversed holds what it holds
law unsafe.in_rev_set:
  for +ss: List<&2, String>
  for xs: List<&2, String>
  {unsafe.all_in(List.reverse(&2, String, ss), xs) == unsafe.all_in(ss, xs) : Bool}

def unsafe.in_rev_set(ss, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Bool, Imports.has(List.reverse(&2, String, ss), x), Imports.has(ss, x), unsafe.has_rev(ss, x)) :
        {Bool.and(_, unsafe.all_in(List.reverse(&2, String, ss), t)) == Bool.and(Imports.has(ss, x),
          unsafe.all_in(ss, t))
          : Bool}
      %Equal.sym(Bool, unsafe.all_in(List.reverse(&2, String, ss), t), unsafe.all_in(ss, t), unsafe.in_rev_set(ss, t)) :
        {Bool.and(Imports.has(ss, x), _) == Bool.and(Imports.has(ss, x), unsafe.all_in(ss, t)) : Bool}
      {==}

# the digests as the walk reads them

# the walk's graph lookup is unsafe.imports
law unsafe.deps_imports:
  for ds: List<&2, Digest.Digest>
  for +pp: String
  {Imports.deps_of(Digest.edges(ds), pp) == Laws.unsafe.imports(ds, pp) : List<&2, String>}

def unsafe.deps_imports(ds, pp):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, +norm, dir, is_laws, is_law_file, exempt, tops, says, +deps, unsafes, laws}, +rest}:
      %Equal.sym(List<&2, String>, Imports.deps_of(Digest.edges(rest), pp), Laws.unsafe.imports(rest, pp),
          unsafe.deps_imports(rest, pp)) :
        {Bool.pick(List<&2, String>, String.eq(norm, pp), deps, _)
          == Bool.pick(List<&2, String>, String.eq(norm, pp), deps, Laws.unsafe.imports(rest, pp)) : List<&2, String>}
      {==}

# the walk's read files are unsafe.read
law unsafe.read_paths:
  for ds: List<&2, Digest.Digest>
  for +pp: String
  {Imports.has(Imports.paths(Digest.edges(ds)), pp) == Laws.unsafe.read(ds, pp) : Bool}

def unsafe.read_paths(ds, pp):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, +norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, +rest}:
      %Equal.sym(Bool, Imports.has(Imports.paths(Digest.edges(rest)), pp), Laws.unsafe.read(rest, pp),
          unsafe.read_paths(rest, pp)) :
        {Bool.or(String.eq(norm, pp), _) == Bool.or(String.eq(norm, pp), Laws.unsafe.read(rest, pp)) : Bool}
      {==}

# as many read files as digests
law unsafe.len_paths:
  for ds: List<&2, Digest.Digest>
  {List.length(&2, String, Imports.paths(Digest.edges(ds))) == List.length(&2, Digest.Digest, ds) : Nat}

def unsafe.len_paths(ds):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, +rest}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, String, Imports.paths(Digest.edges(rest))),
        List.length(&2, Digest.Digest, rest), unsafe.len_paths(rest))

# an or of a not: when the not's argument is True, the right is
law unsafe.or_not:
  for r: Bool
  for -h2: Bool
  for e: {Bool.or(Bool.not(r), h2) == True{} : Bool}
  for er: {r == True{} : Bool}
  {h2 == True{} : Bool}

def unsafe.or_not(r, h2, e, er):
  match r:
    case False{}:
      Empty.absurd({h2 == True{} : Bool}, unsafe.false_true(er))
    case True{}:
      e

# the head of a shut list, String.eq to p or not, carried to what p imports
law unsafe.shut_at.at:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for +h: String
  for -t: List<&2, String>
  for +p: String
  for b: Bool
  for eb: {String.eq(h, p) == b : Bool}
  for hh: {Laws.unsafe.held(ds, ss, Laws.unsafe.imports(ds, h)) == True{} : Bool}
  for hx: {Bool.or(b, Imports.has(t, p)) == True{} : Bool}
  for ih: {Imports.has(t, p) == True{} : Bool}
    -> {Laws.unsafe.held(ds, ss, Laws.unsafe.imports(ds, p)) == True{} : Bool}
  {Laws.unsafe.held(ds, ss, Laws.unsafe.imports(ds, p)) == True{} : Bool}

def unsafe.shut_at.at(ds, ss, h, _t, p, b, eb, hh, hx, ih):
  match b:
    case True{}:
      %unsafe.seq(h, p, eb) : {Laws.unsafe.held(ds, ss, Laws.unsafe.imports(ds, _)) == True{} : Bool}
      hh
    case False{}:
      ih(hx)

# ss shut over ps holds what the run imports of each path ps has
law unsafe.shut_at:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for ps: List<&2, String>
  for +p: String
  for +hs: {Laws.unsafe.shut(ds, ss, ps) == True{} : Bool}
  for hp: {Imports.has(ps, p) == True{} : Bool}
  {Laws.unsafe.held(ds, ss, Laws.unsafe.imports(ds, p)) == True{} : Bool}

def unsafe.shut_at(ds, ss, ps, p, hs, hp):
  match ps:
    case Nil{}:
      Empty.absurd({Laws.unsafe.held(ds, ss, Laws.unsafe.imports(ds, p)) == True{} : Bool}, unsafe.false_true(hp))
    case Con{+h, +t}:
      unsafe.shut_at.at(ds, ss, h, t, p, String.eq(h, p), {==},
        unsafe.and_l(Laws.unsafe.held(ds, ss, Laws.unsafe.imports(ds, h)), Laws.unsafe.shut(ds, ss, t), hs), hp,
        z => unsafe.shut_at(ds, ss, t, p,
          unsafe.and_r(Laws.unsafe.held(ds, ss, Laws.unsafe.imports(ds, h)), Laws.unsafe.shut(ds, ss, t), hs), z))

# one import the walk takes up, when ss holds the run's imports: kept or
# not, ss holds what comes out
law unsafe.fresh_in.at:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for +seen: List<&2, String>
  for +d: String
  for +more: List<&2, String>
  for c: Bool
  for hc: {Bool.and(Bool.and(Imports.has(Imports.paths(Digest.edges(ds)), d), Bool.not(Imports.has(seen, d))),
    Bool.not(Imports.has(more, d))) == c : Bool}
  for hd: {Bool.or(Bool.not(Laws.unsafe.read(ds, d)), Imports.has(ss, d)) == True{} : Bool}
  for hm: {unsafe.all_in(ss, more) == True{} : Bool}
  {unsafe.all_in(ss, Bool.pick(List<&2, String>, c, d <> more, more)) == True{} : Bool}

def unsafe.fresh_in.at(ds, ss, seen, d, more, c, hc, hd, hm):
  match c:
    case False{}:
      hm
    case True{}:
      +hr = Imports.has(Imports.paths(Digest.edges(ds)), d)
      h1 = unsafe.and_l(Bool.and(hr, Bool.not(Imports.has(seen, d))), Bool.not(Imports.has(more, d)), hc)
      h2 = unsafe.and_l(hr, Bool.not(Imports.has(seen, d)), h1)
      h3 = Equal.trans(Bool, Laws.unsafe.read(ds, d), hr, True{},
        Equal.sym(Bool, hr, Laws.unsafe.read(ds, d), unsafe.read_paths(ds, d)), h2)
      unsafe.and_true(Imports.has(ss, d), unsafe.all_in(ss, more),
        unsafe.or_not(Laws.unsafe.read(ds, d), Imports.has(ss, d), hd, h3), hm)

# what the walk takes up from xs is held by ss, when ss holds the run's
# imports among xs
law unsafe.fresh_in:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for xs: List<&2, String>
  for +seen: List<&2, String>
  for +hx: {Laws.unsafe.held(ds, ss, xs) == True{} : Bool}
  {unsafe.all_in(ss, Imports.fresh(xs, seen, Imports.paths(Digest.edges(ds)))) == True{} : Bool}

def unsafe.fresh_in(ds, ss, xs, seen, hx):
  match xs:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      +more = Imports.fresh(rest, seen, Imports.paths(Digest.edges(ds)))
      +hd = Bool.or(Bool.not(Laws.unsafe.read(ds, d)), Imports.has(ss, d))
      unsafe.fresh_in.at(ds, ss, seen, d, more,
        Bool.and(Bool.and(Imports.has(Imports.paths(Digest.edges(ds)), d), Bool.not(Imports.has(seen, d))),
          Bool.not(Imports.has(more, d))), {==},
        unsafe.and_l(hd, Laws.unsafe.held(ds, ss, rest), hx),
        unsafe.fresh_in(ds, ss, rest, seen, unsafe.and_r(hd, Laws.unsafe.held(ds, ss, rest), hx)))

# a shut list that holds the walk's worklist and what it has seen holds
# everything the walk returns
law unsafe.least_walk:
  for +ds: List<&2, Digest.Digest>
  for fuel: Nat
  for todo: List<&2, String>
  for +seen: List<&2, String>
  for +ss: List<&2, String>
  for +hs: {Laws.unsafe.shut(ds, ss, ss) == True{} : Bool}
  for +ht: {unsafe.all_in(ss, todo) == True{} : Bool}
  for hn: {unsafe.all_in(ss, seen) == True{} : Bool}
  {unsafe.all_in(ss, Imports.reach(fuel, todo, seen, Digest.edges(ds), Imports.paths(Digest.edges(ds)))) == True{}
    : Bool}

def unsafe.least_walk(ds, fuel, todo, seen, ss, hs, ht, hn):
  match fuel todo:
    case 0n _t:
      hn
    case 1n+f Nil{}:
      hn
    case 1n+f Con{+p, +rest}:
      +deps = Imports.deps_of(Digest.edges(ds), p)
      +found = Imports.fresh(deps, seen, Imports.paths(Digest.edges(ds)))
      hi = unsafe.shut_at(ds, ss, ss, p, hs, unsafe.and_l(Imports.has(ss, p), unsafe.all_in(ss, rest), ht))
      hd = Equal.trans(Bool, Laws.unsafe.held(ds, ss, deps), Laws.unsafe.held(ds, ss, Laws.unsafe.imports(ds, p)),
        True{}, Equal.cong(List<&2, String>, Bool, z => Laws.unsafe.held(ds, ss, z), deps, Laws.unsafe.imports(ds, p),
          unsafe.deps_imports(ds, p)), hi)
      +hf = unsafe.fresh_in(ds, ss, deps, seen, hd)
      unsafe.least_walk(ds, f, List.append(&2, String, found, rest),
        List.append(&2, String, List.reverse(&2, String, found), seen), ss, hs,
        unsafe.in_app(ss, found, rest, hf, unsafe.and_r(Imports.has(ss, p), unsafe.all_in(ss, rest), ht)),
        unsafe.in_app(ss, List.reverse(&2, String, found), seen, unsafe.in_rev(ss, found, hf), hn))

# the walk keeps every path it has seen
law unsafe.keep:
  for +ds: List<&2, Digest.Digest>
  for fuel: Nat
  for todo: List<&2, String>
  for +seen: List<&2, String>
  for +x: String
  for hx: {Imports.has(seen, x) == True{} : Bool}
  {Imports.has(Imports.reach(fuel, todo, seen, Digest.edges(ds), Imports.paths(Digest.edges(ds))), x) == True{} : Bool}

def unsafe.keep(ds, fuel, todo, seen, x, hx):
  match fuel todo:
    case 0n _t:
      hx
    case 1n+f Nil{}:
      hx
    case 1n+f Con{+p, +rest}:
      +found = Imports.fresh(Imports.deps_of(Digest.edges(ds), p), seen, Imports.paths(Digest.edges(ds)))
      +rf = List.reverse(&2, String, found)
      unsafe.keep(ds, f, List.append(&2, String, found, rest), List.append(&2, String, rf, seen), x,
        Equal.trans(Bool, Imports.has(List.append(&2, String, rf, seen), x),
          Bool.or(Imports.has(rf, x), Imports.has(seen, x)), True{}, unsafe.has_app(rf, seen, x),
          unsafe.or_r(Imports.has(rf, x), Imports.has(seen, x), hx)))

def Laws.unsafe_from(ds, from):
  +ww = Imports.reach(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds),
    Imports.paths(Digest.edges(ds)))
  Equal.trans(Bool, Imports.has(List.reverse(&2, String, ww), from), Imports.has(ww, from), True{},
    unsafe.has_rev(ww, from),
    unsafe.keep(ds, List.length(&2, Digest.Digest, ds), [from], [from], from,
      unsafe.or_l(String.eq(from, from), False{}, unsafe.srefl(from))))

def Laws.unsafe_least(ds, from, ss, pp, hf, hs, hp):
  +ww = Imports.reach(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds),
    Imports.paths(Digest.edges(ds)))
  +h1 = unsafe.and_true(Imports.has(ss, from), True{}, hf, {==})
  unsafe.has_sub(ss, ww, pp, unsafe.least_walk(ds, List.length(&2, Digest.Digest, ds), [from], [from], ss, hs, h1, h1),
    Equal.trans(Bool, Imports.has(ww, pp), Imports.has(List.reverse(&2, String, ww), pp), True{},
      Equal.sym(Bool, Imports.has(List.reverse(&2, String, ww), pp), Imports.has(ww, pp), unsafe.has_rev(ww, pp)), hp))

# the walk's invariant over qs: each path of qs is still on the worklist, or
# what the run has of its imports is seen
def unsafe.inv(
  +ds: List<&2, Digest.Digest>,
  +todo: List<&2, String>,
  +seen: List<&2, String>,
  qs: List<&2, String>
) -> Bool:
  match qs:
    case Nil{}:
      True{}
    case Con{+q, rest}:
      +more = unsafe.inv(ds, todo, seen, rest)
      Bool.and(Bool.or(Imports.has(todo, q), Laws.unsafe.held(ds, seen, Laws.unsafe.imports(ds, q))), more)

# with the worklist empty, the invariant is shut
law unsafe.inv_nil:
  for +ds: List<&2, Digest.Digest>
  for +seen: List<&2, String>
  for qs: List<&2, String>
  {unsafe.inv(ds, [], seen, qs) == Laws.unsafe.shut(ds, seen, qs) : Bool}

def unsafe.inv_nil(ds, seen, qs):
  match qs:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      %Equal.sym(Bool, unsafe.inv(ds, [], seen, t), Laws.unsafe.shut(ds, seen, t), unsafe.inv_nil(ds, seen, t)) :
        {Bool.and(Laws.unsafe.held(ds, seen, Laws.unsafe.imports(ds, q)), _)
          == Bool.and(Laws.unsafe.held(ds, seen, Laws.unsafe.imports(ds, q)), Laws.unsafe.shut(ds, seen, t)) : Bool}
      {==}

# paths the worklist holds keep the invariant
law unsafe.inv_todo:
  for +ds: List<&2, Digest.Digest>
  for +todo: List<&2, String>
  for +seen: List<&2, String>
  for qs: List<&2, String>
  for +h: {unsafe.all_in(todo, qs) == True{} : Bool}
  {unsafe.inv(ds, todo, seen, qs) == True{} : Bool}

def unsafe.inv_todo(ds, todo, seen, qs, h):
  match qs:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      unsafe.and_true(Bool.or(Imports.has(todo, q), Laws.unsafe.held(ds, seen, Laws.unsafe.imports(ds, q))),
        unsafe.inv(ds, todo, seen, t),
        unsafe.or_l(Imports.has(todo, q), Laws.unsafe.held(ds, seen, Laws.unsafe.imports(ds, q)),
          unsafe.and_l(Imports.has(todo, q), unsafe.all_in(todo, t), h)),
        unsafe.inv_todo(ds, todo, seen, t, unsafe.and_r(Imports.has(todo, q), unsafe.all_in(todo, t), h)))

# the invariant over two lists is the invariant over them appended
law unsafe.inv_app:
  for +ds: List<&2, Digest.Digest>
  for +todo: List<&2, String>
  for +seen: List<&2, String>
  for aa: List<&2, String>
  for +bb: List<&2, String>
  for +ha: {unsafe.inv(ds, todo, seen, aa) == True{} : Bool}
  for hb: {unsafe.inv(ds, todo, seen, bb) == True{} : Bool}
  {unsafe.inv(ds, todo, seen, List.append(&2, String, aa, bb)) == True{} : Bool}

def unsafe.inv_app(ds, todo, seen, aa, bb, ha, hb):
  match aa:
    case Nil{}:
      hb
    case Con{+q, +t}:
      +hq = Bool.or(Imports.has(todo, q), Laws.unsafe.held(ds, seen, Laws.unsafe.imports(ds, q)))
      unsafe.and_true(hq, unsafe.inv(ds, todo, seen, List.append(&2, String, t, bb)),
        unsafe.and_l(hq, unsafe.inv(ds, todo, seen, t), ha),
        unsafe.inv_app(ds, todo, seen, t, bb, unsafe.and_r(hq, unsafe.inv(ds, todo, seen, t), ha), hb))

# one import, held in a list or not, carried to a list that holds that list
law unsafe.held_grow.at:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for +tt: List<&2, String>
  for +d: String
  for b: Bool
  for eb: {Imports.has(ss, d) == b : Bool}
  for hst: {unsafe.all_in(tt, ss) == True{} : Bool}
  for hh: {Bool.or(Bool.not(Laws.unsafe.read(ds, d)), b) == True{} : Bool}
  {Bool.or(Bool.not(Laws.unsafe.read(ds, d)), Imports.has(tt, d)) == True{} : Bool}

def unsafe.held_grow.at(ds, ss, tt, d, b, eb, hst, hh):
  match b:
    case True{}:
      unsafe.or_r(Bool.not(Laws.unsafe.read(ds, d)), Imports.has(tt, d), unsafe.has_sub(tt, ss, d, hst, eb))
    case False{}:
      +nr = Bool.not(Laws.unsafe.read(ds, d))
      unsafe.or_l(nr, Imports.has(tt, d), Equal.trans(Bool, nr, Bool.or(nr, False{}), True{},
        Equal.sym(Bool, Bool.or(nr, False{}), nr, unsafe.or_false(nr)), hh))

# what the run imports among xs, held in ss, is held in a list that holds ss
law unsafe.held_grow:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for +tt: List<&2, String>
  for xs: List<&2, String>
  for +h: {Laws.unsafe.held(ds, ss, xs) == True{} : Bool}
  for +hst: {unsafe.all_in(tt, ss) == True{} : Bool}
  {Laws.unsafe.held(ds, tt, xs) == True{} : Bool}

def unsafe.held_grow(ds, ss, tt, xs, h, hst):
  match xs:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      +hd = Bool.or(Bool.not(Laws.unsafe.read(ds, d)), Imports.has(ss, d))
      unsafe.and_true(Bool.or(Bool.not(Laws.unsafe.read(ds, d)), Imports.has(tt, d)), Laws.unsafe.held(ds, tt, rest),
        unsafe.held_grow.at(ds, ss, tt, d, Imports.has(ss, d), {==}, hst,
          unsafe.and_l(hd, Laws.unsafe.held(ds, ss, rest), h)),
        unsafe.held_grow(ds, ss, tt, rest, unsafe.and_r(hd, Laws.unsafe.held(ds, ss, rest), h), hst))

# what the walk takes up, kept or not, leaves the rest of it held
law unsafe.fresh_more:
  for +ss: List<&2, String>
  for +d: String
  for +more: List<&2, String>
  for c: Bool
  for h: {unsafe.all_in(ss, Bool.pick(List<&2, String>, c, d <> more, more)) == True{} : Bool}
  {unsafe.all_in(ss, more) == True{} : Bool}

def unsafe.fresh_more(ss, d, more, c, h):
  match c:
    case True{}:
      unsafe.and_r(Imports.has(ss, d), unsafe.all_in(ss, more), h)
    case False{}:
      h

# one import the walk looks at: in the run, it was seen, is taken up later,
# or is taken up now, so a list that holds all three holds it
law unsafe.fresh_held.at:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for +seen: List<&2, String>
  for +d: String
  for +more: List<&2, String>
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for e1: {Imports.has(Imports.paths(Digest.edges(ds)), d) == b1 : Bool}
  for e2: {Imports.has(seen, d) == b2 : Bool}
  for e3: {Imports.has(more, d) == b3 : Bool}
  for hs: {unsafe.all_in(ss, seen) == True{} : Bool}
  for hm: {unsafe.all_in(ss, more) == True{} : Bool}
  for hf: {unsafe.all_in(ss, Bool.pick(List<&2, String>, Bool.and(Bool.and(b1, Bool.not(b2)), Bool.not(b3)), d <> more,
    more)) == True{} : Bool}
  {Bool.or(Bool.not(Laws.unsafe.read(ds, d)), Imports.has(ss, d)) == True{} : Bool}

def unsafe.fresh_held.at(ds, ss, seen, d, more, b1, b2, b3, e1, e2, e3, hs, hm, hf):
  match b1:
    case False{}:
      er = Equal.trans(Bool, Laws.unsafe.read(ds, d), Imports.has(Imports.paths(Digest.edges(ds)), d), False{},
        Equal.sym(Bool, Imports.has(Imports.paths(Digest.edges(ds)), d), Laws.unsafe.read(ds, d),
          unsafe.read_paths(ds, d)), e1)
      %Equal.sym(Bool, Laws.unsafe.read(ds, d), False{}, er) :
        {Bool.or(Bool.not(_), Imports.has(ss, d)) == True{} : Bool}
      {==}
    case True{}:
      match b2:
        case True{}:
          unsafe.or_r(Bool.not(Laws.unsafe.read(ds, d)), Imports.has(ss, d), unsafe.has_sub(ss, seen, d, hs, e2))
        case False{}:
          match b3:
            case True{}:
              unsafe.or_r(Bool.not(Laws.unsafe.read(ds, d)), Imports.has(ss, d), unsafe.has_sub(ss, more, d, hm, e3))
            case False{}:
              unsafe.or_r(Bool.not(Laws.unsafe.read(ds, d)), Imports.has(ss, d),
                unsafe.and_l(Imports.has(ss, d), unsafe.all_in(ss, more), hf))

# a list that holds what the walk has seen and what it takes up from xs
# holds every import of xs in the run
law unsafe.fresh_held:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for xs: List<&2, String>
  for +seen: List<&2, String>
  for +hs: {unsafe.all_in(ss, seen) == True{} : Bool}
  for +hf: {unsafe.all_in(ss, Imports.fresh(xs, seen, Imports.paths(Digest.edges(ds)))) == True{} : Bool}
  {Laws.unsafe.held(ds, ss, xs) == True{} : Bool}

def unsafe.fresh_held(ds, ss, xs, seen, hs, hf):
  match xs:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      +more = Imports.fresh(rest, seen, Imports.paths(Digest.edges(ds)))
      +b1 = Imports.has(Imports.paths(Digest.edges(ds)), d)
      +b2 = Imports.has(seen, d)
      +b3 = Imports.has(more, d)
      +hm = unsafe.fresh_more(ss, d, more, Bool.and(Bool.and(b1, Bool.not(b2)), Bool.not(b3)), hf)
      unsafe.and_true(Bool.or(Bool.not(Laws.unsafe.read(ds, d)), Imports.has(ss, d)), Laws.unsafe.held(ds, ss, rest),
        unsafe.fresh_held.at(ds, ss, seen, d, more, b1, b2, b3, {==}, {==}, {==}, hs, hm, hf),
        unsafe.fresh_held(ds, ss, rest, seen, hs, hm))

# one path of what was seen, before a step of the walk and after it: still
# on the worklist, or its imports in the run seen
law unsafe.inv_keep.at:
  for +ds: List<&2, Digest.Digest>
  for +p: String
  for +rest: List<&2, String>
  for +seen: List<&2, String>
  for +found: List<&2, String>
  for +seen2: List<&2, String>
  for +q: String
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for e1: {Laws.unsafe.held(ds, seen, Laws.unsafe.imports(ds, q)) == b1 : Bool}
  for e2: {String.eq(p, q) == b2 : Bool}
  for e3: {Imports.has(rest, q) == b3 : Bool}
  for hp: {Laws.unsafe.held(ds, seen2, Laws.unsafe.imports(ds, p)) == True{} : Bool}
  for hg: {unsafe.all_in(seen2, seen) == True{} : Bool}
  for h0: {Bool.or(Bool.or(b2, b3), b1) == True{} : Bool}
  {Bool.or(Imports.has(List.append(&2, String, found, rest), q), Laws.unsafe.held(ds, seen2, Laws.unsafe.imports(ds,
    q)))
    == True{} : Bool}

def unsafe.inv_keep.at(ds, p, rest, seen, found, seen2, q, b1, b2, b3, e1, e2, e3, hp, hg, h0):
  match b1:
    case True{}:
      unsafe.or_r(Imports.has(List.append(&2, String, found, rest), q),
        Laws.unsafe.held(ds, seen2, Laws.unsafe.imports(ds, q)),
        unsafe.held_grow(ds, seen, seen2, Laws.unsafe.imports(ds, q), e1, hg))
    case False{}:
      match b2:
        case True{}:
          %unsafe.seq(p, q, e2) :
            {Bool.or(Imports.has(List.append(&2, String, found, rest), q),
              Laws.unsafe.held(ds, seen2, Laws.unsafe.imports(ds, _))) == True{} : Bool}
          unsafe.or_r(Imports.has(List.append(&2, String, found, rest), q),
            Laws.unsafe.held(ds, seen2, Laws.unsafe.imports(ds, p)), hp)
        case False{}:
          match b3:
            case True{}:
              +app = List.append(&2, String, found, rest)
              unsafe.or_l(Imports.has(app, q), Laws.unsafe.held(ds, seen2, Laws.unsafe.imports(ds, q)),
                Equal.trans(Bool, Imports.has(app, q), Bool.or(Imports.has(found, q), Imports.has(rest, q)), True{},
                  unsafe.has_app(found, rest, q), unsafe.or_r(Imports.has(found, q), Imports.has(rest, q), e3)))
            case False{}:
              Empty.absurd({Bool.or(Imports.has(List.append(&2, String, found, rest), q),
                Laws.unsafe.held(ds, seen2, Laws.unsafe.imports(ds, q))) == True{} : Bool}, unsafe.false_true(h0))

# what was seen keeps the invariant across a step of the walk, when the
# step's new list holds the old one and what p imports from the run
law unsafe.inv_keep:
  for +ds: List<&2, Digest.Digest>
  for +p: String
  for +rest: List<&2, String>
  for +seen: List<&2, String>
  for +found: List<&2, String>
  for +seen2: List<&2, String>
  for qs: List<&2, String>
  for +hp: {Laws.unsafe.held(ds, seen2, Laws.unsafe.imports(ds, p)) == True{} : Bool}
  for +hg: {unsafe.all_in(seen2, seen) == True{} : Bool}
  for +hi: {unsafe.inv(ds, p <> rest, seen, qs) == True{} : Bool}
  {unsafe.inv(ds, List.append(&2, String, found, rest), seen2, qs) == True{} : Bool}

def unsafe.inv_keep(ds, p, rest, seen, found, seen2, qs, hp, hg, hi):
  match qs:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      +b1 = Laws.unsafe.held(ds, seen, Laws.unsafe.imports(ds, q))
      +hq = Bool.or(Bool.or(String.eq(p, q), Imports.has(rest, q)), b1)
      unsafe.and_true(
        Bool.or(Imports.has(List.append(&2, String, found, rest), q), Laws.unsafe.held(ds, seen2,
          Laws.unsafe.imports(ds, q))),
        unsafe.inv(ds, List.append(&2, String, found, rest), seen2, t),
        unsafe.inv_keep.at(ds, p, rest, seen, found, seen2, q, b1, String.eq(p, q), Imports.has(rest, q), {==}, {==},
          {==}, hp, hg, unsafe.and_l(hq, unsafe.inv(ds, p <> rest, seen, t), hi)),
        unsafe.inv_keep(ds, p, rest, seen, found, seen2, t, hp, hg, unsafe.and_r(hq, unsafe.inv(ds, p <> rest, seen, t),
          hi)))

# the walk's fuel: a count of the read files it has not seen yet

# adding 0 on the right
law unsafe.add_zero:
  for a: Nat
  {Nat.add(a, 0n) == a : Nat}

def unsafe.add_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 0n), p, unsafe.add_zero(p))

# adding a successor on the right
law unsafe.add_succ:
  for a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def unsafe.add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 1n+b), 1n+Nat.add(p, b), unsafe.add_succ(p, b))

# add groups either way
law unsafe.add_assoc:
  for a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def unsafe.add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), unsafe.add_assoc(p, b, c))

# add's first two arguments trade places
law unsafe.add_swap:
  for a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}

def unsafe.add_swap(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.trans(Nat, 1n+Nat.add(p, Nat.add(b, c)), 1n+Nat.add(b, Nat.add(p, c)), Nat.add(b, 1n+Nat.add(p, c)),
        Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, Nat.add(b, c)), Nat.add(b, Nat.add(p, c)), unsafe.add_swap(p, b, c)),
        Equal.sym(Nat, Nat.add(b, 1n+Nat.add(p, c)), 1n+Nat.add(b, Nat.add(p, c)), unsafe.add_succ(b, Nat.add(p, c))))

# an append is as long as its parts together
law unsafe.len_app:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  {List.length(&2, String, List.append(&2, String, xs, ys))
    == Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)) : Nat}

def unsafe.len_app(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, String, List.append(&2, String, t, ys)),
        Nat.add(List.length(&2, String, t), List.length(&2, String, ys)), unsafe.len_app(t, ys))

# the Nat before a successor
def unsafe.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# successors that are equal are of equal Nats
law unsafe.succ_inj:
  for -a: Nat
  for -b: Nat
  for e: {1n+a == 1n+b : Nat}
  {a == b : Nat}

def unsafe.succ_inj(a, b, e):
  Equal.cong(Nat, Nat, n => unsafe.pred(n), 1n+a, 1n+b, e)

# Unit for 0, Empty for a successor
def unsafe.nat_ty(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+_p:
      Empty

# 0 is no successor
law unsafe.zero_succ:
  for -a: Nat
  for e: {0n == 1n+a : Nat}
  Empty

def unsafe.zero_succ(_a, e):
  %e : unsafe.nat_ty(_)
  Unit{}

# the step's sum, regrouped: the fuel left after a step against the step's
# new worklist and its new count
law unsafe.count_arith:
  for -f: Nat
  for +l: Nat
  for -m: Nat
  for +k: Nat
  for +ff: Nat
  for -la: Nat
  for +m2: Nat
  for -m3: Nat
  for +s: Nat
  for h1: {f == Nat.add(l, Nat.add(m, k)) : Nat}
  for h2: {m == Nat.add(ff, Nat.add(m2, s)) : Nat}
  for h3: {la == Nat.add(ff, l) : Nat}
  for h4: {m3 == m2 : Nat}
  {f == Nat.add(la, Nat.add(m3, Nat.add(s, k))) : Nat}

def unsafe.count_arith(f, l, m, k, ff, la, m2, m3, s, h1, h2, h3, h4):
  %Equal.sym(Nat, f, Nat.add(l, Nat.add(m, k)), h1) : {_ == Nat.add(la, Nat.add(m3, Nat.add(s, k))) : Nat}
  %Equal.sym(Nat, m, Nat.add(ff, Nat.add(m2, s)), h2) :
    {Nat.add(l, Nat.add(_, k)) == Nat.add(la, Nat.add(m3, Nat.add(s, k))) : Nat}
  %Equal.sym(Nat, la, Nat.add(ff, l), h3) :
    {Nat.add(l, Nat.add(Nat.add(ff, Nat.add(m2, s)), k)) == Nat.add(_, Nat.add(m3, Nat.add(s, k))) : Nat}
  %Equal.sym(Nat, m3, m2, h4) :
    {Nat.add(l, Nat.add(Nat.add(ff, Nat.add(m2, s)), k)) == Nat.add(Nat.add(ff, l), Nat.add(_, Nat.add(s, k))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(ff, Nat.add(m2, s)), k), Nat.add(ff, Nat.add(Nat.add(m2, s), k)),
      unsafe.add_assoc(ff, Nat.add(m2, s), k)) :
    {Nat.add(l, _) == Nat.add(Nat.add(ff, l), Nat.add(m2, Nat.add(s, k))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(m2, s), k), Nat.add(m2, Nat.add(s, k)), unsafe.add_assoc(m2, s, k)) :
    {Nat.add(l, Nat.add(ff, _)) == Nat.add(Nat.add(ff, l), Nat.add(m2, Nat.add(s, k))) : Nat}
  +yy = Nat.add(m2, Nat.add(s, k))
  Equal.trans(Nat, Nat.add(l, Nat.add(ff, yy)), Nat.add(ff, Nat.add(l, yy)), Nat.add(Nat.add(ff, l), yy),
    unsafe.add_swap(l, ff, yy), Equal.sym(Nat, Nat.add(Nat.add(ff, l), yy), Nat.add(ff, Nat.add(l, yy)),
      unsafe.add_assoc(ff, l, yy)))

# how many paths of rr ss does not have
def unsafe.miss(rr: List<&2, String>, +ss: List<&2, String>) -> Nat:
  match rr:
    case Nil{}:
      0n
    case Con{+h, t}:
      +more = unsafe.miss(t, ss)
      Bool.pick(Nat, Imports.has(ss, h), more, 1n+more)

# an empty list misses every path
law unsafe.miss_nil:
  for rr: List<&2, String>
  {unsafe.miss(rr, []) == List.length(&2, String, rr) : Nat}

def unsafe.miss_nil(rr):
  match rr:
    case Nil{}:
      {==}
    case Con{h, +t}:
      Equal.cong(Nat, Nat, n => 1n+n, unsafe.miss(t, []), List.length(&2, String, t), unsafe.miss_nil(t))

# the count does not see a reversal in front
law unsafe.miss_rev:
  for rr: List<&2, String>
  for +xs: List<&2, String>
  for +ss: List<&2, String>
  {unsafe.miss(rr, List.append(&2, String, List.reverse(&2, String, xs), ss))
    == unsafe.miss(rr, List.append(&2, String, xs, ss)) : Nat}

def unsafe.miss_rev(rr, xs, ss):
  match rr:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +rv = List.reverse(&2, String, xs)
      +aa = List.append(&2, String, rv, ss)
      +bb = List.append(&2, String, xs, ss)
      eh = Equal.trans(Bool, Imports.has(aa, h), Bool.or(Imports.has(rv, h), Imports.has(ss, h)), Imports.has(bb, h),
        unsafe.has_app(rv, ss, h),
        Equal.trans(Bool, Bool.or(Imports.has(rv, h), Imports.has(ss, h)), Bool.or(Imports.has(xs, h),
          Imports.has(ss, h)),
          Imports.has(bb, h),
          Equal.cong(Bool, Bool, z => Bool.or(z, Imports.has(ss, h)), Imports.has(rv, h), Imports.has(xs, h),
            unsafe.has_rev(xs, h)),
          Equal.sym(Bool, Imports.has(bb, h), Bool.or(Imports.has(xs, h), Imports.has(ss, h)), unsafe.has_app(xs, ss,
            h))))
      %Equal.sym(Bool, Imports.has(aa, h), Imports.has(bb, h), eh) :
        {Bool.pick(Nat, _, unsafe.miss(t, aa), 1n+unsafe.miss(t, aa))
          == Bool.pick(Nat, Imports.has(bb, h), unsafe.miss(t, bb), 1n+unsafe.miss(t, bb)) : Nat}
      %Equal.sym(Nat, unsafe.miss(t, aa), unsafe.miss(t, bb), unsafe.miss_rev(t, xs, ss)) :
        {Bool.pick(Nat, Imports.has(bb, h), _, 1n+_)
          == Bool.pick(Nat, Imports.has(bb, h), unsafe.miss(t, bb), 1n+unsafe.miss(t, bb)) : Nat}
      {==}

# a count and a slack, both one more
law unsafe.lift1:
  for -a: Nat
  for -b: Nat
  for w: &s: Nat -> {a == Nat.add(b, s) : Nat}
  exs s2: Nat
  {1n+a == 1n+Nat.add(b, s2) : Nat}

def unsafe.lift1(a, b, w):
  (s, e) = w
  (s, Equal.cong(Nat, Nat, n => 1n+n, a, Nat.add(b, s), e))

# a count one more, with the slack one more
law unsafe.lift2:
  for -a: Nat
  for +b: Nat
  for w: &s: Nat -> {a == Nat.add(b, s) : Nat}
  exs s2: Nat
  {1n+a == Nat.add(b, s2) : Nat}

def unsafe.lift2(a, b, w):
  (s, e) = w
  +s1 = {s : Nat}
  (1n+s1, Equal.trans(Nat, 1n+a, 1n+Nat.add(b, s1), Nat.add(b, 1n+s1),
    Equal.cong(Nat, Nat, n => 1n+n, a, Nat.add(b, s1), e),
    Equal.sym(Nat, Nat.add(b, 1n+s1), 1n+Nat.add(b, s1), unsafe.add_succ(b, s1))))

# one path of rr against d on top of tt: the count without d is no smaller
law unsafe.miss_cons0.at:
  for +tt: List<&2, String>
  for +d: String
  for +t: List<&2, String>
  for b1: Bool
  for b2: Bool
  for w: &s: Nat -> {unsafe.miss(t, tt) == Nat.add(unsafe.miss(t, d <> tt), s) : Nat}
  exs s2: Nat
  {Bool.pick(Nat, b1, unsafe.miss(t, tt), 1n+unsafe.miss(t, tt))
    == Nat.add(Bool.pick(Nat, Bool.or(b2, b1), unsafe.miss(t, d <> tt), 1n+unsafe.miss(t, d <> tt)), s2) : Nat}

def unsafe.miss_cons0.at(tt, d, t, b1, b2, w):
  match b1:
    case True{}:
      match b2:
        case True{}:
          w
        case False{}:
          w
    case False{}:
      match b2:
        case True{}:
          unsafe.lift2(unsafe.miss(t, tt), unsafe.miss(t, d <> tt), w)
        case False{}:
          unsafe.lift1(unsafe.miss(t, tt), unsafe.miss(t, d <> tt), w)

# one path more in a list misses no more paths
law unsafe.miss_cons0:
  for rr: List<&2, String>
  for +tt: List<&2, String>
  for +d: String
  exs s: Nat
  {unsafe.miss(rr, tt) == Nat.add(unsafe.miss(rr, d <> tt), s) : Nat}

def unsafe.miss_cons0(rr, tt, d):
  match rr:
    case Nil{}:
      (0n, {==})
    case Con{+h, +t}:
      unsafe.miss_cons0.at(tt, d, t, Imports.has(tt, h), String.eq(d, h), unsafe.miss_cons0(t, tt, d))

# one path of rr against d, new to tt and among rr, on top of tt
law unsafe.miss_cons1.at:
  for +tt: List<&2, String>
  for +d: String
  for +h: String
  for +t: List<&2, String>
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for e1: {Imports.has(tt, h) == b1 : Bool}
  for e2: {String.eq(d, h) == b2 : Bool}
  for e3: {String.eq(h, d) == b3 : Bool}
  for ht: {Imports.has(tt, d) == False{} : Bool}
  for hr: {Bool.or(b3, Imports.has(t, d)) == True{} : Bool}
  for ih: {Imports.has(t, d) == True{} : Bool}
    -> &s: Nat -> {unsafe.miss(t, tt) == 1n+Nat.add(unsafe.miss(t, d <> tt), s) : Nat}
  exs s2: Nat
  {Bool.pick(Nat, b1, unsafe.miss(t, tt), 1n+unsafe.miss(t, tt))
    == 1n+Nat.add(Bool.pick(Nat, Bool.or(b2, b1), unsafe.miss(t, d <> tt), 1n+unsafe.miss(t, d <> tt)), s2) : Nat}

def unsafe.miss_cons1.at(tt, d, h, t, b1, b2, b3, e1, e2, e3, ht, hr, ih):
  match b1:
    case True{}:
      match b2:
        case True{}:
          match b3:
            case True{}:
              ehd = Equal.cong(String, Bool, z => Imports.has(tt, z), h, d, unsafe.seq(h, d, e3))
              Empty.absurd((&s2: Nat -> {unsafe.miss(t, tt) == 1n+Nat.add(unsafe.miss(t, d <> tt), s2) : Nat}),
                unsafe.false_true(Equal.trans(Bool, False{}, Imports.has(tt, d), True{},
                  Equal.sym(Bool, Imports.has(tt, d), False{}, ht),
                  Equal.trans(Bool, Imports.has(tt, d), Imports.has(tt, h), True{},
                    Equal.sym(Bool, Imports.has(tt, h), Imports.has(tt, d), ehd), e1))))
            case False{}:
              ih(hr)
        case False{}:
          match b3:
            case True{}:
              ehd = Equal.cong(String, Bool, z => Imports.has(tt, z), h, d, unsafe.seq(h, d, e3))
              Empty.absurd((&s2: Nat -> {unsafe.miss(t, tt) == 1n+Nat.add(unsafe.miss(t, d <> tt), s2) : Nat}),
                unsafe.false_true(Equal.trans(Bool, False{}, Imports.has(tt, d), True{},
                  Equal.sym(Bool, Imports.has(tt, d), False{}, ht),
                  Equal.trans(Bool, Imports.has(tt, d), Imports.has(tt, h), True{},
                    Equal.sym(Bool, Imports.has(tt, h), Imports.has(tt, d), ehd), e1))))
            case False{}:
              ih(hr)
    case False{}:
      match b2:
        case True{}:
          unsafe.lift1(unsafe.miss(t, tt), unsafe.miss(t, d <> tt), unsafe.miss_cons0(t, tt, d))
        case False{}:
          match b3:
            case True{}:
              edh = Equal.cong(String, Bool, z => String.eq(d, z), h, d, unsafe.seq(h, d, e3))
              Empty.absurd((&s2: Nat -> {1n+unsafe.miss(t, tt) == 1n+Nat.add(1n+unsafe.miss(t, d <> tt), s2) : Nat}),
                unsafe.false_true(Equal.trans(Bool, False{}, String.eq(d, h), True{},
                  Equal.sym(Bool, String.eq(d, h), False{}, e2),
                  Equal.trans(Bool, String.eq(d, h), String.eq(d, d), True{}, edh, unsafe.srefl(d)))))
            case False{}:
              unsafe.lift1(unsafe.miss(t, tt), 1n+unsafe.miss(t, d <> tt), ih(hr))

# a path of rr new to tt: one more in tt misses at least one path fewer
law unsafe.miss_cons1:
  for rr: List<&2, String>
  for +tt: List<&2, String>
  for +d: String
  for hr: {Imports.has(rr, d) == True{} : Bool}
  for +ht: {Imports.has(tt, d) == False{} : Bool}
  exs s: Nat
  {unsafe.miss(rr, tt) == 1n+Nat.add(unsafe.miss(rr, d <> tt), s) : Nat}

def unsafe.miss_cons1(rr, tt, d, hr, ht):
  match rr:
    case Nil{}:
      Empty.absurd((&s: Nat -> {unsafe.miss([], tt) == 1n+Nat.add(unsafe.miss([], d <> tt), s) : Nat}),
        unsafe.false_true(hr))
    case Con{+h, +t}:
      unsafe.miss_cons1.at(tt, d, h, t, Imports.has(tt, h), String.eq(d, h), String.eq(h, d), {==}, {==}, {==}, ht, hr,
        z => unsafe.miss_cons1(t, tt, d, z, ht))

# the new path's count, with the rest's slack and one step's slack
law unsafe.fresh_count.new:
  for -mm: Nat
  for +ll: Nat
  for -mt: Nat
  for +m2: Nat
  for w: &s: Nat -> {mm == Nat.add(ll, Nat.add(mt, s)) : Nat}
  for v: &s: Nat -> {mt == 1n+Nat.add(m2, s) : Nat}
  exs s3: Nat
  {mm == 1n+Nat.add(ll, Nat.add(m2, s3)) : Nat}

def unsafe.fresh_count.new(mm, ll, mt, m2, w, v):
  (s1, e1) = w
  (s2, e2) = v
  +a1 = {s1 : Nat}
  +a2 = {s2 : Nat}
  (Nat.add(a2, a1), Equal.trans(Nat, mm, Nat.add(ll, Nat.add(1n+Nat.add(m2, a2), a1)), 1n+Nat.add(ll, Nat.add(m2,
    Nat.add(a2, a1))),
    Equal.trans(Nat, mm, Nat.add(ll, Nat.add(mt, a1)), Nat.add(ll, Nat.add(1n+Nat.add(m2, a2), a1)), e1,
      Equal.cong(Nat, Nat, z => Nat.add(ll, Nat.add(z, a1)), mt, 1n+Nat.add(m2, a2), e2)),
    Equal.trans(Nat, Nat.add(ll, 1n+Nat.add(Nat.add(m2, a2), a1)), 1n+Nat.add(ll, Nat.add(Nat.add(m2, a2), a1)),
      1n+Nat.add(ll, Nat.add(m2, Nat.add(a2, a1))), unsafe.add_succ(ll, Nat.add(Nat.add(m2, a2), a1)),
      Equal.cong(Nat, Nat, z => 1n+Nat.add(ll, z), Nat.add(Nat.add(m2, a2), a1), Nat.add(m2, Nat.add(a2, a1)),
        unsafe.add_assoc(m2, a2, a1)))))

# one import the walk looks at: taken up, it is new to the run's count
law unsafe.fresh_count.at:
  for +ds: List<&2, Digest.Digest>
  for +seen: List<&2, String>
  for +d: String
  for +more: List<&2, String>
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for e1: {Imports.has(Imports.paths(Digest.edges(ds)), d) == b1 : Bool}
  for e2: {Imports.has(seen, d) == b2 : Bool}
  for e3: {Imports.has(more, d) == b3 : Bool}
  for w: &s: Nat -> {unsafe.miss(Imports.paths(Digest.edges(ds)), seen) == Nat.add(List.length(&2, String, more),
    Nat.add(unsafe.miss(Imports.paths(Digest.edges(ds)), List.append(&2, String, more, seen)), s)) : Nat}
  exs s2: Nat
  {unsafe.miss(Imports.paths(Digest.edges(ds)), seen)
    == Nat.add(List.length(&2, String, Bool.pick(List<&2, String>, Bool.and(Bool.and(b1, Bool.not(b2)), Bool.not(b3)),
      d <> more, more)), Nat.add(unsafe.miss(Imports.paths(Digest.edges(ds)), List.append(&2, String,
        Bool.pick(List<&2, String>, Bool.and(Bool.and(b1, Bool.not(b2)), Bool.not(b3)), d <> more, more), seen)), s2))
    : Nat}

def unsafe.fresh_count.at(ds, seen, d, more, b1, b2, b3, e1, e2, e3, w):
  match b1:
    case False{}:
      w
    case True{}:
      match b2:
        case True{}:
          w
        case False{}:
          match b3:
            case True{}:
              w
            case False{}:
              +rr = Imports.paths(Digest.edges(ds))
              +tt = List.append(&2, String, more, seen)
              ht = Equal.trans(Bool, Imports.has(tt, d), Bool.or(Imports.has(more, d), Imports.has(seen, d)), False{},
                unsafe.has_app(more, seen, d),
                Equal.trans(Bool, Bool.or(Imports.has(more, d), Imports.has(seen, d)), Imports.has(seen, d), False{},
                  Equal.cong(Bool, Bool, z => Bool.or(z, Imports.has(seen, d)), Imports.has(more, d), False{}, e3), e2))
              unsafe.fresh_count.new(unsafe.miss(rr, seen), List.length(&2, String, more), unsafe.miss(rr, tt),
                unsafe.miss(rr, d <> tt), w, unsafe.miss_cons1(rr, tt, d, e1, ht))

# the walk takes up only files new to what it has seen, each once: the
# count of read files not seen drops by at least as many
law unsafe.fresh_count:
  for +ds: List<&2, Digest.Digest>
  for xs: List<&2, String>
  for +seen: List<&2, String>
  exs s: Nat
  {unsafe.miss(Imports.paths(Digest.edges(ds)), seen)
    == Nat.add(List.length(&2, String, Imports.fresh(xs, seen, Imports.paths(Digest.edges(ds)))),
      Nat.add(unsafe.miss(Imports.paths(Digest.edges(ds)), List.append(&2, String, Imports.fresh(xs, seen,
        Imports.paths(Digest.edges(ds))), seen)), s)) : Nat}

def unsafe.fresh_count(ds, xs, seen):
  match xs:
    case Nil{}:
      +mm = unsafe.miss(Imports.paths(Digest.edges(ds)), seen)
      (0n, Equal.sym(Nat, Nat.add(mm, 0n), mm, unsafe.add_zero(mm)))
    case Con{+d, +rest}:
      +more = Imports.fresh(rest, seen, Imports.paths(Digest.edges(ds)))
      unsafe.fresh_count.at(ds, seen, d, more, Imports.has(Imports.paths(Digest.edges(ds)), d), Imports.has(seen, d),
        Imports.has(more, d), {==}, {==}, {==}, unsafe.fresh_count(ds, rest, seen))

# a count moved along an equality
law unsafe.retarget:
  for -a: Nat
  for -b: Nat
  for -c: Nat
  for e: {a == b : Nat}
  for w: &k: Nat -> {b == 1n+Nat.add(c, k) : Nat}
  exs k2: Nat
  {a == 1n+Nat.add(c, k2) : Nat}

def unsafe.retarget(a, b, c, e, w):
  (k, ek) = w
  +k1 = {k : Nat}
  (k1, Equal.trans(Nat, a, b, 1n+Nat.add(c, k1), e, ek))

# a start that was read: the fuel covers it and every read file it has not
# seen
law unsafe.miss_start:
  for +ds: List<&2, Digest.Digest>
  for +a: String
  for hr: {Imports.has(Imports.paths(Digest.edges(ds)), a) == True{} : Bool}
  exs k: Nat
  {List.length(&2, Digest.Digest, ds) == 1n+Nat.add(unsafe.miss(Imports.paths(Digest.edges(ds)), [a]), k) : Nat}

def unsafe.miss_start(ds, a, hr):
  +rr = Imports.paths(Digest.edges(ds))
  unsafe.retarget(List.length(&2, Digest.Digest, ds), unsafe.miss(rr, []), unsafe.miss(rr, [a]),
    Equal.trans(Nat, List.length(&2, Digest.Digest, ds), List.length(&2, String, rr), unsafe.miss(rr, []),
      Equal.sym(Nat, List.length(&2, String, rr), List.length(&2, Digest.Digest, ds), unsafe.len_paths(ds)),
      Equal.sym(Nat, unsafe.miss(rr, []), List.length(&2, String, rr), unsafe.miss_nil(rr))),
    unsafe.miss_cons1(rr, [], a, hr, {==}))

# a step's fuel, moved to the next step: what the step takes up is paid for
# by what it newly sees
law unsafe.shut_walk.step:
  for -f: Nat
  for +l: Nat
  for -m: Nat
  for +k: Nat
  for +ff: Nat
  for -la: Nat
  for +m2: Nat
  for -m3: Nat
  for h1: {f == Nat.add(l, Nat.add(m, k)) : Nat}
  for w: &s: Nat -> {m == Nat.add(ff, Nat.add(m2, s)) : Nat}
  for h3: {la == Nat.add(ff, l) : Nat}
  for h4: {m3 == m2 : Nat}
  for -gg: Type
  for ih: @k2: Nat -> {f == Nat.add(la, Nat.add(m3, k2)) : Nat} -> gg
  gg

def unsafe.shut_walk.step(f, l, m, k, ff, la, m2, m3, h1, w, h3, h4, _gg, ih):
  (s, e) = w
  +s1 = {s : Nat}
  ih(Nat.add(s1, k), unsafe.count_arith(f, l, m, k, ff, la, m2, m3, s1, h1, e, h3, h4))

# the walk returns a shut list: while fuel lasts the invariant holds, and
# the fuel covers the worklist and every read file not yet seen, so it lasts
# until the worklist is empty
law unsafe.shut_walk:
  for +ds: List<&2, Digest.Digest>
  for fuel: Nat
  for todo: List<&2, String>
  for +seen: List<&2, String>
  for k: Nat
  for hf: {fuel == Nat.add(List.length(&2, String, todo), Nat.add(unsafe.miss(Imports.paths(Digest.edges(ds)), seen),
    k)) : Nat}
  for hi: {unsafe.inv(ds, todo, seen, seen) == True{} : Bool}
  {Laws.unsafe.shut(ds, Imports.reach(fuel, todo, seen, Digest.edges(ds), Imports.paths(Digest.edges(ds))),
    Imports.reach(fuel, todo, seen, Digest.edges(ds), Imports.paths(Digest.edges(ds)))) == True{} : Bool}

def unsafe.shut_walk(ds, fuel, todo, seen, k, hf, hi):
  match fuel todo:
    case 0n Nil{}:
      Equal.trans(Bool, Laws.unsafe.shut(ds, seen, seen), unsafe.inv(ds, [], seen, seen), True{},
        Equal.sym(Bool, unsafe.inv(ds, [], seen, seen), Laws.unsafe.shut(ds, seen, seen), unsafe.inv_nil(ds, seen,
          seen)),
        hi)
    case 0n Con{_p, rest}:
      Empty.absurd({Laws.unsafe.shut(ds, seen, seen) == True{} : Bool},
        unsafe.zero_succ(Nat.add(List.length(&2, String, rest), Nat.add(unsafe.miss(Imports.paths(Digest.edges(ds)),
          seen), k)), hf))
    case 1n+_f Nil{}:
      Equal.trans(Bool, Laws.unsafe.shut(ds, seen, seen), unsafe.inv(ds, [], seen, seen), True{},
        Equal.sym(Bool, unsafe.inv(ds, [], seen, seen), Laws.unsafe.shut(ds, seen, seen), unsafe.inv_nil(ds, seen,
          seen)),
        hi)
    case 1n+(+f) Con{+p, +rest}:
      +rr = Imports.paths(Digest.edges(ds))
      +deps = Imports.deps_of(Digest.edges(ds), p)
      +found = Imports.fresh(deps, seen, rr)
      +rf = List.reverse(&2, String, found)
      +seen2 = List.append(&2, String, rf, seen)
      +todo2 = List.append(&2, String, found, rest)
      +hg = unsafe.in_pre(rf, seen, seen, unsafe.in_refl(seen))
      hfs = unsafe.in_suf(rf, seen, found, Equal.trans(Bool, unsafe.all_in(rf, found), unsafe.all_in(found, found),
        True{}, unsafe.in_rev_set(found, found), unsafe.in_refl(found)))
      hd = unsafe.fresh_held(ds, seen2, deps, seen, hg, hfs)
      hp = Equal.trans(Bool, Laws.unsafe.held(ds, seen2, Laws.unsafe.imports(ds, p)), Laws.unsafe.held(ds, seen2, deps),
        True{}, Equal.sym(Bool, Laws.unsafe.held(ds, seen2, deps), Laws.unsafe.held(ds, seen2,
          Laws.unsafe.imports(ds, p)),
          Equal.cong(List<&2, String>, Bool, z => Laws.unsafe.held(ds, seen2, z), deps, Laws.unsafe.imports(ds, p),
            unsafe.deps_imports(ds, p))), hd)
      ha = unsafe.inv_todo(ds, todo2, seen2, rf, unsafe.in_rev(todo2, found, unsafe.in_suf(found, rest, found,
        unsafe.in_refl(found))))
      hb = unsafe.inv_keep(ds, p, rest, seen, found, seen2, seen, hp, hg, hi)
      +hi2 = unsafe.inv_app(ds, todo2, seen2, rf, seen, ha, hb)
      +mm = unsafe.miss(rr, seen)
      unsafe.shut_walk.step(f, List.length(&2, String, rest), mm, k, List.length(&2, String, found),
        List.length(&2, String, todo2), unsafe.miss(rr, List.append(&2, String, found, seen)), unsafe.miss(rr, seen2),
        unsafe.succ_inj(f, Nat.add(List.length(&2, String, rest), Nat.add(mm, k)), hf),
        unsafe.fresh_count(ds, deps, seen), unsafe.len_app(found, rest), unsafe.miss_rev(rr, found, seen),
        {Laws.unsafe.shut(ds, Imports.reach(f, todo2, seen2, Digest.edges(ds), rr),
          Imports.reach(f, todo2, seen2, Digest.edges(ds), rr)) == True{} : Bool},
        k2 => h2 => unsafe.shut_walk(ds, f, todo2, seen2, k2, h2, hi2))

# a list shut over ps, held in another, leaves that one shut over ps
law unsafe.shut_grow:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for +tt: List<&2, String>
  for ps: List<&2, String>
  for +h: {Laws.unsafe.shut(ds, ss, ps) == True{} : Bool}
  for +hst: {unsafe.all_in(tt, ss) == True{} : Bool}
  {Laws.unsafe.shut(ds, tt, ps) == True{} : Bool}

def unsafe.shut_grow(ds, ss, tt, ps, h, hst):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      +hp = Laws.unsafe.held(ds, ss, Laws.unsafe.imports(ds, p))
      unsafe.and_true(Laws.unsafe.held(ds, tt, Laws.unsafe.imports(ds, p)), Laws.unsafe.shut(ds, tt, t),
        unsafe.held_grow(ds, ss, tt, Laws.unsafe.imports(ds, p), unsafe.and_l(hp, Laws.unsafe.shut(ds, ss, t), h), hst),
        unsafe.shut_grow(ds, ss, tt, t, unsafe.and_r(hp, Laws.unsafe.shut(ds, ss, t), h), hst))

# a list shut over ps is shut over any list that ps holds
law unsafe.shut_sub:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for +ps: List<&2, String>
  for qs: List<&2, String>
  for +hs: {Laws.unsafe.shut(ds, ss, ps) == True{} : Bool}
  for +hq: {unsafe.all_in(ps, qs) == True{} : Bool}
  {Laws.unsafe.shut(ds, ss, qs) == True{} : Bool}

def unsafe.shut_sub(ds, ss, ps, qs, hs, hq):
  match qs:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      unsafe.and_true(Laws.unsafe.held(ds, ss, Laws.unsafe.imports(ds, q)), Laws.unsafe.shut(ds, ss, t),
        unsafe.shut_at(ds, ss, ps, q, hs, unsafe.and_l(Imports.has(ps, q), unsafe.all_in(ps, t), hq)),
        unsafe.shut_sub(ds, ss, ps, t, hs, unsafe.and_r(Imports.has(ps, q), unsafe.all_in(ps, t), hq)))

# one digest, of the path or not, when the path is not in the run
law unsafe.unread_imports.at:
  for -deps: List<&2, String>
  for -more: List<&2, String>
  for -rd: Bool
  for b: Bool
  for hr: {Bool.or(b, rd) == False{} : Bool}
  for ih: {rd == False{} : Bool} -> {more == [] : List<&2, String>}
  {Bool.pick(List<&2, String>, b, deps, more) == [] : List<&2, String>}

def unsafe.unread_imports.at(deps, _more, _rd, b, hr, ih):
  match b:
    case True{}:
      Empty.absurd({deps == [] : List<&2, String>}, unsafe.false_true(Equal.sym(Bool, True{}, False{}, hr)))
    case False{}:
      ih(hr)

# a file not in the run imports nothing
law unsafe.unread_imports:
  for ds: List<&2, Digest.Digest>
  for +pp: String
  for h: {Laws.unsafe.read(ds, pp) == False{} : Bool}
  {Laws.unsafe.imports(ds, pp) == [] : List<&2, String>}

def unsafe.unread_imports(ds, pp, h):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, +norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, +rest}:
      unsafe.unread_imports.at(deps, Laws.unsafe.imports(rest, pp), Laws.unsafe.read(rest, pp), String.eq(norm, pp), h,
        z => unsafe.unread_imports(rest, pp, z))

# a walk with nothing to do returns what it has seen
law unsafe.idle:
  for +ds: List<&2, Digest.Digest>
  for fuel: Nat
  for +seen: List<&2, String>
  {Imports.reach(fuel, [], seen, Digest.edges(ds), Imports.paths(Digest.edges(ds))) == seen : List<&2, String>}

def unsafe.idle(_ds, fuel, _seen):
  match fuel:
    case 0n:
      {==}
    case 1n+_f:
      {==}

# a start that imports nothing reaches only itself
law unsafe.lone_w:
  for +ds: List<&2, Digest.Digest>
  for fuel: Nat
  for +from: String
  for h: {Imports.deps_of(Digest.edges(ds), from) == [] : List<&2, String>}
  {Imports.reach(fuel, [from], [from], Digest.edges(ds), Imports.paths(Digest.edges(ds))) == [from] : List<&2, String>}

def unsafe.lone_w(ds, fuel, from, h):
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      +rr = Imports.paths(Digest.edges(ds))
      %Equal.sym(List<&2, String>, Imports.deps_of(Digest.edges(ds), from), [], h) :
        {Imports.reach(f, List.append(&2, String, Imports.fresh(_, [from], rr), []),
          List.append(&2, String, List.reverse(&2, String, Imports.fresh(_, [from], rr)), [from]), Digest.edges(ds), rr)
          == [from] : List<&2, String>}
      unsafe.idle(ds, f, [from])

# a start that was read: the walk's fuel covers it
law unsafe.shut_top.go:
  for +ds: List<&2, Digest.Digest>
  for +from: String
  for w: &k: Nat -> {List.length(&2, Digest.Digest, ds)
    == 1n+Nat.add(unsafe.miss(Imports.paths(Digest.edges(ds)), [from]), k) : Nat}
  {Laws.unsafe.shut(ds, Imports.reach(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds),
    Imports.paths(Digest.edges(ds))), Imports.reach(List.length(&2, Digest.Digest, ds), [from], [from],
      Digest.edges(ds), Imports.paths(Digest.edges(ds)))) == True{} : Bool}

def unsafe.shut_top.go(ds, from, w):
  (k, e) = w
  +hh = Laws.unsafe.held(ds, [from], Laws.unsafe.imports(ds, from))
  unsafe.shut_walk(ds, List.length(&2, Digest.Digest, ds), [from], [from], k, e,
    unsafe.and_true(Bool.or(Imports.has([from], from), hh), True{},
      unsafe.or_l(Imports.has([from], from), hh, unsafe.or_l(String.eq(from, from), False{}, unsafe.srefl(from))),
        {==}))

# the walk from any start returns a shut list: a start that was read is
# covered by the fuel, and one that was not imports nothing
law unsafe.shut_top:
  for +ds: List<&2, Digest.Digest>
  for +from: String
  for b: Bool
  for eb: {Imports.has(Imports.paths(Digest.edges(ds)), from) == b : Bool}
  {Laws.unsafe.shut(ds, Imports.reach(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds),
    Imports.paths(Digest.edges(ds))), Imports.reach(List.length(&2, Digest.Digest, ds), [from], [from],
      Digest.edges(ds), Imports.paths(Digest.edges(ds)))) == True{} : Bool}

def unsafe.shut_top(ds, from, b, eb):
  match b:
    case True{}:
      unsafe.shut_top.go(ds, from, unsafe.miss_start(ds, from, eb))
    case False{}:
      +rr = Imports.paths(Digest.edges(ds))
      +ww = Imports.reach(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds), rr)
      er = Equal.trans(Bool, Laws.unsafe.read(ds, from), Imports.has(rr, from), False{},
        Equal.sym(Bool, Imports.has(rr, from), Laws.unsafe.read(ds, from), unsafe.read_paths(ds, from)), eb)
      +hn = unsafe.unread_imports(ds, from, er)
      hw = unsafe.lone_w(ds, List.length(&2, Digest.Digest, ds), from, Equal.trans(List<&2, String>,
        Imports.deps_of(Digest.edges(ds), from), Laws.unsafe.imports(ds, from), [], unsafe.deps_imports(ds, from), hn))
      %Equal.sym(List<&2, String>, ww, [from], hw) : {Laws.unsafe.shut(ds, _, _) == True{} : Bool}
      %Equal.sym(List<&2, String>, Laws.unsafe.imports(ds, from), [], hn) :
        {Bool.and(Laws.unsafe.held(ds, [from], _), True{}) == True{} : Bool}
      {==}

def Laws.unsafe_shut(ds, from):
  +ww = Imports.reach(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds),
    Imports.paths(Digest.edges(ds)))
  +rw = List.reverse(&2, String, ww)
  h = unsafe.shut_top(ds, from, Imports.has(Imports.paths(Digest.edges(ds)), from), {==})
  h2 = unsafe.shut_grow(ds, ww, rw, ww, h, Equal.trans(Bool, unsafe.all_in(rw, ww), unsafe.all_in(ww, ww), True{},
    unsafe.in_rev_set(ww, ww), unsafe.in_refl(ww)))
  unsafe.shut_sub(ds, rw, ww, rw, h2, unsafe.in_rev(ww, ww, unsafe.in_refl(ww)))


# Inert text (BOLT-RULE-INERT). Each rule gives the same findings on a
# source read with its comments and strings cut (Laws.inert.toks,
# Laws.inert.node) as on the source; two sources that read the same that way
# then have the same findings. A rule tests a token's kind before its text,
# or compares the text of a token of any kind with a name or a keyword,
# which never starts with `"` or `#`: a string's text, cut or not, never
# equals it. A kind is split only where the rule itself matches on one.

# Unit for False, Empty for True
def inert.false_ty(bb: Bool) -> Type:
  match bb:
    case False{}: Unit
    case True{}: Empty

# False is never True
law inert.false_true:
  for e: {False{} == True{} : Bool}
  Empty

def inert.false_true(e):
  %e : inert.false_ty(_)
  Unit{}

# the left of an and that holds holds
law inert.and_l:
  for a: Bool
  for -b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def inert.and_l(a, _b, e):
  match a:
    case True{}: {==}
    case False{}: Empty.absurd({False{} == True{} : Bool}, inert.false_true(e))

# the right of an and that holds holds
law inert.and_r:
  for a: Bool
  for -b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def inert.and_r(a, b, e):
  match a:
    case True{}: e
    case False{}: Empty.absurd({b == True{} : Bool}, inert.false_true(e))

# two facts that hold make their and hold
law inert.and_both:
  for -a: Bool
  for -b: Bool
  for ea: {a == True{} : Bool}
  for eb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def inert.and_both(a, b, ea, eb):
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# a Bool whose negation holds is False
law inert.not_true:
  for b: Bool
  for e: {Bool.not(b) == True{} : Bool}
  {b == False{} : Bool}

def inert.not_true(b, e):
  match b:
    case False{}: {==}
    case True{}: Empty.absurd({True{} == False{} : Bool}, inert.false_true(e))

# Unit for LT and GT, Empty for EQ
def inert.cmp_ty(cc: Cmp) -> Type:
  match cc:
    case LT{}: Unit
    case EQ{}: Empty
    case GT{}: Unit

# a comparison that is EQ is not LT
law inert.lt_eq:
  for e: {LT{} == EQ{} : Cmp}
  Empty

def inert.lt_eq(e):
  %e : inert.cmp_ty(_)
  Unit{}

# a comparison that is EQ is not GT
law inert.gt_eq:
  for e: {GT{} == EQ{} : Cmp}
  Empty

def inert.gt_eq(e):
  %e : inert.cmp_ty(_)
  Unit{}

# a word comparison that ends EQ was EQ on the bits below
law inert.fin_eq:
  for t: Cmp
  for -ab: Bool
  for -bb: Bool
  for e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}
  {t == EQ{} : Cmp}

def inert.fin_eq(t, _ab, _bb, e):
  match t:
    case LT{}: Empty.absurd({LT{} == EQ{} : Cmp}, inert.lt_eq(e))
    case EQ{}: {==}
    case GT{}: Empty.absurd({GT{} == EQ{} : Cmp}, inert.gt_eq(e))

# a word comparison that ends EQ had the same top bit
law inert.fin_bit:
  for t: Cmp
  for ab: Bool
  for bb: Bool
  for e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}
  {ab == bb : Bool}

def inert.fin_bit(t, ab, bb, e):
  match t:
    case LT{}: Empty.absurd({ab == bb : Bool}, inert.lt_eq(e))
    case GT{}: Empty.absurd({ab == bb : Bool}, inert.gt_eq(e))
    case EQ{}:
      match ab bb:
        case False{} False{}: {==}
        case False{} True{}: Empty.absurd({False{} == True{} : Bool}, inert.lt_eq(e))
        case True{} False{}: Empty.absurd({True{} == False{} : Bool}, inert.gt_eq(e))
        case True{} True{}: {==}

# two words that compare EQ are the same word
law inert.word_eq:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  for +e: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}

def inert.word_eq(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}: {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          hb = inert.fin_bit(Word.cmp(p, at, bt), ab, bb, e)
          ht = inert.word_eq(p, at, bt, inert.fin_eq(Word.cmp(p, at, bt), ab, bb, e))
          %hb : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
          %ht : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
          {==}

# two U32s that compare EQ are the same
law inert.u32_eq:
  for x: U32
  for y: U32
  for e: {U32.cmp(x, y) == EQ{} : Cmp}
  {x == y : U32}

def inert.u32_eq(x, y, e):
  match x y:
    case U32{wx} U32{wy}: Equal.cong(Word(32n), U32, w => U32{w}, wx, wy, inert.word_eq(32n, wx, wy, e))

# a marked char and an unmarked one never compare EQ
law inert.differ:
  for c: Cmp
  for +x: U32
  for +y: U32
  for ec: {U32.cmp(x, y) == c : Cmp}
  for ex: {Laws.inert.mark(Chr{x}) == True{} : Bool}
  for ey: {Laws.inert.mark(Chr{y}) == False{} : Bool}
  {Cmp.is_eq(c) == False{} : Bool}

def inert.differ(c, x, y, ec, ex, ey):
  match c:
    case LT{}: {==}
    case GT{}: {==}
    case EQ{}:
      +my = Equal.trans(Bool, Laws.inert.mark(Chr{y}), Laws.inert.mark(Chr{x}), True{},
        Equal.cong(U32, Bool, z => Laws.inert.mark(Chr{z}), y, x, Equal.sym(U32, x, y, inert.u32_eq(x, y, ec))), ex)
      Empty.absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, inert.false_true(Equal.trans(Bool, False{},
        Laws.inert.mark(Chr{y}), True{}, Equal.sym(Bool, Laws.inert.mark(Chr{y}), False{}, ey), my)))

# a string comparison whose first chars differ is not equal, whatever follows
law inert.fin_false:
  for c: Cmp
  for -r: String
  for -ys: String
  for -h1: Char
  for -h2: Char
  for ec: {Cmp.is_eq(c) == False{} : Bool}
  {String.eq.fin(String.cmp.fin(r, ys, ((h1, h2), c))) == False{} : Bool}

def inert.fin_false(c, r, ys, h1, h2, ec):
  match c:
    case LT{}: {==}
    case GT{}: {==}
    case EQ{}:
      Empty.absurd({String.eq.fin(String.cmp.fin(r, ys, ((h1, h2), EQ{}))) == False{} : Bool},
        inert.false_true(Equal.sym(Bool, True{}, False{}, ec)))

# a text with a marked first char is never equal to one with an unmarked one
law inert.neq.con:
  for h: Char
  for -r: String
  for y: Char
  for -ys: String
  for et: {Laws.inert.mark(h) == True{} : Bool}
  for ex: {Laws.inert.mark(y) == False{} : Bool}
  {String.eq(SCon{h, r}, SCon{y, ys}) == False{} : Bool}

def inert.neq.con(h, r, y, ys, et, ex):
  match h y:
    case Chr{+a} Chr{+b}:
      inert.fin_false(U32.cmp(a, b), r, ys, Chr{a}, Chr{b}, inert.differ(U32.cmp(a, b), a, b, {==}, et, ex))

# a marked text is never equal to an unmarked one
law inert.neq:
  for t: String
  for x: String
  for et: {Laws.inert.marked(t) == True{} : Bool}
  for ex: {Laws.inert.marked(x) == False{} : Bool}
  {String.eq(t, x) == False{} : Bool}

def inert.neq(t, x, et, ex):
  match t x:
    case SNil{} x: Empty.absurd({String.eq(SNil{}, x) == False{} : Bool}, inert.false_true(et))
    case SCon{h, r} SNil{}: {==}
    case SCon{h, r} SCon{y, ys}: inert.neq.con(h, r, y, ys, et, ex)

# a text cut to its first char is marked when the text is
law inert.cut_marked:
  for t: String
  for et: {Laws.inert.marked(t) == True{} : Bool}
  {Laws.inert.marked(Laws.inert.cut(t)) == True{} : Bool}

def inert.cut_marked(t, et):
  match t:
    case SNil{}: et
    case SCon{h, r}: et

# a token's text read that way compares with an unmarked text as it did
law inert.eq_keep:
  for b: Bool
  for +t: String
  for +x: String
  for +ef: {Laws.inert.fits.go(b, t) == True{} : Bool}
  for +ex: {Laws.inert.marked(x) == False{} : Bool}
  {String.eq(Laws.inert.keep(b, t), x) == String.eq(t, x) : Bool}

def inert.eq_keep(b, t, x, ef, ex):
  match b:
    case False{}: {==}
    case True{}:
      Equal.trans(Bool, String.eq(Laws.inert.cut(t), x), False{}, String.eq(t, x),
        inert.neq(Laws.inert.cut(t), x, inert.cut_marked(t, ef), ex),
        Equal.sym(Bool, String.eq(t, x), False{}, inert.neq(t, x, ef, ex)))

# a test guarded by a kind that is never cut reads a token's text as it was
law inert.guard:
  for c: Bool
  for +b: Bool
  for +t: String
  for -p: String -> Bool
  for e: {Bool.and(c, b) == False{} : Bool}
  {Bool.and(c, p(Laws.inert.keep(b, t))) == Bool.and(c, p(t)) : Bool}

def inert.guard(c, b, t, p, e):
  match c:
    case False{}: {==}
    case True{}:
      %Equal.sym(Bool, b, False{}, e) : {p(Laws.inert.keep(_, t)) == p(t) : Bool}
      {==}

# two sources whose readings agree, each reading giving what its source
# gives, give the same
law inert.via:
  for -A: Data
  for -f: A -> List<&2, F.Finding>
  for -a: A
  for -b: A
  for -ca: A
  for -cb: A
  for ea: {f(ca) == f(a) : List<&2, F.Finding>}
  for eb: {f(cb) == f(b) : List<&2, F.Finding>}
  for e: {ca == cb : A}
  {f(a) == f(b) : List<&2, F.Finding>}

def inert.via(A, f, a, b, ca, cb, ea, eb, e):
  Equal.trans(List<&2, F.Finding>, f(a), f(ca), f(b), Equal.sym(List<&2, F.Finding>, f(ca), f(a), ea),
    Equal.trans(List<&2, F.Finding>, f(ca), f(cb), f(b), Equal.cong(A, List<&2, F.Finding>, f, ca, cb, e), eb))

# hole
# ----

# a capitalized name is never cut: one split, for the one kind test on text
law inert.hole.upper:
  for k: Lex.TokKind
  {Bool.and(Calls.kind.upper(k), Laws.inert.blanks(k)) == False{} : Bool}

def inert.hole.upper(k):
  match k:
    case Lex.TName{}: {==}
    case Lex.TUpper{}: {==}
    case Lex.TDotted{}: {==}
    case Lex.TWild{}: {==}
    case Lex.TKey{}: {==}
    case Lex.TNum{}: {==}
    case Lex.TStr{}: {==}
    case Lex.TChar{}: {==}
    case Lex.TComment{}: {==}
    case Lex.TSpace{}: {==}
    case Lex.TNewline{}: {==}
    case Lex.TOp{}: {==}
    case Lex.TColon{}: {==}
    case Lex.TEq{}: {==}
    case Lex.TBind{}: {==}
    case Lex.TArrow{}: {==}
    case Lex.TLam{}: {==}
    case Lex.TAll{}: {==}
    case Lex.TAmp{}: {==}
    case Lex.TOpen{}: {==}
    case Lex.TClose{}: {==}
    case Lex.TComma{}: {==}

# an operator is never cut
law inert.hole.op:
  for k: Lex.TokKind
  {Bool.and(Calls.kind.oper(k), Laws.inert.blanks(k)) == False{} : Bool}

def inert.hole.op(k):
  match k:
    case Lex.TName{}: {==}
    case Lex.TUpper{}: {==}
    case Lex.TDotted{}: {==}
    case Lex.TWild{}: {==}
    case Lex.TKey{}: {==}
    case Lex.TNum{}: {==}
    case Lex.TStr{}: {==}
    case Lex.TChar{}: {==}
    case Lex.TComment{}: {==}
    case Lex.TSpace{}: {==}
    case Lex.TNewline{}: {==}
    case Lex.TOp{}: {==}
    case Lex.TColon{}: {==}
    case Lex.TEq{}: {==}
    case Lex.TBind{}: {==}
    case Lex.TArrow{}: {==}
    case Lex.TLam{}: {==}
    case Lex.TAll{}: {==}
    case Lex.TAmp{}: {==}
    case Lex.TOpen{}: {==}
    case Lex.TClose{}: {==}
    case Lex.TComma{}: {==}

# the TODO test reads kinds, and the text of a capitalized name only
law inert.hole.todo:
  for ts: List<&2, Lex.Tok>
  {Hole.check.todo(Laws.inert.toks(ts)) == Hole.check.todo(ts) : Bool}

def inert.hole.todo(ts):
  match ts:
    case Nil{}: {==}
    case Con{Lex.Tok{+k, +t, l, c}, +rest}:
      +b = Laws.inert.blanks(k)
      %inert.guard(Calls.kind.upper(k), b, t, z => String.eq(z, "TODO"), inert.hole.upper(k)) :
        {Lazy.stop(Bool, Lex.significant(k), Bool.and(Calls.kind.upper(k), String.eq(Laws.inert.keep(b, t), "TODO")),
          _u => Hole.check.todo(Laws.inert.toks(rest)))
            == Lazy.stop(Bool, Lex.significant(k), _, _u => Hole.check.todo(rest))
          : Bool}
      %inert.hole.todo(rest) :
        {Lazy.stop(Bool, Lex.significant(k), Bool.and(Calls.kind.upper(k), String.eq(Laws.inert.keep(b, t), "TODO")),
          _u => Hole.check.todo(Laws.inert.toks(rest))) == Lazy.stop(Bool, Lex.significant(k),
          Bool.and(Calls.kind.upper(k), String.eq(Laws.inert.keep(b, t), "TODO")), _u => _) : Bool}
      {==}

# the width reads kinds and positions only
law inert.hole.width:
  for ts: List<&2, Lex.Tok>
  for +line: U32
  for +col: U32
  {Hole.check.width(Laws.inert.toks(ts), line, col) == Hole.check.width(ts, line, col) : U32}

def inert.hole.width(ts, line, col):
  match ts:
    case Nil{}: {==}
    case Con{Lex.Tok{+k, t, +l, +c}, +rest}:
      +w = Bool.pick(U32, U32.is_eq(l, line), U32.add(U32.sub(c, col), 4), 1)
      %inert.hole.width(rest, line, col) : {Lazy.stop(U32, Lex.significant(k), w,
        _u => Hole.check.width(Laws.inert.toks(rest), line, col))
          == Lazy.stop(U32, Lex.significant(k), w, _u => _) : U32}
      {==}

# hole's walk reads no comment or string
law inert.hole.go:
  for ts: List<&2, Lex.Tok>
  for +path: String
  {Hole.check.go(Laws.inert.toks(ts), path) == Hole.check.go(ts, path) : List<&2, F.Finding>}

def inert.hole.go(ts, path):
  match ts:
    case Nil{}: {==}
    case Con{Lex.Tok{+k, +q, +l, +c}, +rest}:
      +b = Laws.inert.blanks(k)
      +cr = Laws.inert.toks(rest)
      +hit = Bool.and(Calls.kind.oper(k), Lazy.and_then(String.eq(Laws.inert.keep(b, q), "?"),
        _u => Hole.check.todo(cr)))
      +lhs = Lazy.stop(List<&2, F.Finding>, Bool.not(hit), Hole.check.go(cr, path), _u => F.Finding{path, l, c,
        Hole.check.width(cr, l, c), "hole", "This ?TODO hole is still unfilled."} <> Hole.check.go(cr, path))
      %inert.hole.go(rest, path) : {lhs == Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Calls.kind.oper(k),
        Lazy.and_then(String.eq(q, "?"), _u => Hole.check.todo(rest)))), _, _u => F.Finding{path, l, c,
        Hole.check.width(rest, l, c), "hole", "This ?TODO hole is still unfilled."} <> _) : List<&2, F.Finding>}
      %inert.hole.width(rest, l, c) : {lhs == Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Calls.kind.oper(k),
        Lazy.and_then(String.eq(q, "?"), _u => Hole.check.todo(rest)))), Hole.check.go(cr, path), _u => F.Finding{path,
        l, c, _, "hole", "This ?TODO hole is still unfilled."} <> Hole.check.go(cr, path)) : List<&2, F.Finding>}
      %inert.hole.todo(rest) : {lhs == Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Calls.kind.oper(k),
        Lazy.and_then(String.eq(q, "?"), _u => _))), Hole.check.go(cr, path), _u => F.Finding{path, l, c,
        Hole.check.width(cr, l, c), "hole", "This ?TODO hole is still unfilled."} <> Hole.check.go(cr, path)) : List<&2, F.Finding>}
      %inert.guard(Calls.kind.oper(k), b, q, z => Lazy.and_then(String.eq(z, "?"), _u => Hole.check.todo(cr)),
        inert.hole.op(k)) : {lhs == Lazy.stop(List<&2, F.Finding>, Bool.not(_), Hole.check.go(cr, path),
          _u => F.Finding{path, l, c, Hole.check.width(cr, l, c), "hole", "This ?TODO hole is still unfilled."}
          <> Hole.check.go(cr, path)) : List<&2, F.Finding>}
      {==}

def Laws.inert_hole(path, _text, toks, _tree, _bound, _items, _text2, toks2, _tree2, _bound2, _items2, e):
  inert.via(List<&2, Lex.Tok>, z => Hole.check.on(z, path), toks, toks2, Laws.inert.toks(toks), Laws.inert.toks(toks2),
    Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>, z => Lazy.stop(List<&2, F.Finding>, Paths.is_laws(path), [],
      _u => z), Hole.check.go(Laws.inert.toks(toks), path), Hole.check.go(toks, path), inert.hole.go(toks, path)),
    Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>, z => Lazy.stop(List<&2, F.Finding>, Paths.is_laws(path), [],
      _u => z), Hole.check.go(Laws.inert.toks(toks2), path), Hole.check.go(toks2, path), inert.hole.go(toks2, path)), e)

# put
# ---

# reading the tokens that way commutes with a pick between two lists that
# differ by one token in front
law inert.put.pick:
  for b: Bool
  for +x: Lex.Tok
  for +xs: List<&2, Lex.Tok>
  {Laws.inert.toks(Bool.pick(List<&2, Lex.Tok>, b, x <> xs, xs))
    == Bool.pick(List<&2, Lex.Tok>, b, Laws.inert.tok(x) <> Laws.inert.toks(xs),
      Laws.inert.toks(xs)) : List<&2, Lex.Tok>}

def inert.put.pick(b, _x, _xs):
  match b:
    case True{}: {==}
    case False{}: {==}

# the significant tokens of the tokens read that way are the significant
# tokens read that way
law inert.put.sig:
  for ts: List<&2, Lex.Tok>
  {T.sig(Laws.inert.toks(ts)) == Laws.inert.toks(T.sig(ts)) : List<&2, Lex.Tok>}

def inert.put.sig(ts):
  match ts:
    case Nil{}: {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      +x = {Lex.Tok{k, Laws.inert.keep(Laws.inert.blanks(k), t), l, c} : Lex.Tok}
      +cs = Laws.inert.toks(T.sig(rest))
      %Equal.sym(List<&2, Lex.Tok>, T.sig(Laws.inert.toks(rest)), cs, inert.put.sig(rest)) :
        {Bool.pick(List<&2, Lex.Tok>, Lex.significant(k), x <> _, _) == Laws.inert.toks(T.sig(Lex.Tok{k, t, l,
          c} <> rest))
          : List<&2, Lex.Tok>}
      Equal.sym(List<&2, Lex.Tok>, Laws.inert.toks(T.sig(Lex.Tok{k, t, l, c} <> rest)),
        Bool.pick(List<&2, Lex.Tok>, Lex.significant(k), x <> cs, cs),
        inert.put.pick(Lex.significant(k), Lex.Tok{k, t, l, c}, T.sig(rest)))

# a pick between two lists that differ by one token in front keeps the
# tokens as the lexer makes them
law inert.put.pick_ok:
  for b: Bool
  for +x: Lex.Tok
  for +xs: List<&2, Lex.Tok>
  for e: {Bool.and(Laws.inert.fits(x), Laws.inert.oks(xs)) == True{} : Bool}
  for er: {Laws.inert.oks(xs) == True{} : Bool}
  {Laws.inert.oks(Bool.pick(List<&2, Lex.Tok>, b, x <> xs, xs)) == True{} : Bool}

def inert.put.pick_ok(b, _x, _xs, e, er):
  match b:
    case True{}: e
    case False{}: er

# the significant tokens of tokens as the lexer makes them are too
law inert.put.sig_ok:
  for ts: List<&2, Lex.Tok>
  for +e: {Laws.inert.oks(ts) == True{} : Bool}
  {Laws.inert.oks(T.sig(ts)) == True{} : Bool}

def inert.put.sig_ok(ts, e):
  match ts:
    case Nil{}: {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      +h = {Lex.Tok{k, t, l, c} : Lex.Tok}
      +er = inert.put.sig_ok(rest, inert.and_r(Laws.inert.fits(h), Laws.inert.oks(rest), e))
      inert.put.pick_ok(Lex.significant(k), h, T.sig(rest),
        inert.and_both(Laws.inert.fits(h), Laws.inert.oks(T.sig(rest)), inert.and_l(Laws.inert.fits(h),
          Laws.inert.oks(rest), e), er), er)

# the token after `def` is `Map.put` as it was
law inert.put.named:
  for ts: List<&2, Lex.Tok>
  for +e: {Laws.inert.oks(ts) == True{} : Bool}
  {Put.defines.named(Laws.inert.toks(ts)) == Put.defines.named(ts) : Bool}

def inert.put.named(ts, e):
  match ts:
    case Nil{}: {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      inert.eq_keep(Laws.inert.blanks(k), t, "Map.put",
        inert.and_l(Laws.inert.fits(Lex.Tok{k, t, l, c}), Laws.inert.oks(rest), e), {==})

# put's exemption test reads no comment or string: a keyword's text is
# compared with `def`, which no string equals
law inert.put.defines:
  for ts: List<&2, Lex.Tok>
  for +e: {Laws.inert.oks(ts) == True{} : Bool}
  {Put.defines(Laws.inert.toks(ts)) == Put.defines(ts) : Bool}

def inert.put.defines(ts, e):
  match ts:
    case Nil{}: {==}
    case Con{Lex.Tok{+k, +d, +l, +c}, +rest}:
      +er = inert.and_r(Laws.inert.fits(Lex.Tok{k, d, l, c}), Laws.inert.oks(rest), e)
      +cr = Laws.inert.toks(rest)
      +dd = Laws.inert.keep(Laws.inert.blanks(k), d)
      +lhs = Lazy.or_else(Bool.and(Put.defines.key(k), Bool.and(String.eq(dd, "def"), Put.defines.named(cr))),
        _u => Put.defines(cr))
      %inert.eq_keep(Laws.inert.blanks(k), d, "def", inert.and_l(Laws.inert.fits(Lex.Tok{k, d, l, c}),
        Laws.inert.oks(rest), e), {==}) : {lhs == Lazy.or_else(Bool.and(Put.defines.key(k), Bool.and(_,
          Put.defines.named(rest))), _u => Put.defines(rest)) : Bool}
      %inert.put.named(rest, er) : {lhs == Lazy.or_else(Bool.and(Put.defines.key(k), Bool.and(String.eq(dd, "def"), _)),
        _u => Put.defines(rest)) : Bool}
      %inert.put.defines(rest, er) : {lhs == Lazy.or_else(Bool.and(Put.defines.key(k), Bool.and(String.eq(dd, "def"),
        Put.defines.named(cr))), _u => _) : Bool}
      {==}

# a dotted name then an open bracket, their texts read that way: compared
# with `Map.put` and `(` as they were
law inert.put.call:
  for +b1: Bool
  for +t: String
  for +b2: Bool
  for +o: String
  for +l: U32
  for +c: U32
  for +path: String
  for +more: List<&2, F.Finding>
  for +e1: {Laws.inert.fits.go(b1, t) == True{} : Bool}
  for +e2: {Laws.inert.fits.go(b2, o) == True{} : Bool}
  {Put.calls.one(Laws.inert.keep(b1, t), Laws.inert.keep(b2, o), l, c, path, more)
    == Put.calls.one(t, o, l, c, path, more)
    : List<&2, F.Finding>}

def inert.put.call(b1, t, b2, o, l, c, path, more, e1, e2):
  +x = {F.Finding{path, l, c, 7, "put", "Map.put does not compare keys, so a new key can overwrite an existing entry; use Map.set."}
    : F.Finding}
  +lhs = Put.calls.one(Laws.inert.keep(b1, t), Laws.inert.keep(b2, o), l, c, path, more)
  %inert.eq_keep(b1, t, "Map.put", e1, {==}) : {lhs == Bool.pick(List<&2, F.Finding>, Bool.and(_, String.eq(o, "(")),
    x <> more, more) : List<&2, F.Finding>}
  %inert.eq_keep(b2, o, "(", e2, {==}) : {lhs == Bool.pick(List<&2, F.Finding>,
    Bool.and(String.eq(Laws.inert.keep(b1, t), "Map.put"), _), x <> more, more) : List<&2, F.Finding>}
  {==}

# put's walk reads no comment or string: it tests kinds, then compares texts
# with `Map.put` and `(`
law inert.put.calls:
  for ts: List<&2, Lex.Tok>
  for +path: String
  for +e: {Laws.inert.oks(ts) == True{} : Bool}
  {Put.calls(Laws.inert.toks(ts), path) == Put.calls(ts, path) : List<&2, F.Finding>}

def inert.put.calls(ts, path, e):
  match ts:
    case Nil{}: {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      match rest:
        case Nil{}: {==}
        case Con{Lex.Tok{+k2, +o, +l2, +c2}, +r2}:
          +h1 = {Lex.Tok{k, t, l, c} : Lex.Tok}
          +h2 = {Lex.Tok{k2, o, l2, c2} : Lex.Tok}
          +er = inert.and_r(Laws.inert.fits(h1), Laws.inert.oks(rest), e)
          +e2 = inert.and_r(Laws.inert.fits(h2), Laws.inert.oks(r2), er)
          +cr = Laws.inert.toks(rest)
          +cond = Bool.and(Put.calls.dotted(k), Lex.is_open(k2))
          +tt = Laws.inert.keep(Laws.inert.blanks(k), t)
          +oo = Laws.inert.keep(Laws.inert.blanks(k2), o)
          +lhs = Lazy.either(List<&2, F.Finding>, cond, _u => Put.calls.one(tt, oo, l, c, path,
            Put.calls(Laws.inert.toks(r2), path)), _v => Put.calls(cr, path))
          %inert.put.calls(rest, path, er) : {lhs == Lazy.either(List<&2, F.Finding>, cond,
            _u => Put.calls.one(t, o, l, c, path, Put.calls(r2, path)), _v => _) : List<&2, F.Finding>}
          %inert.put.calls(r2, path, e2) : {lhs == Lazy.either(List<&2, F.Finding>, cond,
            _u => Put.calls.one(t, o, l, c, path, _), _v => Put.calls(cr, path)) : List<&2, F.Finding>}
          %inert.put.call(Laws.inert.blanks(k), t, Laws.inert.blanks(k2), o, l, c, path,
            Put.calls(Laws.inert.toks(r2), path), inert.and_l(Laws.inert.fits(h1), Laws.inert.oks(rest), e),
            inert.and_l(Laws.inert.fits(h2), Laws.inert.oks(r2), er)) : {lhs == Lazy.either(List<&2, F.Finding>, cond,
              _u => _, _v => Put.calls(cr, path)) : List<&2, F.Finding>}
          {==}

# put's check reads no comment or string
law inert.put.on:
  for +ts: List<&2, Lex.Tok>
  for +path: String
  for +e: {Laws.inert.oks(ts) == True{} : Bool}
  {Put.check.on(T.sig(Laws.inert.toks(ts)), path) == Put.check.on(T.sig(ts), path) : List<&2, F.Finding>}

def inert.put.on(ts, path, e):
  +s = T.sig(ts)
  +es = inert.put.sig_ok(ts, e)
  +cs = Laws.inert.toks(s)
  %Equal.sym(List<&2, Lex.Tok>, T.sig(Laws.inert.toks(ts)), cs, inert.put.sig(ts)) :
    {Put.check.on(_, path) == Put.check.on(s, path) : List<&2, F.Finding>}
  %inert.put.defines(s, es) : {Lazy.stop(List<&2, F.Finding>, Put.defines(cs), [], _u => Put.calls(cs, path))
    == Lazy.stop(List<&2, F.Finding>, _, [], _u => Put.calls(s, path)) : List<&2, F.Finding>}
  %inert.put.calls(s, path, es) : {Lazy.stop(List<&2, F.Finding>, Put.defines(cs), [], _u => Put.calls(cs, path))
    == Lazy.stop(List<&2, F.Finding>, Put.defines(cs), [], _u => _) : List<&2, F.Finding>}
  {==}

def Laws.inert_put(path, _text, toks, _tree, _bound, _items, _text2, toks2, _tree2, _bound2, _items2, ok, ok2, e):
  inert.via(List<&2, Lex.Tok>, z => Put.check.on(T.sig(z), path), toks, toks2, Laws.inert.toks(toks),
    Laws.inert.toks(toks2), inert.put.on(toks, path, ok), inert.put.on(toks2, path, ok2), e)

# the tree rules: what calls.bend gives them
# ------------------------------------------

# a name no string or comment can equal: it does not start with `"` or `#`
def inert.plain(mm: Maybe<&2, String>) -> Bool:
  match mm:
    case None{}: True{}
    case Some{name}: Bool.not(Laws.inert.marked(name))

# the defs, their signatures and bodies each read that way
def inert.defs(ds: List<&2, Calls.Def>) -> List<&2, Calls.Def>:
  match ds:
    case Nil{}: Nil{}
    case Con{Calls.Def{name, sig, body}, rest}: Calls.Def{name, Laws.inert.node(sig),
      Laws.inert.node(body)} <> inert.defs(rest)

# every def as the lexer makes it: a plain name, and leaves that fit
def inert.dok(ds: List<&2, Calls.Def>) -> Bool:
  match ds:
    case Nil{}: True{}
    case Con{Calls.Def{name, sig, body}, rest}:
      Bool.and(Bool.and(Bool.not(Laws.inert.marked(name)), Bool.and(Laws.inert.ok(sig), Laws.inert.ok(body))),
        inert.dok(rest))

# the chains, each read that way
def inert.nodes(ns: List<&2, Tree.Node>) -> List<&2, Tree.Node>:
  match ns:
    case Nil{}: Nil{}
    case Con{h, t}: Laws.inert.node(h) <> inert.nodes(t)

# every chain's leaves fit
def inert.noks(ns: List<&2, Tree.Node>) -> Bool:
  match ns:
    case Nil{}: True{}
    case Con{h, t}: Bool.and(Laws.inert.ok(h), inert.noks(t))

# a name that can be declared is never cut
law inert.name_code:
  for k: Lex.TokKind
  {Bool.and(Bind.declared.is_name(k), Laws.inert.blanks(k)) == False{} : Bool}

def inert.name_code(k):
  match k:
    case Lex.TName{}: {==}
    case Lex.TUpper{}: {==}
    case Lex.TDotted{}: {==}
    case Lex.TWild{}: {==}
    case Lex.TKey{}: {==}
    case Lex.TNum{}: {==}
    case Lex.TStr{}: {==}
    case Lex.TChar{}: {==}
    case Lex.TComment{}: {==}
    case Lex.TSpace{}: {==}
    case Lex.TNewline{}: {==}
    case Lex.TOp{}: {==}
    case Lex.TColon{}: {==}
    case Lex.TEq{}: {==}
    case Lex.TBind{}: {==}
    case Lex.TArrow{}: {==}
    case Lex.TLam{}: {==}
    case Lex.TAll{}: {==}
    case Lex.TAmp{}: {==}
    case Lex.TOpen{}: {==}
    case Lex.TClose{}: {==}
    case Lex.TComma{}: {==}

# a name picked by a kind that is never cut, as it was
law inert.name_pick:
  for c: Bool
  for +b: Bool
  for +t: String
  for e: {Bool.and(c, b) == False{} : Bool}
  {Bool.pick(Maybe<&2, String>, c, Some{Laws.inert.keep(b, t)}, None{})
    == Bool.pick(Maybe<&2, String>, c, Some{t}, None{}) : Maybe<&2, String>}

def inert.name_pick(c, b, t, e):
  match c:
    case False{}: {==}
    case True{}:
      %Equal.sym(Bool, b, False{}, e) : {Bool.pick(Maybe<&2, String>, True{}, Some{Laws.inert.keep(_, t)}, None{})
        == Bool.pick(Maybe<&2, String>, True{}, Some{t}, None{}) : Maybe<&2, String>}
      {==}

# the name right after a statement's keyword, as it was
law inert.declared.go:
  for kids: Tree.Node
  {Bind.declared.go(Laws.inert.node(kids)) == Bind.declared.go(kids) : Maybe<&2, String>}

def inert.declared.go(kids):
  match kids:
    case Tree.NCons{h, _rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, t, _l, _c}:
              inert.name_pick(Bind.declared.is_name(k), Laws.inert.blanks(k), t, inert.name_code(k))
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a choice whose test and both branches read as they did
law inert.either:
  for -A: Type
  for -c1: Bool
  for -c2: Bool
  for -a1: A
  for -a2: A
  for -b1: A
  for -b2: A
  for ec: {c1 == c2 : Bool}
  for ea: {a1 == a2 : A}
  for eb: {b1 == b2 : A}
  {Lazy.either(A, c1, _u => a1, _v => b1) == Lazy.either(A, c2, _u => a2, _v => b2) : A}

def inert.either(A, c1, _c2, a1, a2, b1, b2, ec, ea, eb):
  %ec : {Lazy.either(A, c1, _u => a1, _v => b1) == Lazy.either(A, _, _u => a2, _v => b2) : A}
  %ea : {Lazy.either(A, c1, _u => a1, _v => b1) == Lazy.either(A, c1, _u => _, _v => b2) : A}
  %eb : {Lazy.either(A, c1, _u => a1, _v => b1) == Lazy.either(A, c1, _u => a1, _v => _) : A}
  {==}

# a node read that way is a leaf of the kind it was
law inert.leaf_kind:
  for nn: Tree.Node
  {Calls.leaf.kind(Laws.inert.node(nn)) == Calls.leaf.kind(nn) : Maybe<&2, Lex.TokKind>}

def inert.leaf_kind(nn):
  match nn:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# a node read that way is a keyword as it was
law inert.declared.key:
  for nn: Tree.Node
  {Bind.declared.key(Laws.inert.node(nn)) == Bind.declared.key(nn) : Bool}

def inert.declared.key(nn):
  match nn:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# the name a statement declares, as it was
law inert.declared:
  for kids: Tree.Node
  {Bind.declared(Laws.inert.node(kids)) == Bind.declared(kids) : Maybe<&2, String>}

def inert.declared(kids):
  match kids:
    case Tree.NCons{+h, +rest}:
      inert.either(Maybe<&2, String>, Bind.declared.key(Laws.inert.node(h)), Bind.declared.key(h),
        Bind.declared.go(Laws.inert.node(rest)), Bind.declared.go(rest), Bind.declared(Laws.inert.node(rest)),
        Bind.declared(rest), inert.declared.key(h), inert.declared.go(rest), inert.declared(rest))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a name picked by a kind that is never cut, from a leaf that fits, is plain
law inert.plain_pick:
  for c: Bool
  for +b: Bool
  for +t: String
  for e1: {Bool.and(c, b) == False{} : Bool}
  for e2: {Laws.inert.fits.go(b, t) == True{} : Bool}
  {inert.plain(Bool.pick(Maybe<&2, String>, c, Some{t}, None{})) == True{} : Bool}

def inert.plain_pick(c, b, t, e1, e2):
  match c:
    case False{}: {==}
    case True{}:
      Equal.trans(Bool, Laws.inert.fits.go(False{}, t), Laws.inert.fits.go(b, t), True{},
        Equal.cong(Bool, Bool, z => Laws.inert.fits.go(z, t), False{}, b, Equal.sym(Bool, b, False{}, e1)), e2)

# the name right after the keyword is a name: plain, when its leaf fits
law inert.plain.go:
  for kids: Tree.Node
  for +e: {Laws.inert.ok(kids) == True{} : Bool}
  {inert.plain(Bind.declared.go(kids)) == True{} : Bool}

def inert.plain.go(kids, e):
  match kids:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              inert.plain_pick(Bind.declared.is_name(k), Laws.inert.blanks(k), t, inert.name_code(k),
                inert.and_l(Laws.inert.fits(Lex.Tok{k, t, l, c}), Laws.inert.ok(rest), e))
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a choice both of whose branches hold a test holds it
law inert.either_ok:
  for -A: Type
  for c: Bool
  for -p: A -> Bool
  for -a: A
  for -b: A
  for ea: {p(a) == True{} : Bool}
  for eb: {p(b) == True{} : Bool}
  {p(Lazy.either(A, c, _u => a, _v => b)) == True{} : Bool}

def inert.either_ok(_A, c, _p, _a, _b, ea, eb):
  match c:
    case True{}: ea
    case False{}: eb

# the name a statement declares is plain, when its leaves fit
law inert.plain.declared:
  for kids: Tree.Node
  for +e: {Laws.inert.ok(kids) == True{} : Bool}
  {inert.plain(Bind.declared(kids)) == True{} : Bool}

def inert.plain.declared(kids, e):
  match kids:
    case Tree.NCons{+h, +rest}:
      +er = inert.and_r(Laws.inert.ok(h), Laws.inert.ok(rest), e)
      inert.either_ok(Maybe<&2, String>, Bind.declared.key(h), z => inert.plain(z), Bind.declared.go(rest),
        Bind.declared(rest), inert.plain.go(rest, er), inert.plain.declared(rest, er))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# pushing a def commutes with reading the defs that way
law inert.defs.push:
  for mm: Maybe<&2, String>
  for +sig: Tree.Node
  for +body: Tree.Node
  for +acc: List<&2, Calls.Def>
  {Calls.defs.push(mm, Laws.inert.node(sig), Laws.inert.node(body), inert.defs(acc))
    == inert.defs(Calls.defs.push(mm, sig, body, acc)) : List<&2, Calls.Def>}

def inert.defs.push(mm, _sig, _body, _acc):
  match mm:
    case None{}: {==}
    case Some{name}: {==}

# pushing a def whose name is plain and whose leaves fit keeps every def so
law inert.dok.push:
  for mm: Maybe<&2, String>
  for +sig: Tree.Node
  for +body: Tree.Node
  for +acc: List<&2, Calls.Def>
  for +en: {inert.plain(mm) == True{} : Bool}
  for +es: {Bool.and(Laws.inert.ok(sig), Laws.inert.ok(body)) == True{} : Bool}
  for +ea: {inert.dok(acc) == True{} : Bool}
  {inert.dok(Calls.defs.push(mm, sig, body, acc)) == True{} : Bool}

def inert.dok.push(mm, sig, body, acc, en, es, ea):
  match mm:
    case None{}: ea
    case Some{+name}:
      inert.and_both(Bool.and(Bool.not(Laws.inert.marked(name)), Bool.and(Laws.inert.ok(sig), Laws.inert.ok(body))),
        inert.dok(acc), inert.and_both(Bool.not(Laws.inert.marked(name)), Bool.and(Laws.inert.ok(sig),
          Laws.inert.ok(body)),
          en, es), ea)

# the defs of a tree read that way are its defs, each read that way; and
# they are as the lexer makes them, when its leaves fit
law inert.defs.of:
  for root: Tree.Node
  {Calls.defs(Laws.inert.node(root)) == inert.defs(Calls.defs(root)) : List<&2, Calls.Def>}

def inert.defs.of(root):
  match root:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{sk, +kids, +body}:
          match sk:
            case Tree.SDef{}:
              %Equal.sym(Maybe<&2, String>, Bind.declared(Laws.inert.node(kids)), Bind.declared(kids),
                inert.declared(kids)) :
                {Calls.defs.push(_, Laws.inert.node(kids), Laws.inert.node(body), Calls.defs(Laws.inert.node(rest)))
                  == inert.defs(Calls.defs.push(Bind.declared(kids), kids, body,
                    Calls.defs(rest))) : List<&2, Calls.Def>}
              %Equal.sym(List<&2, Calls.Def>, Calls.defs(Laws.inert.node(rest)), inert.defs(Calls.defs(rest)),
                inert.defs.of(rest)) : {Calls.defs.push(Bind.declared(kids), Laws.inert.node(kids),
                  Laws.inert.node(body), _)
                  == inert.defs(Calls.defs.push(Bind.declared(kids), kids, body,
                    Calls.defs(rest))) : List<&2, Calls.Def>}
              inert.defs.push(Bind.declared(kids), kids, body, Calls.defs(rest))
            case Tree.SType{}: inert.defs.of(rest)
            case Tree.SLaw{}: inert.defs.of(rest)
            case Tree.SImport{}: inert.defs.of(rest)
            case Tree.SCase{}: inert.defs.of(rest)
            case Tree.SFor{}: inert.defs.of(rest)
            case Tree.SLet{}: inert.defs.of(rest)
            case Tree.STerm{}: inert.defs.of(rest)
        case Tree.Leaf{tok}: inert.defs.of(rest)
        case Tree.Group{o, gk, cl}: inert.defs.of(rest)
        case Tree.NNil{}: inert.defs.of(rest)
        case Tree.NCons{x, y}: inert.defs.of(rest)
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a statement onto defs as the lexer makes them keeps them so: a def whose
# name is plain and whose leaves fit, or no def at all
law inert.dok.stmt:
  for sk: Tree.StmtKind
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +en: {inert.plain(Bind.declared(kids)) == True{} : Bool}
  for +es: {Bool.and(Laws.inert.ok(kids), Laws.inert.ok(body)) == True{} : Bool}
  for +er: {inert.dok(Calls.defs(rest)) == True{} : Bool}
  {inert.dok(Calls.defs(Tree.NCons{Tree.Stmt{sk, kids, body}, rest})) == True{} : Bool}

def inert.dok.stmt(sk, kids, body, rest, en, es, er):
  match sk:
    case Tree.SDef{}: inert.dok.push(Bind.declared(kids), kids, body, Calls.defs(rest), en, es, er)
    case Tree.SType{}: er
    case Tree.SLaw{}: er
    case Tree.SImport{}: er
    case Tree.SCase{}: er
    case Tree.SFor{}: er
    case Tree.SLet{}: er
    case Tree.STerm{}: er

# the defs of a tree whose leaves fit are as the lexer makes them
law inert.dok.of:
  for root: Tree.Node
  for +e: {Laws.inert.ok(root) == True{} : Bool}
  {inert.dok(Calls.defs(root)) == True{} : Bool}

def inert.dok.of(root, e):
  match root:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{sk, +kids, +body}:
          +es = inert.and_l(Bool.and(Laws.inert.ok(kids), Laws.inert.ok(body)), Laws.inert.ok(rest), e)
          +er = inert.dok.of(rest, inert.and_r(Bool.and(Laws.inert.ok(kids), Laws.inert.ok(body)),
            Laws.inert.ok(rest), e))
          inert.dok.stmt(sk, kids, body, rest, inert.plain.declared(kids, inert.and_l(Laws.inert.ok(kids),
            Laws.inert.ok(body),
            es)), es, er)
        case Tree.Leaf{tok}: inert.dok.of(rest, inert.and_r(Laws.inert.fits(tok), Laws.inert.ok(rest), e))
        case Tree.Group{o, gk, cl}: inert.dok.of(rest, inert.and_r(Laws.inert.ok(gk), Laws.inert.ok(rest), e))
        case Tree.NNil{}: inert.dok.of(rest, e)
        case Tree.NCons{x, y}: inert.dok.of(rest, inert.and_r(Laws.inert.ok(Tree.NCons{x, y}), Laws.inert.ok(rest), e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a chain reversed onto another, both read that way, is the reversal read
# that way
law inert.reverse:
  for cells: Tree.Node
  for acc: Tree.Node
  {Tree.reverse(Laws.inert.node(cells), Laws.inert.node(acc)) == Laws.inert.node(Tree.reverse(cells, acc)) : Tree.Node}

def inert.reverse(cells, acc):
  match cells:
    case Tree.NCons{h, t}: inert.reverse(t, Tree.NCons{h, acc})
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a list of chains reversed onto another, both read that way, is the
# reversal read that way
law inert.nodes.rev:
  for xs: List<&2, Tree.Node>
  for acc: List<&2, Tree.Node>
  {List.reverse.go(&2, Tree.Node, inert.nodes(xs), inert.nodes(acc))
    == inert.nodes(List.reverse.go(&2, Tree.Node, xs, acc)) : List<&2, Tree.Node>}

def inert.nodes.rev(xs, acc):
  match xs:
    case Nil{}: {==}
    case Con{h, t}: inert.nodes.rev(t, h <> acc)

# the last argument closed, read that way
law inert.args.end:
  for +cur: Tree.Node
  for +acc: List<&2, Tree.Node>
  {List.reverse(&2, Tree.Node, Tree.reverse(Laws.inert.node(cur), Tree.NNil{}) <> inert.nodes(acc))
    == inert.nodes(List.reverse(&2, Tree.Node, Tree.reverse(cur, Tree.NNil{}) <> acc)) : List<&2, Tree.Node>}

def inert.args.end(cur, acc):
  %Equal.sym(Tree.Node, Tree.reverse(Laws.inert.node(cur), Tree.NNil{}), Laws.inert.node(Tree.reverse(cur,
    Tree.NNil{})),
    inert.reverse(cur, Tree.NNil{})) : {List.reverse(&2, Tree.Node, _ <> inert.nodes(acc))
      == inert.nodes(List.reverse(&2, Tree.Node, Tree.reverse(cur, Tree.NNil{}) <> acc)) : List<&2, Tree.Node>}
  inert.nodes.rev(Tree.reverse(cur, Tree.NNil{}) <> acc, [])

# a comma closes an argument, read that way
law inert.args.comma:
  for +rest: Tree.Node
  for +cur: Tree.Node
  for +acc: List<&2, Tree.Node>
  for ih: {Calls.args.go(Laws.inert.node(rest), Tree.NNil{}, inert.nodes(Tree.reverse(cur, Tree.NNil{}) <> acc))
    == inert.nodes(Calls.args.go(rest, Tree.NNil{}, Tree.reverse(cur, Tree.NNil{}) <> acc)) : List<&2, Tree.Node>}
  {Calls.args.go(Laws.inert.node(rest), Tree.NNil{}, Tree.reverse(Laws.inert.node(cur),
    Tree.NNil{}) <> inert.nodes(acc))
    == inert.nodes(Calls.args.go(rest, Tree.NNil{}, Tree.reverse(cur, Tree.NNil{}) <> acc)) : List<&2, Tree.Node>}

def inert.args.comma(rest, cur, acc, ih):
  %Equal.sym(Tree.Node, Tree.reverse(Laws.inert.node(cur), Tree.NNil{}), Laws.inert.node(Tree.reverse(cur,
    Tree.NNil{})),
    inert.reverse(cur, Tree.NNil{})) : {Calls.args.go(Laws.inert.node(rest), Tree.NNil{}, _ <> inert.nodes(acc))
      == inert.nodes(Calls.args.go(rest, Tree.NNil{}, Tree.reverse(cur, Tree.NNil{}) <> acc)) : List<&2, Tree.Node>}
  ih

# a choice whose branches each read as another's mapped
law inert.either_map0:
  for -A: Type
  for -B: Type
  for c: Bool
  for -g: A -> B
  for -x1: B
  for -x2: A
  for -y1: B
  for -y2: A
  for ex: {x1 == g(x2) : B}
  for ey: {y1 == g(y2) : B}
  {Lazy.either(B, c, _u => x1, _v => y1) == g(Lazy.either(A, c, _u => x2, _v => y2)) : B}

def inert.either_map0(_A, _B, c, _g, _x1, _x2, _y1, _y2, ex, ey):
  match c:
    case True{}: ex
    case False{}: ey

# a choice whose test and branches each read as another's mapped
law inert.either_map:
  for -A: Type
  for -B: Type
  for -c1: Bool
  for +c2: Bool
  for -g: A -> B
  for -x1: B
  for -x2: A
  for -y1: B
  for -y2: A
  for ec: {c1 == c2 : Bool}
  for ex: {x1 == g(x2) : B}
  for ey: {y1 == g(y2) : B}
  {Lazy.either(B, c1, _u => x1, _v => y1) == g(Lazy.either(A, c2, _u => x2, _v => y2)) : B}

def inert.either_map(A, B, c1, c2, g, x1, x2, y1, y2, ec, ex, ey):
  %Equal.sym(Bool, c1, c2, ec) : {Lazy.either(B, _, _u => x1, _v => y1)
    == g(Lazy.either(A, c2, _u => x2, _v => y2)) : B}
  inert.either_map0(A, B, c2, g, x1, x2, y1, y2, ex, ey)

# a node read that way is a leaf of the kind it was, to any kind test
law inert.comma:
  for nn: Tree.Node
  {Calls.kind.leaf(~Lex.is_comma, Laws.inert.node(nn)) == Calls.kind.leaf(~Lex.is_comma, nn) : Bool}

def inert.comma(nn):
  Equal.cong(Maybe<&2, Lex.TokKind>, Bool,
    m => Calls.kind.of(~Lex.is_comma, m), Calls.leaf.kind(Laws.inert.node(nn)), Calls.leaf.kind(nn),
    inert.leaf_kind(nn))

# the arguments of a group read that way are its arguments, each read that way
law inert.args.go:
  for kids: Tree.Node
  for +cur: Tree.Node
  for +acc: List<&2, Tree.Node>
  {Calls.args.go(Laws.inert.node(kids), Laws.inert.node(cur), inert.nodes(acc))
    == inert.nodes(Calls.args.go(kids, cur, acc)) : List<&2, Tree.Node>}

def inert.args.go(kids, cur, acc):
  match kids:
    case Tree.NCons{+h, +rest}:
      +rc = {Tree.reverse(cur, Tree.NNil{}) <> acc : List<&2, Tree.Node>}
      inert.either_map(List<&2, Tree.Node>, List<&2, Tree.Node>, Calls.kind.leaf(~Lex.is_comma, Laws.inert.node(h)),
        Calls.kind.leaf(~Lex.is_comma, h), z => inert.nodes(z),
        Calls.args.go(Laws.inert.node(rest), Tree.NNil{},
          Tree.reverse(Laws.inert.node(cur), Tree.NNil{}) <> inert.nodes(acc)),
        Calls.args.go(rest, Tree.NNil{}, rc),
        Calls.args.go(Laws.inert.node(rest), Tree.NCons{Laws.inert.node(h), Laws.inert.node(cur)}, inert.nodes(acc)),
        Calls.args.go(rest, Tree.NCons{h, cur}, acc), inert.comma(h),
        inert.args.comma(rest, cur, acc, inert.args.go(rest, Tree.NNil{}, rc)),
        inert.args.go(rest, Tree.NCons{h, cur}, acc))
    case Tree.Leaf{tok}: inert.args.end(cur, acc)
    case Tree.Group{o, gk, cl}: inert.args.end(cur, acc)
    case Tree.Stmt{sk, sks, sb}: inert.args.end(cur, acc)
    case Tree.NNil{}: inert.args.end(cur, acc)

# the arguments of a group read that way
law inert.args:
  for kids: Tree.Node
  {Calls.args(Laws.inert.node(kids)) == inert.nodes(Calls.args(kids)) : List<&2, Tree.Node>}

def inert.args(kids):
  inert.args.go(kids, Tree.NNil{}, [])

# the nth argument of arguments read that way is the nth read that way
law inert.arg:
  for as: List<&2, Tree.Node>
  for nn: Nat
  {Calls.arg(inert.nodes(as), nn) == Laws.inert.node(Calls.arg(as, nn)) : Tree.Node}

def inert.arg(as, nn):
  match as nn:
    case Con{h, t} 0n: {==}
    case Con{h, t} 1n+p: inert.arg(t, p)
    case Nil{} m: {==}

# a chain reversed onto another keeps its leaves fitting
law inert.ok.reverse:
  for cells: Tree.Node
  for +acc: Tree.Node
  for +ec: {Laws.inert.ok(cells) == True{} : Bool}
  for +ea: {Laws.inert.ok(acc) == True{} : Bool}
  {Laws.inert.ok(Tree.reverse(cells, acc)) == True{} : Bool}

def inert.ok.reverse(cells, acc, ec, ea):
  match cells:
    case Tree.NCons{+h, +t}:
      inert.ok.reverse(t, Tree.NCons{h, acc}, inert.and_r(Laws.inert.ok(h), Laws.inert.ok(t), ec),
        inert.and_both(Laws.inert.ok(h), Laws.inert.ok(acc), inert.and_l(Laws.inert.ok(h), Laws.inert.ok(t), ec), ea))
    case Tree.Leaf{tok}: ea
    case Tree.Group{o, gk, cl}: ea
    case Tree.Stmt{sk, sks, sb}: ea
    case Tree.NNil{}: ea

# a list of chains reversed onto another keeps every chain's leaves fitting
law inert.noks.rev:
  for xs: List<&2, Tree.Node>
  for +acc: List<&2, Tree.Node>
  for +ex: {inert.noks(xs) == True{} : Bool}
  for +ea: {inert.noks(acc) == True{} : Bool}
  {inert.noks(List.reverse.go(&2, Tree.Node, xs, acc)) == True{} : Bool}

def inert.noks.rev(xs, acc, ex, ea):
  match xs:
    case Nil{}: ea
    case Con{+h, +t}:
      inert.noks.rev(t, h <> acc, inert.and_r(Laws.inert.ok(h), inert.noks(t), ex),
        inert.and_both(Laws.inert.ok(h), inert.noks(acc), inert.and_l(Laws.inert.ok(h), inert.noks(t), ex), ea))

# an argument closed onto arguments that fit keeps them fitting
law inert.ok.close:
  for +cur: Tree.Node
  for +acc: List<&2, Tree.Node>
  for +ec: {Laws.inert.ok(cur) == True{} : Bool}
  for +ea: {inert.noks(acc) == True{} : Bool}
  {inert.noks(Tree.reverse(cur, Tree.NNil{}) <> acc) == True{} : Bool}

def inert.ok.close(cur, acc, ec, ea):
  inert.and_both(Laws.inert.ok(Tree.reverse(cur, Tree.NNil{})), inert.noks(acc), inert.ok.reverse(cur, Tree.NNil{}, ec,
    {==}), ea)

# one more cell of a group: a comma closes an argument, anything else joins it
law inert.ok.args.step:
  for +h: Tree.Node
  for +rest: Tree.Node
  for +cur: Tree.Node
  for +acc: List<&2, Tree.Node>
  for ic: {inert.noks(Calls.args.go(rest, Tree.NNil{}, Tree.reverse(cur, Tree.NNil{}) <> acc)) == True{} : Bool}
  for io: {inert.noks(Calls.args.go(rest, Tree.NCons{h, cur}, acc)) == True{} : Bool}
  {inert.noks(Calls.args.go(Tree.NCons{h, rest}, cur, acc)) == True{} : Bool}

def inert.ok.args.step(h, rest, cur, acc, ic, io):
  inert.either_ok(List<&2, Tree.Node>, Calls.kind.leaf(~Lex.is_comma, h), z => inert.noks(z),
    Calls.args.go(rest, Tree.NNil{}, Tree.reverse(cur, Tree.NNil{}) <> acc),
    Calls.args.go(rest, Tree.NCons{h, cur}, acc),
    ic, io)

# the arguments of a group whose leaves fit fit too
law inert.ok.args.go:
  for kids: Tree.Node
  for +cur: Tree.Node
  for +acc: List<&2, Tree.Node>
  for +ek: {Laws.inert.ok(kids) == True{} : Bool}
  for +ec: {Laws.inert.ok(cur) == True{} : Bool}
  for +ea: {inert.noks(acc) == True{} : Bool}
  {inert.noks(Calls.args.go(kids, cur, acc)) == True{} : Bool}

def inert.ok.args.go(kids, cur, acc, ek, ec, ea):
  match kids:
    case Tree.NCons{+h, +rest}:
      +er = inert.and_r(Laws.inert.ok(h), Laws.inert.ok(rest), ek)
      inert.ok.args.step(h, rest, cur, acc,
        inert.ok.args.go(rest, Tree.NNil{}, Tree.reverse(cur, Tree.NNil{}) <> acc, er, {==}, inert.ok.close(cur, acc,
          ec, ea)),
        inert.ok.args.go(rest, Tree.NCons{h, cur}, acc, er,
          inert.and_both(Laws.inert.ok(h), Laws.inert.ok(cur), inert.and_l(Laws.inert.ok(h), Laws.inert.ok(rest), ek),
            ec), ea))
    case Tree.Leaf{tok}: inert.noks.rev(Tree.reverse(cur, Tree.NNil{}) <> acc, [], inert.ok.close(cur, acc, ec, ea),
      {==})
    case Tree.Group{o, gk, cl}: inert.noks.rev(Tree.reverse(cur, Tree.NNil{}) <> acc, [], inert.ok.close(cur, acc, ec,
      ea), {==})
    case Tree.Stmt{sk, sks, sb}: inert.noks.rev(Tree.reverse(cur, Tree.NNil{}) <> acc, [], inert.ok.close(cur, acc,
      ec, ea), {==})
    case Tree.NNil{}: inert.noks.rev(Tree.reverse(cur, Tree.NNil{}) <> acc, [], inert.ok.close(cur, acc, ec, ea), {==})

# the nth of chains that fit fits
law inert.ok.nth:
  for as: List<&2, Tree.Node>
  for nn: Nat
  for +ea: {inert.noks(as) == True{} : Bool}
  {Laws.inert.ok(Calls.arg(as, nn)) == True{} : Bool}

def inert.ok.nth(as, nn, ea):
  match as nn:
    case Con{+h, +t} 0n: inert.and_l(Laws.inert.ok(h), inert.noks(t), ea)
    case Con{+h, +t} 1n+p: inert.ok.nth(t, p, inert.and_r(Laws.inert.ok(h), inert.noks(t), ea))
    case Nil{} m: {==}

# the nth argument of a group whose leaves fit fits
law inert.ok.arg:
  for +kids: Tree.Node
  for nn: Nat
  for +ek: {Laws.inert.ok(kids) == True{} : Bool}
  {Laws.inert.ok(Calls.arg(Calls.args(kids), nn)) == True{} : Bool}

def inert.ok.arg(kids, nn, ek):
  inert.ok.nth(Calls.args(kids), nn, inert.ok.args.go(kids, Tree.NNil{}, [], ek, {==}, {==}))

# the kids of a group read that way open as they did
law inert.opens:
  for nn: Tree.Node
  for +ss: String
  {Tree.opens(Laws.inert.node(nn), ss) == Tree.opens(nn, ss) : Bool}

def inert.opens(nn, _ss):
  match nn:
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}:
      match o:
        case Lex.Tok{k, t, l, c}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# calls: is there a call of the name?
# ----------------------------------

# a call of the name here, or under the kids or the rest
def inert.calls.at(+tn: Bool, +o: String, a: Bool, b: Bool) -> Bool:
  Bool.or(Bool.and(String.eq(o, "("), tn), Bool.or(a, b))

# a name then a group: the name compared, the group and the rest read as they were
law inert.calls.lg:
  for +kk: Lex.TokKind
  for +t: String
  for +ot: String
  for +name: String
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +ef: {Laws.inert.fits.go(Laws.inert.blanks(kk), t) == True{} : Bool}
  for +en: {Laws.inert.marked(name) == False{} : Bool}
  for ik: {Calls.calls(Laws.inert.node(kids), name) == Calls.calls(kids, name) : Bool}
  for ir: {Calls.calls(Laws.inert.node(r2), name) == Calls.calls(r2, name) : Bool}
  {inert.calls.at(String.eq(Laws.inert.keep(Laws.inert.blanks(kk), t), name), ot, Calls.calls(Laws.inert.node(kids),
    name),
      Calls.calls(Laws.inert.node(r2), name))
    == inert.calls.at(String.eq(t, name), ot, Calls.calls(kids, name), Calls.calls(r2, name)) : Bool}

def inert.calls.lg(kk, t, ot, name, kids, r2, ef, en, ik, ir):
  +lhs = inert.calls.at(String.eq(Laws.inert.keep(Laws.inert.blanks(kk), t), name), ot,
    Calls.calls(Laws.inert.node(kids),
    name), Calls.calls(Laws.inert.node(r2), name))
  %inert.eq_keep(Laws.inert.blanks(kk), t, name, ef, en) :
    {lhs == inert.calls.at(_, ot, Calls.calls(kids, name), Calls.calls(r2, name)) : Bool}
  %ik : {lhs == inert.calls.at(String.eq(Laws.inert.keep(Laws.inert.blanks(kk), t), name), ot, _, Calls.calls(r2, name))
    : Bool}
  %ir : {lhs == inert.calls.at(String.eq(Laws.inert.keep(Laws.inert.blanks(kk), t), name), ot,
    Calls.calls(Laws.inert.node(kids), name), _) : Bool}
  {==}

# an or whose two sides read as they did
law inert.or2:
  for -a1: Bool
  for -a2: Bool
  for -b1: Bool
  for -b2: Bool
  for ea: {a1 == a2 : Bool}
  for eb: {b1 == b2 : Bool}
  {Bool.or(a1, b1) == Bool.or(a2, b2) : Bool}

def inert.or2(a1, _a2, b1, b2, ea, eb):
  %ea : {Bool.or(a1, b1) == Bool.or(_, b2) : Bool}
  %eb : {Bool.or(a1, b1) == Bool.or(a1, _) : Bool}
  {==}

# a chain read that way calls the name as it did, for a plain name
law inert.calls:
  for nn: Tree.Node
  for +name: String
  for +en: {Laws.inert.marked(name) == False{} : Bool}
  for +e: {Laws.inert.ok(nn) == True{} : Bool}
  {Calls.calls(Laws.inert.node(nn), name) == Calls.calls(nn, name) : Bool}

def inert.calls(nn, name, en, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{o, +kids, cl}:
                      match o:
                        case Lex.Tok{ok, +ot, ol, oc}:
                          +eg = inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}), Bool.and(Laws.inert.ok(kids),
                            Laws.inert.ok(r2)), e)
                          inert.calls.lg(k, t, ot, name, kids, r2, inert.and_l(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                            Bool.and(Laws.inert.ok(kids), Laws.inert.ok(r2)), e), en,
                            inert.calls(kids, name, en, inert.and_l(Laws.inert.ok(kids), Laws.inert.ok(r2), eg)),
                            inert.calls(r2, name, en, inert.and_r(Laws.inert.ok(kids), Laws.inert.ok(r2), eg)))
                    case Tree.Leaf{x}: inert.calls(rest, name, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                      Laws.inert.ok(rest), e))
                    case Tree.Stmt{x, y, z}: inert.calls(rest, name, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l,
                      c}), Laws.inert.ok(rest), e))
                    case Tree.NNil{}: inert.calls(rest, name, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                      Laws.inert.ok(rest), e))
                    case Tree.NCons{x, y}: inert.calls(rest, name, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l,
                      c}), Laws.inert.ok(rest), e))
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: inert.calls(rest, name, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l,
                  c}), Laws.inert.ok(rest), e))
                case Tree.Stmt{x, y, z}: inert.calls(rest, name, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                  Laws.inert.ok(rest), e))
                case Tree.NNil{}: {==}
        case Tree.Group{o, +gk, cl}:
          inert.or2(Calls.calls(Laws.inert.node(gk), name), Calls.calls(gk, name), Calls.calls(Laws.inert.node(rest),
            name),
            Calls.calls(rest, name), inert.calls(gk, name, en, inert.and_l(Laws.inert.ok(gk), Laws.inert.ok(rest), e)),
            inert.calls(rest, name, en, inert.and_r(Laws.inert.ok(gk), Laws.inert.ok(rest), e)))
        case Tree.Stmt{+sk, +sks, +sb}:
          +es = inert.and_l(Bool.and(Laws.inert.ok(sks), Laws.inert.ok(sb)), Laws.inert.ok(rest), e)
          inert.or2(Calls.calls(Laws.inert.node(Tree.Stmt{sk, sks, sb}), name), Calls.calls(Tree.Stmt{sk, sks, sb},
            name),
            Calls.calls(Laws.inert.node(rest), name), Calls.calls(rest, name),
            inert.or2(Calls.calls(Laws.inert.node(sks), name), Calls.calls(sks, name),
              Calls.calls(Laws.inert.node(sb), name),
              Calls.calls(sb, name), inert.calls(sks, name, en, inert.and_l(Laws.inert.ok(sks), Laws.inert.ok(sb), es)),
              inert.calls(sb, name, en, inert.and_r(Laws.inert.ok(sks), Laws.inert.ok(sb), es))),
            inert.calls(rest, name, en, inert.and_r(Bool.and(Laws.inert.ok(sks), Laws.inert.ok(sb)),
              Laws.inert.ok(rest), e)))
        case Tree.NNil{}: inert.calls(rest, name, en, e)
        case Tree.NCons{+x, +y}:
          inert.or2(Calls.calls(Laws.inert.node(Tree.NCons{x, y}), name), Calls.calls(Tree.NCons{x, y}, name),
            Calls.calls(Laws.inert.node(rest), name), Calls.calls(rest, name),
            inert.calls(Tree.NCons{x, y}, name, en, inert.and_l(Laws.inert.ok(Tree.NCons{x, y}), Laws.inert.ok(rest),
              e)),
            inert.calls(rest, name, en, inert.and_r(Laws.inert.ok(Tree.NCons{x, y}), Laws.inert.ok(rest), e)))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, +kids, cl}: inert.calls(kids, name, en, e)
    case Tree.Stmt{sk, +kids, +body}:
      inert.or2(Calls.calls(Laws.inert.node(kids), name), Calls.calls(kids, name), Calls.calls(Laws.inert.node(body),
        name),
        Calls.calls(body, name), inert.calls(kids, name, en, inert.and_l(Laws.inert.ok(kids), Laws.inert.ok(body), e)),
        inert.calls(body, name, en, inert.and_r(Laws.inert.ok(kids), Laws.inert.ok(body), e)))
    case Tree.NNil{}: {==}

# the nth argument of a group read that way calls the name as it did
law inert.calls.nth:
  for +kids: Tree.Node
  for +nn: Nat
  for +name: String
  for +en: {Laws.inert.marked(name) == False{} : Bool}
  for +ek: {Laws.inert.ok(kids) == True{} : Bool}
  {Calls.calls(Calls.arg(Calls.args(Laws.inert.node(kids)), nn), name) == Calls.calls(Calls.arg(Calls.args(kids), nn),
    name)
    : Bool}

def inert.calls.nth(kids, nn, name, en, ek):
  %Equal.sym(List<&2, Tree.Node>, Calls.args(Laws.inert.node(kids)), inert.nodes(Calls.args(kids)), inert.args(kids)) :
    {Calls.calls(Calls.arg(_, nn), name) == Calls.calls(Calls.arg(Calls.args(kids), nn), name) : Bool}
  %Equal.sym(Tree.Node, Calls.arg(inert.nodes(Calls.args(kids)), nn), Laws.inert.node(Calls.arg(Calls.args(kids), nn)),
    inert.arg(Calls.args(kids), nn)) : {Calls.calls(_, name) == Calls.calls(Calls.arg(Calls.args(kids), nn),
      name) : Bool}
  inert.calls(Calls.arg(Calls.args(kids), nn), name, en, inert.ok.arg(kids, nn, ek))

# a signature read that way
# -------------------------

# a pick between two chains, each read that way, is the pick read that way
law inert.pick.node:
  for b: Bool
  for +x: Tree.Node
  for +y: Tree.Node
  {Bool.pick(Tree.Node, b, Laws.inert.node(x), Laws.inert.node(y)) == Laws.inert.node(Bool.pick(Tree.Node, b, x, y))
    : Tree.Node}

def inert.pick.node(b, _x, _y):
  match b:
    case True{}: {==}
    case False{}: {==}

# is the type head a List or a String (what Calls.seq tests)?
def inert.seq.of(+hh: String) -> Bool:
  Bool.or(String.eq(hh, "List"), String.eq(hh, "String"))

# the parameter list of a signature read that way is the list read that way
law inert.params.of:
  for sig: Tree.Node
  {Calls.params.of(Laws.inert.node(sig)) == Laws.inert.node(Calls.params.of(sig)) : Tree.Node}

def inert.params.of(sig):
  match sig:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Group{o, +kids, cl}:
          match o:
            case Lex.Tok{k, +ot, l, c}:
              %Equal.sym(Tree.Node, Calls.params.of(Laws.inert.node(rest)), Laws.inert.node(Calls.params.of(rest)),
                inert.params.of(rest)) : {Bool.pick(Tree.Node, String.eq(ot, "("), Laws.inert.node(kids), _)
                  == Laws.inert.node(Bool.pick(Tree.Node, String.eq(ot, "("), kids, Calls.params.of(rest))) : Tree.Node}
              inert.pick.node(String.eq(ot, "("), kids, Calls.params.of(rest))
        case Tree.Leaf{tok}: inert.params.of(rest)
        case Tree.Stmt{sk, sks, sb}: inert.params.of(rest)
        case Tree.NNil{}: inert.params.of(rest)
        case Tree.NCons{x, y}: inert.params.of(rest)
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a node read that way is a `:` as it was
law inert.colon:
  for nn: Tree.Node
  {Calls.kind.leaf(~Calls.kind.colon, Laws.inert.node(nn)) == Calls.kind.leaf(~Calls.kind.colon, nn) : Bool}

def inert.colon(nn):
  Equal.cong(Maybe<&2, Lex.TokKind>, Bool,
    m => Calls.kind.of(~Calls.kind.colon, m), Calls.leaf.kind(Laws.inert.node(nn)), Calls.leaf.kind(nn),
    inert.leaf_kind(nn))

# a node read that way is an arrow as it was
law inert.arrow:
  for nn: Tree.Node
  {Calls.kind.leaf(~Calls.kind.arrow, Laws.inert.node(nn)) == Calls.kind.leaf(~Calls.kind.arrow, nn) : Bool}

def inert.arrow(nn):
  Equal.cong(Maybe<&2, Lex.TokKind>, Bool,
    m => Calls.kind.of(~Calls.kind.arrow, m), Calls.leaf.kind(Laws.inert.node(nn)), Calls.leaf.kind(nn),
    inert.leaf_kind(nn))

# an early-exit or whose test and rest read as they did
law inert.or_else:
  for -c1: Bool
  for -c2: Bool
  for -a1: Bool
  for -a2: Bool
  for ec: {c1 == c2 : Bool}
  for ea: {a1 == a2 : Bool}
  {Lazy.or_else(c1, _u => a1) == Lazy.or_else(c2, _v => a2) : Bool}

def inert.or_else(c1, _c2, a1, a2, ec, ea):
  %ec : {Lazy.or_else(c1, _u => a1) == Lazy.or_else(_, _v => a2) : Bool}
  %ea : {Lazy.or_else(c1, _u => a1) == Lazy.or_else(c1, _v => _) : Bool}
  {==}

# a parameter read that way has a top-level colon as it had
law inert.has_colon:
  for pp: Tree.Node
  {Calls.has_colon(Laws.inert.node(pp)) == Calls.has_colon(pp) : Bool}

def inert.has_colon(pp):
  match pp:
    case Tree.NCons{+h, +rest}:
      inert.or_else(Calls.kind.leaf(~Calls.kind.colon, Laws.inert.node(h)), Calls.kind.leaf(~Calls.kind.colon, h),
        Calls.has_colon(Laws.inert.node(rest)), Calls.has_colon(rest), inert.colon(h), inert.has_colon(rest))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a leaf read that way says what it said, cut when a comment or a string
law inert.leaf_text:
  for nn: Tree.Node
  {Calls.leaf.text(Laws.inert.node(nn))
    == Laws.inert.keep(Calls.kind.leaf(~Laws.inert.blanks, nn), Calls.leaf.text(nn)) : String}

def inert.leaf_text(nn):
  match nn:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# an operator leaf is never cut
law inert.oper_code:
  for nn: Tree.Node
  {Bool.and(Calls.kind.leaf(~Calls.kind.oper, nn), Calls.kind.leaf(~Laws.inert.blanks, nn)) == False{} : Bool}

def inert.oper_code(nn):
  match nn:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}: inert.hole.op(k)
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# a capital-name leaf is never cut
law inert.upper_code:
  for nn: Tree.Node
  {Bool.and(Calls.kind.leaf(~Calls.kind.upper, nn), Calls.kind.leaf(~Laws.inert.blanks, nn)) == False{} : Bool}

def inert.upper_code(nn):
  match nn:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}: inert.hole.upper(k)
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# a node read that way is an operator as it was
law inert.oper:
  for nn: Tree.Node
  {Calls.kind.leaf(~Calls.kind.oper, Laws.inert.node(nn)) == Calls.kind.leaf(~Calls.kind.oper, nn) : Bool}

def inert.oper(nn):
  Equal.cong(Maybe<&2, Lex.TokKind>, Bool,
    m => Calls.kind.of(~Calls.kind.oper, m), Calls.leaf.kind(Laws.inert.node(nn)), Calls.leaf.kind(nn),
    inert.leaf_kind(nn))

# a node read that way is a capital name as it was
law inert.upper:
  for nn: Tree.Node
  {Calls.kind.leaf(~Calls.kind.upper, Laws.inert.node(nn)) == Calls.kind.leaf(~Calls.kind.upper, nn) : Bool}

def inert.upper(nn):
  Equal.cong(Maybe<&2, Lex.TokKind>, Bool,
    m => Calls.kind.of(~Calls.kind.upper, m), Calls.leaf.kind(Laws.inert.node(nn)), Calls.leaf.kind(nn),
    inert.leaf_kind(nn))

# a `-` or `~`
def inert.sign.of(+tt: String) -> Bool:
  Bool.or(String.eq(tt, "-"), String.eq(tt, "~"))

# a parameter read that way opens with a `-` or `~` as it did
law inert.sign:
  for pp: Tree.Node
  {Calls.is_live.sign(Laws.inert.node(pp)) == Calls.is_live.sign(pp) : Bool}

def inert.sign(pp):
  match pp:
    case Tree.NCons{+h, +rest}:
      +ko = Calls.kind.leaf(~Calls.kind.oper, h)
      +kb = Calls.kind.leaf(~Laws.inert.blanks, h)
      %Equal.sym(Bool, Calls.kind.leaf(~Calls.kind.oper, Laws.inert.node(h)), ko, inert.oper(h)) :
        {Bool.and(_, inert.sign.of(Calls.leaf.text(Laws.inert.node(h))))
          == Calls.is_live.sign(Tree.NCons{h, rest}) : Bool}
      %Equal.sym(String, Calls.leaf.text(Laws.inert.node(h)), Laws.inert.keep(kb, Calls.leaf.text(h)),
        inert.leaf_text(h)) : {Bool.and(ko, inert.sign.of(_)) == Calls.is_live.sign(Tree.NCons{h, rest}) : Bool}
      inert.guard(ko, kb, Calls.leaf.text(h), z => inert.sign.of(z), inert.oper_code(h))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a parameter read that way is live as it was
law inert.is_live:
  for +pp: Tree.Node
  {Calls.is_live(Laws.inert.node(pp)) == Calls.is_live(pp) : Bool}

def inert.is_live(pp):
  +lhs = Calls.is_live(Laws.inert.node(pp))
  %inert.sign(pp) : {lhs == Bool.and(Bool.not(_), Calls.has_colon(pp)) : Bool}
  %inert.has_colon(pp) : {lhs == Bool.and(Bool.not(Calls.is_live.sign(Laws.inert.node(pp))), _) : Bool}
  {==}

# a pick guarded by a kind that is never cut reads the text as it was
law inert.pick_guard:
  for +after: Bool
  for c: Bool
  for +b: Bool
  for +t: String
  for +more: String
  for e: {Bool.and(c, b) == False{} : Bool}
  {Bool.pick(String, Bool.and(after, c), Laws.inert.keep(b, t), more) == Bool.pick(String, Bool.and(after, c), t, more)
    : String}

def inert.pick_guard(after, c, b, t, more, e):
  match after:
    case False{}: {==}
    case True{}:
      match c:
        case False{}: {==}
        case True{}:
          %Equal.sym(Bool, b, False{}, e) : {Bool.pick(String, True{}, Laws.inert.keep(_, t), more)
            == Bool.pick(String, True{}, t, more) : String}
          {==}

# a leaf read that way gives the head it gave
law inert.head_leaf:
  for +h: Tree.Node
  for +after: Bool
  for +more: String
  {Bool.pick(String, Bool.and(after, Calls.kind.leaf(~Calls.kind.upper, Laws.inert.node(h))),
    Calls.leaf.text(Laws.inert.node(h)), more)
    == Bool.pick(String, Bool.and(after, Calls.kind.leaf(~Calls.kind.upper, h)), Calls.leaf.text(h), more) : String}

def inert.head_leaf(h, after, more):
  +ku = Calls.kind.leaf(~Calls.kind.upper, h)
  +kb = Calls.kind.leaf(~Laws.inert.blanks, h)
  %Equal.sym(Bool, Calls.kind.leaf(~Calls.kind.upper, Laws.inert.node(h)), ku, inert.upper(h)) :
    {Bool.pick(String, Bool.and(after, _), Calls.leaf.text(Laws.inert.node(h)), more)
      == Bool.pick(String, Bool.and(after, ku), Calls.leaf.text(h), more) : String}
  %Equal.sym(String, Calls.leaf.text(Laws.inert.node(h)), Laws.inert.keep(kb, Calls.leaf.text(h)),
    inert.leaf_text(h)) : {Bool.pick(String, Bool.and(after, ku), _, more)
      == Bool.pick(String, Bool.and(after, ku), Calls.leaf.text(h), more) : String}
  inert.pick_guard(after, ku, kb, Calls.leaf.text(h), more, inert.upper_code(h))

# a parameter's type head read that way is the head it had
law inert.type_head:
  for pp: Tree.Node
  for +after: Bool
  {Calls.type_head(Laws.inert.node(pp), after) == Calls.type_head(pp, after) : String}

def inert.type_head(pp, after):
  match pp:
    case Tree.NCons{+h, +rest}:
      +lhs = Calls.type_head(Laws.inert.node(Tree.NCons{h, rest}), after)
      +c1 = Calls.kind.leaf(~Calls.kind.colon, Laws.inert.node(h))
      %inert.colon(h) : {lhs == Bool.pick(String, Bool.and(after, Calls.kind.leaf(~Calls.kind.upper, h)),
        Calls.leaf.text(h), Calls.type_head(rest, Bool.or(after, _))) : String}
      %inert.type_head(rest, Bool.or(after, c1)) : {lhs == Bool.pick(String,
        Bool.and(after, Calls.kind.leaf(~Calls.kind.upper, h)), Calls.leaf.text(h), _) : String}
      inert.head_leaf(h, after, Calls.type_head(Laws.inert.node(rest), Bool.or(after, c1)))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# the walked type of parameters read that way is the one they had
law inert.walked.go:
  for ps: List<&2, Tree.Node>
  for found: Maybe<&2, String>
  {Calls.walked.go(inert.nodes(ps), found) == Calls.walked.go(ps, found) : String}

def inert.walked.go(ps, found):
  match ps found:
    case Con{+p, rest} None{}:
      %inert.is_live(p) : {Calls.walked.go(inert.nodes(p <> rest), None{}) == Calls.walked.go(rest,
        Lazy.stop(Maybe<&2, String>, Bool.not(_), None{}, _u => Some{Calls.type_head(p, False{})})) : String}
      %inert.type_head(p, False{}) : {Calls.walked.go(inert.nodes(p <> rest), None{}) == Calls.walked.go(rest,
        Lazy.stop(Maybe<&2, String>, Bool.not(Calls.is_live(Laws.inert.node(p))), None{}, _u => Some{_})) : String}
      inert.walked.go(rest, Lazy.stop(Maybe<&2, String>, Bool.not(Calls.is_live(Laws.inert.node(p))), None{},
        _u => Some{Calls.type_head(Laws.inert.node(p), False{})}))
    case Con{p, rest} Some{t}: {==}
    case Nil{} Some{t}: {==}
    case Nil{} None{}: {==}

# a signature read that way walks the type it walked
law inert.seq:
  for +sig: Tree.Node
  {Calls.seq(Laws.inert.node(sig)) == Calls.seq(sig) : Bool}

def inert.seq(sig):
  +ps = Calls.params.of(sig)
  %Equal.sym(Tree.Node, Calls.params.of(Laws.inert.node(sig)), Laws.inert.node(ps), inert.params.of(sig)) :
    {inert.seq.of(Calls.walked.go(Calls.args(_), None{})) == Calls.seq(sig) : Bool}
  %Equal.sym(List<&2, Tree.Node>, Calls.args(Laws.inert.node(ps)), inert.nodes(Calls.args(ps)), inert.args(ps)) :
    {inert.seq.of(Calls.walked.go(_, None{})) == Calls.seq(sig) : Bool}
  %Equal.sym(String, Calls.walked.go(inert.nodes(Calls.args(ps)), None{}), Calls.walked.go(Calls.args(ps), None{}),
    inert.walked.go(Calls.args(ps), None{})) : {inert.seq.of(_) == Calls.seq(sig) : Bool}
  {==}

# a signature read that way returns a proof as it did
law inert.returns_proof:
  for sig: Tree.Node
  {Calls.returns_proof(Laws.inert.node(sig)) == Calls.returns_proof(sig) : Bool}

def inert.returns_proof(sig):
  match sig:
    case Tree.NCons{+h, +rest}:
      match rest:
        case Tree.NCons{+g, +r2}:
          inert.either(Bool, Calls.kind.leaf(~Calls.kind.arrow, Laws.inert.node(h)),
            Calls.kind.leaf(~Calls.kind.arrow, h),
            Calls.returns_proof.or(Tree.opens(Laws.inert.node(g), "{"), Calls.returns_proof(Laws.inert.node(r2))),
            Calls.returns_proof.or(Tree.opens(g, "{"), Calls.returns_proof(r2)),
            Calls.returns_proof(Tree.NCons{Laws.inert.node(g), Laws.inert.node(r2)}),
            Calls.returns_proof(Tree.NCons{g, r2}), inert.arrow(h),
            inert.or2(Tree.opens(Laws.inert.node(g), "{"), Tree.opens(g, "{"), Calls.returns_proof(Laws.inert.node(r2)),
              Calls.returns_proof(r2), inert.opens(g, "{"), inert.returns_proof(r2)),
            inert.returns_proof(rest))
        case Tree.Leaf{x}: inert.returns_proof(rest)
        case Tree.Group{x, y, z}: inert.returns_proof(rest)
        case Tree.Stmt{x, y, z}: inert.returns_proof(rest)
        case Tree.NNil{}: inert.returns_proof(rest)
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a chain read that way has a top-level arrow as it had
law inert.has_arrow:
  for pp: Tree.Node
  {Calls.has_arrow(Laws.inert.node(pp)) == Calls.has_arrow(pp) : Bool}

def inert.has_arrow(pp):
  match pp:
    case Tree.NCons{+h, +rest}:
      inert.or_else(Calls.kind.leaf(~Calls.kind.arrow, Laws.inert.node(h)), Calls.kind.leaf(~Calls.kind.arrow, h),
        Calls.has_arrow(Laws.inert.node(rest)), Calls.has_arrow(rest), inert.arrow(h), inert.has_arrow(rest))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a signature read that way writes a type as it did
law inert.typed:
  for +sig: Tree.Node
  {Calls.typed(Laws.inert.node(sig)) == Calls.typed(sig) : Bool}

def inert.typed(sig):
  +ps = Calls.params.of(sig)
  %Equal.sym(Tree.Node, Calls.params.of(Laws.inert.node(sig)), Laws.inert.node(ps), inert.params.of(sig)) :
    {Lazy.or_else(Calls.has_colon(_), _u => Calls.has_arrow(Laws.inert.node(sig))) == Calls.typed(sig) : Bool}
  inert.or_else(Calls.has_colon(Laws.inert.node(ps)), Calls.has_colon(ps), Calls.has_arrow(Laws.inert.node(sig)),
    Calls.has_arrow(sig), inert.has_colon(ps), inert.has_arrow(sig))

# a signature read that way is a proof as it was
law inert.proof:
  for +sig: Tree.Node
  {Calls.proof(Laws.inert.node(sig)) == Calls.proof(sig) : Bool}

def inert.proof(sig):
  inert.or2(Calls.returns_proof(Laws.inert.node(sig)), Calls.returns_proof(sig),
    Bool.not(Calls.typed(Laws.inert.node(sig))), Bool.not(Calls.typed(sig)), inert.returns_proof(sig),
    Equal.cong(Bool, Bool, z => Bool.not(z), Calls.typed(Laws.inert.node(sig)), Calls.typed(sig), inert.typed(sig)))

# a signature read that way is exempt as it was
law inert.exempt:
  for +path: String
  for +sig: Tree.Node
  {Calls.exempt(path, Laws.inert.node(sig)) == Calls.exempt(path, sig) : Bool}

def inert.exempt(path, sig):
  Equal.cong(Bool, Bool, z => Bool.or(Paths.is_law_file(path), z), Calls.proof(Laws.inert.node(sig)),
    Calls.proof(sig), inert.proof(sig))

# the walks: two or three finding lists that read as they did join the same
law inert.cat2:
  for -a1: List<&2, F.Finding>
  for -a2: List<&2, F.Finding>
  for -b1: List<&2, F.Finding>
  for -b2: List<&2, F.Finding>
  for ea: {a1 == a2 : List<&2, F.Finding>}
  for eb: {b1 == b2 : List<&2, F.Finding>}
  {List.concat(&2, F.Finding, [a1, b1]) == List.concat(&2, F.Finding, [a2, b2]) : List<&2, F.Finding>}

def inert.cat2(a1, _a2, b1, b2, ea, eb):
  %ea : {List.concat(&2, F.Finding, [a1, b1]) == List.concat(&2, F.Finding, [_, b2]) : List<&2, F.Finding>}
  %eb : {List.concat(&2, F.Finding, [a1, b1]) == List.concat(&2, F.Finding, [a1, _]) : List<&2, F.Finding>}
  {==}

# three finding lists that read as they did join the same
law inert.cat3:
  for -a1: List<&2, F.Finding>
  for -a2: List<&2, F.Finding>
  for -b1: List<&2, F.Finding>
  for -b2: List<&2, F.Finding>
  for -c1: List<&2, F.Finding>
  for -c2: List<&2, F.Finding>
  for ea: {a1 == a2 : List<&2, F.Finding>}
  for eb: {b1 == b2 : List<&2, F.Finding>}
  for ec: {c1 == c2 : List<&2, F.Finding>}
  {List.concat(&2, F.Finding, [a1, b1, c1]) == List.concat(&2, F.Finding, [a2, b2, c2]) : List<&2, F.Finding>}

def inert.cat3(a1, _a2, b1, b2, c1, c2, ea, eb, ec):
  %ea : {List.concat(&2, F.Finding, [a1, b1, c1]) == List.concat(&2, F.Finding, [_, b2, c2]) : List<&2, F.Finding>}
  %eb : {List.concat(&2, F.Finding, [a1, b1, c1]) == List.concat(&2, F.Finding, [a1, _, c2]) : List<&2, F.Finding>}
  %ec : {List.concat(&2, F.Finding, [a1, b1, c1]) == List.concat(&2, F.Finding, [a1, b1, _]) : List<&2, F.Finding>}
  {==}

# a rule over a file's defs, given it reports the same over the defs read
# that way, reports the same over the defs of the tree read that way
law inert.lift:
  for -f: List<&2, Calls.Def> -> List<&2, F.Finding>
  for +tree: Tree.Node
  for h: {f(inert.defs(Calls.defs(tree))) == f(Calls.defs(tree)) : List<&2, F.Finding>}
  {f(Calls.defs(Laws.inert.node(tree))) == f(Calls.defs(tree)) : List<&2, F.Finding>}

def inert.lift(f, tree, h):
  %Equal.sym(List<&2, Calls.Def>, Calls.defs(Laws.inert.node(tree)), inert.defs(Calls.defs(tree)),
    inert.defs.of(tree)) :
    {f(_) == f(Calls.defs(tree)) : List<&2, F.Finding>}
  h

# tail
# ----

# a self-call not in tail position, as the walk reports it from what it read
def inert.tail.at(
  +tn: Bool,
  +tp: Bool,
  +o: String,
  +l: U32,
  +c: U32,
  +name: String,
  +path: String,
  +skip: Bool,
  inside: List<&2, F.Finding>,
  rest: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  +call = String.eq(o, "(")
  +more = List.concat(&2, F.Finding, [Bool.pick(List<&2, F.Finding>, Bool.and(call, tp), [], inside), rest])
  Bool.pick(List<&2, F.Finding>, Bool.and(Bool.and(call, tn), Bool.not(skip)),
    F.Finding{path, l, c, U32.from_nat(String.length(name)), "tail",
      "This call to " ++ name ++ " is not a tail call, so a long list or string overflows the stack on the JS lane; carry an accumulator."}
      <> more,
    more)

# a chain read that way is a bare self-call as it was
law inert.tail.bare:
  for kids: Tree.Node
  for +name: String
  for +en: {Laws.inert.marked(name) == False{} : Bool}
  for +e: {Laws.inert.ok(kids) == True{} : Bool}
  {Tail.bare(Laws.inert.node(kids), name) == Tail.bare(kids, name) : Bool}

def inert.tail.bare(kids, name, en, e):
  match kids:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{+g, r}:
                  match r:
                    case Tree.NNil{}:
                      +tt = Laws.inert.keep(Laws.inert.blanks(k), t)
                      %inert.eq_keep(Laws.inert.blanks(k), t, name, inert.and_l(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                        Bool.and(Laws.inert.ok(g), True{}), e), en) :
                        {Bool.and(String.eq(tt, name), Tree.opens(Laws.inert.node(g), "(")) == Bool.and(_,
                          Tree.opens(g, "("))
                          : Bool}
                      %inert.opens(g, "(") : {Bool.and(String.eq(tt, name), Tree.opens(Laws.inert.node(g), "("))
                        == Bool.and(String.eq(tt, name), _) : Bool}
                      {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NCons{x, y}: {==}
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NNil{}: {==}
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a name then a group: the name compared, the group and the rest walked as
# they were
law inert.tail.lg:
  for +kk: Lex.TokKind
  for +t: String
  for +o: String
  for +l: U32
  for +c: U32
  for +name: String
  for +path: String
  for +skip: Bool
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +ef: {Laws.inert.fits.go(Laws.inert.blanks(kk), t) == True{} : Bool}
  for +en: {Laws.inert.marked(name) == False{} : Bool}
  for ik: {Tail.walk(Laws.inert.node(kids), name, path, False{}) == Tail.walk(kids, name, path, False{}) : List<&2,
    F.Finding>}
  for ir: {Tail.walk(Laws.inert.node(r2), name, path, False{}) == Tail.walk(r2, name, path, False{}) : List<&2,
    F.Finding>}
  {inert.tail.at(String.eq(Laws.inert.keep(Laws.inert.blanks(kk), t), name),
      String.eq(Laws.inert.keep(Laws.inert.blanks(kk), t), "Bool.pick"), o, l, c, name, path, skip,
      Tail.walk(Laws.inert.node(kids), name, path, False{}), Tail.walk(Laws.inert.node(r2), name, path, False{}))
    == inert.tail.at(String.eq(t, name), String.eq(t, "Bool.pick"), o, l, c, name, path, skip,
      Tail.walk(kids, name, path, False{}), Tail.walk(r2, name, path, False{})) : List<&2, F.Finding>}

def inert.tail.lg(kk, t, o, l, c, name, path, skip, kids, r2, ef, en, ik, ir):
  +tt = Laws.inert.keep(Laws.inert.blanks(kk), t)
  +wk = Tail.walk(Laws.inert.node(kids), name, path, False{})
  +wr = Tail.walk(Laws.inert.node(r2), name, path, False{})
  +lhs = inert.tail.at(String.eq(tt, name), String.eq(tt, "Bool.pick"), o, l, c, name, path, skip, wk, wr)
  %inert.eq_keep(Laws.inert.blanks(kk), t, name, ef, en) : {lhs == inert.tail.at(_, String.eq(t, "Bool.pick"), o, l, c,
    name, path, skip, Tail.walk(kids, name, path, False{}), Tail.walk(r2, name, path, False{})) : List<&2, F.Finding>}
  %inert.eq_keep(Laws.inert.blanks(kk), t, "Bool.pick", ef, {==}) : {lhs == inert.tail.at(String.eq(tt, name), _, o, l,
    c, name, path, skip, Tail.walk(kids, name, path, False{}), Tail.walk(r2, name, path,
      False{})) : List<&2, F.Finding>}
  %ik : {lhs == inert.tail.at(String.eq(tt, name), String.eq(tt, "Bool.pick"), o, l, c, name, path, skip, _,
    Tail.walk(r2, name, path, False{})) : List<&2, F.Finding>}
  %ir : {lhs == inert.tail.at(String.eq(tt, name), String.eq(tt, "Bool.pick"), o, l, c, name, path, skip, wk, _)
    : List<&2, F.Finding>}
  {==}

# tail's walk reads no string: a leaf's text is compared with the def's name
# and with `Bool.pick`, which no string equals
law inert.tail.walk:
  for nn: Tree.Node
  for +name: String
  for +path: String
  for +skip: Bool
  for +en: {Laws.inert.marked(name) == False{} : Bool}
  for +e: {Laws.inert.ok(nn) == True{} : Bool}
  {Tail.walk(Laws.inert.node(nn), name, path, skip) == Tail.walk(nn, name, path, skip) : List<&2, F.Finding>}

def inert.tail.walk(nn, name, path, skip, en, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{o, +kids, cl}:
                      match o:
                        case Lex.Tok{ok, +ot, ol, oc}:
                          +eg = inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}), Bool.and(Laws.inert.ok(kids),
                            Laws.inert.ok(r2)), e)
                          inert.tail.lg(k, t, ot, l, c, name, path, skip, kids, r2,
                            inert.and_l(Laws.inert.fits(Lex.Tok{k, t, l, c}), Bool.and(Laws.inert.ok(kids),
                              Laws.inert.ok(r2)),
                              e), en,
                            inert.tail.walk(kids, name, path, False{}, en, inert.and_l(Laws.inert.ok(kids),
                              Laws.inert.ok(r2), eg)),
                            inert.tail.walk(r2, name, path, False{}, en, inert.and_r(Laws.inert.ok(kids),
                              Laws.inert.ok(r2), eg)))
                    case Tree.Leaf{x}:
                      inert.tail.walk(rest, name, path, False{}, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                        Laws.inert.ok(rest), e))
                    case Tree.Stmt{x, y, z}:
                      inert.tail.walk(rest, name, path, False{}, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                        Laws.inert.ok(rest), e))
                    case Tree.NNil{}:
                      inert.tail.walk(rest, name, path, False{}, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                        Laws.inert.ok(rest), e))
                    case Tree.NCons{x, y}:
                      inert.tail.walk(rest, name, path, False{}, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                        Laws.inert.ok(rest), e))
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NNil{}: {==}
        case Tree.Group{o, +kids, cl}:
          inert.cat2(Tail.walk(Laws.inert.node(kids), name, path, False{}), Tail.walk(kids, name, path, False{}),
            Tail.walk(Laws.inert.node(rest), name, path, False{}), Tail.walk(rest, name, path, False{}),
            inert.tail.walk(kids, name, path, False{}, en, inert.and_l(Laws.inert.ok(kids), Laws.inert.ok(rest), e)),
            inert.tail.walk(rest, name, path, False{}, en, inert.and_r(Laws.inert.ok(kids), Laws.inert.ok(rest), e)))
        case Tree.Stmt{sk, +kids, +body}:
          +es = inert.and_l(Bool.and(Laws.inert.ok(kids), Laws.inert.ok(body)), Laws.inert.ok(rest), e)
          +ek = inert.and_l(Laws.inert.ok(kids), Laws.inert.ok(body), es)
          +sb = Tail.bare(Laws.inert.node(kids), name)
          inert.cat3(Tail.walk(Laws.inert.node(kids), name, path, sb), Tail.walk(kids, name, path, Tail.bare(kids,
            name)),
            Tail.walk(Laws.inert.node(body), name, path, False{}), Tail.walk(body, name, path, False{}),
            Tail.walk(Laws.inert.node(rest), name, path, False{}), Tail.walk(rest, name, path, False{}),
            Equal.trans(List<&2, F.Finding>, Tail.walk(Laws.inert.node(kids), name, path, sb), Tail.walk(kids, name,
              path, sb),
              Tail.walk(kids, name, path, Tail.bare(kids, name)), inert.tail.walk(kids, name, path, sb, en, ek),
              Equal.cong(Bool, List<&2, F.Finding>, z => Tail.walk(kids, name, path, z), sb, Tail.bare(kids, name),
                inert.tail.bare(kids, name, en, ek))),
            inert.tail.walk(body, name, path, False{}, en, inert.and_r(Laws.inert.ok(kids), Laws.inert.ok(body), es)),
            inert.tail.walk(rest, name, path, False{}, en,
              inert.and_r(Bool.and(Laws.inert.ok(kids), Laws.inert.ok(body)), Laws.inert.ok(rest), e)))
        case Tree.NNil{}: inert.tail.walk(rest, name, path, False{}, en, e)
        case Tree.NCons{x, y}:
          inert.tail.walk(rest, name, path, False{}, en, inert.and_r(Laws.inert.ok(Tree.NCons{x, y}),
            Laws.inert.ok(rest), e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# the name, signature and body of a def as the lexer makes it
law inert.dok.head:
  for +name: String
  for +sig: Tree.Node
  for +body: Tree.Node
  for +rest: List<&2, Calls.Def>
  for +e: {inert.dok(Calls.Def{name, sig, body} <> rest) == True{} : Bool}
  {Laws.inert.marked(name) == False{} : Bool}

def inert.dok.head(name, sig, body, rest, e):
  inert.not_true(Laws.inert.marked(name), inert.and_l(Bool.not(Laws.inert.marked(name)),
    Bool.and(Laws.inert.ok(sig), Laws.inert.ok(body)), inert.and_l(Bool.and(Bool.not(Laws.inert.marked(name)),
      Bool.and(Laws.inert.ok(sig), Laws.inert.ok(body))), inert.dok(rest), e)))

# the body of a def as the lexer makes it fits
law inert.dok.body:
  for +name: String
  for +sig: Tree.Node
  for +body: Tree.Node
  for +rest: List<&2, Calls.Def>
  for +e: {inert.dok(Calls.Def{name, sig, body} <> rest) == True{} : Bool}
  {Laws.inert.ok(body) == True{} : Bool}

def inert.dok.body(name, sig, body, rest, e):
  inert.and_r(Laws.inert.ok(sig), Laws.inert.ok(body), inert.and_r(Bool.not(Laws.inert.marked(name)),
    Bool.and(Laws.inert.ok(sig), Laws.inert.ok(body)), inert.and_l(Bool.and(Bool.not(Laws.inert.marked(name)),
      Bool.and(Laws.inert.ok(sig), Laws.inert.ok(body))), inert.dok(rest), e)))

# the defs after one as the lexer makes them
law inert.dok.rest:
  for +name: String
  for +sig: Tree.Node
  for +body: Tree.Node
  for +rest: List<&2, Calls.Def>
  for +e: {inert.dok(Calls.Def{name, sig, body} <> rest) == True{} : Bool}
  {inert.dok(rest) == True{} : Bool}

def inert.dok.rest(name, sig, body, rest, e):
  inert.and_r(Bool.and(Bool.not(Laws.inert.marked(name)), Bool.and(Laws.inert.ok(sig), Laws.inert.ok(body))),
    inert.dok(rest), e)

# tail's stop for one def, from what it reads of the def
def inert.tail.stop(+seq: Bool, +ex: Bool, walk: List<&2, F.Finding>) -> List<&2, F.Finding>:
  Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(seq, Bool.not(ex))), [], _u => walk)

# tail over the defs read that way reports what it reports over the defs
law inert.tail.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  for +e: {inert.dok(ds) == True{} : Bool}
  {Tail.check.go(inert.defs(ds), path, acc) == Tail.check.go(ds, path, acc) : List<&2, F.Finding>}

def inert.tail.go(ds, path, acc, e):
  match ds:
    case Nil{}: {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +lst = inert.tail.stop(Calls.seq(Laws.inert.node(sig)), Calls.exempt(path, Laws.inert.node(sig)),
        Tail.walk(Laws.inert.node(body), name, path, False{}))
      %inert.seq(sig) : {Tail.check.go(inert.defs(rest), path, lst <> acc) == Tail.check.go(rest, path,
        inert.tail.stop(_, Calls.exempt(path, sig), Tail.walk(body, name, path, False{})) <> acc) : List<&2, F.Finding>}
      %inert.exempt(path, sig) : {Tail.check.go(inert.defs(rest), path, lst <> acc) == Tail.check.go(rest, path,
        inert.tail.stop(Calls.seq(Laws.inert.node(sig)), _, Tail.walk(body, name, path, False{})) <> acc)
        : List<&2, F.Finding>}
      %inert.tail.walk(body, name, path, False{}, inert.dok.head(name, sig, body, rest, e),
        inert.dok.body(name, sig, body, rest, e)) : {Tail.check.go(inert.defs(rest), path, lst <> acc)
          == Tail.check.go(rest, path, inert.tail.stop(Calls.seq(Laws.inert.node(sig)), Calls.exempt(path,
            Laws.inert.node(sig)), _) <> acc) : List<&2, F.Finding>}
      inert.tail.go(rest, path, lst <> acc, inert.dok.rest(name, sig, body, rest, e))

def Laws.inert_tail(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, ok, ok2, e):
  inert.via(Tree.Node, z => Tail.check.go(Calls.defs(z), path, []), tree, tree2, Laws.inert.node(tree),
    Laws.inert.node(tree2),
    inert.lift(z => Tail.check.go(z, path, []), tree, inert.tail.go(Calls.defs(tree), path, [], inert.dok.of(tree,
      ok))),
    inert.lift(z => Tail.check.go(z, path, []), tree2, inert.tail.go(Calls.defs(tree2), path, [], inert.dok.of(tree2,
      ok2))),
    e)

# pick
# ----

# both branches of a pick read that way call the def as they did
law inert.pick.both:
  for +kids: Tree.Node
  for +name: String
  for +en: {Laws.inert.marked(name) == False{} : Bool}
  for +ek: {Laws.inert.ok(kids) == True{} : Bool}
  {Pick.both(Calls.args(Laws.inert.node(kids)), name) == Pick.both(Calls.args(kids), name) : Bool}

def inert.pick.both(kids, name, en, ek):
  +l2 = Calls.calls(Calls.arg(Calls.args(Laws.inert.node(kids)), 2n), name)
  +l3 = Calls.calls(Calls.arg(Calls.args(Laws.inert.node(kids)), 3n), name)
  %inert.calls.nth(kids, 2n, name, en, ek) : {Bool.and(l2, l3) == Bool.and(_, Calls.calls(Calls.arg(Calls.args(kids),
    3n), name)) : Bool}
  %inert.calls.nth(kids, 3n, name, en, ek) : {Bool.and(l2, l3) == Bool.and(l2, _) : Bool}
  {==}

# either branch of a pick read that way calls the def as it did
law inert.pick.once:
  for +kids: Tree.Node
  for +name: String
  for +en: {Laws.inert.marked(name) == False{} : Bool}
  for +ek: {Laws.inert.ok(kids) == True{} : Bool}
  {Pick.once(Calls.args(Laws.inert.node(kids)), name) == Pick.once(Calls.args(kids), name) : Bool}

def inert.pick.once(kids, name, en, ek):
  +l2 = Calls.calls(Calls.arg(Calls.args(Laws.inert.node(kids)), 2n), name)
  +l3 = Calls.calls(Calls.arg(Calls.args(Laws.inert.node(kids)), 3n), name)
  %inert.calls.nth(kids, 2n, name, en, ek) : {Bool.or(l2, l3) == Bool.or(_, Calls.calls(Calls.arg(Calls.args(kids),
    3n), name)) : Bool}
  %inert.calls.nth(kids, 3n, name, en, ek) : {Bool.or(l2, l3) == Bool.or(l2, _) : Bool}
  {==}

# the hush a pick hands its arguments: reported in both branches or in one
def inert.pick.hush(+ip: Bool, +bb: Bool, +oo: Bool, +q: Bool) -> Bool:
  +two = Bool.and(Bool.and(ip, Bool.not(q)), bb)
  +one = Bool.and(Bool.and(ip, Bool.not(two)), Bool.and(Bool.not(q), oo))
  Bool.or(two, one)

# a call's findings from what pick's walk reads of it
def inert.pick.body(
  +ip: Bool,
  +bb: Bool,
  +oo: Bool,
  +q: Bool,
  +l: U32,
  +c: U32,
  +name: String,
  +path: String,
  inner: List<&2, F.Finding>,
  outer: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  +two = Bool.and(Bool.and(ip, Bool.not(q)), bb)
  +one = Bool.and(Bool.and(ip, Bool.not(two)), Bool.and(Bool.not(q), oo))
  +more = List.concat(&2, F.Finding, [inner, outer])
  Bool.pick(List<&2, F.Finding>, two,
    F.Finding{path, l, c, 9, "pick",
      name ++ " calls itself in both branches of Bool.pick, which evaluates both, so both calls run; bind the call once above the pick."}
      <> more,
    Bool.pick(List<&2, F.Finding>, one,
      F.Finding{path, l, c, 9, "pick",
        name ++ " calls itself in one branch of Bool.pick, which evaluates both, so the call always runs and never exits early; use Lazy.stop."}
        <> more,
      more))

# a call as pick's walk takes it: its kids and the rest walked
def inert.pick.at(
  +ip: Bool,
  +bb: Bool,
  +oo: Bool,
  +q: Bool,
  +at: Nat,
  +l: U32,
  +c: U32,
  +name: String,
  +path: String,
  +quiet: Bool,
  +hush: Bool,
  kids: Tree.Node,
  rest: Tree.Node
) -> List<&2, F.Finding>:
  inert.pick.body(ip, bb, oo, q, l, c, name, path, Pick.walk(kids, name, path, q, inert.pick.hush(ip, bb, oo, q), 0n),
    Pick.walk(rest, name, path, quiet, hush, at))

# a call whose kids and rest walk the same read that way
law inert.pick.nodes:
  for +ip: Bool
  for +bb: Bool
  for +oo: Bool
  for +q: Bool
  for +at: Nat
  for +l: U32
  for +c: U32
  for +name: String
  for +path: String
  for +quiet: Bool
  for +hush: Bool
  for +kids: Tree.Node
  for +rest: Tree.Node
  for ik: {Pick.walk(Laws.inert.node(kids), name, path, q, inert.pick.hush(ip, bb, oo, q), 0n)
    == Pick.walk(kids, name, path, q, inert.pick.hush(ip, bb, oo, q), 0n) : List<&2, F.Finding>}
  for ir: {Pick.walk(Laws.inert.node(rest), name, path, quiet, hush, at) == Pick.walk(rest, name, path, quiet, hush,
    at) : List<&2, F.Finding>}
  {inert.pick.at(ip, bb, oo, q, at, l, c, name, path, quiet, hush, Laws.inert.node(kids), Laws.inert.node(rest))
    == inert.pick.at(ip, bb, oo, q, at, l, c, name, path, quiet, hush, kids, rest) : List<&2, F.Finding>}

def inert.pick.nodes(ip, bb, oo, q, at, l, c, name, path, quiet, hush, kids, rest, ik, ir):
  +wk = Pick.walk(Laws.inert.node(kids), name, path, q, inert.pick.hush(ip, bb, oo, q), 0n)
  +wr = Pick.walk(Laws.inert.node(rest), name, path, quiet, hush, at)
  %ik : {inert.pick.body(ip, bb, oo, q, l, c, name, path, wk, wr)
    == inert.pick.body(ip, bb, oo, q, l, c, name, path, _, Pick.walk(rest, name, path, quiet, hush,
      at)) : List<&2, F.Finding>}
  %ir : {inert.pick.body(ip, bb, oo, q, l, c, name, path, wk, wr)
    == inert.pick.body(ip, bb, oo, q, l, c, name, path, wk, _) : List<&2, F.Finding>}
  {==}

# a call whose flags read the same gives the same findings
law inert.pick.flags:
  for +ip1: Bool
  for +ip2: Bool
  for +bb1: Bool
  for +bb2: Bool
  for +oo1: Bool
  for +oo2: Bool
  for +q: Bool
  for +at: Nat
  for +l: U32
  for +c: U32
  for +name: String
  for +path: String
  for +quiet: Bool
  for +hush: Bool
  for +kids: Tree.Node
  for +rest: Tree.Node
  for ei: {ip1 == ip2 : Bool}
  for eb: {bb1 == bb2 : Bool}
  for eo: {oo1 == oo2 : Bool}
  {inert.pick.at(ip1, bb1, oo1, q, at, l, c, name, path, quiet, hush, kids, rest)
    == inert.pick.at(ip2, bb2, oo2, q, at, l, c, name, path, quiet, hush, kids, rest) : List<&2, F.Finding>}

def inert.pick.flags(ip1, _ip2, bb1, bb2, oo1, oo2, q, at, l, c, name, path, quiet, hush, kids, rest, ei, eb, eo):
  +lhs = inert.pick.at(ip1, bb1, oo1, q, at, l, c, name, path, quiet, hush, kids, rest)
  %ei : {lhs == inert.pick.at(_, bb2, oo2, q, at, l, c, name, path, quiet, hush, kids, rest) : List<&2, F.Finding>}
  %eb : {lhs == inert.pick.at(ip1, _, oo2, q, at, l, c, name, path, quiet, hush, kids, rest) : List<&2, F.Finding>}
  %eo : {lhs == inert.pick.at(ip1, bb1, _, q, at, l, c, name, path, quiet, hush, kids, rest) : List<&2, F.Finding>}
  {==}

# pick's walk reads no string: a leaf's text is compared with `Bool.pick`,
# and the branches' with the def's name, which no string equals
law inert.pick.walk:
  for nn: Tree.Node
  for +name: String
  for +path: String
  for +quiet: Bool
  for +hush: Bool
  for +nth: Nat
  for +en: {Laws.inert.marked(name) == False{} : Bool}
  for +e: {Laws.inert.ok(nn) == True{} : Bool}
  {Pick.walk(Laws.inert.node(nn), name, path, quiet, hush, nth) == Pick.walk(nn, name, path, quiet, hush,
    nth) : List<&2, F.Finding>}

def inert.pick.walk(nn, name, path, quiet, hush, nth, en, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{o, +kids, cl}:
                      +eh = inert.and_l(Laws.inert.fits(Lex.Tok{k, t, l, c}), Bool.and(Laws.inert.ok(kids),
                        Laws.inert.ok(r2)), e)
                      +eg = inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}), Bool.and(Laws.inert.ok(kids),
                        Laws.inert.ok(r2)), e)
                      +ek = inert.and_l(Laws.inert.ok(kids), Laws.inert.ok(r2), eg)
                      +er = inert.and_r(Laws.inert.ok(kids), Laws.inert.ok(r2), eg)
                      +at = Pick.next(k, nth)
                      +q = Pick.mute(quiet, hush, at)
                      +ipl = String.eq(Laws.inert.keep(Laws.inert.blanks(k), t), "Bool.pick")
                      +bbl = Pick.both(Calls.args(Laws.inert.node(kids)), name)
                      +ool = Pick.once(Calls.args(Laws.inert.node(kids)), name)
                      +mid = inert.pick.at(ipl, bbl, ool, q, at, l, c, name, path, quiet, hush, kids, r2)
                      Equal.trans(List<&2, F.Finding>,
                        inert.pick.at(ipl, bbl, ool, q, at, l, c, name, path, quiet, hush, Laws.inert.node(kids),
                          Laws.inert.node(r2)), mid,
                        inert.pick.at(String.eq(t, "Bool.pick"), Pick.both(Calls.args(kids), name),
                          Pick.once(Calls.args(kids), name),
                          q, at, l, c, name, path, quiet, hush, kids, r2),
                        inert.pick.nodes(ipl, bbl, ool, q, at, l, c, name, path, quiet, hush, kids, r2,
                          inert.pick.walk(kids, name, path, q, inert.pick.hush(ipl, bbl, ool, q), 0n, en, ek),
                          inert.pick.walk(r2, name, path, quiet, hush, at, en, er)),
                        inert.pick.flags(ipl, String.eq(t, "Bool.pick"), bbl, Pick.both(Calls.args(kids), name), ool,
                          Pick.once(Calls.args(kids), name), q, at, l, c, name, path, quiet, hush, kids, r2,
                          inert.eq_keep(Laws.inert.blanks(k), t, "Bool.pick", eh, {==}), inert.pick.both(kids, name,
                            en, ek),
                          inert.pick.once(kids, name, en, ek)))
                    case Tree.Leaf{x}:
                      inert.pick.walk(rest, name, path, quiet, hush, Pick.next(k, nth), en,
                        inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}), Laws.inert.ok(rest), e))
                    case Tree.Stmt{x, y, z}:
                      inert.pick.walk(rest, name, path, quiet, hush, Pick.next(k, nth), en,
                        inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}), Laws.inert.ok(rest), e))
                    case Tree.NNil{}:
                      inert.pick.walk(rest, name, path, quiet, hush, Pick.next(k, nth), en,
                        inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}), Laws.inert.ok(rest), e))
                    case Tree.NCons{x, y}:
                      inert.pick.walk(rest, name, path, quiet, hush, Pick.next(k, nth), en,
                        inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}), Laws.inert.ok(rest), e))
                case Tree.Leaf{x}:
                  {==}
                case Tree.Group{x, y, z}:
                  {==}
                case Tree.Stmt{x, y, z}:
                  {==}
                case Tree.NNil{}:
                  {==}
        case Tree.Group{o, +kids, cl}:
          +m = Pick.mute(quiet, hush, nth)
          inert.cat2(Pick.walk(Laws.inert.node(kids), name, path, m, False{}, 0n), Pick.walk(kids, name, path, m,
            False{}, 0n),
            Pick.walk(Laws.inert.node(rest), name, path, quiet, hush, nth), Pick.walk(rest, name, path, quiet, hush,
              nth),
            inert.pick.walk(kids, name, path, m, False{}, 0n, en, inert.and_l(Laws.inert.ok(kids),
              Laws.inert.ok(rest), e)),
            inert.pick.walk(rest, name, path, quiet, hush, nth, en, inert.and_r(Laws.inert.ok(kids),
              Laws.inert.ok(rest), e)))
        case Tree.Stmt{sk, +kids, +body}:
          +es = inert.and_l(Bool.and(Laws.inert.ok(kids), Laws.inert.ok(body)), Laws.inert.ok(rest), e)
          +m = Pick.mute(quiet, hush, nth)
          inert.cat3(Pick.walk(Laws.inert.node(kids), name, path, m, False{}, 0n), Pick.walk(kids, name, path, m,
            False{}, 0n),
            Pick.walk(Laws.inert.node(body), name, path, m, False{}, 0n), Pick.walk(body, name, path, m, False{}, 0n),
            Pick.walk(Laws.inert.node(rest), name, path, quiet, hush, nth), Pick.walk(rest, name, path, quiet, hush,
              nth),
            inert.pick.walk(kids, name, path, m, False{}, 0n, en, inert.and_l(Laws.inert.ok(kids),
              Laws.inert.ok(body), es)),
            inert.pick.walk(body, name, path, m, False{}, 0n, en, inert.and_r(Laws.inert.ok(kids),
              Laws.inert.ok(body), es)),
            inert.pick.walk(rest, name, path, quiet, hush, nth, en,
              inert.and_r(Bool.and(Laws.inert.ok(kids), Laws.inert.ok(body)), Laws.inert.ok(rest), e)))
        case Tree.NNil{}:
          inert.pick.walk(rest, name, path, quiet, hush, nth, en, e)
        case Tree.NCons{x, y}:
          inert.pick.walk(rest, name, path, quiet, hush, nth, en, inert.and_r(Laws.inert.ok(Tree.NCons{x, y}),
            Laws.inert.ok(rest), e))
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{o, gk, cl}:
      {==}
    case Tree.Stmt{sk, sks, sb}:
      {==}
    case Tree.NNil{}:
      {==}

# pick's stop for one def
def inert.pick.stop(+ex: Bool, walk: List<&2, F.Finding>) -> List<&2, F.Finding>:
  Lazy.stop(List<&2, F.Finding>, ex, [], _u => walk)

# pick over the defs read that way reports what it reports over the defs
law inert.pick.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  for +e: {inert.dok(ds) == True{} : Bool}
  {Pick.check.go(inert.defs(ds), path, acc) == Pick.check.go(ds, path, acc) : List<&2, F.Finding>}

def inert.pick.go(ds, path, acc, e):
  match ds:
    case Nil{}: {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +lst = inert.pick.stop(Calls.exempt(path, Laws.inert.node(sig)), Pick.walk(Laws.inert.node(body), name, path,
        False{},
        False{}, 0n))
      %inert.exempt(path, sig) : {Pick.check.go(inert.defs(rest), path, lst <> acc) == Pick.check.go(rest, path,
        inert.pick.stop(_, Pick.walk(body, name, path, False{}, False{}, 0n)) <> acc) : List<&2, F.Finding>}
      %inert.pick.walk(body, name, path, False{}, False{}, 0n, inert.dok.head(name, sig, body, rest, e),
        inert.dok.body(name, sig, body, rest, e)) : {Pick.check.go(inert.defs(rest), path, lst <> acc)
          == Pick.check.go(rest, path, inert.pick.stop(Calls.exempt(path, Laws.inert.node(sig)), _) <> acc)
          : List<&2, F.Finding>}
      inert.pick.go(rest, path, lst <> acc, inert.dok.rest(name, sig, body, rest, e))

def Laws.inert_pick(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, ok, ok2, e):
  inert.via(Tree.Node, z => Pick.check.go(Calls.defs(z), path, []), tree, tree2, Laws.inert.node(tree),
    Laws.inert.node(tree2),
    inert.lift(z => Pick.check.go(z, path, []), tree, inert.pick.go(Calls.defs(tree), path, [], inert.dok.of(tree,
      ok))),
    inert.lift(z => Pick.check.go(z, path, []), tree2, inert.pick.go(Calls.defs(tree2), path, [], inert.dok.of(tree2,
      ok2))),
    e)

# doc
# ---

# a line that is a `#` line exactly when b says so
def inert.doc.line(bb: Bool) -> String:
  match bb:
    case True{}: "#"
    case False{}: ""

# the lines rebuilt from which of them start with `#`
def inert.doc.relines(bs: List<&2, Bool>) -> List<&2, String>:
  match bs:
    case Nil{}: Nil{}
    case Con{h, t}: inert.doc.line(h) <> inert.doc.relines(t)

# a line rebuilt from its `#` test starts with `#` as it did
law inert.doc.hash1:
  for b: Bool
  {String.starts_with(inert.doc.line(b), "#") == b : Bool}

def inert.doc.hash1(b):
  match b:
    case True{}: {==}
    case False{}: {==}

# the `#` test on the lines rebuilt is the test on the lines
law inert.doc.hash:
  for lines: List<&2, String>
  for +nn: U32
  {Doc.check.hash(inert.doc.relines(Laws.inert.hashes(lines)), nn) == Doc.check.hash(lines, nn) : Bool}

def inert.doc.hash(lines, nn):
  match lines:
    case Nil{}: {==}
    case Con{+hh, tt}:
      +h1 = String.starts_with(hh, "#")
      %inert.doc.hash1(h1) : {Lazy.stop(Bool, U32.is_eq(nn, 0), String.starts_with(inert.doc.line(h1), "#"),
        _u => Doc.check.hash(inert.doc.relines(Laws.inert.hashes(tt)), U32.sub(nn, 1)))
        == Lazy.stop(Bool, U32.is_eq(nn, 0), _, _u => Doc.check.hash(tt, U32.sub(nn, 1))) : Bool}
      %inert.doc.hash(tt, U32.sub(nn, 1)) : {Lazy.stop(Bool, U32.is_eq(nn, 0), String.starts_with(inert.doc.line(h1),
        "#"),
        _u => Doc.check.hash(inert.doc.relines(Laws.inert.hashes(tt)), U32.sub(nn, 1)))
        == Lazy.stop(Bool, U32.is_eq(nn, 0), String.starts_with(inert.doc.line(h1), "#"), _u => _) : Bool}
      {==}

# doc's walk reads its items' kinds, names and lines, and of its lines only
# which start with `#`
law inert.doc.go:
  for items: List<&2, Outline.Item>
  for +path: String
  for +lines: List<&2, String>
  {Doc.check.go(Laws.inert.items(items), path, inert.doc.relines(Laws.inert.hashes(lines)))
    == Doc.check.go(items, path, lines) : List<&2, F.Finding>}

def inert.doc.go(items, path, lines):
  match items:
    case Nil{}: {==}
    case Con{Outline.Item{+k, +name, +line, +s, +d, +p}, +rest}:
      +rl = inert.doc.relines(Laws.inert.hashes(lines))
      +lhs = Doc.check.go(Laws.inert.items(Outline.Item{k, name, line, s, d, p} <> rest), path, rl)
      %inert.doc.hash(lines, U32.sub(line, 1)) : {lhs == Bool.pick(List<&2, F.Finding>,
        Lazy.and_then(Bool.and(Doc.needs(k),
        Bool.not(Doc.exempt(name))), _u => Bool.not(Lazy.and_then(Bool.not(U32.is_eq(line, 0)), _v => _))),
        F.Finding{path, line, 0, 0, "doc", Doc.what(k) ++ " " ++ name ++ " has no comment above it."}
          <> Doc.check.go(rest, path, lines), Doc.check.go(rest, path, lines)) : List<&2, F.Finding>}
      %inert.doc.go(rest, path, lines) : {lhs == Bool.pick(List<&2, F.Finding>, Lazy.and_then(Bool.and(Doc.needs(k),
        Bool.not(Doc.exempt(name))), _u => Bool.not(Lazy.and_then(Bool.not(U32.is_eq(line, 0)),
          _v => Doc.check.hash(rl, U32.sub(line, 1))))),
        F.Finding{path, line, 0, 0, "doc", Doc.what(k) ++ " " ++ name ++ " has no comment above it."} <> _, _)
        : List<&2, F.Finding>}
      {==}

def Laws.inert_doc(path, text, toks, _tree, _bound, items, text2, toks2, _tree2, _bound2, items2, ei, el):
  +l1 = Doc.lines(text, toks)
  +l2 = Doc.lines(text2, toks2)
  +r1 = Doc.check.go(Laws.inert.items(items), path, inert.doc.relines(Laws.inert.hashes(l1)))
  +m = Doc.check.go(Laws.inert.items(items2), path, inert.doc.relines(Laws.inert.hashes(l1)))
  +r2 = Doc.check.go(Laws.inert.items(items2), path, inert.doc.relines(Laws.inert.hashes(l2)))
  +w1 = Doc.check.go(items, path, l1)
  +w2 = Doc.check.go(items2, path, l2)
  Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
    z => Lazy.stop(List<&2, F.Finding>, Bool.or(Paths.is_proof(path), Paths.is_test(path)), [], _u => z), w1, w2,
    Equal.trans(List<&2, F.Finding>, w1, r1, w2, Equal.sym(List<&2, F.Finding>, r1, w1, inert.doc.go(items, path, l1)),
      Equal.trans(List<&2, F.Finding>, r1, m, w2,
        Equal.cong(List<&2, Outline.Item>, List<&2, F.Finding>,
          z => Doc.check.go(z, path, inert.doc.relines(Laws.inert.hashes(l1))), Laws.inert.items(items),
          Laws.inert.items(items2), ei),
        Equal.trans(List<&2, F.Finding>, m, r2, w2,
          Equal.cong(List<&2, Bool>, List<&2, F.Finding>,
            z => Doc.check.go(Laws.inert.items(items2), path, inert.doc.relines(z)), Laws.inert.hashes(l1),
            Laws.inert.hashes(l2), el),
          inert.doc.go(items2, path, l2)))))

# param
# -----

# param's walk over binders whose notes are already cut
def inert.param.go(binds: List<&2, Bind.Bind>, +path: String) -> List<&2, F.Finding>:
  match binds:
    case Nil{}: Nil{}
    case Con{Bind.Bind{+nm, +line, +col, +kind, +cn}, rest}:
      +more = inert.param.go(rest, path)
      +quant = Bool.or(Bool.not(String.contains(cn, ":")), String.ends_with(cn, ": Quant"))
      Bool.pick(List<&2, F.Finding>, Bool.and(Param.check.is_param(kind), Bool.and(Param.check.short(nm),
        Bool.not(Bool.or(Param.check.upper(nm), quant)))),
        F.Finding{path, line, col, U32.from_nat(String.length(nm)), "param",
          "Parameter " ++ nm ++ " is too short; use at least 2 characters."} <> more, more)

# param's walk reads each binder's note with its strings cut
law inert.param.walk:
  for binds: List<&2, Bind.Bind>
  for +path: String
  {inert.param.go(Laws.inert.binds(binds), path) == Param.check.go(binds, path) : List<&2, F.Finding>}

def inert.param.walk(binds, path):
  match binds:
    case Nil{}: {==}
    case Con{Bind.Bind{+nm, +line, +col, +kind, +note}, +rest}:
      %inert.param.walk(rest, path) : {inert.param.go(Laws.inert.binds(Bind.Bind{nm, line, col, kind, note} <> rest),
        path)
        == Bool.pick(List<&2, F.Finding>, Bool.and(Param.check.is_param(kind), Bool.and(Param.check.short(nm),
          Bool.not(Param.check.allowed(nm,
            note)))), F.Finding{path, line, col, U32.from_nat(String.length(nm)), "param",
            "Parameter " ++ nm ++ " is too short; use at least 2 characters."} <> _, _) : List<&2, F.Finding>}
      {==}

def Laws.inert_param(b1, b2, path, e):
  +v1 = Laws.inert.binds(b1)
  +v2 = Laws.inert.binds(b2)
  Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
    z => Lazy.stop(List<&2, F.Finding>, Paths.is_proof(path), [], _u => z), Param.check.go(b1, path),
    Param.check.go(b2, path),
    Equal.trans(List<&2, F.Finding>, Param.check.go(b1, path), inert.param.go(v1, path), Param.check.go(b2, path),
      Equal.sym(List<&2, F.Finding>, inert.param.go(v1, path), Param.check.go(b1, path), inert.param.walk(b1, path)),
      Equal.trans(List<&2, F.Finding>, inert.param.go(v1, path), inert.param.go(v2, path), Param.check.go(b2, path),
        Equal.cong(List<&2, Bind.Bind>, List<&2, F.Finding>, z => inert.param.go(z, path), v1, v2, e),
        inert.param.walk(b2, path))))

# strict
# ------

# a node read that way ends a stretch as it did
law inert.strict.ends:
  for nn: Tree.Node
  {Calls.kind.leaf(~Strict.seg_op.ends, Laws.inert.node(nn)) == Calls.kind.leaf(~Strict.seg_op.ends, nn) : Bool}

def inert.strict.ends(nn):
  Equal.cong(Maybe<&2, Lex.TokKind>, Bool,
    m => Calls.kind.of(~Strict.seg_op.ends, m), Calls.leaf.kind(Laws.inert.node(nn)), Calls.leaf.kind(nn),
    inert.leaf_kind(nn))

# a chain read that way holds `&&` or `||` in its stretch as it did
law inert.strict.seg:
  for nn: Tree.Node
  {Strict.seg_op(Laws.inert.node(nn)) == Strict.seg_op(nn) : Bool}

def inert.strict.seg(nn):
  match nn:
    case Tree.NCons{+h, +rest}:
      +ke = Calls.kind.leaf(~Strict.seg_op.ends, h)
      +ko = Calls.kind.leaf(~Calls.kind.oper, h)
      +kb = Calls.kind.leaf(~Laws.inert.blanks, h)
      +th = Calls.leaf.text(h)
      +rhs = Strict.seg_op(Tree.NCons{h, rest})
      +ih = Laws.inert.node(h)
      +ir = Laws.inert.node(rest)
      %Equal.sym(Bool, Calls.kind.leaf(~Strict.seg_op.ends, ih), ke, inert.strict.ends(h)) :
        {Lazy.stop(Bool, _, False{},
        _u => Strict.seg_op.or(Bool.and(Calls.kind.leaf(~Calls.kind.oper, ih), Strict.logic(Calls.leaf.text(ih))),
          Strict.seg_op(ir))) == rhs : Bool}
      %Equal.sym(Bool, Calls.kind.leaf(~Calls.kind.oper, ih), ko, inert.oper(h)) : {Lazy.stop(Bool, ke, False{},
        _u => Strict.seg_op.or(Bool.and(_, Strict.logic(Calls.leaf.text(ih))), Strict.seg_op(ir))) == rhs : Bool}
      %Equal.sym(String, Calls.leaf.text(ih), Laws.inert.keep(kb, th), inert.leaf_text(h)) : {Lazy.stop(Bool, ke,
        False{}, _u => Strict.seg_op.or(Bool.and(ko, Strict.logic(_)), Strict.seg_op(ir))) == rhs : Bool}
      %Equal.sym(Bool, Strict.seg_op(ir), Strict.seg_op(rest), inert.strict.seg(rest)) : {Lazy.stop(Bool, ke,
        False{}, _u => Strict.seg_op.or(Bool.and(ko, Strict.logic(Laws.inert.keep(kb, th))), _)) == rhs : Bool}
      %Equal.sym(Bool, Bool.and(ko, Strict.logic(Laws.inert.keep(kb, th))), Bool.and(ko, Strict.logic(th)),
        inert.guard(ko, kb, th, z => Strict.logic(z), inert.oper_code(h))) : {Lazy.stop(Bool, ke, False{},
          _u => Strict.seg_op.or(_, Strict.seg_op(rest))) == rhs : Bool}
      {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a leaf read by its kind, each branch reading as it did
law inert.strict.leaf:
  for +kk: Lex.TokKind
  for -a1: List<&2, F.Finding>
  for -a2: List<&2, F.Finding>
  for -b1: List<&2, F.Finding>
  for -b2: List<&2, F.Finding>
  for -c1: List<&2, F.Finding>
  for -c2: List<&2, F.Finding>
  for ea: {a1 == a2 : List<&2, F.Finding>}
  for eb: {b1 == b2 : List<&2, F.Finding>}
  for ec: {c1 == c2 : List<&2, F.Finding>}
  {Strict.leaf(kk, _u => a1, _v => b1, _w => c1) == Strict.leaf(kk, _u => a2, _v => b2, _w => c2) : List<&2, F.Finding>}

def inert.strict.leaf(kk, a1, _a2, b1, b2, c1, c2, ea, eb, ec):
  -lhs = Strict.leaf(kk, _u => a1, _v => b1, _w => c1)
  %ea : {lhs == Strict.leaf(kk, _u => _, _v => b2, _w => c2) : List<&2, F.Finding>}
  %eb : {lhs == Strict.leaf(kk, _u => a1, _v => _, _w => c2) : List<&2, F.Finding>}
  %ec : {lhs == Strict.leaf(kk, _u => a1, _v => b1, _w => _) : List<&2, F.Finding>}
  {==}

# the stretch a group after a name is walked in, the name read that way
law inert.strict.inner:
  for +kk: Lex.TokKind
  for +t: String
  for +o: String
  for +hot: Bool
  for +ef: {Laws.inert.fits.go(Laws.inert.blanks(kk), t) == True{} : Bool}
  {Strict.inner(hot, o, Laws.inert.keep(Laws.inert.blanks(kk), t)) == Strict.inner(hot, o, t) : Bool}

def inert.strict.inner(kk, t, o, hot, ef):
  +tt = Laws.inert.keep(Laws.inert.blanks(kk), t)
  %inert.eq_keep(Laws.inert.blanks(kk), t, "Bool.and", ef, {==}) : {Strict.inner(hot, o, tt)
    == Bool.or(hot, Bool.and(String.eq(o, "("), Bool.or(_, String.eq(t, "Bool.or")))) : Bool}
  %inert.eq_keep(Laws.inert.blanks(kk), t, "Bool.or", ef, {==}) : {Strict.inner(hot, o, tt)
    == Bool.or(hot, Bool.and(String.eq(o, "("), Bool.or(String.eq(tt, "Bool.and"), _))) : Bool}
  {==}

# past a comma or a `=>`, the rest walked in the stretch its own operators set
law inert.strict.past:
  for +rest: Tree.Node
  for +name: String
  for +path: String
  for +outer: Bool
  for -hh: Bool -> Bool
  for ih: {Strict.walk(Laws.inert.node(rest), name, path, outer, hh(Strict.seg_op(Laws.inert.node(rest))))
    == Strict.walk(rest, name, path, outer, hh(Strict.seg_op(Laws.inert.node(rest)))) : List<&2, F.Finding>}
  {Strict.walk(Laws.inert.node(rest), name, path, outer, hh(Strict.seg_op(Laws.inert.node(rest))))
    == Strict.walk(rest, name, path, outer, hh(Strict.seg_op(rest))) : List<&2, F.Finding>}

def inert.strict.past(rest, name, path, outer, hh, ih):
  %inert.strict.seg(rest) : {Strict.walk(Laws.inert.node(rest), name, path, outer,
    hh(Strict.seg_op(Laws.inert.node(rest))))
    == Strict.walk(rest, name, path, outer, hh(_)) : List<&2, F.Finding>}
  ih

# a name then a group: the name compared, the group and the rest walked as
# they were
law inert.strict.lg:
  for +kk: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +o: String
  for +name: String
  for +path: String
  for +outer: Bool
  for +hot: Bool
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +ef: {Laws.inert.fits.go(Laws.inert.blanks(kk), t) == True{} : Bool}
  for +en: {Laws.inert.marked(name) == False{} : Bool}
  for ik: {Strict.walk(Laws.inert.node(kids), name, path, Strict.inner(hot, o, Laws.inert.keep(Laws.inert.blanks(kk),
    t)),
      Bool.or(Strict.inner(hot, o, Laws.inert.keep(Laws.inert.blanks(kk), t)), Strict.seg_op(Laws.inert.node(kids))))
    == Strict.walk(kids, name, path, Strict.inner(hot, o, Laws.inert.keep(Laws.inert.blanks(kk), t)),
      Bool.or(Strict.inner(hot, o, Laws.inert.keep(Laws.inert.blanks(kk), t)), Strict.seg_op(Laws.inert.node(kids))))
    : List<&2, F.Finding>}
  for ir: {Strict.walk(Laws.inert.node(r2), name, path, outer, hot) == Strict.walk(r2, name, path, outer, hot)
    : List<&2, F.Finding>}
  {Strict.call(Laws.inert.keep(Laws.inert.blanks(kk), t), l, c, o, name, path, hot,
      Strict.walk(Laws.inert.node(kids), name, path, Strict.inner(hot, o, Laws.inert.keep(Laws.inert.blanks(kk), t)),
        Bool.or(Strict.inner(hot, o, Laws.inert.keep(Laws.inert.blanks(kk), t)), Strict.seg_op(Laws.inert.node(kids)))),
      Strict.walk(Laws.inert.node(r2), name, path, outer, hot))
    == Strict.call(t, l, c, o, name, path, hot,
      Strict.walk(kids, name, path, Strict.inner(hot, o, t), Bool.or(Strict.inner(hot, o, t), Strict.seg_op(kids))),
      Strict.walk(r2, name, path, outer, hot)) : List<&2, F.Finding>}

def inert.strict.lg(kk, t, l, c, o, name, path, outer, hot, kids, r2, ef, en, ik, ir):
  +tt = Laws.inert.keep(Laws.inert.blanks(kk), t)
  +i1 = Strict.inner(hot, o, tt)
  +wk = Strict.walk(Laws.inert.node(kids), name, path, i1, Bool.or(i1, Strict.seg_op(Laws.inert.node(kids))))
  +wr = Strict.walk(Laws.inert.node(r2), name, path, outer, hot)
  +lhs = Strict.call(tt, l, c, o, name, path, hot, wk, wr)
  %inert.strict.inner(kk, t, o, hot, ef) : {lhs == Strict.call(t, l, c, o, name, path, hot, Strict.walk(kids, name,
    path, _,
    Bool.or(_, Strict.seg_op(kids))), Strict.walk(r2, name, path, outer, hot)) : List<&2, F.Finding>}
  %inert.strict.seg(kids) : {lhs == Strict.call(t, l, c, o, name, path, hot, Strict.walk(kids, name, path, i1,
    Bool.or(i1, _)), Strict.walk(r2, name, path, outer, hot)) : List<&2, F.Finding>}
  %ik : {lhs == Strict.call(t, l, c, o, name, path, hot, _, Strict.walk(r2, name, path, outer, hot)) : List<&2,
    F.Finding>}
  %ir : {lhs == Strict.call(t, l, c, o, name, path, hot, wk, _) : List<&2, F.Finding>}
  %inert.eq_keep(Laws.inert.blanks(kk), t, name, ef, en) : {Strict.call(tt, l, c, o, name, path, hot, wk, wr)
    == Bool.pick(List<&2, F.Finding>, Bool.and(Bool.and(String.eq(o, "("), _), hot),
      F.Finding{path, l, c, U32.from_nat(String.length(name)), "strict",
        name ++ " calls itself inside Bool.and or Bool.or, which evaluate both sides, so there is no short-circuit; match on the Bool in a helper."}
        <> List.concat(&2, F.Finding, [wk, wr]), List.concat(&2, F.Finding, [wk, wr])) : List<&2, F.Finding>}
  {==}

# a leaf then a cell that is no group: each branch walks the rest as it did
law inert.strict.gen:
  for +kk: Lex.TokKind
  for +rest: Tree.Node
  for +name: String
  for +path: String
  for +outer: Bool
  for +hot: Bool
  for ea: {Strict.walk(Laws.inert.node(rest), name, path, outer, Bool.or(outer, Strict.seg_op(Laws.inert.node(rest))))
    == Strict.walk(rest, name, path, outer, Bool.or(outer, Strict.seg_op(rest))) : List<&2, F.Finding>}
  for eb: {Strict.walk(Laws.inert.node(rest), name, path, outer, Strict.seg_op(Laws.inert.node(rest)))
    == Strict.walk(rest, name, path, outer, Strict.seg_op(rest)) : List<&2, F.Finding>}
  for ec: {Strict.walk(Laws.inert.node(rest), name, path, outer, hot) == Strict.walk(rest, name, path, outer, hot)
    : List<&2, F.Finding>}
  {Strict.leaf(kk, _u => Strict.walk(Laws.inert.node(rest), name, path, outer, Bool.or(outer,
      Strict.seg_op(Laws.inert.node(rest)))), _v => Strict.walk(Laws.inert.node(rest), name, path, outer,
      Strict.seg_op(Laws.inert.node(rest))), _w => Strict.walk(Laws.inert.node(rest), name, path, outer, hot))
    == Strict.leaf(kk, _u => Strict.walk(rest, name, path, outer, Bool.or(outer, Strict.seg_op(rest))),
      _v => Strict.walk(rest, name, path, outer, Strict.seg_op(rest)), _w => Strict.walk(rest, name, path, outer, hot))
    : List<&2, F.Finding>}

def inert.strict.gen(kk, rest, name, path, outer, hot, ea, eb, ec):
  inert.strict.leaf(kk, Strict.walk(Laws.inert.node(rest), name, path, outer, Bool.or(outer,
    Strict.seg_op(Laws.inert.node(rest)))), Strict.walk(rest, name, path, outer, Bool.or(outer, Strict.seg_op(rest))),
    Strict.walk(Laws.inert.node(rest), name, path, outer, Strict.seg_op(Laws.inert.node(rest))),
    Strict.walk(rest, name, path, outer, Strict.seg_op(rest)), Strict.walk(Laws.inert.node(rest), name, path, outer,
      hot),
    Strict.walk(rest, name, path, outer, hot), ea, eb, ec)

# strict's walk reads no string: a leaf's text is compared with the def's
# name, `Bool.and` and `Bool.or`, which no string equals
law inert.strict.walk:
  for nn: Tree.Node
  for +name: String
  for +path: String
  for +outer: Bool
  for +hot: Bool
  for +en: {Laws.inert.marked(name) == False{} : Bool}
  for +e: {Laws.inert.ok(nn) == True{} : Bool}
  {Strict.walk(Laws.inert.node(nn), name, path, outer, hot) == Strict.walk(nn, name, path, outer, hot) : List<&2,
    F.Finding>}

def inert.strict.walk(nn, name, path, outer, hot, en, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{o, +kids, cl}:
                      match o:
                        case Lex.Tok{ok, +ot, ol, oc}:
                          +a1 = Strict.walk(Laws.inert.node(rest), name, path, outer, Bool.or(outer,
                            Strict.seg_op(Laws.inert.node(rest))))
                          +b1 = Strict.walk(Laws.inert.node(rest), name, path, outer,
                            Strict.seg_op(Laws.inert.node(rest)))
                          +k1 = Strict.walk(Laws.inert.node(kids), name, path, Strict.inner(hot, ot,
                            Laws.inert.keep(Laws.inert.blanks(k), t)), Bool.or(Strict.inner(hot, ot,
                              Laws.inert.keep(Laws.inert.blanks(k), t)), Strict.seg_op(Laws.inert.node(kids))))
                          +c1 = Strict.call(Laws.inert.keep(Laws.inert.blanks(k), t), l, c, ot, name, path, hot, k1,
                            Strict.walk(Laws.inert.node(r2), name, path, outer, hot))
                          +k0 = Strict.walk(kids, name, path, Strict.inner(hot, ot, t), Bool.or(Strict.inner(hot, ot,
                            t),
                            Strict.seg_op(kids)))
                          +c0 = Strict.call(t, l, c, ot, name, path, hot, k0, Strict.walk(r2, name, path, outer, hot))
                          inert.strict.leaf(k, a1, Strict.walk(rest, name, path, outer, Bool.or(outer,
                            Strict.seg_op(rest))), b1,
                            Strict.walk(rest, name, path, outer, Strict.seg_op(rest)), c1, c0,
                            inert.strict.past(rest, name, path, outer, z => Bool.or(outer, z), inert.strict.walk(rest,
                              name, path, outer,
                              Bool.or(outer,
                                Strict.seg_op(Laws.inert.node(rest))), en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t,
                                  l, c}), Laws.inert.ok(rest), e))),
                            inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path,
                              outer,
                              Strict.seg_op(Laws.inert.node(rest)), en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l,
                                c}), Laws.inert.ok(rest), e))),
                            inert.strict.lg(k, t, l, c, ot, name, path, outer, hot, kids, r2,
                              inert.and_l(Laws.inert.fits(Lex.Tok{k, t, l, c}), Bool.and(Laws.inert.ok(kids),
                                Laws.inert.ok(r2)), e), en,
                              inert.strict.walk(kids, name, path, Strict.inner(hot, ot,
                                Laws.inert.keep(Laws.inert.blanks(k), t)), Bool.or(Strict.inner(hot, ot,
                                  Laws.inert.keep(Laws.inert.blanks(k), t)), Strict.seg_op(Laws.inert.node(kids))), en,
                                inert.and_l(Laws.inert.ok(kids), Laws.inert.ok(r2),
                                  inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}), Bool.and(Laws.inert.ok(kids),
                                    Laws.inert.ok(r2)), e))),
                              inert.strict.walk(r2, name, path, outer, hot, en, inert.and_r(Laws.inert.ok(kids),
                                Laws.inert.ok(r2), inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                                  Bool.and(Laws.inert.ok(kids), Laws.inert.ok(r2)), e)))))
                    case Tree.Leaf{x}:
                      inert.strict.gen(k, rest, name, path, outer, hot,
                        inert.strict.past(rest, name, path, outer, z => Bool.or(outer, z), inert.strict.walk(rest,
                          name, path, outer,
                          Bool.or(outer,
                            Strict.seg_op(Laws.inert.node(rest))), en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l,
                              c}), Laws.inert.ok(rest), e))),
                        inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path, outer,
                          Strict.seg_op(Laws.inert.node(rest)), en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                            Laws.inert.ok(rest), e))),
                        inert.strict.walk(rest, name, path, outer, hot, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t,
                          l, c}), Laws.inert.ok(rest), e)))
                    case Tree.Stmt{x, y, z}:
                      inert.strict.gen(k, rest, name, path, outer, hot,
                        inert.strict.past(rest, name, path, outer, z => Bool.or(outer, z), inert.strict.walk(rest,
                          name, path, outer,
                          Bool.or(outer,
                            Strict.seg_op(Laws.inert.node(rest))), en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l,
                              c}), Laws.inert.ok(rest), e))),
                        inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path, outer,
                          Strict.seg_op(Laws.inert.node(rest)), en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                            Laws.inert.ok(rest), e))),
                        inert.strict.walk(rest, name, path, outer, hot, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t,
                          l, c}), Laws.inert.ok(rest), e)))
                    case Tree.NNil{}:
                      inert.strict.gen(k, rest, name, path, outer, hot,
                        inert.strict.past(rest, name, path, outer, z => Bool.or(outer, z), inert.strict.walk(rest,
                          name, path, outer,
                          Bool.or(outer,
                            Strict.seg_op(Laws.inert.node(rest))), en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l,
                              c}), Laws.inert.ok(rest), e))),
                        inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path, outer,
                          Strict.seg_op(Laws.inert.node(rest)), en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                            Laws.inert.ok(rest), e))),
                        inert.strict.walk(rest, name, path, outer, hot, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t,
                          l, c}), Laws.inert.ok(rest), e)))
                    case Tree.NCons{x, y}:
                      inert.strict.gen(k, rest, name, path, outer, hot,
                        inert.strict.past(rest, name, path, outer, z => Bool.or(outer, z), inert.strict.walk(rest,
                          name, path, outer,
                          Bool.or(outer,
                            Strict.seg_op(Laws.inert.node(rest))), en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l,
                              c}), Laws.inert.ok(rest), e))),
                        inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path, outer,
                          Strict.seg_op(Laws.inert.node(rest)), en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                            Laws.inert.ok(rest), e))),
                        inert.strict.walk(rest, name, path, outer, hot, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t,
                          l, c}), Laws.inert.ok(rest), e)))
                case Tree.Leaf{x}:
                  inert.strict.gen(k, rest, name, path, outer, hot,
                    inert.strict.past(rest, name, path, outer, z => Bool.or(outer, z), inert.strict.walk(rest, name,
                      path, outer,
                      Bool.or(outer, Strict.seg_op(Laws.inert.node(rest))), en, inert.and_r(Laws.inert.fits(Lex.Tok{k,
                        t, l, c}), Laws.inert.ok(rest), e))),
                    inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path, outer,
                      Strict.seg_op(Laws.inert.node(rest)), en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                        Laws.inert.ok(rest), e))),
                    inert.strict.walk(rest, name, path, outer, hot, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l,
                      c}), Laws.inert.ok(rest), e)))
                case Tree.Group{x, y, z}:
                  inert.strict.gen(k, rest, name, path, outer, hot,
                    inert.strict.past(rest, name, path, outer, z => Bool.or(outer, z), inert.strict.walk(rest, name,
                      path, outer,
                      Bool.or(outer, Strict.seg_op(Laws.inert.node(rest))), en, inert.and_r(Laws.inert.fits(Lex.Tok{k,
                        t, l, c}), Laws.inert.ok(rest), e))),
                    inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path, outer,
                      Strict.seg_op(Laws.inert.node(rest)), en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                        Laws.inert.ok(rest), e))),
                    inert.strict.walk(rest, name, path, outer, hot, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l,
                      c}), Laws.inert.ok(rest), e)))
                case Tree.Stmt{x, y, z}:
                  inert.strict.gen(k, rest, name, path, outer, hot,
                    inert.strict.past(rest, name, path, outer, z => Bool.or(outer, z), inert.strict.walk(rest, name,
                      path, outer,
                      Bool.or(outer, Strict.seg_op(Laws.inert.node(rest))), en, inert.and_r(Laws.inert.fits(Lex.Tok{k,
                        t, l, c}), Laws.inert.ok(rest), e))),
                    inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path, outer,
                      Strict.seg_op(Laws.inert.node(rest)), en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                        Laws.inert.ok(rest), e))),
                    inert.strict.walk(rest, name, path, outer, hot, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l,
                      c}), Laws.inert.ok(rest), e)))
                case Tree.NNil{}:
                  inert.strict.gen(k, rest, name, path, outer, hot,
                    inert.strict.past(rest, name, path, outer, z => Bool.or(outer, z), inert.strict.walk(rest, name,
                      path, outer,
                      Bool.or(outer, Strict.seg_op(Laws.inert.node(rest))), en, inert.and_r(Laws.inert.fits(Lex.Tok{k,
                        t, l, c}), Laws.inert.ok(rest), e))),
                    inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path, outer,
                      Strict.seg_op(Laws.inert.node(rest)), en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l, c}),
                        Laws.inert.ok(rest), e))),
                    inert.strict.walk(rest, name, path, outer, hot, en, inert.and_r(Laws.inert.fits(Lex.Tok{k, t, l,
                      c}), Laws.inert.ok(rest), e)))
        case Tree.Group{o, +kids, cl}:
          inert.cat2(Strict.walk(Laws.inert.node(kids), name, path, hot, Bool.or(hot,
            Strict.seg_op(Laws.inert.node(kids)))),
            Strict.walk(kids, name, path, hot, Bool.or(hot, Strict.seg_op(kids))),
            Strict.walk(Laws.inert.node(rest), name, path, outer, hot), Strict.walk(rest, name, path, outer, hot),
            inert.strict.past(kids, name, path, hot, z => Bool.or(hot, z), inert.strict.walk(kids, name, path, hot,
              Bool.or(hot, Strict.seg_op(Laws.inert.node(kids))), en, inert.and_l(Laws.inert.ok(kids),
                Laws.inert.ok(rest), e))),
            inert.strict.walk(rest, name, path, outer, hot, en, inert.and_r(Laws.inert.ok(kids), Laws.inert.ok(rest),
              e)))
        case Tree.Stmt{sk, +kids, +body}:
          +es = inert.and_l(Bool.and(Laws.inert.ok(kids), Laws.inert.ok(body)), Laws.inert.ok(rest), e)
          inert.cat3(Strict.walk(Laws.inert.node(kids), name, path, False{}, Strict.seg_op(Laws.inert.node(kids))),
            Strict.walk(kids, name, path, False{}, Strict.seg_op(kids)),
            Strict.walk(Laws.inert.node(body), name, path, False{}, False{}), Strict.walk(body, name, path, False{},
              False{}),
            Strict.walk(Laws.inert.node(rest), name, path, outer, hot), Strict.walk(rest, name, path, outer, hot),
            inert.strict.past(kids, name, path, False{}, z => z, inert.strict.walk(kids, name, path, False{},
              Strict.seg_op(Laws.inert.node(kids)), en, inert.and_l(Laws.inert.ok(kids), Laws.inert.ok(body), es))),
            inert.strict.walk(body, name, path, False{}, False{}, en, inert.and_r(Laws.inert.ok(kids),
              Laws.inert.ok(body), es)),
            inert.strict.walk(rest, name, path, outer, hot, en,
              inert.and_r(Bool.and(Laws.inert.ok(kids), Laws.inert.ok(body)), Laws.inert.ok(rest), e)))
        case Tree.NNil{}: inert.strict.walk(rest, name, path, outer, hot, en, e)
        case Tree.NCons{x, y}:
          inert.strict.walk(rest, name, path, outer, hot, en, inert.and_r(Laws.inert.ok(Tree.NCons{x, y}),
            Laws.inert.ok(rest),
            e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# strict's stop for one def
def inert.strict.stop(+ex: Bool, walk: List<&2, F.Finding>) -> List<&2, F.Finding>:
  Lazy.stop(List<&2, F.Finding>, ex, [], _u => walk)

# strict over the defs read that way reports what it reports over the defs
law inert.strict.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  for +e: {inert.dok(ds) == True{} : Bool}
  {Strict.check.go(inert.defs(ds), path, acc) == Strict.check.go(ds, path, acc) : List<&2, F.Finding>}

def inert.strict.go(ds, path, acc, e):
  match ds:
    case Nil{}: {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +lst = inert.strict.stop(Calls.exempt(path, Laws.inert.node(sig)), Strict.walk(Laws.inert.node(body), name, path,
        False{}, False{}))
      %inert.exempt(path, sig) : {Strict.check.go(inert.defs(rest), path, lst <> acc) == Strict.check.go(rest, path,
        inert.strict.stop(_, Strict.walk(body, name, path, False{}, False{})) <> acc) : List<&2, F.Finding>}
      %inert.strict.walk(body, name, path, False{}, False{}, inert.dok.head(name, sig, body, rest, e),
        inert.dok.body(name, sig, body, rest, e)) : {Strict.check.go(inert.defs(rest), path, lst <> acc)
          == Strict.check.go(rest, path, inert.strict.stop(Calls.exempt(path, Laws.inert.node(sig)), _) <> acc)
          : List<&2, F.Finding>}
      inert.strict.go(rest, path, lst <> acc, inert.dok.rest(name, sig, body, rest, e))

def Laws.inert_strict(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, ok, ok2, e):
  inert.via(Tree.Node, z => Strict.check.go(Calls.defs(z), path, []), tree, tree2, Laws.inert.node(tree),
    Laws.inert.node(tree2),
    inert.lift(z => Strict.check.go(z, path, []), tree, inert.strict.go(Calls.defs(tree), path, [], inert.dok.of(tree,
      ok))),
    inert.lift(z => Strict.check.go(z, path, []), tree2, inert.strict.go(Calls.defs(tree2), path, [],
      inert.dok.of(tree2, ok2))), e)
