# proofs of laws/ParamReportsShortNames.bend
import Base
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/rules/style/param.bend as Param
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/rules/correctness/pick.bend as Pick
import ../laws/ParamReportsShortNames.bend as Laws
import ./lemmas/Nat.bend as M1
import ./lemmas/Pick.bend as M2
import ./lemmas/HoleEarlyAnd.bend as M3
import ../src/lazy/lazy.bend as Lazy

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

# the rule's hit, as a plain and, is the law's too_short
law param.hit.and:
  for kk: Bind.BindKind
  for +nm: String
  for +note: String
  {Bool.and(Param.check.is_param(kk),
      Bool.and(Param.check.short(nm), Bool.not(Param.check.allowed(nm, note)))) == Laws.too_short(kk, nm, note) : Bool}

def param.hit.and(kk, nm, note):
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

# the rule's hit, which reads a note only for a short parameter, is the
# law's too_short
law param.hit:
  for +kk: Bind.BindKind
  for +nm: String
  for +note: String
  {Lazy.and_then(Param.check.is_param(kk),
      _u => Lazy.and_then(Param.check.short(nm), _v => Bool.not(Param.check.allowed(nm, note))))
    == Laws.too_short(kk, nm, note) : Bool}

def param.hit(kk, nm, note):
  Equal.trans(Bool,
    Lazy.and_then(Param.check.is_param(kk),
      _u => Lazy.and_then(Param.check.short(nm), _v => Bool.not(Param.check.allowed(nm, note)))),
    Bool.and(Param.check.is_param(kk),
      Bool.and(Param.check.short(nm), Bool.not(Param.check.allowed(nm, note)))),
    Laws.too_short(kk, nm, note),
    M3.hole.and(Param.check.is_param(kk),
      Lazy.and_then(Param.check.short(nm), _v => Bool.not(Param.check.allowed(nm, note))),
      Bool.and(Param.check.short(nm), Bool.not(Param.check.allowed(nm, note))),
      M3.hole.and(Param.check.short(nm), Bool.not(Param.check.allowed(nm, note)),
        Bool.not(Param.check.allowed(nm, note)), {==})),
    param.hit.and(kk, nm, note))

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
    Bool.pick(Nat, Lazy.and_then(Param.check.is_param(kk),
      _u => Lazy.and_then(Param.check.short(nm), _v => Bool.not(Param.check.allowed(nm, note)))),
      1n+Laws.short_count(rest), Laws.short_count(rest)),
    Bool.pick(Nat, Laws.too_short(kk, nm, note), 1n+Laws.short_count(rest), Laws.short_count(rest)),
    M1.nat.pick(Lazy.and_then(Param.check.is_param(kk),
      _u => Lazy.and_then(Param.check.short(nm), _v => Bool.not(Param.check.allowed(nm, note)))),
      F.Finding{path, line, col, U32.from_nat(String.length(nm)), "param",
        "Parameter " ++ nm ++ " is too short; use at least 2 characters."},
      Param.check.go(rest, path), Laws.short_count(rest), ih),
    Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, 1n+Laws.short_count(rest), Laws.short_count(rest)),
      Lazy.and_then(Param.check.is_param(kk),
      _u => Lazy.and_then(Param.check.short(nm), _v => Bool.not(Param.check.allowed(nm, note)))),
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

def Laws.param_counts(binds, path):
  M2.param.stop(Paths.is_proof(path), Param.check.go(binds, path), Laws.short_count(binds), param.go(binds, path))
