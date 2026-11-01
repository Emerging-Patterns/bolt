# proofs of laws/CodeRulesIgnoreCommentsAndStrings.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/rules/style/param.bend as Param
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/correctness/put.bend as Put
import ../src/rules/correctness/hole.bend as Hole
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/calls.bend as Calls
import ../src/rules/style/doc.bend as Doc
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/pedantic/tail.bend as Tail
import ../src/rules/suspicious/concat.bend as Concat
import ../src/rules/suspicious/eager.bend as Eager
import ../src/rules/suspicious/strict.bend as Strict
import ../src/rules/suspicious/hoist.bend as Hoist
import ../src/rules/suspicious/index.bend as Index
import ../src/rules/suspicious/ring.bend as Ring
import ../src/rules/suspicious/table.bend as Table
import ../src/rules/suspicious/unit.bend as UnitRule
import ../src/rules/suspicious/scan.bend as Scan
import ../src/rules/correctness/arms.bend as Arms
import ../src/rules/suspicious/unused.bend as Unused
import ../src/rules/suspicious/fuel.bend as FuelRule
import ../src/rules/style/wrap.bend as Wrap
import ../src/rules/suspicious/thunk.bend as Thunk
import ../laws/CodeRulesIgnoreCommentsAndStrings.bend as Laws
import ../laws/defs/InertText.bend as D1
import ./lemmas/InertTextFacts.bend as M1
import ./lemmas/UnusedBinderPick.bend as M2
import ./lemmas/CarriedSearch.bend as CS

# a Bool whose negation holds is False
law inert.not_true:
  for b: Bool
  for e: {Bool.not(b) == True{} : Bool}
  {b == False{} : Bool}

def inert.not_true(b, e):
  match b:
    case False{}: {==}
    case True{}: Empty.absurd({True{} == False{} : Bool}, M1.inert.false_true(e))

# a test guarded by a kind that is never cut reads a token's text as it was
law inert.guard:
  for c: Bool
  for +b: Bool
  for +t: String
  for -p: String -> Bool
  for e: {Bool.and(c, b) == False{} : Bool}
  {Bool.and(c, p(D1.inert.keep(b, t))) == Bool.and(c, p(t)) : Bool}

def inert.guard(c, b, t, p, e):
  match c:
    case False{}: {==}
    case True{}:
      %Equal.sym(Bool, b, False{}, e) : {p(D1.inert.keep(_, t)) == p(t) : Bool}
      {==}

# hole
# ----

# a capitalized name is never cut: one split, for the one kind test on text
law inert.hole.upper:
  for k: Lex.TokKind
  {Bool.and(Calls.kind.upper(k), D1.inert.blanks(k)) == False{} : Bool}

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
  {Bool.and(Calls.kind.oper(k), D1.inert.blanks(k)) == False{} : Bool}

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
  {Hole.check.todo(D1.inert.toks(ts)) == Hole.check.todo(ts) : Bool}

def inert.hole.todo(ts):
  match ts:
    case Nil{}: {==}
    case Con{Lex.Tok{+k, +t, l, c}, +rest}:
      +b = D1.inert.blanks(k)
      %inert.guard(Calls.kind.upper(k), b, t, z => String.eq(z, "TODO"), inert.hole.upper(k)) :
        {Lazy.stop(Bool, Lex.significant(k), Bool.and(Calls.kind.upper(k), String.eq(D1.inert.keep(b, t), "TODO")),
          _u => Hole.check.todo(D1.inert.toks(rest)))
            == Lazy.stop(Bool, Lex.significant(k), _, _u => Hole.check.todo(rest))
          : Bool}
      %inert.hole.todo(rest) :
        {Lazy.stop(Bool, Lex.significant(k), Bool.and(Calls.kind.upper(k), String.eq(D1.inert.keep(b, t), "TODO")),
          _u => Hole.check.todo(D1.inert.toks(rest))) == Lazy.stop(Bool, Lex.significant(k),
          Bool.and(Calls.kind.upper(k), String.eq(D1.inert.keep(b, t), "TODO")), _u => _) : Bool}
      {==}

# the width reads kinds and positions only
law inert.hole.width:
  for ts: List<&2, Lex.Tok>
  for +line: U32
  for +col: U32
  {Hole.check.width(D1.inert.toks(ts), line, col) == Hole.check.width(ts, line, col) : U32}

def inert.hole.width(ts, line, col):
  match ts:
    case Nil{}: {==}
    case Con{Lex.Tok{+k, t, +l, +c}, +rest}:
      +w = Bool.pick(U32, U32.is_eq(l, line), U32.add(U32.sub(c, col), 4), 1)
      %inert.hole.width(rest, line, col) : {Lazy.stop(U32, Lex.significant(k), w,
        _u => Hole.check.width(D1.inert.toks(rest), line, col))
          == Lazy.stop(U32, Lex.significant(k), w, _u => _) : U32}
      {==}

# hole's walk reads no comment or string
law inert.hole.go:
  for ts: List<&2, Lex.Tok>
  for +path: String
  {Hole.check.go(D1.inert.toks(ts), path) == Hole.check.go(ts, path) : List<&2, F.Finding>}

def inert.hole.go(ts, path):
  match ts:
    case Nil{}: {==}
    case Con{Lex.Tok{+k, +q, +l, +c}, +rest}:
      +b = D1.inert.blanks(k)
      +cr = D1.inert.toks(rest)
      +hit = Bool.and(Calls.kind.oper(k), Lazy.and_then(String.eq(D1.inert.keep(b, q), "?"),
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
        Hole.check.width(cr, l, c), "hole", "This ?TODO hole is still unfilled."} <> Hole.check.go(cr,
            path)) : List<&2, F.Finding>}
      %inert.guard(Calls.kind.oper(k), b, q, z => Lazy.and_then(String.eq(z, "?"), _u => Hole.check.todo(cr)),
        inert.hole.op(k)) : {lhs == Lazy.stop(List<&2, F.Finding>, Bool.not(_), Hole.check.go(cr, path),
          _u => F.Finding{path, l, c, Hole.check.width(cr, l, c), "hole", "This ?TODO hole is still unfilled."}
          <> Hole.check.go(cr, path)) : List<&2, F.Finding>}
      {==}

def Laws.inert_hole(path, _text, toks, _tree, _bound, _items, _text2, toks2, _tree2, _bound2, _items2, e):
  M1.inert.via(List<&2, Lex.Tok>, z => Hole.check.on(z, path), toks, toks2, D1.inert.toks(toks), D1.inert.toks(toks2),
    Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>, z => Lazy.stop(List<&2, F.Finding>, Paths.is_laws(path), [],
      _u => z), Hole.check.go(D1.inert.toks(toks), path), Hole.check.go(toks, path), inert.hole.go(toks, path)),
    Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>, z => Lazy.stop(List<&2, F.Finding>, Paths.is_laws(path), [],
      _u => z), Hole.check.go(D1.inert.toks(toks2), path), Hole.check.go(toks2, path), inert.hole.go(toks2, path)), e)

# the token after `def` is `Map.put` as it was
law inert.put.named:
  for ts: List<&2, Lex.Tok>
  for +e: {D1.inert.oks(ts) == True{} : Bool}
  {Put.defines.named(D1.inert.toks(ts)) == Put.defines.named(ts) : Bool}

def inert.put.named(ts, e):
  match ts:
    case Nil{}: {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      M1.inert.eq_keep(D1.inert.blanks(k), t, "Map.put",
        M1.inert.and_l(D1.inert.fits(Lex.Tok{k, t, l, c}), D1.inert.oks(rest), e), {==})

# put's exemption test reads no comment or string: a keyword's text is
# compared with `def`, which no string equals
law inert.put.defines:
  for ts: List<&2, Lex.Tok>
  for +e: {D1.inert.oks(ts) == True{} : Bool}
  {Put.defines(D1.inert.toks(ts)) == Put.defines(ts) : Bool}

def inert.put.defines(ts, e):
  match ts:
    case Nil{}: {==}
    case Con{Lex.Tok{+k, +d, +l, +c}, +rest}:
      +er = M1.inert.and_r(D1.inert.fits(Lex.Tok{k, d, l, c}), D1.inert.oks(rest), e)
      +cr = D1.inert.toks(rest)
      +dd = D1.inert.keep(D1.inert.blanks(k), d)
      +lhs = Lazy.or_else(Bool.and(Put.defines.key(k), Bool.and(String.eq(dd, "def"), Put.defines.named(cr))),
        _u => Put.defines(cr))
      %M1.inert.eq_keep(D1.inert.blanks(k), d, "def", M1.inert.and_l(D1.inert.fits(Lex.Tok{k, d, l, c}),
        D1.inert.oks(rest), e), {==}) : {lhs == Lazy.or_else(Bool.and(Put.defines.key(k), Bool.and(_,
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
  for +e1: {D1.inert.fits.go(b1, t) == True{} : Bool}
  for +e2: {D1.inert.fits.go(b2, o) == True{} : Bool}
  {Put.calls.one(D1.inert.keep(b1, t), D1.inert.keep(b2, o), l, c, path, more)
    == Put.calls.one(t, o, l, c, path, more)
    : List<&2, F.Finding>}

def inert.put.call(b1, t, b2, o, l, c, path, more, e1, e2):
  +x = {F.Finding{path, l, c, 7, "put",
      "Map.put does not compare keys, so a new key can overwrite an existing entry; use Map.set."}
    : F.Finding}
  +lhs = Put.calls.one(D1.inert.keep(b1, t), D1.inert.keep(b2, o), l, c, path, more)
  %M1.inert.eq_keep(b1, t, "Map.put", e1, {==}) : {lhs == Bool.pick(List<&2, F.Finding>, Bool.and(_, String.eq(o, "(")),
    x <> more, more) : List<&2, F.Finding>}
  %M1.inert.eq_keep(b2, o, "(", e2, {==}) : {lhs == Bool.pick(List<&2, F.Finding>,
    Bool.and(String.eq(D1.inert.keep(b1, t), "Map.put"), _), x <> more, more) : List<&2, F.Finding>}
  {==}

# put's walk reads no comment or string: it tests kinds, then compares texts
# with `Map.put` and `(`
law inert.put.calls:
  for ts: List<&2, Lex.Tok>
  for +path: String
  for +e: {D1.inert.oks(ts) == True{} : Bool}
  {Put.calls(D1.inert.toks(ts), path) == Put.calls(ts, path) : List<&2, F.Finding>}

def inert.put.calls(ts, path, e):
  match ts:
    case Nil{}: {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      match rest:
        case Nil{}: {==}
        case Con{Lex.Tok{+k2, +o, +l2, +c2}, +r2}:
          +h1 = {Lex.Tok{k, t, l, c} : Lex.Tok}
          +h2 = {Lex.Tok{k2, o, l2, c2} : Lex.Tok}
          +er = M1.inert.and_r(D1.inert.fits(h1), D1.inert.oks(rest), e)
          +e2 = M1.inert.and_r(D1.inert.fits(h2), D1.inert.oks(r2), er)
          +cr = D1.inert.toks(rest)
          +cond = Bool.and(Put.calls.dotted(k), Lex.is_open(k2))
          +tt = D1.inert.keep(D1.inert.blanks(k), t)
          +oo = D1.inert.keep(D1.inert.blanks(k2), o)
          +lhs = Lazy.either(List<&2, F.Finding>, cond, _u => Put.calls.one(tt, oo, l, c, path,
            Put.calls(D1.inert.toks(r2), path)), _v => Put.calls(cr, path))
          %inert.put.calls(rest, path, er) : {lhs == Lazy.either(List<&2, F.Finding>, cond,
            _u => Put.calls.one(t, o, l, c, path, Put.calls(r2, path)), _v => _) : List<&2, F.Finding>}
          %inert.put.calls(r2, path, e2) : {lhs == Lazy.either(List<&2, F.Finding>, cond,
            _u => Put.calls.one(t, o, l, c, path, _), _v => Put.calls(cr, path)) : List<&2, F.Finding>}
          %inert.put.call(D1.inert.blanks(k), t, D1.inert.blanks(k2), o, l, c, path,
            Put.calls(D1.inert.toks(r2), path), M1.inert.and_l(D1.inert.fits(h1), D1.inert.oks(rest), e),
            M1.inert.and_l(D1.inert.fits(h2), D1.inert.oks(r2), er)) : {lhs == Lazy.either(List<&2, F.Finding>, cond,
              _u => _, _v => Put.calls(cr, path)) : List<&2, F.Finding>}
          {==}

# put's check reads no comment or string
law inert.put.on:
  for +ts: List<&2, Lex.Tok>
  for +path: String
  for +e: {D1.inert.oks(ts) == True{} : Bool}
  {Put.check.on(T.sig(D1.inert.toks(ts)), path) == Put.check.on(T.sig(ts), path) : List<&2, F.Finding>}

def inert.put.on(ts, path, e):
  +s = T.sig(ts)
  +es = M1.inert.put.sig_ok(ts, e)
  +cs = D1.inert.toks(s)
  %Equal.sym(List<&2, Lex.Tok>, T.sig(D1.inert.toks(ts)), cs, M1.inert.put.sig(ts)) :
    {Put.check.on(_, path) == Put.check.on(s, path) : List<&2, F.Finding>}
  %inert.put.defines(s, es) : {Lazy.stop(List<&2, F.Finding>, Put.defines(cs), [], _u => Put.calls(cs, path))
    == Lazy.stop(List<&2, F.Finding>, _, [], _u => Put.calls(s, path)) : List<&2, F.Finding>}
  %inert.put.calls(s, path, es) : {Lazy.stop(List<&2, F.Finding>, Put.defines(cs), [], _u => Put.calls(cs, path))
    == Lazy.stop(List<&2, F.Finding>, Put.defines(cs), [], _u => _) : List<&2, F.Finding>}
  {==}

def Laws.inert_put(path, _text, toks, _tree, _bound, _items, _text2, toks2, _tree2, _bound2, _items2, ok, ok2, e):
  M1.inert.via(List<&2, Lex.Tok>, z => Put.check.on(T.sig(z), path), toks, toks2, D1.inert.toks(toks),
    D1.inert.toks(toks2), inert.put.on(toks, path, ok), inert.put.on(toks2, path, ok2), e)

# the tree rules: what calls.bend gives them
# ------------------------------------------

# a name no string or comment can equal: it does not start with `"` or `#`
def inert.plain(mm: Maybe<&2, String>) -> Bool:
  match mm:
    case None{}: True{}
    case Some{name}: Bool.not(D1.inert.marked(name))

# the defs, their signatures and bodies each read that way
def inert.defs(ds: List<&2, Calls.Def>) -> List<&2, Calls.Def>:
  match ds:
    case Nil{}: Nil{}
    case Con{Calls.Def{name, sig, body}, rest}: Calls.Def{name, D1.inert.node(sig),
      D1.inert.node(body)} <> inert.defs(rest)

# every def as the lexer makes it: a plain name, and leaves that fit
def inert.dok(ds: List<&2, Calls.Def>) -> Bool:
  match ds:
    case Nil{}: True{}
    case Con{Calls.Def{name, sig, body}, rest}:
      Bool.and(Bool.and(Bool.not(D1.inert.marked(name)), Bool.and(D1.inert.ok(sig), D1.inert.ok(body))),
        inert.dok(rest))

# the chains, each read that way
def inert.nodes(ns: List<&2, Tree.Node>) -> List<&2, Tree.Node>:
  match ns:
    case Nil{}: Nil{}
    case Con{h, t}: D1.inert.node(h) <> inert.nodes(t)

# every chain's leaves fit
def inert.noks(ns: List<&2, Tree.Node>) -> Bool:
  match ns:
    case Nil{}: True{}
    case Con{h, t}: Bool.and(D1.inert.ok(h), inert.noks(t))

# a name that can be declared is never cut
law inert.name_code:
  for k: Lex.TokKind
  {Bool.and(Bind.declared.is_name(k), D1.inert.blanks(k)) == False{} : Bool}

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
  {Bool.pick(Maybe<&2, String>, c, Some{D1.inert.keep(b, t)}, None{})
    == Bool.pick(Maybe<&2, String>, c, Some{t}, None{}) : Maybe<&2, String>}

def inert.name_pick(c, b, t, e):
  match c:
    case False{}: {==}
    case True{}:
      %Equal.sym(Bool, b, False{}, e) : {Bool.pick(Maybe<&2, String>, True{}, Some{D1.inert.keep(_, t)}, None{})
        == Bool.pick(Maybe<&2, String>, True{}, Some{t}, None{}) : Maybe<&2, String>}
      {==}

# the name right after a statement's keyword, as it was
law inert.declared.go:
  for kids: Tree.Node
  {Bind.declared.go(D1.inert.node(kids)) == Bind.declared.go(kids) : Maybe<&2, String>}

def inert.declared.go(kids):
  match kids:
    case Tree.NCons{h, _rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, t, _l, _c}:
              inert.name_pick(Bind.declared.is_name(k), D1.inert.blanks(k), t, inert.name_code(k))
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
  {Calls.leaf.kind(D1.inert.node(nn)) == Calls.leaf.kind(nn) : Maybe<&2, Lex.TokKind>}

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
  {Bind.declared.key(D1.inert.node(nn)) == Bind.declared.key(nn) : Bool}

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
  {Bind.declared(D1.inert.node(kids)) == Bind.declared(kids) : Maybe<&2, String>}

def inert.declared(kids):
  match kids:
    case Tree.NCons{+h, +rest}:
      inert.either(Maybe<&2, String>, Bind.declared.key(D1.inert.node(h)), Bind.declared.key(h),
        Bind.declared.go(D1.inert.node(rest)), Bind.declared.go(rest), Bind.declared(D1.inert.node(rest)),
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
  for e2: {D1.inert.fits.go(b, t) == True{} : Bool}
  {inert.plain(Bool.pick(Maybe<&2, String>, c, Some{t}, None{})) == True{} : Bool}

def inert.plain_pick(c, b, t, e1, e2):
  match c:
    case False{}: {==}
    case True{}:
      Equal.trans(Bool, D1.inert.fits.go(False{}, t), D1.inert.fits.go(b, t), True{},
        Equal.cong(Bool, Bool, z => D1.inert.fits.go(z, t), False{}, b, Equal.sym(Bool, b, False{}, e1)), e2)

# the name right after the keyword is a name: plain, when its leaf fits
law inert.plain.go:
  for kids: Tree.Node
  for +e: {D1.inert.ok(kids) == True{} : Bool}
  {inert.plain(Bind.declared.go(kids)) == True{} : Bool}

def inert.plain.go(kids, e):
  match kids:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              inert.plain_pick(Bind.declared.is_name(k), D1.inert.blanks(k), t, inert.name_code(k),
                M1.inert.and_l(D1.inert.fits(Lex.Tok{k, t, l, c}), D1.inert.ok(rest), e))
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
  for +e: {D1.inert.ok(kids) == True{} : Bool}
  {inert.plain(Bind.declared(kids)) == True{} : Bool}

def inert.plain.declared(kids, e):
  match kids:
    case Tree.NCons{+h, +rest}:
      +er = M1.inert.and_r(D1.inert.ok(h), D1.inert.ok(rest), e)
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
  {Calls.defs.push(mm, D1.inert.node(sig), D1.inert.node(body), inert.defs(acc))
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
  for +es: {Bool.and(D1.inert.ok(sig), D1.inert.ok(body)) == True{} : Bool}
  for +ea: {inert.dok(acc) == True{} : Bool}
  {inert.dok(Calls.defs.push(mm, sig, body, acc)) == True{} : Bool}

def inert.dok.push(mm, sig, body, acc, en, es, ea):
  match mm:
    case None{}: ea
    case Some{+name}:
      M1.inert.and_both(Bool.and(Bool.not(D1.inert.marked(name)), Bool.and(D1.inert.ok(sig), D1.inert.ok(body))),
        inert.dok(acc), M1.inert.and_both(Bool.not(D1.inert.marked(name)), Bool.and(D1.inert.ok(sig),
          D1.inert.ok(body)),
          en, es), ea)

# the defs of a tree read that way are its defs, each read that way; and
# they are as the lexer makes them, when its leaves fit
law inert.defs.of:
  for root: Tree.Node
  {Calls.defs(D1.inert.node(root)) == inert.defs(Calls.defs(root)) : List<&2, Calls.Def>}

def inert.defs.of(root):
  match root:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{sk, +kids, +body}:
          match sk:
            case Tree.SDef{}:
              %Equal.sym(Maybe<&2, String>, Bind.declared(D1.inert.node(kids)), Bind.declared(kids),
                inert.declared(kids)) :
                {Calls.defs.push(_, D1.inert.node(kids), D1.inert.node(body), Calls.defs(D1.inert.node(rest)))
                  == inert.defs(Calls.defs.push(Bind.declared(kids), kids, body,
                    Calls.defs(rest))) : List<&2, Calls.Def>}
              %Equal.sym(List<&2, Calls.Def>, Calls.defs(D1.inert.node(rest)), inert.defs(Calls.defs(rest)),
                inert.defs.of(rest)) : {Calls.defs.push(Bind.declared(kids), D1.inert.node(kids),
                  D1.inert.node(body), _)
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
  for +es: {Bool.and(D1.inert.ok(kids), D1.inert.ok(body)) == True{} : Bool}
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
  for +e: {D1.inert.ok(root) == True{} : Bool}
  {inert.dok(Calls.defs(root)) == True{} : Bool}

def inert.dok.of(root, e):
  match root:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{sk, +kids, +body}:
          +es = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
          +er = inert.dok.of(rest, M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)),
            D1.inert.ok(rest), e))
          inert.dok.stmt(sk, kids, body, rest, inert.plain.declared(kids, M1.inert.and_l(D1.inert.ok(kids),
            D1.inert.ok(body),
            es)), es, er)
        case Tree.Leaf{tok}: inert.dok.of(rest, M1.inert.and_r(D1.inert.fits(tok), D1.inert.ok(rest), e))
        case Tree.Group{o, gk, cl}: inert.dok.of(rest, M1.inert.and_r(D1.inert.ok(gk), D1.inert.ok(rest), e))
        case Tree.NNil{}: inert.dok.of(rest, e)
        case Tree.NCons{x, y}: inert.dok.of(rest, M1.inert.and_r(D1.inert.ok(Tree.NCons{x, y}), D1.inert.ok(rest), e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a chain reversed onto another, both read that way, is the reversal read
# that way
law inert.reverse:
  for cells: Tree.Node
  for acc: Tree.Node
  {Tree.reverse(D1.inert.node(cells), D1.inert.node(acc)) == D1.inert.node(Tree.reverse(cells, acc)) : Tree.Node}

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
  {List.reverse(&2, Tree.Node, Tree.reverse(D1.inert.node(cur), Tree.NNil{}) <> inert.nodes(acc))
    == inert.nodes(List.reverse(&2, Tree.Node, Tree.reverse(cur, Tree.NNil{}) <> acc)) : List<&2, Tree.Node>}

def inert.args.end(cur, acc):
  %Equal.sym(Tree.Node, Tree.reverse(D1.inert.node(cur), Tree.NNil{}), D1.inert.node(Tree.reverse(cur,
    Tree.NNil{})),
    inert.reverse(cur, Tree.NNil{})) : {List.reverse(&2, Tree.Node, _ <> inert.nodes(acc))
      == inert.nodes(List.reverse(&2, Tree.Node, Tree.reverse(cur, Tree.NNil{}) <> acc)) : List<&2, Tree.Node>}
  inert.nodes.rev(Tree.reverse(cur, Tree.NNil{}) <> acc, [])

# a comma closes an argument, read that way
law inert.args.comma:
  for +rest: Tree.Node
  for +cur: Tree.Node
  for +acc: List<&2, Tree.Node>
  for ih: {Calls.args.go(D1.inert.node(rest), Tree.NNil{}, inert.nodes(Tree.reverse(cur, Tree.NNil{}) <> acc))
    == inert.nodes(Calls.args.go(rest, Tree.NNil{}, Tree.reverse(cur, Tree.NNil{}) <> acc)) : List<&2, Tree.Node>}
  {Calls.args.go(D1.inert.node(rest), Tree.NNil{}, Tree.reverse(D1.inert.node(cur),
    Tree.NNil{}) <> inert.nodes(acc))
    == inert.nodes(Calls.args.go(rest, Tree.NNil{}, Tree.reverse(cur, Tree.NNil{}) <> acc)) : List<&2, Tree.Node>}

def inert.args.comma(rest, cur, acc, ih):
  %Equal.sym(Tree.Node, Tree.reverse(D1.inert.node(cur), Tree.NNil{}), D1.inert.node(Tree.reverse(cur,
    Tree.NNil{})),
    inert.reverse(cur, Tree.NNil{})) : {Calls.args.go(D1.inert.node(rest), Tree.NNil{}, _ <> inert.nodes(acc))
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
  {Calls.kind.leaf(~Lex.is_comma, D1.inert.node(nn)) == Calls.kind.leaf(~Lex.is_comma, nn) : Bool}

def inert.comma(nn):
  Equal.cong(Maybe<&2, Lex.TokKind>, Bool,
    m => Calls.kind.of(~Lex.is_comma, m), Calls.leaf.kind(D1.inert.node(nn)), Calls.leaf.kind(nn),
    inert.leaf_kind(nn))

# the arguments of a group read that way are its arguments, each read that way
law inert.args.go:
  for kids: Tree.Node
  for +cur: Tree.Node
  for +acc: List<&2, Tree.Node>
  {Calls.args.go(D1.inert.node(kids), D1.inert.node(cur), inert.nodes(acc))
    == inert.nodes(Calls.args.go(kids, cur, acc)) : List<&2, Tree.Node>}

def inert.args.go(kids, cur, acc):
  match kids:
    case Tree.NCons{+h, +rest}:
      +rc = {Tree.reverse(cur, Tree.NNil{}) <> acc : List<&2, Tree.Node>}
      inert.either_map(List<&2, Tree.Node>, List<&2, Tree.Node>, Calls.kind.leaf(~Lex.is_comma, D1.inert.node(h)),
        Calls.kind.leaf(~Lex.is_comma, h), z => inert.nodes(z),
        Calls.args.go(D1.inert.node(rest), Tree.NNil{},
          Tree.reverse(D1.inert.node(cur), Tree.NNil{}) <> inert.nodes(acc)),
        Calls.args.go(rest, Tree.NNil{}, rc),
        Calls.args.go(D1.inert.node(rest), Tree.NCons{D1.inert.node(h), D1.inert.node(cur)}, inert.nodes(acc)),
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
  {Calls.args(D1.inert.node(kids)) == inert.nodes(Calls.args(kids)) : List<&2, Tree.Node>}

def inert.args(kids):
  inert.args.go(kids, Tree.NNil{}, [])

# the nth argument of arguments read that way is the nth read that way
law inert.arg:
  for as: List<&2, Tree.Node>
  for nn: Nat
  {Calls.arg(inert.nodes(as), nn) == D1.inert.node(Calls.arg(as, nn)) : Tree.Node}

def inert.arg(as, nn):
  match as nn:
    case Con{h, t} 0n: {==}
    case Con{h, t} 1n+p: inert.arg(t, p)
    case Nil{} m: {==}

# a chain reversed onto another keeps its leaves fitting
law inert.ok.reverse:
  for cells: Tree.Node
  for +acc: Tree.Node
  for +ec: {D1.inert.ok(cells) == True{} : Bool}
  for +ea: {D1.inert.ok(acc) == True{} : Bool}
  {D1.inert.ok(Tree.reverse(cells, acc)) == True{} : Bool}

def inert.ok.reverse(cells, acc, ec, ea):
  match cells:
    case Tree.NCons{+h, +t}:
      inert.ok.reverse(t, Tree.NCons{h, acc}, M1.inert.and_r(D1.inert.ok(h), D1.inert.ok(t), ec),
        M1.inert.and_both(D1.inert.ok(h), D1.inert.ok(acc), M1.inert.and_l(D1.inert.ok(h), D1.inert.ok(t), ec), ea))
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
      inert.noks.rev(t, h <> acc, M1.inert.and_r(D1.inert.ok(h), inert.noks(t), ex),
        M1.inert.and_both(D1.inert.ok(h), inert.noks(acc), M1.inert.and_l(D1.inert.ok(h), inert.noks(t), ex), ea))

# an argument closed onto arguments that fit keeps them fitting
law inert.ok.close:
  for +cur: Tree.Node
  for +acc: List<&2, Tree.Node>
  for +ec: {D1.inert.ok(cur) == True{} : Bool}
  for +ea: {inert.noks(acc) == True{} : Bool}
  {inert.noks(Tree.reverse(cur, Tree.NNil{}) <> acc) == True{} : Bool}

def inert.ok.close(cur, acc, ec, ea):
  M1.inert.and_both(D1.inert.ok(Tree.reverse(cur, Tree.NNil{})), inert.noks(acc), inert.ok.reverse(cur, Tree.NNil{}, ec,
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
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  for +ec: {D1.inert.ok(cur) == True{} : Bool}
  for +ea: {inert.noks(acc) == True{} : Bool}
  {inert.noks(Calls.args.go(kids, cur, acc)) == True{} : Bool}

def inert.ok.args.go(kids, cur, acc, ek, ec, ea):
  match kids:
    case Tree.NCons{+h, +rest}:
      +er = M1.inert.and_r(D1.inert.ok(h), D1.inert.ok(rest), ek)
      inert.ok.args.step(h, rest, cur, acc,
        inert.ok.args.go(rest, Tree.NNil{}, Tree.reverse(cur, Tree.NNil{}) <> acc, er, {==}, inert.ok.close(cur, acc,
          ec, ea)),
        inert.ok.args.go(rest, Tree.NCons{h, cur}, acc, er,
          M1.inert.and_both(D1.inert.ok(h), D1.inert.ok(cur), M1.inert.and_l(D1.inert.ok(h), D1.inert.ok(rest), ek),
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
  {D1.inert.ok(Calls.arg(as, nn)) == True{} : Bool}

def inert.ok.nth(as, nn, ea):
  match as nn:
    case Con{+h, +t} 0n: M1.inert.and_l(D1.inert.ok(h), inert.noks(t), ea)
    case Con{+h, +t} 1n+p: inert.ok.nth(t, p, M1.inert.and_r(D1.inert.ok(h), inert.noks(t), ea))
    case Nil{} m: {==}

# the nth argument of a group whose leaves fit fits
law inert.ok.arg:
  for +kids: Tree.Node
  for nn: Nat
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  {D1.inert.ok(Calls.arg(Calls.args(kids), nn)) == True{} : Bool}

def inert.ok.arg(kids, nn, ek):
  inert.ok.nth(Calls.args(kids), nn, inert.ok.args.go(kids, Tree.NNil{}, [], ek, {==}, {==}))

# the kids of a group read that way open as they did
law inert.opens:
  for nn: Tree.Node
  for +ss: String
  {Tree.opens(D1.inert.node(nn), ss) == Tree.opens(nn, ss) : Bool}

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
  for +ef: {D1.inert.fits.go(D1.inert.blanks(kk), t) == True{} : Bool}
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for ik: {Calls.calls(D1.inert.node(kids), name) == Calls.calls(kids, name) : Bool}
  for ir: {Calls.calls(D1.inert.node(r2), name) == Calls.calls(r2, name) : Bool}
  {inert.calls.at(String.eq(D1.inert.keep(D1.inert.blanks(kk), t), name), ot, Calls.calls(D1.inert.node(kids),
    name),
      Calls.calls(D1.inert.node(r2), name))
    == inert.calls.at(String.eq(t, name), ot, Calls.calls(kids, name), Calls.calls(r2, name)) : Bool}

def inert.calls.lg(kk, t, ot, name, kids, r2, ef, en, ik, ir):
  +lhs = inert.calls.at(String.eq(D1.inert.keep(D1.inert.blanks(kk), t), name), ot,
    Calls.calls(D1.inert.node(kids),
    name), Calls.calls(D1.inert.node(r2), name))
  %M1.inert.eq_keep(D1.inert.blanks(kk), t, name, ef, en) :
    {lhs == inert.calls.at(_, ot, Calls.calls(kids, name), Calls.calls(r2, name)) : Bool}
  %ik : {lhs == inert.calls.at(String.eq(D1.inert.keep(D1.inert.blanks(kk), t), name), ot, _, Calls.calls(r2, name))
    : Bool}
  %ir : {lhs == inert.calls.at(String.eq(D1.inert.keep(D1.inert.blanks(kk), t), name), ot,
    Calls.calls(D1.inert.node(kids), name), _) : Bool}
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

# the same for List.contains's step (List.any.if, bend 2.0.37)
law inert.if2:
  for -a1: Bool
  for -a2: Bool
  for -b1: Bool
  for -b2: Bool
  for ea: {a1 == a2 : Bool}
  for eb: {b1 == b2 : Bool}
  {List.any.if(_u => b1, a1) == List.any.if(_u => b2, a2) : Bool}

def inert.if2(a1, _a2, b1, b2, ea, eb):
  %ea : {List.any.if(_u => b1, a1) == List.any.if(_u => b2, _) : Bool}
  %eb : {List.any.if(_u => b1, a1) == List.any.if(_u => _, a1) : Bool}
  {==}

# a chain read that way calls the name as it did, for a plain name
law inert.calls:
  for nn: Tree.Node
  for +name: String
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Calls.calls(D1.inert.node(nn), name) == Calls.calls(nn, name) : Bool}

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
                          +eg = M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}), Bool.and(D1.inert.ok(kids),
                            D1.inert.ok(r2)), e)
                          inert.calls.lg(k, t, ot, name, kids, r2, M1.inert.and_l(D1.inert.fits(Lex.Tok{k, t, l, c}),
                            Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e), en,
                            inert.calls(kids, name, en, M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)),
                            inert.calls(r2, name, en, M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(r2), eg)))
                    case Tree.Leaf{x}: inert.calls(rest, name, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}),
                      D1.inert.ok(rest), e))
                    case Tree.Stmt{x, y, z}: inert.calls(rest, name, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l,
                      c}), D1.inert.ok(rest), e))
                    case Tree.NNil{}: inert.calls(rest, name, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}),
                      D1.inert.ok(rest), e))
                    case Tree.NCons{x, y}: inert.calls(rest, name, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l,
                      c}), D1.inert.ok(rest), e))
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: inert.calls(rest, name, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l,
                  c}), D1.inert.ok(rest), e))
                case Tree.Stmt{x, y, z}: inert.calls(rest, name, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}),
                  D1.inert.ok(rest), e))
                case Tree.NNil{}: {==}
        case Tree.Group{o, +gk, cl}:
          inert.or2(Calls.calls(D1.inert.node(gk), name), Calls.calls(gk, name), Calls.calls(D1.inert.node(rest),
            name),
            Calls.calls(rest, name), inert.calls(gk, name, en, M1.inert.and_l(D1.inert.ok(gk), D1.inert.ok(rest), e)),
            inert.calls(rest, name, en, M1.inert.and_r(D1.inert.ok(gk), D1.inert.ok(rest), e)))
        case Tree.Stmt{+sk, +sks, +sb}:
          +es = M1.inert.and_l(Bool.and(D1.inert.ok(sks), D1.inert.ok(sb)), D1.inert.ok(rest), e)
          inert.or2(Calls.calls(D1.inert.node(Tree.Stmt{sk, sks, sb}), name), Calls.calls(Tree.Stmt{sk, sks, sb},
            name),
            Calls.calls(D1.inert.node(rest), name), Calls.calls(rest, name),
            inert.or2(Calls.calls(D1.inert.node(sks), name), Calls.calls(sks, name),
              Calls.calls(D1.inert.node(sb), name),
              Calls.calls(sb, name), inert.calls(sks, name, en, M1.inert.and_l(D1.inert.ok(sks), D1.inert.ok(sb), es)),
              inert.calls(sb, name, en, M1.inert.and_r(D1.inert.ok(sks), D1.inert.ok(sb), es))),
            inert.calls(rest, name, en, M1.inert.and_r(Bool.and(D1.inert.ok(sks), D1.inert.ok(sb)),
              D1.inert.ok(rest), e)))
        case Tree.NNil{}: inert.calls(rest, name, en, e)
        case Tree.NCons{+x, +y}:
          inert.or2(Calls.calls(D1.inert.node(Tree.NCons{x, y}), name), Calls.calls(Tree.NCons{x, y}, name),
            Calls.calls(D1.inert.node(rest), name), Calls.calls(rest, name),
            inert.calls(Tree.NCons{x, y}, name, en, M1.inert.and_l(D1.inert.ok(Tree.NCons{x, y}), D1.inert.ok(rest),
              e)),
            inert.calls(rest, name, en, M1.inert.and_r(D1.inert.ok(Tree.NCons{x, y}), D1.inert.ok(rest), e)))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, +kids, cl}: inert.calls(kids, name, en, e)
    case Tree.Stmt{sk, +kids, +body}:
      inert.or2(Calls.calls(D1.inert.node(kids), name), Calls.calls(kids, name), Calls.calls(D1.inert.node(body),
        name),
        Calls.calls(body, name), inert.calls(kids, name, en, M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), e)),
        inert.calls(body, name, en, M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), e)))
    case Tree.NNil{}: {==}

# the nth argument of a group read that way calls the name as it did
law inert.calls.nth:
  for +kids: Tree.Node
  for +nn: Nat
  for +name: String
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  {Calls.calls(Calls.arg(Calls.args(D1.inert.node(kids)), nn), name) == Calls.calls(Calls.arg(Calls.args(kids), nn),
    name)
    : Bool}

def inert.calls.nth(kids, nn, name, en, ek):
  %Equal.sym(List<&2, Tree.Node>, Calls.args(D1.inert.node(kids)), inert.nodes(Calls.args(kids)), inert.args(kids)) :
    {Calls.calls(Calls.arg(_, nn), name) == Calls.calls(Calls.arg(Calls.args(kids), nn), name) : Bool}
  %Equal.sym(Tree.Node, Calls.arg(inert.nodes(Calls.args(kids)), nn), D1.inert.node(Calls.arg(Calls.args(kids), nn)),
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
  {Bool.pick(Tree.Node, b, D1.inert.node(x), D1.inert.node(y)) == D1.inert.node(Bool.pick(Tree.Node, b, x, y))
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
  {Calls.params.of(D1.inert.node(sig)) == D1.inert.node(Calls.params.of(sig)) : Tree.Node}

def inert.params.of(sig):
  match sig:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Group{o, +kids, +cl}:
          match o:
            case Lex.Tok{+k, +ot, +l, +c}:
              %Equal.sym(Tree.Node,
                Calls.params.of(Tree.NCons{Tree.Group{Lex.Tok{k, ot, l, c}, D1.inert.node(kids), cl},
                  D1.inert.node(rest)}),
                Bool.pick(Tree.Node, String.eq(ot, "("), D1.inert.node(kids),
                Calls.params.of(D1.inert.node(rest))), CS.cs.params.of(k, ot, l, c, D1.inert.node(kids), cl,
                D1.inert.node(rest))) : {_ == D1.inert.node(Calls.params.of(Tree.NCons{Tree.Group{Lex.Tok{k, ot, l, c},
                kids, cl}, rest})) : Tree.Node}
              %Equal.sym(Tree.Node, Calls.params.of(Tree.NCons{Tree.Group{Lex.Tok{k, ot, l, c}, kids, cl}, rest}),
                Bool.pick(Tree.Node, String.eq(ot, "("), kids, Calls.params.of(rest)), CS.cs.params.of(k, ot, l, c,
                kids, cl, rest)) : {Bool.pick(Tree.Node, String.eq(ot, "("), D1.inert.node(kids),
                Calls.params.of(D1.inert.node(rest))) == D1.inert.node(_) : Tree.Node}
              %Equal.sym(Tree.Node, Calls.params.of(D1.inert.node(rest)), D1.inert.node(Calls.params.of(rest)),
                inert.params.of(rest)) : {Bool.pick(Tree.Node, String.eq(ot, "("), D1.inert.node(kids), _)
                  == D1.inert.node(Bool.pick(Tree.Node, String.eq(ot, "("), kids, Calls.params.of(rest))) : Tree.Node}
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
  {Calls.kind.leaf(~Calls.kind.colon, D1.inert.node(nn)) == Calls.kind.leaf(~Calls.kind.colon, nn) : Bool}

def inert.colon(nn):
  Equal.cong(Maybe<&2, Lex.TokKind>, Bool,
    m => Calls.kind.of(~Calls.kind.colon, m), Calls.leaf.kind(D1.inert.node(nn)), Calls.leaf.kind(nn),
    inert.leaf_kind(nn))

# a node read that way is an arrow as it was
law inert.arrow:
  for nn: Tree.Node
  {Calls.kind.leaf(~Calls.kind.arrow, D1.inert.node(nn)) == Calls.kind.leaf(~Calls.kind.arrow, nn) : Bool}

def inert.arrow(nn):
  Equal.cong(Maybe<&2, Lex.TokKind>, Bool,
    m => Calls.kind.of(~Calls.kind.arrow, m), Calls.leaf.kind(D1.inert.node(nn)), Calls.leaf.kind(nn),
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
  {Calls.has_colon(D1.inert.node(pp)) == Calls.has_colon(pp) : Bool}

def inert.has_colon(pp):
  match pp:
    case Tree.NCons{+h, +rest}:
      inert.or_else(Calls.kind.leaf(~Calls.kind.colon, D1.inert.node(h)), Calls.kind.leaf(~Calls.kind.colon, h),
        Calls.has_colon(D1.inert.node(rest)), Calls.has_colon(rest), inert.colon(h), inert.has_colon(rest))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a leaf read that way says what it said, cut when a comment or a string
law inert.leaf_text:
  for nn: Tree.Node
  {Calls.leaf.text(D1.inert.node(nn))
    == D1.inert.keep(Calls.kind.leaf(~D1.inert.blanks, nn), Calls.leaf.text(nn)) : String}

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
  {Bool.and(Calls.kind.leaf(~Calls.kind.oper, nn), Calls.kind.leaf(~D1.inert.blanks, nn)) == False{} : Bool}

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
  {Bool.and(Calls.kind.leaf(~Calls.kind.upper, nn), Calls.kind.leaf(~D1.inert.blanks, nn)) == False{} : Bool}

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
  {Calls.kind.leaf(~Calls.kind.oper, D1.inert.node(nn)) == Calls.kind.leaf(~Calls.kind.oper, nn) : Bool}

def inert.oper(nn):
  Equal.cong(Maybe<&2, Lex.TokKind>, Bool,
    m => Calls.kind.of(~Calls.kind.oper, m), Calls.leaf.kind(D1.inert.node(nn)), Calls.leaf.kind(nn),
    inert.leaf_kind(nn))

# a node read that way is a capital name as it was
law inert.upper:
  for nn: Tree.Node
  {Calls.kind.leaf(~Calls.kind.upper, D1.inert.node(nn)) == Calls.kind.leaf(~Calls.kind.upper, nn) : Bool}

def inert.upper(nn):
  Equal.cong(Maybe<&2, Lex.TokKind>, Bool,
    m => Calls.kind.of(~Calls.kind.upper, m), Calls.leaf.kind(D1.inert.node(nn)), Calls.leaf.kind(nn),
    inert.leaf_kind(nn))

# a `-` or `~`
def inert.sign.of(+tt: String) -> Bool:
  Bool.or(String.eq(tt, "-"), String.eq(tt, "~"))

# a parameter read that way opens with a `-` or `~` as it did
law inert.sign:
  for pp: Tree.Node
  {Calls.is_live.sign(D1.inert.node(pp)) == Calls.is_live.sign(pp) : Bool}

def inert.sign(pp):
  match pp:
    case Tree.NCons{+h, +rest}:
      +ko = Calls.kind.leaf(~Calls.kind.oper, h)
      +kb = Calls.kind.leaf(~D1.inert.blanks, h)
      %Equal.sym(Bool, Calls.kind.leaf(~Calls.kind.oper, D1.inert.node(h)), ko, inert.oper(h)) :
        {Bool.and(_, inert.sign.of(Calls.leaf.text(D1.inert.node(h))))
          == Calls.is_live.sign(Tree.NCons{h, rest}) : Bool}
      %Equal.sym(String, Calls.leaf.text(D1.inert.node(h)), D1.inert.keep(kb, Calls.leaf.text(h)),
        inert.leaf_text(h)) : {Bool.and(ko, inert.sign.of(_)) == Calls.is_live.sign(Tree.NCons{h, rest}) : Bool}
      inert.guard(ko, kb, Calls.leaf.text(h), z => inert.sign.of(z), inert.oper_code(h))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a parameter read that way is live as it was
law inert.is_live:
  for +pp: Tree.Node
  {Calls.is_live(D1.inert.node(pp)) == Calls.is_live(pp) : Bool}

def inert.is_live(pp):
  +lhs = Calls.is_live(D1.inert.node(pp))
  %inert.sign(pp) : {lhs == Bool.and(Bool.not(_), Calls.has_colon(pp)) : Bool}
  %inert.has_colon(pp) : {lhs == Bool.and(Bool.not(Calls.is_live.sign(D1.inert.node(pp))), _) : Bool}
  {==}

# a pick guarded by a kind that is never cut reads the text as it was
law inert.pick_guard:
  for +after: Bool
  for c: Bool
  for +b: Bool
  for +t: String
  for +more: String
  for e: {Bool.and(c, b) == False{} : Bool}
  {Bool.pick(String, Bool.and(after, c), D1.inert.keep(b, t), more) == Bool.pick(String, Bool.and(after, c), t, more)
    : String}

def inert.pick_guard(after, c, b, t, more, e):
  match after:
    case False{}: {==}
    case True{}:
      match c:
        case False{}: {==}
        case True{}:
          %Equal.sym(Bool, b, False{}, e) : {Bool.pick(String, True{}, D1.inert.keep(_, t), more)
            == Bool.pick(String, True{}, t, more) : String}
          {==}

# a leaf read that way gives the head it gave
law inert.head_leaf:
  for +h: Tree.Node
  for +after: Bool
  for +more: String
  {Bool.pick(String, Bool.and(after, Calls.kind.leaf(~Calls.kind.upper, D1.inert.node(h))),
    Calls.leaf.text(D1.inert.node(h)), more)
    == Bool.pick(String, Bool.and(after, Calls.kind.leaf(~Calls.kind.upper, h)), Calls.leaf.text(h), more) : String}

def inert.head_leaf(h, after, more):
  +ku = Calls.kind.leaf(~Calls.kind.upper, h)
  +kb = Calls.kind.leaf(~D1.inert.blanks, h)
  %Equal.sym(Bool, Calls.kind.leaf(~Calls.kind.upper, D1.inert.node(h)), ku, inert.upper(h)) :
    {Bool.pick(String, Bool.and(after, _), Calls.leaf.text(D1.inert.node(h)), more)
      == Bool.pick(String, Bool.and(after, ku), Calls.leaf.text(h), more) : String}
  %Equal.sym(String, Calls.leaf.text(D1.inert.node(h)), D1.inert.keep(kb, Calls.leaf.text(h)),
    inert.leaf_text(h)) : {Bool.pick(String, Bool.and(after, ku), _, more)
      == Bool.pick(String, Bool.and(after, ku), Calls.leaf.text(h), more) : String}
  inert.pick_guard(after, ku, kb, Calls.leaf.text(h), more, inert.upper_code(h))

# a parameter's type head read that way is the head it had
law inert.type_head:
  for pp: Tree.Node
  for +after: Bool
  {Calls.type_head(D1.inert.node(pp), after) == Calls.type_head(pp, after) : String}

def inert.type_head(pp, after):
  match pp:
    case Tree.NCons{+h, +rest}:
      +lhs = Calls.type_head(D1.inert.node(Tree.NCons{h, rest}), after)
      +c1 = Calls.kind.leaf(~Calls.kind.colon, D1.inert.node(h))
      %Equal.sym(String, Calls.type_head(Tree.NCons{h, rest}, after), Bool.pick(String,
        Bool.and(after, Calls.kind.leaf(~Calls.kind.upper, h)), Calls.leaf.text(h), Calls.type_head(rest,
        Bool.or(after, Calls.kind.leaf(~Calls.kind.colon, h)))), CS.cs.type_head(h, rest, after)) : {lhs == _ : String}
      %inert.colon(h) : {lhs == Bool.pick(String, Bool.and(after, Calls.kind.leaf(~Calls.kind.upper, h)),
        Calls.leaf.text(h), Calls.type_head(rest, Bool.or(after, _))) : String}
      %inert.type_head(rest, Bool.or(after, c1)) : {lhs == Bool.pick(String,
        Bool.and(after, Calls.kind.leaf(~Calls.kind.upper, h)), Calls.leaf.text(h), _) : String}
      Equal.trans(String, lhs, Bool.pick(String, Bool.and(after, Calls.kind.leaf(~Calls.kind.upper, D1.inert.node(h))),
        Calls.leaf.text(D1.inert.node(h)), Calls.type_head(D1.inert.node(rest), Bool.or(after, c1))),
        Bool.pick(String, Bool.and(after, Calls.kind.leaf(~Calls.kind.upper, h)), Calls.leaf.text(h),
          Calls.type_head(D1.inert.node(rest), Bool.or(after, c1))),
        CS.cs.type_head(D1.inert.node(h), D1.inert.node(rest), after),
        inert.head_leaf(h, after, Calls.type_head(D1.inert.node(rest), Bool.or(after, c1))))
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
        Lazy.stop(Maybe<&2, String>, Bool.not(Calls.is_live(D1.inert.node(p))), None{}, _u => Some{_})) : String}
      inert.walked.go(rest, Lazy.stop(Maybe<&2, String>, Bool.not(Calls.is_live(D1.inert.node(p))), None{},
        _u => Some{Calls.type_head(D1.inert.node(p), False{})}))
    case Con{p, rest} Some{t}: {==}
    case Nil{} Some{t}: {==}
    case Nil{} None{}: {==}

# a signature read that way walks the type it walked
law inert.seq:
  for +sig: Tree.Node
  {Calls.seq(D1.inert.node(sig)) == Calls.seq(sig) : Bool}

def inert.seq(sig):
  +ps = Calls.params.of(sig)
  %Equal.sym(Tree.Node, Calls.params.of(D1.inert.node(sig)), D1.inert.node(ps), inert.params.of(sig)) :
    {inert.seq.of(Calls.walked.go(Calls.args(_), None{})) == Calls.seq(sig) : Bool}
  %Equal.sym(List<&2, Tree.Node>, Calls.args(D1.inert.node(ps)), inert.nodes(Calls.args(ps)), inert.args(ps)) :
    {inert.seq.of(Calls.walked.go(_, None{})) == Calls.seq(sig) : Bool}
  %Equal.sym(String, Calls.walked.go(inert.nodes(Calls.args(ps)), None{}), Calls.walked.go(Calls.args(ps), None{}),
    inert.walked.go(Calls.args(ps), None{})) : {inert.seq.of(_) == Calls.seq(sig) : Bool}
  {==}

# a signature read that way returns a proof as it did
law inert.returns_proof:
  for sig: Tree.Node
  {Calls.returns_proof(D1.inert.node(sig)) == Calls.returns_proof(sig) : Bool}

def inert.returns_proof(sig):
  match sig:
    case Tree.NCons{+h, +rest}:
      match rest:
        case Tree.NCons{+g, +r2}:
          inert.either(Bool, Calls.kind.leaf(~Calls.kind.arrow, D1.inert.node(h)),
            Calls.kind.leaf(~Calls.kind.arrow, h),
            Calls.returns_proof.or(Tree.opens(D1.inert.node(g), "{"), Calls.returns_proof(D1.inert.node(r2))),
            Calls.returns_proof.or(Tree.opens(g, "{"), Calls.returns_proof(r2)),
            Calls.returns_proof(Tree.NCons{D1.inert.node(g), D1.inert.node(r2)}),
            Calls.returns_proof(Tree.NCons{g, r2}), inert.arrow(h),
            inert.or2(Tree.opens(D1.inert.node(g), "{"), Tree.opens(g, "{"), Calls.returns_proof(D1.inert.node(r2)),
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
  {Calls.has_arrow(D1.inert.node(pp)) == Calls.has_arrow(pp) : Bool}

def inert.has_arrow(pp):
  match pp:
    case Tree.NCons{+h, +rest}:
      inert.or_else(Calls.kind.leaf(~Calls.kind.arrow, D1.inert.node(h)), Calls.kind.leaf(~Calls.kind.arrow, h),
        Calls.has_arrow(D1.inert.node(rest)), Calls.has_arrow(rest), inert.arrow(h), inert.has_arrow(rest))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a signature read that way writes a type as it did
law inert.typed:
  for +sig: Tree.Node
  {Calls.typed(D1.inert.node(sig)) == Calls.typed(sig) : Bool}

def inert.typed(sig):
  +ps = Calls.params.of(sig)
  %Equal.sym(Tree.Node, Calls.params.of(D1.inert.node(sig)), D1.inert.node(ps), inert.params.of(sig)) :
    {Lazy.or_else(Calls.has_colon(_), _u => Calls.has_arrow(D1.inert.node(sig))) == Calls.typed(sig) : Bool}
  inert.or_else(Calls.has_colon(D1.inert.node(ps)), Calls.has_colon(ps), Calls.has_arrow(D1.inert.node(sig)),
    Calls.has_arrow(sig), inert.has_colon(ps), inert.has_arrow(sig))

# a signature read that way is a proof as it was
law inert.proof:
  for +sig: Tree.Node
  {Calls.proof(D1.inert.node(sig)) == Calls.proof(sig) : Bool}

def inert.proof(sig):
  inert.or2(Calls.returns_proof(D1.inert.node(sig)), Calls.returns_proof(sig),
    Bool.not(Calls.typed(D1.inert.node(sig))), Bool.not(Calls.typed(sig)), inert.returns_proof(sig),
    Equal.cong(Bool, Bool, z => Bool.not(z), Calls.typed(D1.inert.node(sig)), Calls.typed(sig), inert.typed(sig)))

# a signature read that way is exempt as it was
law inert.exempt:
  for +path: String
  for +sig: Tree.Node
  {Calls.exempt(path, D1.inert.node(sig)) == Calls.exempt(path, sig) : Bool}

def inert.exempt(path, sig):
  Equal.cong(Bool, Bool, z => Bool.or(Paths.is_law_file(path), z), Calls.proof(D1.inert.node(sig)),
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
  {f(Calls.defs(D1.inert.node(tree))) == f(Calls.defs(tree)) : List<&2, F.Finding>}

def inert.lift(f, tree, h):
  %Equal.sym(List<&2, Calls.Def>, Calls.defs(D1.inert.node(tree)), inert.defs(Calls.defs(tree)),
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
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for +e: {D1.inert.ok(kids) == True{} : Bool}
  {Tail.bare(D1.inert.node(kids), name) == Tail.bare(kids, name) : Bool}

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
                      +tt = D1.inert.keep(D1.inert.blanks(k), t)
                      %M1.inert.eq_keep(D1.inert.blanks(k), t, name, M1.inert.and_l(D1.inert.fits(Lex.Tok{k, t, l, c}),
                        Bool.and(D1.inert.ok(g), True{}), e), en) :
                        {Bool.and(String.eq(tt, name), Tree.opens(D1.inert.node(g), "(")) == Bool.and(_,
                          Tree.opens(g, "("))
                          : Bool}
                      %inert.opens(g, "(") : {Bool.and(String.eq(tt, name), Tree.opens(D1.inert.node(g), "("))
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
  for +ef: {D1.inert.fits.go(D1.inert.blanks(kk), t) == True{} : Bool}
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for ik: {Tail.walk(D1.inert.node(kids), name, path, False{}) == Tail.walk(kids, name, path, False{}) : List<&2,
    F.Finding>}
  for ir: {Tail.walk(D1.inert.node(r2), name, path, False{}) == Tail.walk(r2, name, path, False{}) : List<&2,
    F.Finding>}
  {inert.tail.at(String.eq(D1.inert.keep(D1.inert.blanks(kk), t), name),
      String.eq(D1.inert.keep(D1.inert.blanks(kk), t), "Bool.pick"), o, l, c, name, path, skip,
      Tail.walk(D1.inert.node(kids), name, path, False{}), Tail.walk(D1.inert.node(r2), name, path, False{}))
    == inert.tail.at(String.eq(t, name), String.eq(t, "Bool.pick"), o, l, c, name, path, skip,
      Tail.walk(kids, name, path, False{}), Tail.walk(r2, name, path, False{})) : List<&2, F.Finding>}

def inert.tail.lg(kk, t, o, l, c, name, path, skip, kids, r2, ef, en, ik, ir):
  +tt = D1.inert.keep(D1.inert.blanks(kk), t)
  +wk = Tail.walk(D1.inert.node(kids), name, path, False{})
  +wr = Tail.walk(D1.inert.node(r2), name, path, False{})
  +lhs = inert.tail.at(String.eq(tt, name), String.eq(tt, "Bool.pick"), o, l, c, name, path, skip, wk, wr)
  %M1.inert.eq_keep(D1.inert.blanks(kk), t, name, ef, en) : {lhs == inert.tail.at(_, String.eq(t, "Bool.pick"), o, l, c,
    name, path, skip, Tail.walk(kids, name, path, False{}), Tail.walk(r2, name, path, False{})) : List<&2, F.Finding>}
  %M1.inert.eq_keep(D1.inert.blanks(kk), t, "Bool.pick", ef, {==}) : {lhs == inert.tail.at(String.eq(tt, name), _, o, l,
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
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Tail.walk(D1.inert.node(nn), name, path, skip) == Tail.walk(nn, name, path, skip) : List<&2, F.Finding>}

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
                          +eg = M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}), Bool.and(D1.inert.ok(kids),
                            D1.inert.ok(r2)), e)
                          inert.tail.lg(k, t, ot, l, c, name, path, skip, kids, r2,
                            M1.inert.and_l(D1.inert.fits(Lex.Tok{k, t, l, c}), Bool.and(D1.inert.ok(kids),
                              D1.inert.ok(r2)),
                              e), en,
                            inert.tail.walk(kids, name, path, False{}, en, M1.inert.and_l(D1.inert.ok(kids),
                              D1.inert.ok(r2), eg)),
                            inert.tail.walk(r2, name, path, False{}, en, M1.inert.and_r(D1.inert.ok(kids),
                              D1.inert.ok(r2), eg)))
                    case Tree.Leaf{x}:
                      inert.tail.walk(rest, name, path, False{}, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}),
                        D1.inert.ok(rest), e))
                    case Tree.Stmt{x, y, z}:
                      inert.tail.walk(rest, name, path, False{}, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}),
                        D1.inert.ok(rest), e))
                    case Tree.NNil{}:
                      inert.tail.walk(rest, name, path, False{}, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}),
                        D1.inert.ok(rest), e))
                    case Tree.NCons{x, y}:
                      inert.tail.walk(rest, name, path, False{}, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}),
                        D1.inert.ok(rest), e))
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NNil{}: {==}
        case Tree.Group{o, +kids, cl}:
          inert.cat2(Tail.walk(D1.inert.node(kids), name, path, False{}), Tail.walk(kids, name, path, False{}),
            Tail.walk(D1.inert.node(rest), name, path, False{}), Tail.walk(rest, name, path, False{}),
            inert.tail.walk(kids, name, path, False{}, en, M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(rest), e)),
            inert.tail.walk(rest, name, path, False{}, en, M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(rest), e)))
        case Tree.Stmt{sk, +kids, +body}:
          +es = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
          +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es)
          +sb = Tail.bare(D1.inert.node(kids), name)
          inert.cat3(Tail.walk(D1.inert.node(kids), name, path, sb), Tail.walk(kids, name, path, Tail.bare(kids,
            name)),
            Tail.walk(D1.inert.node(body), name, path, False{}), Tail.walk(body, name, path, False{}),
            Tail.walk(D1.inert.node(rest), name, path, False{}), Tail.walk(rest, name, path, False{}),
            Equal.trans(List<&2, F.Finding>, Tail.walk(D1.inert.node(kids), name, path, sb), Tail.walk(kids, name,
              path, sb),
              Tail.walk(kids, name, path, Tail.bare(kids, name)), inert.tail.walk(kids, name, path, sb, en, ek),
              Equal.cong(Bool, List<&2, F.Finding>, z => Tail.walk(kids, name, path, z), sb, Tail.bare(kids, name),
                inert.tail.bare(kids, name, en, ek))),
            inert.tail.walk(body, name, path, False{}, en, M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es)),
            inert.tail.walk(rest, name, path, False{}, en,
              M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)))
        case Tree.NNil{}: inert.tail.walk(rest, name, path, False{}, en, e)
        case Tree.NCons{x, y}:
          inert.tail.walk(rest, name, path, False{}, en, M1.inert.and_r(D1.inert.ok(Tree.NCons{x, y}),
            D1.inert.ok(rest), e))
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
  {D1.inert.marked(name) == False{} : Bool}

def inert.dok.head(name, sig, body, rest, e):
  inert.not_true(D1.inert.marked(name), M1.inert.and_l(Bool.not(D1.inert.marked(name)),
    Bool.and(D1.inert.ok(sig), D1.inert.ok(body)), M1.inert.and_l(Bool.and(Bool.not(D1.inert.marked(name)),
      Bool.and(D1.inert.ok(sig), D1.inert.ok(body))), inert.dok(rest), e)))

# the body of a def as the lexer makes it fits
law inert.dok.body:
  for +name: String
  for +sig: Tree.Node
  for +body: Tree.Node
  for +rest: List<&2, Calls.Def>
  for +e: {inert.dok(Calls.Def{name, sig, body} <> rest) == True{} : Bool}
  {D1.inert.ok(body) == True{} : Bool}

def inert.dok.body(name, sig, body, rest, e):
  M1.inert.and_r(D1.inert.ok(sig), D1.inert.ok(body), M1.inert.and_r(Bool.not(D1.inert.marked(name)),
    Bool.and(D1.inert.ok(sig), D1.inert.ok(body)), M1.inert.and_l(Bool.and(Bool.not(D1.inert.marked(name)),
      Bool.and(D1.inert.ok(sig), D1.inert.ok(body))), inert.dok(rest), e)))

# the defs after one as the lexer makes them
law inert.dok.rest:
  for +name: String
  for +sig: Tree.Node
  for +body: Tree.Node
  for +rest: List<&2, Calls.Def>
  for +e: {inert.dok(Calls.Def{name, sig, body} <> rest) == True{} : Bool}
  {inert.dok(rest) == True{} : Bool}

def inert.dok.rest(name, sig, body, rest, e):
  M1.inert.and_r(Bool.and(Bool.not(D1.inert.marked(name)), Bool.and(D1.inert.ok(sig), D1.inert.ok(body))),
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
      +lst = inert.tail.stop(Calls.seq(D1.inert.node(sig)), Calls.exempt(path, D1.inert.node(sig)),
        Tail.walk(D1.inert.node(body), name, path, False{}))
      %inert.seq(sig) : {Tail.check.go(inert.defs(rest), path, lst <> acc) == Tail.check.go(rest, path,
        inert.tail.stop(_, Calls.exempt(path, sig), Tail.walk(body, name, path, False{})) <> acc) : List<&2, F.Finding>}
      %inert.exempt(path, sig) : {Tail.check.go(inert.defs(rest), path, lst <> acc) == Tail.check.go(rest, path,
        inert.tail.stop(Calls.seq(D1.inert.node(sig)), _, Tail.walk(body, name, path, False{})) <> acc)
        : List<&2, F.Finding>}
      %inert.tail.walk(body, name, path, False{}, inert.dok.head(name, sig, body, rest, e),
        inert.dok.body(name, sig, body, rest, e)) : {Tail.check.go(inert.defs(rest), path, lst <> acc)
          == Tail.check.go(rest, path, inert.tail.stop(Calls.seq(D1.inert.node(sig)), Calls.exempt(path,
            D1.inert.node(sig)), _) <> acc) : List<&2, F.Finding>}
      inert.tail.go(rest, path, lst <> acc, inert.dok.rest(name, sig, body, rest, e))

def Laws.inert_tail(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, ok, ok2, e):
  M1.inert.via(Tree.Node, z => Tail.check.go(Calls.defs(z), path, []), tree, tree2, D1.inert.node(tree),
    D1.inert.node(tree2),
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
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  {Pick.both(Calls.args(D1.inert.node(kids)), name) == Pick.both(Calls.args(kids), name) : Bool}

def inert.pick.both(kids, name, en, ek):
  +l2 = Calls.calls(Calls.arg(Calls.args(D1.inert.node(kids)), 2n), name)
  +l3 = Calls.calls(Calls.arg(Calls.args(D1.inert.node(kids)), 3n), name)
  %inert.calls.nth(kids, 2n, name, en, ek) : {Bool.and(l2, l3) == Bool.and(_, Calls.calls(Calls.arg(Calls.args(kids),
    3n), name)) : Bool}
  %inert.calls.nth(kids, 3n, name, en, ek) : {Bool.and(l2, l3) == Bool.and(l2, _) : Bool}
  {==}

# either branch of a pick read that way calls the def as it did
law inert.pick.once:
  for +kids: Tree.Node
  for +name: String
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  {Pick.once(Calls.args(D1.inert.node(kids)), name) == Pick.once(Calls.args(kids), name) : Bool}

def inert.pick.once(kids, name, en, ek):
  +l2 = Calls.calls(Calls.arg(Calls.args(D1.inert.node(kids)), 2n), name)
  +l3 = Calls.calls(Calls.arg(Calls.args(D1.inert.node(kids)), 3n), name)
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
        name ++ " calls itself in one branch of Bool.pick, which evaluates both, so the call always runs and never exits early; branch with `match` on the condition instead."}
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
  for ik: {Pick.walk(D1.inert.node(kids), name, path, q, inert.pick.hush(ip, bb, oo, q), 0n)
    == Pick.walk(kids, name, path, q, inert.pick.hush(ip, bb, oo, q), 0n) : List<&2, F.Finding>}
  for ir: {Pick.walk(D1.inert.node(rest), name, path, quiet, hush, at) == Pick.walk(rest, name, path, quiet, hush,
    at) : List<&2, F.Finding>}
  {inert.pick.at(ip, bb, oo, q, at, l, c, name, path, quiet, hush, D1.inert.node(kids), D1.inert.node(rest))
    == inert.pick.at(ip, bb, oo, q, at, l, c, name, path, quiet, hush, kids, rest) : List<&2, F.Finding>}

def inert.pick.nodes(ip, bb, oo, q, at, l, c, name, path, quiet, hush, kids, rest, ik, ir):
  +wk = Pick.walk(D1.inert.node(kids), name, path, q, inert.pick.hush(ip, bb, oo, q), 0n)
  +wr = Pick.walk(D1.inert.node(rest), name, path, quiet, hush, at)
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
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Pick.walk(D1.inert.node(nn), name, path, quiet, hush, nth) == Pick.walk(nn, name, path, quiet, hush,
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
                      +eh = M1.inert.and_l(D1.inert.fits(Lex.Tok{k, t, l, c}), Bool.and(D1.inert.ok(kids),
                        D1.inert.ok(r2)), e)
                      +eg = M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}), Bool.and(D1.inert.ok(kids),
                        D1.inert.ok(r2)), e)
                      +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                      +er = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                      +at = Pick.next(k, nth)
                      +q = Pick.mute(quiet, hush, at)
                      +ipl = String.eq(D1.inert.keep(D1.inert.blanks(k), t), "Bool.pick")
                      +bbl = Pick.both(Calls.args(D1.inert.node(kids)), name)
                      +ool = Pick.once(Calls.args(D1.inert.node(kids)), name)
                      +mid = inert.pick.at(ipl, bbl, ool, q, at, l, c, name, path, quiet, hush, kids, r2)
                      Equal.trans(List<&2, F.Finding>,
                        inert.pick.at(ipl, bbl, ool, q, at, l, c, name, path, quiet, hush, D1.inert.node(kids),
                          D1.inert.node(r2)), mid,
                        inert.pick.at(String.eq(t, "Bool.pick"), Pick.both(Calls.args(kids), name),
                          Pick.once(Calls.args(kids), name),
                          q, at, l, c, name, path, quiet, hush, kids, r2),
                        inert.pick.nodes(ipl, bbl, ool, q, at, l, c, name, path, quiet, hush, kids, r2,
                          inert.pick.walk(kids, name, path, q, inert.pick.hush(ipl, bbl, ool, q), 0n, en, ek),
                          inert.pick.walk(r2, name, path, quiet, hush, at, en, er)),
                        inert.pick.flags(ipl, String.eq(t, "Bool.pick"), bbl, Pick.both(Calls.args(kids), name), ool,
                          Pick.once(Calls.args(kids), name), q, at, l, c, name, path, quiet, hush, kids, r2,
                          M1.inert.eq_keep(D1.inert.blanks(k), t, "Bool.pick", eh, {==}), inert.pick.both(kids, name,
                            en, ek),
                          inert.pick.once(kids, name, en, ek)))
                    case Tree.Leaf{x}:
                      inert.pick.walk(rest, name, path, quiet, hush, Pick.next(k, nth), en,
                        M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}), D1.inert.ok(rest), e))
                    case Tree.Stmt{x, y, z}:
                      inert.pick.walk(rest, name, path, quiet, hush, Pick.next(k, nth), en,
                        M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}), D1.inert.ok(rest), e))
                    case Tree.NNil{}:
                      inert.pick.walk(rest, name, path, quiet, hush, Pick.next(k, nth), en,
                        M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}), D1.inert.ok(rest), e))
                    case Tree.NCons{x, y}:
                      inert.pick.walk(rest, name, path, quiet, hush, Pick.next(k, nth), en,
                        M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}), D1.inert.ok(rest), e))
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
          inert.cat2(Pick.walk(D1.inert.node(kids), name, path, m, False{}, 0n), Pick.walk(kids, name, path, m,
            False{}, 0n),
            Pick.walk(D1.inert.node(rest), name, path, quiet, hush, nth), Pick.walk(rest, name, path, quiet, hush,
              nth),
            inert.pick.walk(kids, name, path, m, False{}, 0n, en, M1.inert.and_l(D1.inert.ok(kids),
              D1.inert.ok(rest), e)),
            inert.pick.walk(rest, name, path, quiet, hush, nth, en, M1.inert.and_r(D1.inert.ok(kids),
              D1.inert.ok(rest), e)))
        case Tree.Stmt{sk, +kids, +body}:
          +es = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
          +m = Pick.mute(quiet, hush, nth)
          inert.cat3(Pick.walk(D1.inert.node(kids), name, path, m, False{}, 0n), Pick.walk(kids, name, path, m,
            False{}, 0n),
            Pick.walk(D1.inert.node(body), name, path, m, False{}, 0n), Pick.walk(body, name, path, m, False{}, 0n),
            Pick.walk(D1.inert.node(rest), name, path, quiet, hush, nth), Pick.walk(rest, name, path, quiet, hush,
              nth),
            inert.pick.walk(kids, name, path, m, False{}, 0n, en, M1.inert.and_l(D1.inert.ok(kids),
              D1.inert.ok(body), es)),
            inert.pick.walk(body, name, path, m, False{}, 0n, en, M1.inert.and_r(D1.inert.ok(kids),
              D1.inert.ok(body), es)),
            inert.pick.walk(rest, name, path, quiet, hush, nth, en,
              M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)))
        case Tree.NNil{}:
          inert.pick.walk(rest, name, path, quiet, hush, nth, en, e)
        case Tree.NCons{x, y}:
          inert.pick.walk(rest, name, path, quiet, hush, nth, en, M1.inert.and_r(D1.inert.ok(Tree.NCons{x, y}),
            D1.inert.ok(rest), e))
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
      +lst = inert.pick.stop(Calls.exempt(path, D1.inert.node(sig)), Pick.walk(D1.inert.node(body), name, path,
        False{},
        False{}, 0n))
      %inert.exempt(path, sig) : {Pick.check.go(inert.defs(rest), path, lst <> acc) == Pick.check.go(rest, path,
        inert.pick.stop(_, Pick.walk(body, name, path, False{}, False{}, 0n)) <> acc) : List<&2, F.Finding>}
      %inert.pick.walk(body, name, path, False{}, False{}, 0n, inert.dok.head(name, sig, body, rest, e),
        inert.dok.body(name, sig, body, rest, e)) : {Pick.check.go(inert.defs(rest), path, lst <> acc)
          == Pick.check.go(rest, path, inert.pick.stop(Calls.exempt(path, D1.inert.node(sig)), _) <> acc)
          : List<&2, F.Finding>}
      inert.pick.go(rest, path, lst <> acc, inert.dok.rest(name, sig, body, rest, e))

def Laws.inert_pick(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, ok, ok2, e):
  M1.inert.via(Tree.Node, z => Pick.check.go(Calls.defs(z), path, []), tree, tree2, D1.inert.node(tree),
    D1.inert.node(tree2),
    inert.lift(z => Pick.check.go(z, path, []), tree, inert.pick.go(Calls.defs(tree), path, [], inert.dok.of(tree,
      ok))),
    inert.lift(z => Pick.check.go(z, path, []), tree2, inert.pick.go(Calls.defs(tree2), path, [], inert.dok.of(tree2,
      ok2))),
    e)

# doc
# ---

# a line that starts as ll says
def inert.doc.line(ll: Laws.inert.Lead) -> String:
  match ll:
    case Laws.LHash{}: "#"
    case Laws.LAt{}: "@"
    case Laws.LPlain{}: ""

# the lines rebuilt from how each of them starts
def inert.doc.relines(bs: List<&2, Laws.inert.Lead>) -> List<&2, String>:
  match bs:
    case Nil{}: Nil{}
    case Con{h, t}: inert.doc.line(h) <> inert.doc.relines(t)

# a line rebuilt from how it starts steps doc's read down as it did
law inert.doc.after1:
  for b1: Bool
  for b2: Bool
  for +ok: Bool
  {Doc.check.after(inert.doc.line(Laws.inert.lead(b1, b2)), ok) == Bool.or(b1, Bool.and(b2, ok)) : Bool}

def inert.doc.after1(b1, b2, _ok):
  match b1:
    case True{}: {==}
    case False{}:
      match b2:
        case True{}: {==}
        case False{}: {==}

# doc's read down the lines rebuilt is its read down the lines
law inert.doc.lead:
  for lines: List<&2, String>
  for +nn: U32
  for +ok: Bool
  {Doc.check.lead(inert.doc.relines(Laws.inert.leads(lines)), nn, ok) == Doc.check.lead(lines, nn, ok) : Bool}

def inert.doc.lead(lines, nn, ok):
  match lines:
    case Nil{}: {==}
    case Con{+hh, +tt}:
      +a1 = Doc.check.after(inert.doc.line(Laws.inert.lead(String.starts_with(hh, "#"), String.starts_with(hh, "@"))),
        ok)
      +a2 = Doc.check.after(hh, ok)
      +rt = inert.doc.relines(Laws.inert.leads(tt))
      Equal.cong(Bool, Bool, z => Lazy.stop(Bool, U32.is_eq(nn, 0), ok, _u => z),
        Doc.check.lead(rt, U32.sub(nn, 1), a1), Doc.check.lead(tt, U32.sub(nn, 1), a2),
        Equal.trans(Bool, Doc.check.lead(rt, U32.sub(nn, 1), a1), Doc.check.lead(rt, U32.sub(nn, 1), a2),
          Doc.check.lead(tt, U32.sub(nn, 1), a2),
          Equal.cong(Bool, Bool, z => Doc.check.lead(rt, U32.sub(nn, 1), z), a1, a2,
            inert.doc.after1(String.starts_with(hh, "#"), String.starts_with(hh, "@"), ok)),
          inert.doc.lead(tt, U32.sub(nn, 1), a2)))

# doc's walk reads its items' kinds, names and lines, and of its lines only
# how each starts
law inert.doc.go:
  for items: List<&2, Outline.Item>
  for +path: String
  for +lines: List<&2, String>
  {Doc.check.go(Laws.inert.items(items), path, inert.doc.relines(Laws.inert.leads(lines)))
    == Doc.check.go(items, path, lines) : List<&2, F.Finding>}

def inert.doc.go(items, path, lines):
  match items:
    case Nil{}: {==}
    case Con{Outline.Item{+k, +name, +line, s, d, p}, +rest}:
      +rl = inert.doc.relines(Laws.inert.leads(lines))
      +x = {F.Finding{path, line, 0, 0, "doc", Doc.what(k) ++ " " ++ name ++ " has no comment above it."} : F.Finding}
      +nd = Bool.and(Doc.needs(k), Bool.not(Doc.exempt(name)))
      +m1 = Doc.check.go(Laws.inert.items(rest), path, rl)
      +m2 = Doc.check.go(rest, path, lines)
      Equal.trans(List<&2, F.Finding>,
        Bool.pick(List<&2, F.Finding>, Lazy.and_then(nd, _u => Bool.not(Doc.check.above(rl, line))), x <> m1, m1),
        Bool.pick(List<&2, F.Finding>, Lazy.and_then(nd, _u => Bool.not(Doc.check.above(lines, line))), x <> m1, m1),
        Bool.pick(List<&2, F.Finding>, Lazy.and_then(nd, _u => Bool.not(Doc.check.above(lines, line))), x <> m2, m2),
        Equal.cong(Bool, List<&2, F.Finding>,
          z => Bool.pick(List<&2, F.Finding>, Lazy.and_then(nd, _u => Bool.not(z)), x <> m1, m1),
          Doc.check.above(rl, line), Doc.check.above(lines, line), inert.doc.lead(lines, line, False{})),
        Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
          z => Bool.pick(List<&2, F.Finding>, Lazy.and_then(nd, _u => Bool.not(Doc.check.above(lines, line))),
            x <> z, z),
          m1, m2, inert.doc.go(rest, path, lines)))

def Laws.inert_doc(path, text, toks, _tree, _bound, items, text2, toks2, _tree2, _bound2, items2, ei, el):
  +l1 = Doc.lines(text, toks)
  +l2 = Doc.lines(text2, toks2)
  +r1 = Doc.check.go(Laws.inert.items(items), path, inert.doc.relines(Laws.inert.leads(l1)))
  +m = Doc.check.go(Laws.inert.items(items2), path, inert.doc.relines(Laws.inert.leads(l1)))
  +r2 = Doc.check.go(Laws.inert.items(items2), path, inert.doc.relines(Laws.inert.leads(l2)))
  +w1 = Doc.check.go(items, path, l1)
  +w2 = Doc.check.go(items2, path, l2)
  Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
    z => Lazy.stop(List<&2, F.Finding>, Bool.or(Paths.is_proof(path), Paths.is_test(path)), [], _u => z), w1, w2,
    Equal.trans(List<&2, F.Finding>, w1, r1, w2, Equal.sym(List<&2, F.Finding>, r1, w1, inert.doc.go(items, path, l1)),
      Equal.trans(List<&2, F.Finding>, r1, m, w2,
        Equal.cong(List<&2, Outline.Item>, List<&2, F.Finding>,
          z => Doc.check.go(z, path, inert.doc.relines(Laws.inert.leads(l1))), Laws.inert.items(items),
          Laws.inert.items(items2), ei),
        Equal.trans(List<&2, F.Finding>, m, r2, w2,
          Equal.cong(List<&2, Laws.inert.Lead>, List<&2, F.Finding>,
            z => Doc.check.go(Laws.inert.items(items2), path, inert.doc.relines(z)), Laws.inert.leads(l1),
            Laws.inert.leads(l2), el),
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
  {Calls.kind.leaf(~Strict.seg_op.ends, D1.inert.node(nn)) == Calls.kind.leaf(~Strict.seg_op.ends, nn) : Bool}

def inert.strict.ends(nn):
  Equal.cong(Maybe<&2, Lex.TokKind>, Bool,
    m => Calls.kind.of(~Strict.seg_op.ends, m), Calls.leaf.kind(D1.inert.node(nn)), Calls.leaf.kind(nn),
    inert.leaf_kind(nn))

# a chain read that way holds `&&` or `||` in its stretch as it did
law inert.strict.seg:
  for nn: Tree.Node
  {Strict.seg_op(D1.inert.node(nn)) == Strict.seg_op(nn) : Bool}

def inert.strict.seg(nn):
  match nn:
    case Tree.NCons{+h, +rest}:
      +ke = Calls.kind.leaf(~Strict.seg_op.ends, h)
      +ko = Calls.kind.leaf(~Calls.kind.oper, h)
      +kb = Calls.kind.leaf(~D1.inert.blanks, h)
      +th = Calls.leaf.text(h)
      +rhs = Strict.seg_op(Tree.NCons{h, rest})
      +ih = D1.inert.node(h)
      +ir = D1.inert.node(rest)
      %Equal.sym(Bool, Calls.kind.leaf(~Strict.seg_op.ends, ih), ke, inert.strict.ends(h)) :
        {Lazy.stop(Bool, _, False{},
        _u => Strict.seg_op.or(Bool.and(Calls.kind.leaf(~Calls.kind.oper, ih), Strict.logic(Calls.leaf.text(ih))),
          Strict.seg_op(ir))) == rhs : Bool}
      %Equal.sym(Bool, Calls.kind.leaf(~Calls.kind.oper, ih), ko, inert.oper(h)) : {Lazy.stop(Bool, ke, False{},
        _u => Strict.seg_op.or(Bool.and(_, Strict.logic(Calls.leaf.text(ih))), Strict.seg_op(ir))) == rhs : Bool}
      %Equal.sym(String, Calls.leaf.text(ih), D1.inert.keep(kb, th), inert.leaf_text(h)) : {Lazy.stop(Bool, ke,
        False{}, _u => Strict.seg_op.or(Bool.and(ko, Strict.logic(_)), Strict.seg_op(ir))) == rhs : Bool}
      %Equal.sym(Bool, Strict.seg_op(ir), Strict.seg_op(rest), inert.strict.seg(rest)) : {Lazy.stop(Bool, ke,
        False{}, _u => Strict.seg_op.or(Bool.and(ko, Strict.logic(D1.inert.keep(kb, th))), _)) == rhs : Bool}
      %Equal.sym(Bool, Bool.and(ko, Strict.logic(D1.inert.keep(kb, th))), Bool.and(ko, Strict.logic(th)),
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
  for +ef: {D1.inert.fits.go(D1.inert.blanks(kk), t) == True{} : Bool}
  {Strict.inner(hot, o, D1.inert.keep(D1.inert.blanks(kk), t)) == Strict.inner(hot, o, t) : Bool}

def inert.strict.inner(kk, t, o, hot, ef):
  +tt = D1.inert.keep(D1.inert.blanks(kk), t)
  %M1.inert.eq_keep(D1.inert.blanks(kk), t, "Bool.and", ef, {==}) : {Strict.inner(hot, o, tt)
    == Bool.or(hot, Bool.and(String.eq(o, "("), Bool.or(_, String.eq(t, "Bool.or")))) : Bool}
  %M1.inert.eq_keep(D1.inert.blanks(kk), t, "Bool.or", ef, {==}) : {Strict.inner(hot, o, tt)
    == Bool.or(hot, Bool.and(String.eq(o, "("), Bool.or(String.eq(tt, "Bool.and"), _))) : Bool}
  {==}

# past a comma or a `=>`, the rest walked in the stretch its own operators set
law inert.strict.past:
  for +rest: Tree.Node
  for +name: String
  for +path: String
  for +outer: Bool
  for -hh: Bool -> Bool
  for ih: {Strict.walk(D1.inert.node(rest), name, path, outer, hh(Strict.seg_op(D1.inert.node(rest))))
    == Strict.walk(rest, name, path, outer, hh(Strict.seg_op(D1.inert.node(rest)))) : List<&2, F.Finding>}
  {Strict.walk(D1.inert.node(rest), name, path, outer, hh(Strict.seg_op(D1.inert.node(rest))))
    == Strict.walk(rest, name, path, outer, hh(Strict.seg_op(rest))) : List<&2, F.Finding>}

def inert.strict.past(rest, name, path, outer, hh, ih):
  %inert.strict.seg(rest) : {Strict.walk(D1.inert.node(rest), name, path, outer,
    hh(Strict.seg_op(D1.inert.node(rest))))
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
  for +ef: {D1.inert.fits.go(D1.inert.blanks(kk), t) == True{} : Bool}
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for ik: {Strict.walk(D1.inert.node(kids), name, path, Strict.inner(hot, o, D1.inert.keep(D1.inert.blanks(kk),
    t)),
      Bool.or(Strict.inner(hot, o, D1.inert.keep(D1.inert.blanks(kk), t)), Strict.seg_op(D1.inert.node(kids))))
    == Strict.walk(kids, name, path, Strict.inner(hot, o, D1.inert.keep(D1.inert.blanks(kk), t)),
      Bool.or(Strict.inner(hot, o, D1.inert.keep(D1.inert.blanks(kk), t)), Strict.seg_op(D1.inert.node(kids))))
    : List<&2, F.Finding>}
  for ir: {Strict.walk(D1.inert.node(r2), name, path, outer, hot) == Strict.walk(r2, name, path, outer, hot)
    : List<&2, F.Finding>}
  {Strict.call(D1.inert.keep(D1.inert.blanks(kk), t), l, c, o, name, path, hot,
      Strict.walk(D1.inert.node(kids), name, path, Strict.inner(hot, o, D1.inert.keep(D1.inert.blanks(kk), t)),
        Bool.or(Strict.inner(hot, o, D1.inert.keep(D1.inert.blanks(kk), t)), Strict.seg_op(D1.inert.node(kids)))),
      Strict.walk(D1.inert.node(r2), name, path, outer, hot))
    == Strict.call(t, l, c, o, name, path, hot,
      Strict.walk(kids, name, path, Strict.inner(hot, o, t), Bool.or(Strict.inner(hot, o, t), Strict.seg_op(kids))),
      Strict.walk(r2, name, path, outer, hot)) : List<&2, F.Finding>}

def inert.strict.lg(kk, t, l, c, o, name, path, outer, hot, kids, r2, ef, en, ik, ir):
  +tt = D1.inert.keep(D1.inert.blanks(kk), t)
  +i1 = Strict.inner(hot, o, tt)
  +wk = Strict.walk(D1.inert.node(kids), name, path, i1, Bool.or(i1, Strict.seg_op(D1.inert.node(kids))))
  +wr = Strict.walk(D1.inert.node(r2), name, path, outer, hot)
  +lhs = Strict.call(tt, l, c, o, name, path, hot, wk, wr)
  %inert.strict.inner(kk, t, o, hot, ef) : {lhs == Strict.call(t, l, c, o, name, path, hot, Strict.walk(kids, name,
    path, _,
    Bool.or(_, Strict.seg_op(kids))), Strict.walk(r2, name, path, outer, hot)) : List<&2, F.Finding>}
  %inert.strict.seg(kids) : {lhs == Strict.call(t, l, c, o, name, path, hot, Strict.walk(kids, name, path, i1,
    Bool.or(i1, _)), Strict.walk(r2, name, path, outer, hot)) : List<&2, F.Finding>}
  %ik : {lhs == Strict.call(t, l, c, o, name, path, hot, _, Strict.walk(r2, name, path, outer, hot)) : List<&2,
    F.Finding>}
  %ir : {lhs == Strict.call(t, l, c, o, name, path, hot, wk, _) : List<&2, F.Finding>}
  %M1.inert.eq_keep(D1.inert.blanks(kk), t, name, ef, en) : {Strict.call(tt, l, c, o, name, path, hot, wk, wr)
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
  for ea: {Strict.walk(D1.inert.node(rest), name, path, outer, Bool.or(outer, Strict.seg_op(D1.inert.node(rest))))
    == Strict.walk(rest, name, path, outer, Bool.or(outer, Strict.seg_op(rest))) : List<&2, F.Finding>}
  for eb: {Strict.walk(D1.inert.node(rest), name, path, outer, Strict.seg_op(D1.inert.node(rest)))
    == Strict.walk(rest, name, path, outer, Strict.seg_op(rest)) : List<&2, F.Finding>}
  for ec: {Strict.walk(D1.inert.node(rest), name, path, outer, hot) == Strict.walk(rest, name, path, outer, hot)
    : List<&2, F.Finding>}
  {Strict.leaf(kk, _u => Strict.walk(D1.inert.node(rest), name, path, outer, Bool.or(outer,
      Strict.seg_op(D1.inert.node(rest)))), _v => Strict.walk(D1.inert.node(rest), name, path, outer,
      Strict.seg_op(D1.inert.node(rest))), _w => Strict.walk(D1.inert.node(rest), name, path, outer, hot))
    == Strict.leaf(kk, _u => Strict.walk(rest, name, path, outer, Bool.or(outer, Strict.seg_op(rest))),
      _v => Strict.walk(rest, name, path, outer, Strict.seg_op(rest)), _w => Strict.walk(rest, name, path, outer, hot))
    : List<&2, F.Finding>}

def inert.strict.gen(kk, rest, name, path, outer, hot, ea, eb, ec):
  inert.strict.leaf(kk, Strict.walk(D1.inert.node(rest), name, path, outer, Bool.or(outer,
    Strict.seg_op(D1.inert.node(rest)))), Strict.walk(rest, name, path, outer, Bool.or(outer, Strict.seg_op(rest))),
    Strict.walk(D1.inert.node(rest), name, path, outer, Strict.seg_op(D1.inert.node(rest))),
    Strict.walk(rest, name, path, outer, Strict.seg_op(rest)), Strict.walk(D1.inert.node(rest), name, path, outer,
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
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Strict.walk(D1.inert.node(nn), name, path, outer, hot) == Strict.walk(nn, name, path, outer, hot) : List<&2,
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
                          +a1 = Strict.walk(D1.inert.node(rest), name, path, outer, Bool.or(outer,
                            Strict.seg_op(D1.inert.node(rest))))
                          +b1 = Strict.walk(D1.inert.node(rest), name, path, outer,
                            Strict.seg_op(D1.inert.node(rest)))
                          +k1 = Strict.walk(D1.inert.node(kids), name, path, Strict.inner(hot, ot,
                            D1.inert.keep(D1.inert.blanks(k), t)), Bool.or(Strict.inner(hot, ot,
                              D1.inert.keep(D1.inert.blanks(k), t)), Strict.seg_op(D1.inert.node(kids))))
                          +c1 = Strict.call(D1.inert.keep(D1.inert.blanks(k), t), l, c, ot, name, path, hot, k1,
                            Strict.walk(D1.inert.node(r2), name, path, outer, hot))
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
                                Strict.seg_op(D1.inert.node(rest))), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t,
                                  l, c}), D1.inert.ok(rest), e))),
                            inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path,
                              outer,
                              Strict.seg_op(D1.inert.node(rest)), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l,
                                c}), D1.inert.ok(rest), e))),
                            inert.strict.lg(k, t, l, c, ot, name, path, outer, hot, kids, r2,
                              M1.inert.and_l(D1.inert.fits(Lex.Tok{k, t, l, c}), Bool.and(D1.inert.ok(kids),
                                D1.inert.ok(r2)), e), en,
                              inert.strict.walk(kids, name, path, Strict.inner(hot, ot,
                                D1.inert.keep(D1.inert.blanks(k), t)), Bool.or(Strict.inner(hot, ot,
                                  D1.inert.keep(D1.inert.blanks(k), t)), Strict.seg_op(D1.inert.node(kids))), en,
                                M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2),
                                  M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}), Bool.and(D1.inert.ok(kids),
                                    D1.inert.ok(r2)), e))),
                              inert.strict.walk(r2, name, path, outer, hot, en, M1.inert.and_r(D1.inert.ok(kids),
                                D1.inert.ok(r2), M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}),
                                  Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e)))))
                    case Tree.Leaf{x}:
                      inert.strict.gen(k, rest, name, path, outer, hot,
                        inert.strict.past(rest, name, path, outer, z => Bool.or(outer, z), inert.strict.walk(rest,
                          name, path, outer,
                          Bool.or(outer,
                            Strict.seg_op(D1.inert.node(rest))), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l,
                              c}), D1.inert.ok(rest), e))),
                        inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path, outer,
                          Strict.seg_op(D1.inert.node(rest)), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}),
                            D1.inert.ok(rest), e))),
                        inert.strict.walk(rest, name, path, outer, hot, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t,
                          l, c}), D1.inert.ok(rest), e)))
                    case Tree.Stmt{x, y, z}:
                      inert.strict.gen(k, rest, name, path, outer, hot,
                        inert.strict.past(rest, name, path, outer, z => Bool.or(outer, z), inert.strict.walk(rest,
                          name, path, outer,
                          Bool.or(outer,
                            Strict.seg_op(D1.inert.node(rest))), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l,
                              c}), D1.inert.ok(rest), e))),
                        inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path, outer,
                          Strict.seg_op(D1.inert.node(rest)), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}),
                            D1.inert.ok(rest), e))),
                        inert.strict.walk(rest, name, path, outer, hot, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t,
                          l, c}), D1.inert.ok(rest), e)))
                    case Tree.NNil{}:
                      inert.strict.gen(k, rest, name, path, outer, hot,
                        inert.strict.past(rest, name, path, outer, z => Bool.or(outer, z), inert.strict.walk(rest,
                          name, path, outer,
                          Bool.or(outer,
                            Strict.seg_op(D1.inert.node(rest))), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l,
                              c}), D1.inert.ok(rest), e))),
                        inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path, outer,
                          Strict.seg_op(D1.inert.node(rest)), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}),
                            D1.inert.ok(rest), e))),
                        inert.strict.walk(rest, name, path, outer, hot, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t,
                          l, c}), D1.inert.ok(rest), e)))
                    case Tree.NCons{x, y}:
                      inert.strict.gen(k, rest, name, path, outer, hot,
                        inert.strict.past(rest, name, path, outer, z => Bool.or(outer, z), inert.strict.walk(rest,
                          name, path, outer,
                          Bool.or(outer,
                            Strict.seg_op(D1.inert.node(rest))), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l,
                              c}), D1.inert.ok(rest), e))),
                        inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path, outer,
                          Strict.seg_op(D1.inert.node(rest)), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}),
                            D1.inert.ok(rest), e))),
                        inert.strict.walk(rest, name, path, outer, hot, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t,
                          l, c}), D1.inert.ok(rest), e)))
                case Tree.Leaf{x}:
                  inert.strict.gen(k, rest, name, path, outer, hot,
                    inert.strict.past(rest, name, path, outer, z => Bool.or(outer, z), inert.strict.walk(rest, name,
                      path, outer,
                      Bool.or(outer, Strict.seg_op(D1.inert.node(rest))), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k,
                        t, l, c}), D1.inert.ok(rest), e))),
                    inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path, outer,
                      Strict.seg_op(D1.inert.node(rest)), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}),
                        D1.inert.ok(rest), e))),
                    inert.strict.walk(rest, name, path, outer, hot, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l,
                      c}), D1.inert.ok(rest), e)))
                case Tree.Group{x, y, z}:
                  inert.strict.gen(k, rest, name, path, outer, hot,
                    inert.strict.past(rest, name, path, outer, z => Bool.or(outer, z), inert.strict.walk(rest, name,
                      path, outer,
                      Bool.or(outer, Strict.seg_op(D1.inert.node(rest))), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k,
                        t, l, c}), D1.inert.ok(rest), e))),
                    inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path, outer,
                      Strict.seg_op(D1.inert.node(rest)), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}),
                        D1.inert.ok(rest), e))),
                    inert.strict.walk(rest, name, path, outer, hot, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l,
                      c}), D1.inert.ok(rest), e)))
                case Tree.Stmt{x, y, z}:
                  inert.strict.gen(k, rest, name, path, outer, hot,
                    inert.strict.past(rest, name, path, outer, z => Bool.or(outer, z), inert.strict.walk(rest, name,
                      path, outer,
                      Bool.or(outer, Strict.seg_op(D1.inert.node(rest))), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k,
                        t, l, c}), D1.inert.ok(rest), e))),
                    inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path, outer,
                      Strict.seg_op(D1.inert.node(rest)), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}),
                        D1.inert.ok(rest), e))),
                    inert.strict.walk(rest, name, path, outer, hot, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l,
                      c}), D1.inert.ok(rest), e)))
                case Tree.NNil{}:
                  inert.strict.gen(k, rest, name, path, outer, hot,
                    inert.strict.past(rest, name, path, outer, z => Bool.or(outer, z), inert.strict.walk(rest, name,
                      path, outer,
                      Bool.or(outer, Strict.seg_op(D1.inert.node(rest))), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k,
                        t, l, c}), D1.inert.ok(rest), e))),
                    inert.strict.past(rest, name, path, outer, z => z, inert.strict.walk(rest, name, path, outer,
                      Strict.seg_op(D1.inert.node(rest)), en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l, c}),
                        D1.inert.ok(rest), e))),
                    inert.strict.walk(rest, name, path, outer, hot, en, M1.inert.and_r(D1.inert.fits(Lex.Tok{k, t, l,
                      c}), D1.inert.ok(rest), e)))
        case Tree.Group{o, +kids, cl}:
          inert.cat2(Strict.walk(D1.inert.node(kids), name, path, hot, Bool.or(hot,
            Strict.seg_op(D1.inert.node(kids)))),
            Strict.walk(kids, name, path, hot, Bool.or(hot, Strict.seg_op(kids))),
            Strict.walk(D1.inert.node(rest), name, path, outer, hot), Strict.walk(rest, name, path, outer, hot),
            inert.strict.past(kids, name, path, hot, z => Bool.or(hot, z), inert.strict.walk(kids, name, path, hot,
              Bool.or(hot, Strict.seg_op(D1.inert.node(kids))), en, M1.inert.and_l(D1.inert.ok(kids),
                D1.inert.ok(rest), e))),
            inert.strict.walk(rest, name, path, outer, hot, en, M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(rest),
              e)))
        case Tree.Stmt{sk, +kids, +body}:
          +es = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
          inert.cat3(Strict.walk(D1.inert.node(kids), name, path, False{}, Strict.seg_op(D1.inert.node(kids))),
            Strict.walk(kids, name, path, False{}, Strict.seg_op(kids)),
            Strict.walk(D1.inert.node(body), name, path, False{}, False{}), Strict.walk(body, name, path, False{},
              False{}),
            Strict.walk(D1.inert.node(rest), name, path, outer, hot), Strict.walk(rest, name, path, outer, hot),
            inert.strict.past(kids, name, path, False{}, z => z, inert.strict.walk(kids, name, path, False{},
              Strict.seg_op(D1.inert.node(kids)), en, M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es))),
            inert.strict.walk(body, name, path, False{}, False{}, en, M1.inert.and_r(D1.inert.ok(kids),
              D1.inert.ok(body), es)),
            inert.strict.walk(rest, name, path, outer, hot, en,
              M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)))
        case Tree.NNil{}: inert.strict.walk(rest, name, path, outer, hot, en, e)
        case Tree.NCons{x, y}:
          inert.strict.walk(rest, name, path, outer, hot, en, M1.inert.and_r(D1.inert.ok(Tree.NCons{x, y}),
            D1.inert.ok(rest),
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
      +lst = inert.strict.stop(Calls.exempt(path, D1.inert.node(sig)), Strict.walk(D1.inert.node(body), name, path,
        False{}, False{}))
      %inert.exempt(path, sig) : {Strict.check.go(inert.defs(rest), path, lst <> acc) == Strict.check.go(rest, path,
        inert.strict.stop(_, Strict.walk(body, name, path, False{}, False{})) <> acc) : List<&2, F.Finding>}
      %inert.strict.walk(body, name, path, False{}, False{}, inert.dok.head(name, sig, body, rest, e),
        inert.dok.body(name, sig, body, rest, e)) : {Strict.check.go(inert.defs(rest), path, lst <> acc)
          == Strict.check.go(rest, path, inert.strict.stop(Calls.exempt(path, D1.inert.node(sig)), _) <> acc)
          : List<&2, F.Finding>}
      inert.strict.go(rest, path, lst <> acc, inert.dok.rest(name, sig, body, rest, e))

def Laws.inert_strict(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, ok, ok2, e):
  M1.inert.via(Tree.Node, z => Strict.check.go(Calls.defs(z), path, []), tree, tree2, D1.inert.node(tree),
    D1.inert.node(tree2),
    inert.lift(z => Strict.check.go(z, path, []), tree, inert.strict.go(Calls.defs(tree), path, [], inert.dok.of(tree,
      ok))),
    inert.lift(z => Strict.check.go(z, path, []), tree2, inert.strict.go(Calls.defs(tree2), path, [],
      inert.dok.of(tree2, ok2))), e)

# Inert text, the other rules (laws/CodeRulesIgnoreCommentsAndStrings.bend). The same reading as above,
# for the rules over a file's defs that it did not reach.

# the rest of a chain as the lexer makes it fits
law inert.ok_t:
  for +h: Tree.Node
  for +t: Tree.Node
  for e: {D1.inert.ok(Tree.NCons{h, t}) == True{} : Bool}
  {D1.inert.ok(t) == True{} : Bool}

def inert.ok_t(h, t, e):
  M1.inert.and_r(D1.inert.ok(h), D1.inert.ok(t), e)

# the head of a chain as the lexer makes it fits
law inert.ok_h:
  for +h: Tree.Node
  for +t: Tree.Node
  for e: {D1.inert.ok(Tree.NCons{h, t}) == True{} : Bool}
  {D1.inert.ok(h) == True{} : Bool}

def inert.ok_h(h, t, e):
  M1.inert.and_l(D1.inert.ok(h), D1.inert.ok(t), e)

# an and with False on its right is False
law inert.and_false:
  for x: Bool
  {Bool.and(x, False{}) == False{} : Bool}

def inert.and_false(x):
  match x:
    case True{}: {==}
    case False{}: {==}

# a stop whose test and walk read as they did
law inert.stop:
  for -b1: Bool
  for -b2: Bool
  for -w1: List<&2, F.Finding>
  for -w2: List<&2, F.Finding>
  for eb: {b1 == b2 : Bool}
  for ew: {w1 == w2 : List<&2, F.Finding>}
  {Lazy.stop(List<&2, F.Finding>, b1, [], _u => w1) == Lazy.stop(List<&2, F.Finding>, b2, [], _v => w2)
    : List<&2, F.Finding>}

def inert.stop(b1, _b2, w1, w2, eb, ew):
  %eb : {Lazy.stop(List<&2, F.Finding>, b1, [], _u => w1) == Lazy.stop(List<&2, F.Finding>, _, [], _v => w2)
    : List<&2, F.Finding>}
  %ew : {Lazy.stop(List<&2, F.Finding>, b1, [], _u => w1) == Lazy.stop(List<&2, F.Finding>, b1, [], _v => _)
    : List<&2, F.Finding>}
  {==}

# a self-calling def's gate, read that way: it calls itself and is not exempt
# as it did
law inert.gate:
  for +path: String
  for +name: String
  for +sig: Tree.Node
  for +body: Tree.Node
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for +eb: {D1.inert.ok(body) == True{} : Bool}
  {Bool.not(Bool.and(Calls.calls(D1.inert.node(body), name), Bool.not(Calls.exempt(path, D1.inert.node(sig)))))
    == Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))) : Bool}

def inert.gate(path, name, sig, body, en, eb):
  +lhs = Bool.not(Bool.and(Calls.calls(D1.inert.node(body), name), Bool.not(Calls.exempt(path,
    D1.inert.node(sig)))))
  %inert.calls(body, name, en, eb) : {lhs == Bool.not(Bool.and(_, Bool.not(Calls.exempt(path, sig)))) : Bool}
  %inert.exempt(path, sig) : {lhs == Bool.not(Bool.and(Calls.calls(D1.inert.node(body), name), Bool.not(_)))
    : Bool}
  {==}

# an unmarked char and a marked one never compare EQ
law inert.differ_r:
  for c: Cmp
  for +x: U32
  for +y: U32
  for ec: {U32.cmp(x, y) == c : Cmp}
  for ex: {D1.inert.mark(Chr{x}) == False{} : Bool}
  for ey: {D1.inert.mark(Chr{y}) == True{} : Bool}
  {Cmp.is_eq(c) == False{} : Bool}

def inert.differ_r(c, x, y, ec, ex, ey):
  match c:
    case LT{}: {==}
    case GT{}: {==}
    case EQ{}:
      +mx = Equal.trans(Bool, D1.inert.mark(Chr{x}), D1.inert.mark(Chr{y}), True{},
        Equal.cong(U32, Bool, z => D1.inert.mark(Chr{z}), x, y, M1.inert.u32_eq(x, y, ec)), ey)
      Empty.absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, M1.inert.false_true(Equal.trans(Bool, False{},
        D1.inert.mark(Chr{x}), True{}, Equal.sym(Bool, D1.inert.mark(Chr{x}), False{}, ex), mx)))

# a text with an unmarked first char is never equal to one with a marked one
law inert.neq.con_r:
  for h: Char
  for r: String
  for y: Char
  for ys: String
  for ex: {D1.inert.mark(h) == False{} : Bool}
  for et: {D1.inert.mark(y) == True{} : Bool}
  {String.eq(SCon{h, r}, SCon{y, ys}) == False{} : Bool}

def inert.neq.con_r(h, r, y, ys, ex, et):
  match h y:
    case Chr{+a} Chr{+b}:
      M1.inert.fin_false(U32.cmp(a, b), r, ys, inert.differ_r(U32.cmp(a, b), a, b, {==}, ex, et))

# an unmarked text is never equal to a marked one
law inert.neq_r:
  for x: String
  for t: String
  for ex: {D1.inert.marked(x) == False{} : Bool}
  for et: {D1.inert.marked(t) == True{} : Bool}
  {String.eq(x, t) == False{} : Bool}

def inert.neq_r(x, t, ex, et):
  match x t:
    case x SNil{}: Empty.absurd({String.eq(x, SNil{}) == False{} : Bool}, M1.inert.false_true(et))
    case SNil{} SCon{y, ys}: {==}
    case SCon{h, r} SCon{y, ys}: inert.neq.con_r(h, r, y, ys, ex, et)

# an unmarked text compares with a token's text read that way as it did
law inert.eq_keep_r:
  for b: Bool
  for +t: String
  for +x: String
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +ex: {D1.inert.marked(x) == False{} : Bool}
  {String.eq(x, D1.inert.keep(b, t)) == String.eq(x, t) : Bool}

def inert.eq_keep_r(b, t, x, ef, ex):
  match b:
    case False{}: {==}
    case True{}:
      Equal.trans(Bool, String.eq(x, D1.inert.cut(t)), False{}, String.eq(x, t),
        inert.neq_r(x, D1.inert.cut(t), ex, M1.inert.cut_marked(t, ef)),
        Equal.sym(Bool, String.eq(x, t), False{}, inert.neq_r(x, t, ex, ef)))

# no text of the list starts with `"` or `#`
def inert.plains(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}: True{}
    case Con{h, t}: Bool.and(Bool.not(D1.inert.marked(h)), inert.plains(t))

# a list of unmarked texts holds a token's text read that way as it did
law inert.contains_keep:
  for xs: List<&2, String>
  for +b: Bool
  for +t: String
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +ep: {inert.plains(xs) == True{} : Bool}
  {List.contains(~String, ~String.eq, xs, D1.inert.keep(b, t)) == List.contains(~String, ~String.eq, xs, t) : Bool}

def inert.contains_keep(xs, b, t, ef, ep):
  match xs:
    case Nil{}: {==}
    case Con{+h, +r}:
      +kt = D1.inert.keep(b, t)
      inert.if2(String.eq(h, kt), String.eq(h, t), List.contains(~String, ~String.eq, r, kt),
        List.contains(~String, ~String.eq, r, t),
        inert.eq_keep_r(b, t, h, ef, inert.not_true(D1.inert.marked(h), M1.inert.and_l(Bool.not(D1.inert.marked(h)),
          inert.plains(r), ep))),
        inert.contains_keep(r, b, t, ef, M1.inert.and_r(Bool.not(D1.inert.marked(h)), inert.plains(r), ep)))

# table
# -----

# a chain read that way is one number as it was
law inert.table.literal:
  for nn: Tree.Node
  {Table.literal(D1.inert.node(nn)) == Table.literal(nn) : Bool}

def inert.table.literal(nn):
  match nn:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}: {==}
                case Lex.TUpper{}: {==}
                case Lex.TDotted{}: {==}
                case Lex.TWild{}: {==}
                case Lex.TKey{}: {==}
                case Lex.TNum{}:
                  match r:
                    case Tree.NNil{}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NCons{x, y}: {==}
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
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a chain read that way is one number as it was
law inert.table.lone_num:
  for nn: Tree.Node
  {Table.lone_num(D1.inert.node(nn)) == Table.lone_num(nn) : Bool}

def inert.table.lone_num(nn):
  match nn:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}: {==}
                case Lex.TUpper{}: {==}
                case Lex.TDotted{}: {==}
                case Lex.TWild{}: {==}
                case Lex.TKey{}: {==}
                case Lex.TNum{}:
                  match r:
                    case Tree.NNil{}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NCons{x, y}: {==}
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
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a chain read that way holds a top-level token of an unmarked text as it did
law inert.table.top_has:
  for nn: Tree.Node
  for +want: String
  for +ew: {D1.inert.marked(want) == False{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Table.top_has(D1.inert.node(nn), want) == Table.top_has(nn, want) : Bool}

def inert.table.top_has(nn, want, ew, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              inert.or2(String.eq(D1.inert.keep(D1.inert.blanks(k), t), want), String.eq(t, want),
                Table.top_has(D1.inert.node(rest), want), Table.top_has(rest, want),
                M1.inert.eq_keep(D1.inert.blanks(k), t, want, inert.ok_h(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e), ew),
                inert.table.top_has(rest, want, ew, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e)))
        case Tree.Group{o, gk, cl}: inert.table.top_has(rest, want, ew, inert.ok_t(Tree.Group{o, gk, cl}, rest, e))
        case Tree.Stmt{sk, sks, sb}: inert.table.top_has(rest, want, ew, inert.ok_t(Tree.Stmt{sk, sks, sb}, rest, e))
        case Tree.NNil{}: inert.table.top_has(rest, want, ew, e)
        case Tree.NCons{x, y}: inert.table.top_has(rest, want, ew, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# an operator then a number, the size after it read as it was
law inert.table.sized_more:
  for +op: String
  for +r2: Tree.Node
  for ih: {Table.array_sized(D1.inert.node(r2)) == Table.array_sized(r2) : Bool}
  {Bool.or(Bool.or(String.eq(op, "*"), String.eq(op, "^")), Table.array_sized(D1.inert.node(r2)))
    == Bool.or(Bool.or(String.eq(op, "*"), String.eq(op, "^")), Table.array_sized(r2)) : Bool}

def inert.table.sized_more(op, r2, ih):
  Equal.cong(Bool, Bool, z => Bool.or(Bool.or(String.eq(op, "*"), String.eq(op, "^")), z),
    Table.array_sized(D1.inert.node(r2)), Table.array_sized(r2), ih)

# a chain read that way is sized by a number as it was: only an operator's
# text is read
law inert.table.array_sized:
  for nn: Tree.Node
  {Table.array_sized(D1.inert.node(nn)) == Table.array_sized(nn) : Bool}

def inert.table.array_sized(nn):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, op, l, c}:
              match k:
                case Lex.TName{}: inert.table.array_sized(rest)
                case Lex.TUpper{}: inert.table.array_sized(rest)
                case Lex.TDotted{}: inert.table.array_sized(rest)
                case Lex.TWild{}: inert.table.array_sized(rest)
                case Lex.TKey{}: inert.table.array_sized(rest)
                case Lex.TNum{}: inert.table.array_sized(rest)
                case Lex.TStr{}: inert.table.array_sized(rest)
                case Lex.TChar{}: inert.table.array_sized(rest)
                case Lex.TComment{}: inert.table.array_sized(rest)
                case Lex.TSpace{}: inert.table.array_sized(rest)
                case Lex.TNewline{}: inert.table.array_sized(rest)
                case Lex.TOp{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Leaf{tok2}:
                          match tok2:
                            case Lex.Tok{k2, t2, l2, c2}:
                              match k2:
                                case Lex.TName{}: inert.table.array_sized(rest)
                                case Lex.TUpper{}: inert.table.array_sized(rest)
                                case Lex.TDotted{}: inert.table.array_sized(rest)
                                case Lex.TWild{}: inert.table.array_sized(rest)
                                case Lex.TKey{}: inert.table.array_sized(rest)
                                case Lex.TNum{}: inert.table.sized_more(op, r2, inert.table.array_sized(r2))
                                case Lex.TStr{}: inert.table.array_sized(rest)
                                case Lex.TChar{}: inert.table.array_sized(rest)
                                case Lex.TComment{}: inert.table.array_sized(rest)
                                case Lex.TSpace{}: inert.table.array_sized(rest)
                                case Lex.TNewline{}: inert.table.array_sized(rest)
                                case Lex.TOp{}: inert.table.array_sized(rest)
                                case Lex.TColon{}: inert.table.array_sized(rest)
                                case Lex.TEq{}: inert.table.array_sized(rest)
                                case Lex.TBind{}: inert.table.array_sized(rest)
                                case Lex.TArrow{}: inert.table.array_sized(rest)
                                case Lex.TLam{}: inert.table.array_sized(rest)
                                case Lex.TAll{}: inert.table.array_sized(rest)
                                case Lex.TAmp{}: inert.table.array_sized(rest)
                                case Lex.TOpen{}: inert.table.array_sized(rest)
                                case Lex.TClose{}: inert.table.array_sized(rest)
                                case Lex.TComma{}: inert.table.array_sized(rest)
                        case Tree.Group{x, y, z}: inert.table.array_sized(rest)
                        case Tree.Stmt{x, y, z}: inert.table.array_sized(rest)
                        case Tree.NNil{}: inert.table.array_sized(rest)
                        case Tree.NCons{x, y}: inert.table.array_sized(rest)
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TColon{}: inert.table.array_sized(rest)
                case Lex.TEq{}: inert.table.array_sized(rest)
                case Lex.TBind{}: inert.table.array_sized(rest)
                case Lex.TArrow{}: inert.table.array_sized(rest)
                case Lex.TLam{}: inert.table.array_sized(rest)
                case Lex.TAll{}: inert.table.array_sized(rest)
                case Lex.TAmp{}: inert.table.array_sized(rest)
                case Lex.TOpen{}: inert.table.array_sized(rest)
                case Lex.TClose{}: inert.table.array_sized(rest)
                case Lex.TComma{}: inert.table.array_sized(rest)
        case Tree.Group{o, gk, cl}: inert.table.array_sized(rest)
        case Tree.Stmt{sk, sks, sb}: inert.table.array_sized(rest)
        case Tree.NNil{}: inert.table.array_sized(rest)
        case Tree.NCons{x, y}: inert.table.array_sized(rest)
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# arguments read that way end with one number as they did
law inert.table.range_count:
  for as: List<&2, Tree.Node>
  {Table.range_count(inert.nodes(as)) == Table.range_count(as) : Bool}

def inert.table.range_count(as):
  match as:
    case Nil{}: {==}
    case Con{h, +rest}:
      match rest:
        case Nil{}: inert.table.lone_num(h)
        case Con{x, y}: inert.table.range_count(rest)

# what a constant-size constructor reads: its name against the three, its
# count argument and its last
def inert.table.bparts(+r1: Bool, r2: Bool, +r3: Bool, ln: Bool, rc: Bool) -> Bool:
  Bool.or(Bool.and(Bool.or(r1, r2), ln), Bool.and(r3, rc))

# a name then its group, both read that way: a constant-size constructor as
# it was
law inert.table.built_call:
  for +b: Bool
  for +t: String
  for +kids: Tree.Node
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  {Table.built_call(D1.inert.keep(b, t), D1.inert.node(kids)) == Table.built_call(t, kids) : Bool}

def inert.table.built_call(b, t, kids, ef):
  +kt = D1.inert.keep(b, t)
  +lhs = Table.built_call(kt, D1.inert.node(kids))
  +aa = Calls.args(kids)
  %M1.inert.eq_keep(b, t, "List.replicate", ef, {==}) : {lhs == inert.table.bparts(_, String.eq(t, "Array.new"),
    String.eq(t, "List.range"), Table.lone_num(Calls.arg(aa, 2n)), Table.range_count(aa)) : Bool}
  %M1.inert.eq_keep(b, t, "Array.new", ef, {==}) : {lhs == inert.table.bparts(String.eq(kt, "List.replicate"), _,
    String.eq(t, "List.range"), Table.lone_num(Calls.arg(aa, 2n)), Table.range_count(aa)) : Bool}
  %M1.inert.eq_keep(b, t, "List.range", ef, {==}) : {lhs == inert.table.bparts(String.eq(kt, "List.replicate"),
    String.eq(kt, "Array.new"), _, Table.lone_num(Calls.arg(aa, 2n)), Table.range_count(aa)) : Bool}
  %inert.table.lone_num(Calls.arg(aa, 2n)) : {lhs == inert.table.bparts(String.eq(kt, "List.replicate"),
    String.eq(kt, "Array.new"), String.eq(kt, "List.range"), _, Table.range_count(aa)) : Bool}
  %inert.arg(aa, 2n) : {lhs == inert.table.bparts(String.eq(kt, "List.replicate"), String.eq(kt, "Array.new"),
    String.eq(kt, "List.range"), Table.lone_num(_), Table.range_count(aa)) : Bool}
  %inert.table.range_count(aa) : {lhs == inert.table.bparts(String.eq(kt, "List.replicate"),
    String.eq(kt, "Array.new"), String.eq(kt, "List.range"), Table.lone_num(Calls.arg(inert.nodes(aa), 2n)), _)
    : Bool}
  %inert.args(kids) : {lhs == inert.table.bparts(String.eq(kt, "List.replicate"), String.eq(kt, "Array.new"),
    String.eq(kt, "List.range"), Table.lone_num(Calls.arg(_, 2n)), Table.range_count(_)) : Bool}
  {==}

# a list literal or sized array read that way, by its kids
def inert.table.lparts(+o: String, h1: Bool, h2: Bool, az: Bool) -> Bool:
  Bool.and(String.eq(o, "["), Bool.or(h1, Bool.and(h2, az)))

# a bracket group read that way is a list literal or a sized array as it was
law inert.table.bracket:
  for +o: String
  for +kids: Tree.Node
  for +e: {D1.inert.ok(kids) == True{} : Bool}
  {inert.table.lparts(o, Table.top_has(D1.inert.node(kids), ","), Table.top_has(D1.inert.node(kids), ":"),
    Table.array_sized(D1.inert.node(kids)))
    == inert.table.lparts(o, Table.top_has(kids, ","), Table.top_has(kids, ":"), Table.array_sized(kids)) : Bool}

def inert.table.bracket(o, kids, e):
  +lhs = inert.table.lparts(o, Table.top_has(D1.inert.node(kids), ","), Table.top_has(D1.inert.node(kids), ":"),
    Table.array_sized(D1.inert.node(kids)))
  %inert.table.top_has(kids, ",", {==}, e) : {lhs == inert.table.lparts(o, _, Table.top_has(kids, ":"),
    Table.array_sized(kids)) : Bool}
  %inert.table.top_has(kids, ":", {==}, e) : {lhs == inert.table.lparts(o, Table.top_has(D1.inert.node(kids), ","),
    _, Table.array_sized(kids)) : Bool}
  %inert.table.array_sized(kids) : {lhs == inert.table.lparts(o, Table.top_has(D1.inert.node(kids), ","),
    Table.top_has(D1.inert.node(kids), ":"), _) : Bool}
  {==}

# a `(` group after a name, both read that way: a constant-size constructor
# as it was
law inert.table.call_built:
  for +o: String
  for b: Bool
  for +t: String
  for +kids: Tree.Node
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  {Bool.and(String.eq(o, "("), Table.built_call(D1.inert.keep(b, t), D1.inert.node(kids)))
    == Bool.and(String.eq(o, "("), Table.built_call(t, kids)) : Bool}

def inert.table.call_built(o, b, t, kids, ef):
  Equal.cong(Bool, Bool, z => Bool.and(String.eq(o, "("), z), Table.built_call(D1.inert.keep(b, t),
    D1.inert.node(kids)), Table.built_call(t, kids), inert.table.built_call(b, t, kids, ef))

# a chain read that way is a fixed table written inline as it was
law inert.table.built:
  for nn: Tree.Node
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Table.built(D1.inert.node(nn)) == Table.built(nn) : Bool}

def inert.table.built(nn, e):
  match nn:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Group{o, +kids, cl}:
          match o:
            case Lex.Tok{ok, +ot, ol, oc}:
              match r:
                case Tree.NNil{}:
                  inert.table.bracket(ot, kids, M1.inert.and_l(D1.inert.ok(kids), True{}, e))
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NCons{x, y}: {==}
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match r:
                case Tree.NCons{g, +r2}:
                  match g:
                    case Tree.Group{go, +gkids, gcl}:
                      match go:
                        case Lex.Tok{gk, +o, gl, gc}:
                          match r2:
                            case Tree.NNil{}:
                              inert.table.call_built(o, D1.inert.blanks(k), t, gkids,
                                inert.ok_h(Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc},
                                  gkids, gcl}, Tree.NNil{}}, e))
                            case Tree.Leaf{x}: {==}
                            case Tree.Group{x, y, z}: {==}
                            case Tree.Stmt{x, y, z}: {==}
                            case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                    case Tree.NCons{x, y}: {==}
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NNil{}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a chain read that way is a call `name()` of the name it was: only a name's
# text is read
law inert.table.call_name:
  for nn: Tree.Node
  {Table.call_name(D1.inert.node(nn)) == Table.call_name(nn) : String}

def inert.table.call_name(nn):
  match nn:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, gk, gc}:
                          match go:
                            case Lex.Tok{a1, a2, a3, a4}:
                              match r2:
                                case Tree.NNil{}: {==}
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
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
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a chain read that way is the one name it was
law inert.table.lone_name:
  for nn: Tree.Node
  {Table.lone_name(D1.inert.node(nn)) == Table.lone_name(nn) : String}

def inert.table.lone_name(nn):
  match nn:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}:
                  match r:
                    case Tree.NNil{}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NCons{x, y}: {==}
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
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a chain read that way is the one name use it was
law inert.table.lone_key:
  for nn: Tree.Node
  {Table.lone_key(D1.inert.node(nn)) == Table.lone_key(nn) : String}

def inert.table.lone_key(nn):
  match nn:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}:
                  match r:
                    case Tree.NNil{}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NCons{x, y}: {==}
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
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# what owns reads of a list argument: inline, called, named, used
def inert.table.oparts(bt: Bool, +called: String, +named: String, +used: String, +fixed: List<&2, String>) -> Bool:
  Bool.or(bt, Bool.or(
    Bool.and(Bool.not(String.is_empty(named)),
      Bool.or(List.contains(~String, ~String.eq, fixed, named), List.contains(~String, ~String.eq, fixed, used))),
    Bool.and(Bool.not(String.is_empty(called)), List.contains(~String, ~String.eq, fixed, called))))

# a list argument read that way is a fixed table as it was
law inert.table.owns:
  for +nn: Tree.Node
  for +fixed: List<&2, String>
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Table.owns(D1.inert.node(nn), fixed) == Table.owns(nn, fixed) : Bool}

def inert.table.owns(nn, fixed, e):
  +ii = D1.inert.node(nn)
  +lhs = Table.owns(ii, fixed)
  %inert.table.built(nn, e) : {lhs == inert.table.oparts(_, Table.call_name(nn), Table.lone_name(nn),
    Table.lone_key(nn), fixed) : Bool}
  %inert.table.call_name(nn) : {lhs == inert.table.oparts(Table.built(ii), _, Table.lone_name(nn), Table.lone_key(nn),
    fixed) : Bool}
  %inert.table.lone_name(nn) : {lhs == inert.table.oparts(Table.built(ii), Table.call_name(ii), _, Table.lone_key(nn),
    fixed) : Bool}
  %inert.table.lone_key(nn) : {lhs == inert.table.oparts(Table.built(ii), Table.call_name(ii), Table.lone_name(ii), _,
    fixed) : Bool}
  {==}

# the name a statement read that way binds is the one it bound: only a
# name's text is read
law inert.table.bind_name:
  for nn: Tree.Node
  for +seen: Bool
  for +bad: Bool
  for +nm: String
  {Table.bind_name(D1.inert.node(nn), seen, bad, nm) == Table.bind_name(nn, seen, bad, nm) : String}

def inert.table.bind_name(nn, seen, bad, nm):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, l, c}:
              match k:
                case Lex.TName{}: inert.table.bind_name(rest, True{}, Bool.or(bad, seen), t)
                case Lex.TUpper{}: inert.table.bind_name(rest, seen, True{}, nm)
                case Lex.TDotted{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TWild{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TKey{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TNum{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TStr{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TChar{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TComment{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TSpace{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TNewline{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TOp{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TColon{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TEq{}: {==}
                case Lex.TBind{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TArrow{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TLam{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TAll{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TAmp{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TOpen{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TClose{}: inert.table.bind_name(rest, seen, bad, nm)
                case Lex.TComma{}: inert.table.bind_name(rest, seen, bad, nm)
        case Tree.Group{o, gk, cl}: inert.table.bind_name(rest, seen, bad, nm)
        case Tree.Stmt{sk, sks, sb}: inert.table.bind_name(rest, seen, bad, nm)
        case Tree.NNil{}: inert.table.bind_name(rest, seen, bad, nm)
        case Tree.NCons{x, y}: inert.table.bind_name(rest, seen, bad, nm)
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# the right-hand side of a statement read that way is the one it had, read
# that way
law inert.table.bind_rhs:
  for nn: Tree.Node
  {Table.bind_rhs(D1.inert.node(nn)) == D1.inert.node(Table.bind_rhs(nn)) : Tree.Node}

def inert.table.bind_rhs(nn):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}: inert.table.bind_rhs(rest)
                case Lex.TUpper{}: inert.table.bind_rhs(rest)
                case Lex.TDotted{}: inert.table.bind_rhs(rest)
                case Lex.TWild{}: inert.table.bind_rhs(rest)
                case Lex.TKey{}: inert.table.bind_rhs(rest)
                case Lex.TNum{}: inert.table.bind_rhs(rest)
                case Lex.TStr{}: inert.table.bind_rhs(rest)
                case Lex.TChar{}: inert.table.bind_rhs(rest)
                case Lex.TComment{}: inert.table.bind_rhs(rest)
                case Lex.TSpace{}: inert.table.bind_rhs(rest)
                case Lex.TNewline{}: inert.table.bind_rhs(rest)
                case Lex.TOp{}: inert.table.bind_rhs(rest)
                case Lex.TColon{}: inert.table.bind_rhs(rest)
                case Lex.TEq{}: {==}
                case Lex.TBind{}: inert.table.bind_rhs(rest)
                case Lex.TArrow{}: inert.table.bind_rhs(rest)
                case Lex.TLam{}: inert.table.bind_rhs(rest)
                case Lex.TAll{}: inert.table.bind_rhs(rest)
                case Lex.TAmp{}: inert.table.bind_rhs(rest)
                case Lex.TOpen{}: inert.table.bind_rhs(rest)
                case Lex.TClose{}: inert.table.bind_rhs(rest)
                case Lex.TComma{}: inert.table.bind_rhs(rest)
        case Tree.Group{o, gk, cl}: inert.table.bind_rhs(rest)
        case Tree.Stmt{sk, sks, sb}: inert.table.bind_rhs(rest)
        case Tree.NNil{}: inert.table.bind_rhs(rest)
        case Tree.NCons{x, y}: inert.table.bind_rhs(rest)
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# the right-hand side of a statement as the lexer makes it fits
law inert.table.ok_rhs:
  for nn: Tree.Node
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {D1.inert.ok(Table.bind_rhs(nn)) == True{} : Bool}

def inert.table.ok_rhs(nn, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, +l, +c}:
              match k:
                case Lex.TName{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, rest, e))
                case Lex.TUpper{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}}, rest, e))
                case Lex.TDotted{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}}, rest, e))
                case Lex.TWild{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TWild{}, t, l, c}}, rest, e))
                case Lex.TKey{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TKey{}, t, l, c}}, rest, e))
                case Lex.TNum{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}}, rest, e))
                case Lex.TStr{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TStr{}, t, l, c}}, rest, e))
                case Lex.TChar{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TChar{}, t, l, c}}, rest, e))
                case Lex.TComment{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TComment{}, t, l, c}}, rest, e))
                case Lex.TSpace{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TSpace{}, t, l, c}}, rest, e))
                case Lex.TNewline{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TNewline{}, t, l, c}}, rest, e))
                case Lex.TOp{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOp{}, t, l, c}}, rest, e))
                case Lex.TColon{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}}, rest, e))
                case Lex.TEq{}:
                  inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest, e)
                case Lex.TBind{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}}, rest, e))
                case Lex.TArrow{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TArrow{}, t, l, c}}, rest, e))
                case Lex.TLam{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}}, rest, e))
                case Lex.TAll{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TAll{}, t, l, c}}, rest, e))
                case Lex.TAmp{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TAmp{}, t, l, c}}, rest, e))
                case Lex.TOpen{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOpen{}, t, l, c}}, rest, e))
                case Lex.TClose{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TClose{}, t, l, c}}, rest, e))
                case Lex.TComma{}:
                  inert.table.ok_rhs(rest,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, rest, e))
        case Tree.Group{o, gk, cl}: inert.table.ok_rhs(rest, inert.ok_t(Tree.Group{o, gk, cl}, rest, e))
        case Tree.Stmt{sk, sks, sb}: inert.table.ok_rhs(rest, inert.ok_t(Tree.Stmt{sk, sks, sb}, rest, e))
        case Tree.NNil{}: inert.table.ok_rhs(rest, e)
        case Tree.NCons{x, y}: inert.table.ok_rhs(rest, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# the names a let read that way leaves in scope are the ones it left
law inert.table.next:
  for +kids: Tree.Node
  for +live: List<&2, String>
  for +e: {D1.inert.ok(kids) == True{} : Bool}
  {Table.rebind(Table.bind_name(D1.inert.node(kids), False{}, False{}, ""),
    Table.built(Table.bind_rhs(D1.inert.node(kids))), live)
    == Table.rebind(Table.bind_name(kids, False{}, False{}, ""), Table.built(Table.bind_rhs(kids)), live)
    : List<&2, String>}

def inert.table.next(kids, live, e):
  +lhs = Table.rebind(Table.bind_name(D1.inert.node(kids), False{}, False{}, ""),
    Table.built(Table.bind_rhs(D1.inert.node(kids))), live)
  %inert.table.bind_name(kids, False{}, False{}, "") : {lhs == Table.rebind(_, Table.built(Table.bind_rhs(kids)), live)
    : List<&2, String>}
  %inert.table.built(Table.bind_rhs(kids), inert.table.ok_rhs(kids, e)) : {lhs
    == Table.rebind(Table.bind_name(D1.inert.node(kids), False{}, False{}, ""), _, live) : List<&2, String>}
  %inert.table.bind_rhs(kids) : {lhs == Table.rebind(Table.bind_name(D1.inert.node(kids), False{}, False{}, ""),
    Table.built(_), live) : List<&2, String>}
  {==}

# the keys of the name uses under a chain read that way are the ones it had
law inert.table.lets:
  for nn: Tree.Node
  for +live: List<&2, String>
  for +acc: List<&2, String>
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Table.lets(D1.inert.node(nn), live, acc) == Table.lets(nn, live, acc) : List<&2, String>}

def inert.table.lets(nn, live, acc, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{+sk, +kids, +body}:
          +es = inert.ok_h(Tree.Stmt{sk, kids, body}, rest, e)
          +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es)
          +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es)
          +er = inert.ok_t(Tree.Stmt{sk, kids, body}, rest, e)
          +nx = Table.rebind(Table.bind_name(D1.inert.node(kids), False{}, False{}, ""),
            Table.built(Table.bind_rhs(D1.inert.node(kids))), live)
          +l1 = Table.lets(D1.inert.node(kids), live, acc)
          +l2 = Table.lets(D1.inert.node(body), live, l1)
          +lhs = Table.lets(D1.inert.node(rest), nx, l2)
          %inert.table.lets(kids, live, acc, ek) : {lhs == Table.lets(rest, Table.rebind(Table.bind_name(kids, False{},
            False{}, ""), Table.built(Table.bind_rhs(kids)), live), Table.lets(body, live, _)) : List<&2, String>}
          %inert.table.lets(body, live, l1, eb) : {lhs == Table.lets(rest, Table.rebind(Table.bind_name(kids, False{},
            False{}, ""), Table.built(Table.bind_rhs(kids)), live), _) : List<&2, String>}
          %inert.table.next(kids, live, ek) : {lhs == Table.lets(rest, _, l2) : List<&2, String>}
          inert.table.lets(rest, nx, l2, er)
        case Tree.Group{+o, +kids, +cl}:
          +l1 = Table.lets(D1.inert.node(kids), live, acc)
          %inert.table.lets(kids, live, acc, inert.ok_h(Tree.Group{o, kids, cl}, rest, e)) : {Table.lets(
            D1.inert.node(rest), live, l1) == Table.lets(rest, live, _) : List<&2, String>}
          inert.table.lets(rest, live, l1, inert.ok_t(Tree.Group{o, kids, cl}, rest, e))
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, +l, +c}:
              match k:
                case Lex.TName{}:
                  inert.table.lets(rest, live, Table.use_at(t, l, c, live, acc),
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, rest, e))
                case Lex.TUpper{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}}, rest, e))
                case Lex.TDotted{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}}, rest, e))
                case Lex.TWild{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TWild{}, t, l, c}}, rest, e))
                case Lex.TKey{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TKey{}, t, l, c}}, rest, e))
                case Lex.TNum{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}}, rest, e))
                case Lex.TStr{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TStr{}, t, l, c}}, rest, e))
                case Lex.TChar{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TChar{}, t, l, c}}, rest, e))
                case Lex.TComment{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TComment{}, t, l, c}}, rest, e))
                case Lex.TSpace{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TSpace{}, t, l, c}}, rest, e))
                case Lex.TNewline{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TNewline{}, t, l, c}}, rest, e))
                case Lex.TOp{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOp{}, t, l, c}}, rest, e))
                case Lex.TColon{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}}, rest, e))
                case Lex.TEq{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest, e))
                case Lex.TBind{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}}, rest, e))
                case Lex.TArrow{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TArrow{}, t, l, c}}, rest, e))
                case Lex.TLam{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}}, rest, e))
                case Lex.TAll{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TAll{}, t, l, c}}, rest, e))
                case Lex.TAmp{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TAmp{}, t, l, c}}, rest, e))
                case Lex.TOpen{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOpen{}, t, l, c}}, rest, e))
                case Lex.TClose{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TClose{}, t, l, c}}, rest, e))
                case Lex.TComma{}:
                  inert.table.lets(rest, live, acc,
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, rest, e))
        case Tree.NNil{}: inert.table.lets(rest, live, acc, e)
        case Tree.NCons{x, y}: inert.table.lets(rest, live, acc, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# the fixed tables in scope of a body read that way are the ones they were
law inert.table.scope:
  for +body: Tree.Node
  for +mods: List<&2, String>
  for +e: {D1.inert.ok(body) == True{} : Bool}
  {Table.scope(D1.inert.node(body), mods) == Table.scope(body, mods) : List<&2, String>}

def inert.table.scope(body, mods, e):
  inert.table.lets(body, [], mods, e)

# a def whose body read that way is one fixed table as it was
law inert.table.mod_one:
  for body: Tree.Node
  for +name: String
  for +acc: List<&2, String>
  for +e: {D1.inert.ok(body) == True{} : Bool}
  {Table.mod_one(D1.inert.node(body), name, acc) == Table.mod_one(body, name, acc) : List<&2, String>}

def inert.table.mod_one(body, name, acc, e):
  match body:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Stmt{sk, +kids, +inn}:
          match r:
            case Tree.NNil{}:
              Equal.cong(Bool, List<&2, String>, z => Bool.pick(List<&2, String>, z, name <> acc, acc),
                Table.built(D1.inert.node(kids)), Table.built(kids), inert.table.built(kids,
                  M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(inn), M1.inert.and_l(Bool.and(D1.inert.ok(kids),
                    D1.inert.ok(inn)), True{}, e))))
            case Tree.Leaf{x}: {==}
            case Tree.Group{x, y, z}: {==}
            case Tree.Stmt{x, y, z}: {==}
            case Tree.NCons{x, y}: {==}
        case Tree.Leaf{tok}: {==}
        case Tree.Group{o, gk, cl}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# the file's table defs, over defs read that way, are the ones they were
law inert.table.modules:
  for ds: List<&2, Calls.Def>
  for +acc: List<&2, String>
  for +e: {inert.dok(ds) == True{} : Bool}
  {Table.modules(inert.defs(ds), acc) == Table.modules(ds, acc) : List<&2, String>}

def inert.table.modules(ds, acc, e):
  match ds:
    case Nil{}: {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      %inert.table.mod_one(body, name, acc, inert.dok.body(name, sig, body, rest, e)) : {Table.modules(inert.defs(rest),
        Table.mod_one(D1.inert.node(body), name, acc)) == Table.modules(rest, _) : List<&2, String>}
      inert.table.modules(rest, Table.mod_one(D1.inert.node(body), name, acc), inert.dok.rest(name, sig, body, rest,
        e))

# what hit reads of a call: its name against get and set, its index and list
def inert.table.hq(
  +open: Bool,
  +get: Bool,
  set: Bool,
  lit: Bool,
  own: Bool,
  +tt: String,
  +path: String,
  +line: U32,
  +col: U32
) -> List<&2, F.Finding>:
  Bool.pick(List<&2, F.Finding>, Bool.and(Bool.and(open, Bool.or(get, set)), Bool.and(Bool.not(lit), own)),
    [Table.cite(get, path, line, col, U32.from_nat(String.length(tt)))], [])

# a call named neither get nor set is no hit
law inert.table.hq_off:
  for open: Bool
  for lit: Bool
  for own: Bool
  for +tt: String
  for +path: String
  for +line: U32
  for +col: U32
  {inert.table.hq(open, False{}, False{}, lit, own, tt, path, line, col) == [] : List<&2, F.Finding>}

def inert.table.hq_off(open, _lit, _own, _tt, _path, _line, _col):
  match open:
    case True{}: {==}
    case False{}: {==}

# a call whose name is no get and no set, as hit reads it, is no hit
law inert.table.hit_off:
  for +open: Bool
  for +tt: String
  for +kids: Tree.Node
  for +fixed: List<&2, String>
  for +path: String
  for +line: U32
  for +col: U32
  for eg: {String.eq(tt, "List.get") == False{} : Bool}
  for es: {String.eq(tt, "List.set") == False{} : Bool}
  {Table.hit(open, tt, kids, fixed, path, line, col) == [] : List<&2, F.Finding>}

def inert.table.hit_off(open, tt, kids, fixed, path, line, col, eg, es):
  +aa = Calls.args(kids)
  +lit = Table.literal(Calls.arg(aa, 3n))
  +own = Table.owns(Calls.arg(aa, 2n), fixed)
  %Equal.sym(Bool, String.eq(tt, "List.get"), False{}, eg) : {inert.table.hq(open, _, String.eq(tt, "List.set"), lit,
    own, tt, path, line, col) == [] : List<&2, F.Finding>}
  %Equal.sym(Bool, String.eq(tt, "List.set"), False{}, es) : {inert.table.hq(open, False{}, _, lit, own, tt, path,
    line, col) == [] : List<&2, F.Finding>}
  inert.table.hq_off(open, lit, own, tt, path, line, col)

# a call read that way is the hit it was: a string is named neither get nor
# set, and a name is read as it was
law inert.table.hit:
  for +open: Bool
  for b: Bool
  for +t: String
  for +kids: Tree.Node
  for +fixed: List<&2, String>
  for +path: String
  for +line: U32
  for +col: U32
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  {Table.hit(open, D1.inert.keep(b, t), D1.inert.node(kids), fixed, path, line, col)
    == Table.hit(open, t, kids, fixed, path, line, col) : List<&2, F.Finding>}

def inert.table.hit(open, b, t, kids, fixed, path, line, col, ef, ek):
  match b:
    case True{}:
      Equal.trans(List<&2, F.Finding>, Table.hit(open, D1.inert.cut(t), D1.inert.node(kids), fixed, path, line,
        col), [], Table.hit(open, t, kids, fixed, path, line, col),
        inert.table.hit_off(open, D1.inert.cut(t), D1.inert.node(kids), fixed, path, line, col,
          M1.inert.neq(D1.inert.cut(t), "List.get", M1.inert.cut_marked(t, ef), {==}),
          M1.inert.neq(D1.inert.cut(t), "List.set", M1.inert.cut_marked(t, ef), {==})),
        Equal.sym(List<&2, F.Finding>, Table.hit(open, t, kids, fixed, path, line, col), [],
          inert.table.hit_off(open, t, kids, fixed, path, line, col, M1.inert.neq(t, "List.get", ef, {==}),
            M1.inert.neq(t, "List.set", ef, {==}))))
    case False{}:
      +aa = Calls.args(kids)
      +lhs = Table.hit(open, t, D1.inert.node(kids), fixed, path, line, col)
      %inert.table.literal(Calls.arg(aa, 3n)) : {lhs == inert.table.hq(open, String.eq(t, "List.get"),
        String.eq(t, "List.set"), _, Table.owns(Calls.arg(aa, 2n), fixed), t, path, line, col) : List<&2, F.Finding>}
      %inert.table.owns(Calls.arg(aa, 2n), fixed, inert.ok.arg(kids, 2n, ek)) : {lhs == inert.table.hq(open,
        String.eq(t, "List.get"), String.eq(t, "List.set"), Table.literal(D1.inert.node(Calls.arg(aa, 3n))), _, t,
        path, line, col) : List<&2, F.Finding>}
      %inert.arg(aa, 3n) : {lhs == inert.table.hq(open, String.eq(t, "List.get"), String.eq(t, "List.set"),
        Table.literal(_), Table.owns(D1.inert.node(Calls.arg(aa, 2n)), fixed), t, path, line, col)
        : List<&2, F.Finding>}
      %inert.arg(aa, 2n) : {lhs == inert.table.hq(open, String.eq(t, "List.get"), String.eq(t, "List.set"),
        Table.literal(Calls.arg(inert.nodes(aa), 3n)), Table.owns(_, fixed), t, path, line, col) : List<&2, F.Finding>}
      %inert.args(kids) : {lhs == inert.table.hq(open, String.eq(t, "List.get"), String.eq(t, "List.set"),
        Table.literal(Calls.arg(_, 3n)), Table.owns(Calls.arg(_, 2n), fixed), t, path, line, col)
        : List<&2, F.Finding>}
      {==}

# a name then a group: the call's hit, the group and the rest walked as they were
law inert.table.lg:
  for +kk: Lex.TokKind
  for +t: String
  for +o: String
  for +l: U32
  for +c: U32
  for +path: String
  for +fixed: List<&2, String>
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +ef: {D1.inert.fits.go(D1.inert.blanks(kk), t) == True{} : Bool}
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  for ik: {Table.walk(D1.inert.node(kids), path, fixed) == Table.walk(kids, path, fixed) : List<&2, F.Finding>}
  for ir: {Table.walk(D1.inert.node(r2), path, fixed) == Table.walk(r2, path, fixed) : List<&2, F.Finding>}
  {List.concat(&2, F.Finding, [Table.hit(String.eq(o, "("), D1.inert.keep(D1.inert.blanks(kk), t),
    D1.inert.node(kids), fixed, path, l, c), Table.walk(D1.inert.node(kids), path, fixed),
    Table.walk(D1.inert.node(r2), path, fixed)])
    == List.concat(&2, F.Finding, [Table.hit(String.eq(o, "("), t, kids, fixed, path, l, c), Table.walk(kids, path,
      fixed), Table.walk(r2, path, fixed)]) : List<&2, F.Finding>}

def inert.table.lg(kk, t, o, l, c, path, fixed, kids, r2, ef, ek, ik, ir):
  inert.cat3(Table.hit(String.eq(o, "("), D1.inert.keep(D1.inert.blanks(kk), t), D1.inert.node(kids), fixed, path,
    l, c), Table.hit(String.eq(o, "("), t, kids, fixed, path, l, c), Table.walk(D1.inert.node(kids), path, fixed),
    Table.walk(kids, path, fixed), Table.walk(D1.inert.node(r2), path, fixed), Table.walk(r2, path, fixed),
    inert.table.hit(String.eq(o, "("), D1.inert.blanks(kk), t, kids, fixed, path, l, c, ef, ek), ik, ir)

# table's walk reads no string: a leaf's text is compared with `List.get`
# and `List.set`, which no string equals
law inert.table.walk:
  for nn: Tree.Node
  for +path: String
  for +fixed: List<&2, String>
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Table.walk(D1.inert.node(nn), path, fixed) == Table.walk(nn, path, fixed) : List<&2, F.Finding>}

def inert.table.walk(nn, path, fixed, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{+o, +kids, +cl}:
                      match o:
                        case Lex.Tok{+ok, +ot, +ol, +oc}:
                          +lf = {Tree.Leaf{Lex.Tok{k, t, l, c}} : Tree.Node}
                          +eg = inert.ok_t(lf, Tree.NCons{Tree.Group{Lex.Tok{ok, ot, ol, oc}, kids, cl}, r2}, e)
                          +ec = inert.ok_h(Tree.Group{Lex.Tok{ok, ot, ol, oc}, kids, cl}, r2, eg)
                          inert.table.lg(k, t, ot, l, c, path, fixed, kids, r2,
                            inert.ok_h(lf, Tree.NCons{Tree.Group{Lex.Tok{ok, ot, ol, oc}, kids, cl}, r2}, e), ec,
                            inert.table.walk(kids, path, fixed, ec),
                            inert.table.walk(r2, path, fixed, inert.ok_t(Tree.Group{Lex.Tok{ok, ot, ol, oc}, kids,
                              cl}, r2, eg)))
                    case Tree.Leaf{x}:
                      inert.table.walk(rest, path, fixed, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.Stmt{x, y, z}:
                      inert.table.walk(rest, path, fixed, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NNil{}:
                      inert.table.walk(rest, path, fixed, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NCons{x, y}:
                      inert.table.walk(rest, path, fixed, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NNil{}: {==}
        case Tree.Group{+o, +kids, +cl}:
          inert.cat2(Table.walk(D1.inert.node(kids), path, fixed), Table.walk(kids, path, fixed),
            Table.walk(D1.inert.node(rest), path, fixed), Table.walk(rest, path, fixed),
            inert.table.walk(kids, path, fixed, inert.ok_h(Tree.Group{o, kids, cl}, rest, e)),
            inert.table.walk(rest, path, fixed, inert.ok_t(Tree.Group{o, kids, cl}, rest, e)))
        case Tree.Stmt{+sk, +kids, +body}:
          +es = inert.ok_h(Tree.Stmt{sk, kids, body}, rest, e)
          inert.cat3(Table.walk(D1.inert.node(kids), path, fixed), Table.walk(kids, path, fixed),
            Table.walk(D1.inert.node(body), path, fixed), Table.walk(body, path, fixed),
            Table.walk(D1.inert.node(rest), path, fixed), Table.walk(rest, path, fixed),
            inert.table.walk(kids, path, fixed, M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es)),
            inert.table.walk(body, path, fixed, M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es)),
            inert.table.walk(rest, path, fixed, inert.ok_t(Tree.Stmt{sk, kids, body}, rest, e)))
        case Tree.NNil{}: inert.table.walk(rest, path, fixed, e)
        case Tree.NCons{x, y}: inert.table.walk(rest, path, fixed, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# table over the defs read that way reports what it reports over the defs
law inert.table.go:
  for ds: List<&2, Calls.Def>
  for +mods: List<&2, String>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  for +e: {inert.dok(ds) == True{} : Bool}
  {Table.check.go(inert.defs(ds), mods, path, acc) == Table.check.go(ds, mods, path, acc) : List<&2, F.Finding>}

def inert.table.go(ds, mods, path, acc, e):
  match ds:
    case Nil{}: {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +en = inert.dok.head(name, sig, body, rest, e)
      +eb = inert.dok.body(name, sig, body, rest, e)
      +ib = D1.inert.node(body)
      +lst = Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Calls.calls(ib, name), Bool.not(Calls.exempt(path,
        D1.inert.node(sig))))), [], _u => Table.walk(ib, path, Table.scope(ib, mods)))
      %inert.table.scope(body, mods, eb) : {Table.check.go(inert.defs(rest), mods, path, lst <> acc)
        == Table.check.go(rest, mods, path, Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Calls.calls(body, name),
          Bool.not(Calls.exempt(path, sig)))), [], _u => Table.walk(body, path, _)) <> acc) : List<&2, F.Finding>}
      %inert.stop(Bool.not(Bool.and(Calls.calls(ib, name), Bool.not(Calls.exempt(path, D1.inert.node(sig))))),
        Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))),
        Table.walk(ib, path, Table.scope(ib, mods)), Table.walk(body, path, Table.scope(ib, mods)),
        inert.gate(path, name, sig, body, en, eb), inert.table.walk(body, path, Table.scope(ib, mods), eb)) :
        {Table.check.go(inert.defs(rest), mods, path, lst <> acc) == Table.check.go(rest, mods, path, _ <> acc)
          : List<&2, F.Finding>}
      inert.table.go(rest, mods, path, lst <> acc, inert.dok.rest(name, sig, body, rest, e))

# table over the defs read that way, their table defs read that way too
law inert.table.all:
  for +ds: List<&2, Calls.Def>
  for +path: String
  for +e: {inert.dok(ds) == True{} : Bool}
  {Table.check.go(inert.defs(ds), Table.modules(inert.defs(ds), []), path, [])
    == Table.check.go(ds, Table.modules(ds, []), path, []) : List<&2, F.Finding>}

def inert.table.all(ds, path, e):
  %inert.table.modules(ds, [], e) : {Table.check.go(inert.defs(ds), Table.modules(inert.defs(ds), []), path, [])
    == Table.check.go(ds, _, path, []) : List<&2, F.Finding>}
  inert.table.go(ds, Table.modules(inert.defs(ds), []), path, [], e)

def Laws.inert_table(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, ok, ok2, e):
  M1.inert.via(Tree.Node, z => Table.check.go(Calls.defs(z), Table.modules(Calls.defs(z), []), path, []), tree, tree2,
    D1.inert.node(tree), D1.inert.node(tree2),
    inert.lift(z => Table.check.go(z, Table.modules(z, []), path, []), tree, inert.table.all(Calls.defs(tree), path,
      inert.dok.of(tree, ok))),
    inert.lift(z => Table.check.go(z, Table.modules(z, []), path, []), tree2, inert.table.all(Calls.defs(tree2), path,
      inert.dok.of(tree2, ok2))),
    e)

# index
# -----

# a chain read that way is one number as it was
law inert.index.literal:
  for nn: Tree.Node
  {Index.literal(D1.inert.node(nn)) == Index.literal(nn) : Bool}

def inert.index.literal(nn):
  match nn:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}: {==}
                case Lex.TUpper{}: {==}
                case Lex.TDotted{}: {==}
                case Lex.TWild{}: {==}
                case Lex.TKey{}: {==}
                case Lex.TNum{}:
                  match r:
                    case Tree.NNil{}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NCons{x, y}: {==}
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
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a list argument read that way is table's as it was
law inert.index.held:
  for list: Bool
  for +coll: Tree.Node
  for +fixed: List<&2, String>
  for +e: {D1.inert.ok(coll) == True{} : Bool}
  {Index.held(list, D1.inert.node(coll), fixed) == Index.held(list, coll, fixed) : Bool}

def inert.index.held(list, coll, fixed, e):
  match list:
    case False{}: {==}
    case True{}: inert.table.owns(coll, fixed, e)

# what index reads of a call: its name against the two, its index, its list
# and what the group and the rest report
def inert.index.at(
  +o: String,
  +list: Bool,
  sget: Bool,
  lit: Bool,
  hd: Bool,
  +t: String,
  +l: U32,
  +c: U32,
  +path: String,
  +more: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  Bool.pick(List<&2, F.Finding>, Bool.and(Bool.and(String.eq(o, "("), Bool.or(list, sget)), Bool.and(Bool.not(lit),
    Bool.not(hd))),
    F.Finding{path, l, c, U32.from_nat(String.length(t)), "index",
      t ++ " in a recursive def walks the list from its head on every step, which is quadratic; recurse over the list itself."} <> more,
    more)

# a call named neither get is no finding
law inert.index.off:
  for +o: String
  for lit: Bool
  for hd: Bool
  for +t: String
  for +l: U32
  for +c: U32
  for +path: String
  for +more: List<&2, F.Finding>
  {inert.index.at(o, False{}, False{}, lit, hd, t, l, c, path, more) == more : List<&2, F.Finding>}

def inert.index.off(o, lit, hd, t, l, c, path, more):
  %Equal.sym(Bool, Bool.and(String.eq(o, "("), False{}), False{}, inert.and_false(String.eq(o, "("))) :
    {Bool.pick(List<&2, F.Finding>, Bool.and(_, Bool.and(Bool.not(lit), Bool.not(hd))),
      F.Finding{path, l, c, U32.from_nat(String.length(t)), "index",
        t ++ " in a recursive def walks the list from its head on every step, which is quadratic; recurse over the list itself."}
        <> more, more) == more : List<&2, F.Finding>}
  {==}

# a call whose name is no get, as index reads it, is no finding
law inert.index.off2:
  for +o: String
  for lit: Bool
  for hd: Bool
  for +t: String
  for +l: U32
  for +c: U32
  for +path: String
  for +more: List<&2, F.Finding>
  for +self: String
  for eg: {String.eq(t, "List.get") == False{} : Bool}
  for es: {String.eq(t, "String.get") == False{} : Bool}
  {inert.index.at(o, Index.named(t, self, "List.get"), Index.named(t, self, "String.get"), lit, hd, t, l, c, path,
    more) == more : List<&2, F.Finding>}

def inert.index.off2(o, lit, hd, t, l, c, path, more, self, eg, es):
  +ns = Bool.not(String.eq(t, self))
  %Equal.sym(Bool, String.eq(t, "List.get"), False{}, eg) : {inert.index.at(o, Bool.and(_, ns),
    Bool.and(String.eq(t, "String.get"), ns), lit, hd, t, l, c, path, more) == more : List<&2, F.Finding>}
  %Equal.sym(Bool, String.eq(t, "String.get"), False{}, es) : {inert.index.at(o, Bool.and(False{}, ns),
    Bool.and(_, ns), lit, hd, t, l, c, path, more) == more : List<&2, F.Finding>}
  inert.index.off(o, lit, hd, t, l, c, path, more)

# what index reads of a call from its name, its group and what they report
def inert.index.call(
  +o: String,
  +tt: String,
  +kids: Tree.Node,
  +l: U32,
  +c: U32,
  +path: String,
  +fixed: List<&2, String>,
  +self: String,
  +more: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  +go = Index.named(tt, self, "List.get")
  +aa = Calls.args(kids)
  inert.index.at(o, go, Index.named(tt, self, "String.get"), Index.literal(Calls.arg(aa, Bool.pick(Nat, go, 3n, 1n))),
    Index.held(go, Calls.arg(aa, 2n), fixed), tt, l, c, path, more)

# a call named no get, read either way, is no finding
law inert.index.calloff:
  for +o: String
  for +tt: String
  for +kids: Tree.Node
  for +l: U32
  for +c: U32
  for +path: String
  for +fixed: List<&2, String>
  for +more: List<&2, F.Finding>
  for +self: String
  for eg: {String.eq(tt, "List.get") == False{} : Bool}
  for es: {String.eq(tt, "String.get") == False{} : Bool}
  {inert.index.call(o, tt, kids, l, c, path, fixed, self, more) == more : List<&2, F.Finding>}

def inert.index.calloff(o, tt, kids, l, c, path, fixed, more, self, eg, es):
  +go = Index.named(tt, self, "List.get")
  +aa = Calls.args(kids)
  inert.index.off2(o, Index.literal(Calls.arg(aa, Bool.pick(Nat, go, 3n, 1n))), Index.held(go, Calls.arg(aa, 2n),
    fixed), tt, l, c, path, more, self, eg, es)

# a name then a group, read that way: the call reported as it was, the group
# and the rest walked as they were
law inert.index.lg:
  for b: Bool
  for +t: String
  for +o: String
  for +l: U32
  for +c: U32
  for +path: String
  for +fixed: List<&2, String>
  for +self: String
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  for ik: {Index.walk(D1.inert.node(kids), path, fixed, self) == Index.walk(kids, path, fixed, self)
    : List<&2, F.Finding>}
  for ir: {Index.walk(D1.inert.node(r2), path, fixed, self) == Index.walk(r2, path, fixed, self)
    : List<&2, F.Finding>}
  {inert.index.call(o, D1.inert.keep(b, t), D1.inert.node(kids), l, c, path, fixed, self,
    List.concat(&2, F.Finding, [Index.walk(D1.inert.node(kids), path, fixed, self),
      Index.walk(D1.inert.node(r2), path, fixed, self)]))
    == inert.index.call(o, t, kids, l, c, path, fixed, self, List.concat(&2, F.Finding,
      [Index.walk(kids, path, fixed, self), Index.walk(r2, path, fixed, self)])) : List<&2, F.Finding>}

def inert.index.lg(b, t, o, l, c, path, fixed, self, kids, r2, ef, ek, ik, ir):
  match b:
    case True{}:
      +wk = Index.walk(D1.inert.node(kids), path, fixed, self)
      +wr = Index.walk(D1.inert.node(r2), path, fixed, self)
      +mi = List.concat(&2, F.Finding, [wk, wr])
      +mo = List.concat(&2, F.Finding, [Index.walk(kids, path, fixed, self), Index.walk(r2, path, fixed, self)])
      +ct = D1.inert.cut(t)
      Equal.trans(List<&2, F.Finding>, inert.index.call(o, ct, D1.inert.node(kids), l, c, path, fixed, self, mi), mi,
        inert.index.call(o, t, kids, l, c, path, fixed, self, mo),
        inert.index.calloff(o, ct, D1.inert.node(kids), l, c, path, fixed, mi, self,
          M1.inert.neq(ct, "List.get", M1.inert.cut_marked(t, ef), {==}),
          M1.inert.neq(ct, "String.get", M1.inert.cut_marked(t, ef), {==})),
        Equal.trans(List<&2, F.Finding>, mi, mo, inert.index.call(o, t, kids, l, c, path, fixed, self, mo),
          inert.cat2(wk, Index.walk(kids, path, fixed, self), wr, Index.walk(r2, path, fixed, self), ik, ir),
          Equal.sym(List<&2, F.Finding>, inert.index.call(o, t, kids, l, c, path, fixed, self, mo), mo,
            inert.index.calloff(o, t, kids, l, c, path, fixed, mo, self, M1.inert.neq(t, "List.get", ef, {==}),
              M1.inert.neq(t, "String.get", ef, {==})))))
    case False{}:
      +wk = Index.walk(D1.inert.node(kids), path, fixed, self)
      +wr = Index.walk(D1.inert.node(r2), path, fixed, self)
      +mo = List.concat(&2, F.Finding, [Index.walk(kids, path, fixed, self), Index.walk(r2, path, fixed, self)])
      +go = Index.named(t, self, "List.get")
      +gs = Index.named(t, self, "String.get")
      +aa = Calls.args(kids)
      +nn = Bool.pick(Nat, go, 3n, 1n)
      +lhs = inert.index.call(o, t, D1.inert.node(kids), l, c, path, fixed, self,
        List.concat(&2, F.Finding, [wk, wr]))
      %inert.index.literal(Calls.arg(aa, nn)) : {lhs == inert.index.at(o, go, gs, _, Index.held(go, Calls.arg(aa, 2n),
        fixed), t, l, c, path, mo) : List<&2, F.Finding>}
      %inert.index.held(go, Calls.arg(aa, 2n), fixed, inert.ok.arg(kids, 2n, ek)) : {lhs == inert.index.at(o, go, gs,
        Index.literal(D1.inert.node(Calls.arg(aa, nn))), _, t, l, c, path, mo) : List<&2, F.Finding>}
      %inert.arg(aa, nn) : {lhs == inert.index.at(o, go, gs, Index.literal(_), Index.held(go,
        D1.inert.node(Calls.arg(aa, 2n)), fixed), t, l, c, path, mo) : List<&2, F.Finding>}
      %inert.arg(aa, 2n) : {lhs == inert.index.at(o, go, gs, Index.literal(Calls.arg(inert.nodes(aa), nn)),
        Index.held(go, _, fixed), t, l, c, path, mo) : List<&2, F.Finding>}
      %inert.args(kids) : {lhs == inert.index.at(o, go, gs, Index.literal(Calls.arg(_, nn)), Index.held(go,
        Calls.arg(_, 2n), fixed), t, l, c, path, mo) : List<&2, F.Finding>}
      %inert.cat2(wk, Index.walk(kids, path, fixed, self), wr, Index.walk(r2, path, fixed, self), ik, ir) : {lhs
        == inert.index.at(o, go, gs, Index.literal(Calls.arg(Calls.args(D1.inert.node(kids)), nn)), Index.held(go,
          Calls.arg(Calls.args(D1.inert.node(kids)), 2n), fixed), t, l, c, path, _) : List<&2, F.Finding>}
      {==}

# index's walk reads no string: a leaf's text is compared with `List.get`
# and `String.get`, which no string equals
law inert.index.walk:
  for nn: Tree.Node
  for +path: String
  for +fixed: List<&2, String>
  for +self: String
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Index.walk(D1.inert.node(nn), path, fixed, self) == Index.walk(nn, path, fixed, self) : List<&2, F.Finding>}

def inert.index.walk(nn, path, fixed, self, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{o, +kids, +cl}:
                      match o:
                        case Lex.Tok{+ok, +ot, +ol, +oc}:
                          +lf = {Tree.Leaf{Lex.Tok{k, t, l, c}} : Tree.Node}
                          +eg = inert.ok_t(lf, Tree.NCons{Tree.Group{Lex.Tok{ok, ot, ol, oc}, kids, cl}, r2}, e)
                          +ec = inert.ok_h(Tree.Group{Lex.Tok{ok, ot, ol, oc}, kids, cl}, r2, eg)
                          inert.index.lg(D1.inert.blanks(k), t, ot, l, c, path, fixed, self, kids, r2,
                            inert.ok_h(lf, Tree.NCons{Tree.Group{Lex.Tok{ok, ot, ol, oc}, kids, cl}, r2}, e), ec,
                            inert.index.walk(kids, path, fixed, self, ec),
                            inert.index.walk(r2, path, fixed, self, inert.ok_t(Tree.Group{Lex.Tok{ok, ot, ol, oc}, kids,
                              cl}, r2, eg)))
                    case Tree.Leaf{x}:
                      inert.index.walk(rest, path, fixed, self, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.Stmt{x, y, z}:
                      inert.index.walk(rest, path, fixed, self, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NNil{}:
                      inert.index.walk(rest, path, fixed, self, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NCons{x, y}:
                      inert.index.walk(rest, path, fixed, self, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NNil{}: {==}
        case Tree.Group{+o, +kids, +cl}:
          inert.cat2(Index.walk(D1.inert.node(kids), path, fixed, self), Index.walk(kids, path, fixed, self),
            Index.walk(D1.inert.node(rest), path, fixed, self), Index.walk(rest, path, fixed, self),
            inert.index.walk(kids, path, fixed, self, inert.ok_h(Tree.Group{o, kids, cl}, rest, e)),
            inert.index.walk(rest, path, fixed, self, inert.ok_t(Tree.Group{o, kids, cl}, rest, e)))
        case Tree.Stmt{+sk, +kids, +body}:
          +es = inert.ok_h(Tree.Stmt{sk, kids, body}, rest, e)
          inert.cat3(Index.walk(D1.inert.node(kids), path, fixed, self), Index.walk(kids, path, fixed, self),
            Index.walk(D1.inert.node(body), path, fixed, self), Index.walk(body, path, fixed, self),
            Index.walk(D1.inert.node(rest), path, fixed, self), Index.walk(rest, path, fixed, self),
            inert.index.walk(kids, path, fixed, self, M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es)),
            inert.index.walk(body, path, fixed, self, M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es)),
            inert.index.walk(rest, path, fixed, self, inert.ok_t(Tree.Stmt{sk, kids, body}, rest, e)))
        case Tree.NNil{}: inert.index.walk(rest, path, fixed, self, e)
        case Tree.NCons{x, y}: inert.index.walk(rest, path, fixed, self, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# index over the defs read that way reports what it reports over the defs
law inert.index.go:
  for ds: List<&2, Calls.Def>
  for +mods: List<&2, String>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  for +e: {inert.dok(ds) == True{} : Bool}
  {Index.check.go(inert.defs(ds), mods, path, acc) == Index.check.go(ds, mods, path, acc) : List<&2, F.Finding>}

def inert.index.go(ds, mods, path, acc, e):
  match ds:
    case Nil{}: {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +en = inert.dok.head(name, sig, body, rest, e)
      +eb = inert.dok.body(name, sig, body, rest, e)
      +ib = D1.inert.node(body)
      +lst = Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Calls.calls(ib, name), Bool.not(Calls.exempt(path,
        D1.inert.node(sig))))), [], _u => Index.walk(ib, path, Table.scope(ib, mods), name))
      %inert.table.scope(body, mods, eb) : {Index.check.go(inert.defs(rest), mods, path, lst <> acc)
        == Index.check.go(rest, mods, path, Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Calls.calls(body, name),
          Bool.not(Calls.exempt(path, sig)))), [], _u => Index.walk(body, path, _, name)) <> acc) : List<&2, F.Finding>}
      %inert.stop(Bool.not(Bool.and(Calls.calls(ib, name), Bool.not(Calls.exempt(path, D1.inert.node(sig))))),
        Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))),
        Index.walk(ib, path, Table.scope(ib, mods), name), Index.walk(body, path, Table.scope(ib, mods), name),
        inert.gate(path, name, sig, body, en, eb), inert.index.walk(body, path, Table.scope(ib, mods), name, eb)) :
        {Index.check.go(inert.defs(rest), mods, path, lst <> acc) == Index.check.go(rest, mods, path, _ <> acc)
          : List<&2, F.Finding>}
      inert.index.go(rest, mods, path, lst <> acc, inert.dok.rest(name, sig, body, rest, e))

# index over the defs read that way, their table defs read that way too
law inert.index.all:
  for +ds: List<&2, Calls.Def>
  for +path: String
  for +e: {inert.dok(ds) == True{} : Bool}
  {Index.check.go(inert.defs(ds), Table.modules(inert.defs(ds), []), path, [])
    == Index.check.go(ds, Table.modules(ds, []), path, []) : List<&2, F.Finding>}

def inert.index.all(ds, path, e):
  %inert.table.modules(ds, [], e) : {Index.check.go(inert.defs(ds), Table.modules(inert.defs(ds), []), path, [])
    == Index.check.go(ds, _, path, []) : List<&2, F.Finding>}
  inert.index.go(ds, Table.modules(inert.defs(ds), []), path, [], e)

def Laws.inert_index(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, ok, ok2, e):
  M1.inert.via(Tree.Node, z => Index.check.go(Calls.defs(z), Table.modules(Calls.defs(z), []), path, []), tree, tree2,
    D1.inert.node(tree), D1.inert.node(tree2),
    inert.lift(z => Index.check.go(z, Table.modules(z, []), path, []), tree, inert.index.all(Calls.defs(tree), path,
      inert.dok.of(tree, ok))),
    inert.lift(z => Index.check.go(z, Table.modules(z, []), path, []), tree2, inert.index.all(Calls.defs(tree2), path,
      inert.dok.of(tree2, ok2))),
    e)

# concat
# ------

# a leaf read that way is the lowercase name it was: only a name's text is kept
law inert.concat.name_tok:
  for nn: Tree.Node
  {Concat.lone.name(D1.inert.node(nn)) == Concat.lone.name(nn) : Maybe<&2, Lex.Tok>}

def inert.concat.name_tok(nn):
  match nn:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}:
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
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# a chain read that way is the one lowercase name it was
law inert.concat.lone:
  for nn: Tree.Node
  {Concat.lone(D1.inert.node(nn)) == Concat.lone(nn) : Maybe<&2, Lex.Tok>}

def inert.concat.lone(nn):
  match nn:
    case Tree.NCons{h, +r}:
      match r:
        case Tree.NNil{}: inert.concat.name_tok(h)
        case Tree.Leaf{x}: {==}
        case Tree.Group{x, y, z}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# what appended reads of a call: whether it is List.append or String.append,
# and its arguments
def inert.concat.ap(+list: Bool, str: Bool, as: List<&2, Tree.Node>) -> Maybe<&2, Lex.Tok>:
  Bool.pick(Maybe<&2, Lex.Tok>, Bool.or(list, str), Concat.lone(Calls.arg(as, Bool.pick(Nat, list, 2n, 0n))), None{})

# the arguments read that way append onto the name they did
law inert.concat.ap_nodes:
  for +list: Bool
  for str: Bool
  for +as: List<&2, Tree.Node>
  {inert.concat.ap(list, str, inert.nodes(as)) == inert.concat.ap(list, str, as) : Maybe<&2, Lex.Tok>}

def inert.concat.ap_nodes(list, str, as):
  +nn = Bool.pick(Nat, list, 2n, 0n)
  %inert.concat.lone(Calls.arg(as, nn)) : {inert.concat.ap(list, str, inert.nodes(as))
    == Bool.pick(Maybe<&2, Lex.Tok>, Bool.or(list, str), _, None{}) : Maybe<&2, Lex.Tok>}
  %inert.arg(as, nn) : {inert.concat.ap(list, str, inert.nodes(as))
    == Bool.pick(Maybe<&2, Lex.Tok>, Bool.or(list, str), Concat.lone(_), None{}) : Maybe<&2, Lex.Tok>}
  {==}

# a call's name and arguments, read that way, append onto the name they did
law inert.concat.appended:
  for +b: Bool
  for +t: String
  for +kids: Tree.Node
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  {Concat.appended(D1.inert.keep(b, t), Calls.args(D1.inert.node(kids))) == Concat.appended(t, Calls.args(kids))
    : Maybe<&2, Lex.Tok>}

def inert.concat.appended(b, t, kids, ef):
  +kt = D1.inert.keep(b, t)
  +aa = Calls.args(kids)
  +lhs = Concat.appended(kt, Calls.args(D1.inert.node(kids)))
  %M1.inert.eq_keep(b, t, "List.append", ef, {==}) : {lhs == inert.concat.ap(_, String.eq(t, "String.append"), aa)
    : Maybe<&2, Lex.Tok>}
  %M1.inert.eq_keep(b, t, "String.append", ef, {==}) : {lhs == inert.concat.ap(String.eq(kt, "List.append"), _, aa)
    : Maybe<&2, Lex.Tok>}
  %inert.concat.ap_nodes(String.eq(kt, "List.append"), String.eq(kt, "String.append"), aa) : {lhs == _
    : Maybe<&2, Lex.Tok>}
  %inert.args(kids) : {lhs == inert.concat.ap(String.eq(kt, "List.append"), String.eq(kt, "String.append"), _)
    : Maybe<&2, Lex.Tok>}
  {==}

# a leaf then a group, read that way: the call appends onto the name it did
law inert.concat.call:
  for h: Tree.Node
  for +kids: Tree.Node
  for +e: {D1.inert.ok(h) == True{} : Bool}
  {Concat.onto.call(D1.inert.node(h), D1.inert.node(kids)) == Concat.onto.call(h, kids) : Maybe<&2, Lex.Tok>}

def inert.concat.call(h, kids, e):
  match h:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{+k, +t, l, c}: inert.concat.appended(D1.inert.blanks(k), t, kids, e)
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# a first cell and the second, read that way, append onto the name they did
law inert.concat.next:
  for +h: Tree.Node
  for h2: Tree.Node
  for +e: {D1.inert.ok(h) == True{} : Bool}
  for +e2: {D1.inert.ok(h2) == True{} : Bool}
  {Concat.onto.next(D1.inert.node(h), D1.inert.node(h2)) == Concat.onto.next(h, h2) : Maybe<&2, Lex.Tok>}

def inert.concat.next(h, h2, e, e2):
  match h2:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{+k, +o, l, c}:
          +lhs = Concat.onto.next(D1.inert.node(h), Tree.Leaf{D1.inert.tok(Lex.Tok{k, o, l, c})})
          %M1.inert.eq_keep(D1.inert.blanks(k), o, "++", e2, {==}) : {lhs == Bool.pick(Maybe<&2, Lex.Tok>,
            Bool.and(Calls.kind.oper(k), _), Concat.lone.name(h), None{}) : Maybe<&2, Lex.Tok>}
          %inert.concat.name_tok(h) : {lhs == Bool.pick(Maybe<&2, Lex.Tok>, Bool.and(Calls.kind.oper(k),
            String.eq(D1.inert.keep(D1.inert.blanks(k), o), "++")), _, None{}) : Maybe<&2, Lex.Tok>}
          {==}
    case Tree.Group{o, +kids, cl}: inert.concat.call(h, kids, e)
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# an argument read that way appends onto the name it did
law inert.concat.onto:
  for aa: Tree.Node
  for +e: {D1.inert.ok(aa) == True{} : Bool}
  {Concat.onto(D1.inert.node(aa)) == Concat.onto(aa) : Maybe<&2, Lex.Tok>}

def inert.concat.onto(aa, e):
  match aa:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Group{go, +kids, +gc}:
          match go:
            case Lex.Tok{+gk, +o, +gl, +gcol}:
              match rest:
                case Tree.NNil{}:
                  Equal.cong(Maybe<&2, Lex.Tok>, Maybe<&2, Lex.Tok>, z => Lazy.stop(Maybe<&2, Lex.Tok>,
                    Bool.not(String.eq(o, "(")), None{}, _u => z), Concat.onto(D1.inert.node(kids)),
                    Concat.onto(kids), inert.concat.onto(kids,
                      inert.ok_h(Tree.Group{Lex.Tok{gk, o, gl, gcol}, kids, gc}, Tree.NNil{}, e)))
                case Tree.NCons{+h2, +r2}:
                  inert.concat.next(Tree.Group{Lex.Tok{gk, o, gl, gcol}, kids, gc}, h2,
                    inert.ok_h(Tree.Group{Lex.Tok{gk, o, gl, gcol}, kids, gc}, Tree.NCons{h2, r2}, e),
                    inert.ok_h(h2, r2,
                      inert.ok_t(Tree.Group{Lex.Tok{gk, o, gl, gcol}, kids, gc}, Tree.NCons{h2, r2}, e)))
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
        case Tree.Leaf{+tok}:
          match rest:
            case Tree.NCons{+h2, +r2}:
              inert.concat.next(Tree.Leaf{tok}, h2, inert.ok_h(Tree.Leaf{tok}, Tree.NCons{h2, r2}, e),
                inert.ok_h(h2, r2, inert.ok_t(Tree.Leaf{tok}, Tree.NCons{h2, r2}, e)))
            case Tree.Leaf{x}: {==}
            case Tree.Group{x, y, z}: {==}
            case Tree.Stmt{x, y, z}: {==}
            case Tree.NNil{}: {==}
        case Tree.Stmt{+sk, +sks, +sb}:
          match rest:
            case Tree.NCons{+h2, +r2}:
              inert.concat.next(Tree.Stmt{sk, sks, sb}, h2, inert.ok_h(Tree.Stmt{sk, sks, sb}, Tree.NCons{h2, r2}, e),
                inert.ok_h(h2, r2, inert.ok_t(Tree.Stmt{sk, sks, sb}, Tree.NCons{h2, r2}, e)))
            case Tree.Leaf{x}: {==}
            case Tree.Group{x, y, z}: {==}
            case Tree.Stmt{x, y, z}: {==}
            case Tree.NNil{}: {==}
        case Tree.NNil{}:
          match rest:
            case Tree.NCons{+h2, +r2}:
              inert.concat.next(Tree.NNil{}, h2, {==}, inert.ok_h(h2, r2, e))
            case Tree.Leaf{x}: {==}
            case Tree.Group{x, y, z}: {==}
            case Tree.Stmt{x, y, z}: {==}
            case Tree.NNil{}: {==}
        case Tree.NCons{+x1, +y1}:
          match rest:
            case Tree.NCons{+h2, +r2}:
              inert.concat.next(Tree.NCons{x1, y1}, h2, inert.ok_h(Tree.NCons{x1, y1}, Tree.NCons{h2, r2}, e),
                inert.ok_h(h2, r2, inert.ok_t(Tree.NCons{x1, y1}, Tree.NCons{h2, r2}, e)))
            case Tree.Leaf{x}: {==}
            case Tree.Group{x, y, z}: {==}
            case Tree.Stmt{x, y, z}: {==}
            case Tree.NNil{}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# an argument read that way reads the let of its lone name as it did
law inert.concat.via:
  for +aa: Tree.Node
  for +lets: List<&2, Concat.Let>
  {Concat.via(D1.inert.node(aa), lets) == Concat.via(aa, lets) : Maybe<&2, Lex.Tok>}

def inert.concat.via(aa, lets):
  Equal.cong(Maybe<&2, Lex.Tok>, Maybe<&2, Lex.Tok>, z => Concat.via.of(z, lets), Concat.lone(D1.inert.node(aa)),
    Concat.lone(aa), inert.concat.lone(aa))

# an argument read that way appends, in place or through a let, as it did
law inert.concat.seen:
  for +aa: Tree.Node
  for +lets: List<&2, Concat.Let>
  for +e: {D1.inert.ok(aa) == True{} : Bool}
  {Concat.seen(D1.inert.node(aa), lets) == Concat.seen(aa, lets) : Maybe<&2, Lex.Tok>}

def inert.concat.seen(aa, lets, e):
  +lhs = Concat.seen(D1.inert.node(aa), lets)
  %inert.concat.onto(aa, e) : {lhs == Concat.either(_, Concat.via(aa, lets)) : Maybe<&2, Lex.Tok>}
  %inert.concat.via(aa, lets) : {lhs == Concat.either(Concat.onto(D1.inert.node(aa)), _) : Maybe<&2, Lex.Tok>}
  {==}

# a node read that way is an `=` as it was
law inert.concat.is_eq:
  for nn: Tree.Node
  {Calls.kind.leaf(~Concat.bound.eq, D1.inert.node(nn)) == Calls.kind.leaf(~Concat.bound.eq, nn) : Bool}

def inert.concat.is_eq(nn):
  Equal.cong(Maybe<&2, Lex.TokKind>, Bool,
    m => Calls.kind.of(~Concat.bound.eq, m), Calls.leaf.kind(D1.inert.node(nn)), Calls.leaf.kind(nn),
    inert.leaf_kind(nn))

# a name, `=` and the right side read that way make the let they made
law inert.concat.bound_of:
  for mm: Maybe<&2, Lex.Tok>
  for +h2: Tree.Node
  for +rhs: Tree.Node
  for +e: {D1.inert.ok(rhs) == True{} : Bool}
  {Concat.bound.of(mm, D1.inert.node(h2), D1.inert.node(rhs)) == Concat.bound.of(mm, h2, rhs)
    : Maybe<&2, Concat.Let>}

def inert.concat.bound_of(mm, h2, rhs, e):
  match mm:
    case None{}: {==}
    case Some{tok}:
      match tok:
        case Lex.Tok{k, +t, l, c}:
          +lhs = Concat.bound.of(Some{Lex.Tok{k, t, l, c}}, D1.inert.node(h2), D1.inert.node(rhs))
          %inert.concat.onto(rhs, e) : {lhs == Lazy.stop(Maybe<&2, Concat.Let>,
            Bool.not(Calls.kind.leaf(~Concat.bound.eq, h2)), None{}, _u => Some{Concat.Let{t, _}})
            : Maybe<&2, Concat.Let>}
          %inert.concat.is_eq(h2) : {lhs == Lazy.stop(Maybe<&2, Concat.Let>, Bool.not(_), None{},
            _u => Some{Concat.Let{t, Concat.onto(D1.inert.node(rhs))}}) : Maybe<&2, Concat.Let>}
          {==}

# a plain name, `=` and the right side read that way make the let they made
law inert.concat.named:
  for +hh: Tree.Node
  for +h2: Tree.Node
  for +rhs: Tree.Node
  for +e: {D1.inert.ok(rhs) == True{} : Bool}
  {Concat.bound.named(D1.inert.node(hh), D1.inert.node(h2), D1.inert.node(rhs)) == Concat.bound.named(hh, h2, rhs)
    : Maybe<&2, Concat.Let>}

def inert.concat.named(hh, h2, rhs, e):
  +lhs = Concat.bound.named(D1.inert.node(hh), D1.inert.node(h2), D1.inert.node(rhs))
  %inert.concat.bound_of(Concat.lone.name(hh), h2, rhs, e) : {lhs == _ : Maybe<&2, Concat.Let>}
  %inert.concat.name_tok(hh) : {lhs == Concat.bound.of(_, D1.inert.node(h2), D1.inert.node(rhs))
    : Maybe<&2, Concat.Let>}
  {==}

# a leaf as the lexer makes it: its text marked exactly when it is cut
law inert.leaf_fits:
  for nn: Tree.Node
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {D1.inert.fits.go(Calls.kind.leaf(~D1.inert.blanks, nn), Calls.leaf.text(nn)) == True{} : Bool}

def inert.leaf_fits(nn, e):
  match nn:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}: e
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# `+`, a plain name, `=` and the right side read that way make the let they made
law inert.concat.plus:
  for +h1: Tree.Node
  for +h2: Tree.Node
  for rest: Tree.Node
  for +e1: {D1.inert.ok(h1) == True{} : Bool}
  for +er: {D1.inert.ok(rest) == True{} : Bool}
  {Concat.bound.plus(D1.inert.node(h1), D1.inert.node(h2), D1.inert.node(rest))
    == Concat.bound.plus(h1, h2, rest) : Maybe<&2, Concat.Let>}

def inert.concat.plus(h1, h2, rest, e1, er):
  match rest:
    case Tree.NCons{+h3, +rhs}:
      +kb = Calls.kind.leaf(~D1.inert.blanks, h1)
      +lt = Calls.leaf.text(h1)
      +lhs = Concat.bound.plus(D1.inert.node(h1), D1.inert.node(h2), D1.inert.node(Tree.NCons{h3, rhs}))
      %inert.concat.named(h2, h3, rhs, inert.ok_t(h3, rhs, er)) : {lhs == Lazy.stop(Maybe<&2, Concat.Let>,
        Bool.not(String.eq(lt, "+")), None{}, _u => _) : Maybe<&2, Concat.Let>}
      %M1.inert.eq_keep(kb, lt, "+", inert.leaf_fits(h1, e1), {==}) : {lhs == Lazy.stop(Maybe<&2, Concat.Let>,
        Bool.not(_), None{}, _u => Concat.bound.named(D1.inert.node(h2), D1.inert.node(h3), D1.inert.node(rhs)))
        : Maybe<&2, Concat.Let>}
      %inert.leaf_text(h1) : {lhs == Lazy.stop(Maybe<&2, Concat.Let>, Bool.not(String.eq(_, "+")), None{},
        _u => Concat.bound.named(D1.inert.node(h2), D1.inert.node(h3), D1.inert.node(rhs)))
        : Maybe<&2, Concat.Let>}
      {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a statement's own tokens read that way make the let they made
law inert.concat.bound:
  for kids: Tree.Node
  for +e: {D1.inert.ok(kids) == True{} : Bool}
  {Concat.bound(D1.inert.node(kids)) == Concat.bound(kids) : Maybe<&2, Concat.Let>}

def inert.concat.bound(kids, e):
  match kids:
    case Tree.NCons{+h1, +rest}:
      match rest:
        case Tree.NCons{+h2, +r}:
          +e1 = inert.ok_h(h1, Tree.NCons{h2, r}, e)
          +er = inert.ok_t(h2, r, inert.ok_t(h1, Tree.NCons{h2, r}, e))
          inert.either(Maybe<&2, Concat.Let>, Calls.kind.leaf(~Calls.kind.oper, D1.inert.node(h1)),
            Calls.kind.leaf(~Calls.kind.oper, h1),
            Concat.bound.plus(D1.inert.node(h1), D1.inert.node(h2), D1.inert.node(r)),
            Concat.bound.plus(h1, h2, r),
            Concat.bound.named(D1.inert.node(h1), D1.inert.node(h2), D1.inert.node(r)),
            Concat.bound.named(h1, h2, r), inert.oper(h1), inert.concat.plus(h1, h2, r, e1, er),
            inert.concat.named(h1, h2, r, er))
        case Tree.Leaf{x}: {==}
        case Tree.Group{x, y, z}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# the lets after a statement read that way are the ones they were
law inert.concat.after:
  for kind: Tree.StmtKind
  for +kids: Tree.Node
  for +lets: List<&2, Concat.Let>
  for +e: {D1.inert.ok(kids) == True{} : Bool}
  {Concat.after(kind, D1.inert.node(kids), lets) == Concat.after(kind, kids, lets) : List<&2, Concat.Let>}

def inert.concat.after(kind, kids, lets, e):
  match kind:
    case Tree.SLet{}:
      Equal.cong(Maybe<&2, Concat.Let>, List<&2, Concat.Let>, z => Concat.push(z, lets),
        Concat.bound(D1.inert.node(kids)), Concat.bound(kids), inert.concat.bound(kids, e))
    case Tree.SDef{}: {==}
    case Tree.SType{}: {==}
    case Tree.SLaw{}: {==}
    case Tree.SImport{}: {==}
    case Tree.SCase{}: {==}
    case Tree.SFor{}: {==}
    case Tree.STerm{}: {==}

# a self-call's arguments read that way hit as they did
law inert.concat.hits:
  for as: List<&2, Tree.Node>
  for +params: List<&2, String>
  for +lets: List<&2, Concat.Let>
  for +path: String
  for +acc: List<&2, F.Finding>
  for +e: {inert.noks(as) == True{} : Bool}
  {Concat.hits(inert.nodes(as), params, lets, path, acc) == Concat.hits(as, params, lets, path, acc)
    : List<&2, F.Finding>}

def inert.concat.hits(as, params, lets, path, acc, e):
  match as:
    case Nil{}: {==}
    case Con{+a, +rest}:
      +slot = Maybe.default(&2, String, List.head(&2, String, params), "")
      +nx = Concat.hit(Concat.seen(D1.inert.node(a), lets), slot, path, acc)
      %inert.concat.seen(a, lets, M1.inert.and_l(D1.inert.ok(a), inert.noks(rest), e)) : {Concat.hits(
        inert.nodes(rest), List.tail(&2, String, params), lets, path, nx) == Concat.hits(rest, List.tail(&2, String,
          params), lets, path, Concat.hit(_, slot, path, acc)) : List<&2, F.Finding>}
      inert.concat.hits(rest, List.tail(&2, String, params), lets, path, nx, M1.inert.and_r(D1.inert.ok(a),
        inert.noks(rest), e))

# a name then a group: the self-call's arguments, the group and the rest
# walked as they were
law inert.concat.lg:
  for +b: Bool
  for +t: String
  for +o: String
  for +name: String
  for +params: List<&2, String>
  for +lets: List<&2, Concat.Let>
  for +path: String
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  for ik: {Concat.walk(D1.inert.node(kids), name, params, lets, path) == Concat.walk(kids, name, params, lets, path)
    : List<&2, F.Finding>}
  for ir: {Concat.walk(D1.inert.node(r2), name, params, lets, path) == Concat.walk(r2, name, params, lets, path)
    : List<&2, F.Finding>}
  {List.concat(&2, F.Finding, [Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(String.eq(o, "("),
    String.eq(D1.inert.keep(b, t), name))), [], _u => Concat.hits(Calls.args(D1.inert.node(kids)), params, lets,
      path, [])), Concat.walk(D1.inert.node(kids), name, params, lets, path), Concat.walk(D1.inert.node(r2), name,
        params, lets, path)])
    == List.concat(&2, F.Finding, [Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(String.eq(o, "("),
      String.eq(t, name))), [], _u => Concat.hits(Calls.args(kids), params, lets, path, [])), Concat.walk(kids, name,
        params, lets, path), Concat.walk(r2, name, params, lets, path)]) : List<&2, F.Finding>}

def inert.concat.lg(b, t, o, name, params, lets, path, kids, r2, ef, en, ek, ik, ir):
  +aa = Calls.args(kids)
  +hi = Concat.hits(Calls.args(D1.inert.node(kids)), params, lets, path, [])
  +eh = Equal.trans(List<&2, F.Finding>, hi, Concat.hits(inert.nodes(aa), params, lets, path, []), Concat.hits(aa,
    params, lets, path, []), Equal.cong(List<&2, Tree.Node>, List<&2, F.Finding>,
      z => Concat.hits(z, params, lets, path, []),
      Calls.args(D1.inert.node(kids)), inert.nodes(aa), inert.args(kids)),
    inert.concat.hits(aa, params, lets, path, [], inert.ok.args.go(kids, Tree.NNil{}, [], ek, {==}, {==})))
  inert.cat3(Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(String.eq(o, "("), String.eq(D1.inert.keep(b, t),
    name))), [], _u => hi), Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(String.eq(o, "("), String.eq(t, name))),
      [], _u => Concat.hits(aa, params, lets, path, [])),
    Concat.walk(D1.inert.node(kids), name, params, lets, path), Concat.walk(kids, name, params, lets, path),
    Concat.walk(D1.inert.node(r2), name, params, lets, path), Concat.walk(r2, name, params, lets, path),
    inert.stop(Bool.not(Bool.and(String.eq(o, "("), String.eq(D1.inert.keep(b, t), name))), Bool.not(Bool.and(
      String.eq(o, "("), String.eq(t, name))), hi, Concat.hits(aa, params, lets, path, []),
      Equal.cong(Bool, Bool, z => Bool.not(Bool.and(String.eq(o, "("), z)), String.eq(D1.inert.keep(b, t), name),
        String.eq(t, name), M1.inert.eq_keep(b, t, name, ef, en)), eh),
    ik, ir)

# concat's walk reads no string: a leaf's text is compared with the def's
# name, which no string equals, and an argument's appends only with names
law inert.concat.walk:
  for nn: Tree.Node
  for +name: String
  for +params: List<&2, String>
  for +lets: List<&2, Concat.Let>
  for +path: String
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Concat.walk(D1.inert.node(nn), name, params, lets, path) == Concat.walk(nn, name, params, lets, path)
    : List<&2, F.Finding>}

def inert.concat.walk(nn, name, params, lets, path, en, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{o, +kids, +cl}:
                      match o:
                        case Lex.Tok{+ok, +ot, +ol, +oc}:
                          +lf = {Tree.Leaf{Lex.Tok{k, t, l, c}} : Tree.Node}
                          +gp = {Tree.Group{Lex.Tok{ok, ot, ol, oc}, kids, cl} : Tree.Node}
                          +eg = inert.ok_t(lf, Tree.NCons{gp, r2}, e)
                          +ec = inert.ok_h(gp, r2, eg)
                          inert.concat.lg(D1.inert.blanks(k), t, ot, name, params, lets, path, kids, r2,
                            inert.ok_h(lf, Tree.NCons{gp, r2}, e), en, ec,
                            inert.concat.walk(kids, name, params, lets, path, en, ec),
                            inert.concat.walk(r2, name, params, lets, path, en, inert.ok_t(gp, r2, eg)))
                    case Tree.Leaf{x}:
                      inert.concat.walk(rest, name, params, lets, path, en,
                        inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.Stmt{x, y, z}:
                      inert.concat.walk(rest, name, params, lets, path, en,
                        inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NNil{}:
                      inert.concat.walk(rest, name, params, lets, path, en,
                        inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NCons{x, y}:
                      inert.concat.walk(rest, name, params, lets, path, en,
                        inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NNil{}: {==}
        case Tree.Group{+o, +kids, +cl}:
          inert.cat2(Concat.walk(D1.inert.node(kids), name, params, lets, path),
            Concat.walk(kids, name, params, lets, path),
            Concat.walk(D1.inert.node(rest), name, params, lets, path), Concat.walk(rest, name, params, lets, path),
            inert.concat.walk(kids, name, params, lets, path, en, inert.ok_h(Tree.Group{o, kids, cl}, rest, e)),
            inert.concat.walk(rest, name, params, lets, path, en, inert.ok_t(Tree.Group{o, kids, cl}, rest, e)))
        case Tree.Stmt{+sk, +kids, +body}:
          +es = inert.ok_h(Tree.Stmt{sk, kids, body}, rest, e)
          +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es)
          +la = Concat.after(sk, kids, lets)
          +li = Concat.after(sk, D1.inert.node(kids), lets)
          inert.cat3(Concat.walk(D1.inert.node(kids), name, params, lets, path), Concat.walk(kids, name, params, lets,
            path), Concat.walk(D1.inert.node(body), name, params, lets, path), Concat.walk(body, name, params, lets,
              path), Concat.walk(D1.inert.node(rest), name, params, li, path), Concat.walk(rest, name, params, la,
                path),
            inert.concat.walk(kids, name, params, lets, path, en, ek),
            inert.concat.walk(body, name, params, lets, path, en, M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body),
              es)),
            Equal.trans(List<&2, F.Finding>, Concat.walk(D1.inert.node(rest), name, params, li, path),
              Concat.walk(D1.inert.node(rest), name, params, la, path), Concat.walk(rest, name, params, la, path),
              Equal.cong(List<&2, Concat.Let>, List<&2, F.Finding>, z => Concat.walk(D1.inert.node(rest), name,
                params, z, path), li, la, inert.concat.after(sk, kids, lets, ek)),
              inert.concat.walk(rest, name, params, la, path, en, inert.ok_t(Tree.Stmt{sk, kids, body}, rest, e))))
        case Tree.NNil{}: inert.concat.walk(rest, name, params, lets, path, en, e)
        case Tree.NCons{x, y}:
          inert.concat.walk(rest, name, params, lets, path, en, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a parameter read that way has the name it had: only a name's text is read
law inert.param_name:
  for pp: Tree.Node
  {Calls.param_name(D1.inert.node(pp)) == Calls.param_name(pp) : String}

def inert.param_name(pp):
  match pp:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}: {==}
                case Lex.TUpper{}: inert.param_name(rest)
                case Lex.TDotted{}: inert.param_name(rest)
                case Lex.TWild{}: inert.param_name(rest)
                case Lex.TKey{}: inert.param_name(rest)
                case Lex.TNum{}: inert.param_name(rest)
                case Lex.TStr{}: inert.param_name(rest)
                case Lex.TChar{}: inert.param_name(rest)
                case Lex.TComment{}: inert.param_name(rest)
                case Lex.TSpace{}: inert.param_name(rest)
                case Lex.TNewline{}: inert.param_name(rest)
                case Lex.TOp{}: inert.param_name(rest)
                case Lex.TColon{}: {==}
                case Lex.TEq{}: inert.param_name(rest)
                case Lex.TBind{}: inert.param_name(rest)
                case Lex.TArrow{}: inert.param_name(rest)
                case Lex.TLam{}: inert.param_name(rest)
                case Lex.TAll{}: inert.param_name(rest)
                case Lex.TAmp{}: inert.param_name(rest)
                case Lex.TOpen{}: inert.param_name(rest)
                case Lex.TClose{}: inert.param_name(rest)
                case Lex.TComma{}: inert.param_name(rest)
        case Tree.Group{o, gk, cl}: inert.param_name(rest)
        case Tree.Stmt{sk, sks, sb}: inert.param_name(rest)
        case Tree.NNil{}: inert.param_name(rest)
        case Tree.NCons{x, y}: inert.param_name(rest)
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# the names of parameters read that way are the names they had
law inert.names.go:
  for ps: List<&2, Tree.Node>
  for +acc: List<&2, String>
  {Calls.names.go(inert.nodes(ps), acc) == Calls.names.go(ps, acc) : List<&2, String>}

def inert.names.go(ps, acc):
  match ps:
    case Nil{}: {==}
    case Con{+p, +rest}:
      %inert.param_name(p) : {Calls.names.go(inert.nodes(rest), Calls.param_name(D1.inert.node(p)) <> acc)
        == Calls.names.go(rest, _ <> acc) : List<&2, String>}
      inert.names.go(rest, Calls.param_name(D1.inert.node(p)) <> acc)

# the names of a def's parameters, its signature read that way
law inert.names:
  for +sig: Tree.Node
  {Calls.names(D1.inert.node(sig)) == Calls.names(sig) : List<&2, String>}

def inert.names(sig):
  +pp = Calls.params.of(sig)
  +lhs = Calls.names(D1.inert.node(sig))
  %inert.names.go(Calls.args(pp), []) : {lhs == _ : List<&2, String>}
  %inert.args(pp) : {lhs == Calls.names.go(_, []) : List<&2, String>}
  %inert.params.of(sig) : {lhs == Calls.names.go(Calls.args(_), []) : List<&2, String>}
  {==}

# concat over the defs read that way reports what it reports over the defs
law inert.concat.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  for +e: {inert.dok(ds) == True{} : Bool}
  {Concat.check.go(inert.defs(ds), path, acc) == Concat.check.go(ds, path, acc) : List<&2, F.Finding>}

def inert.concat.go(ds, path, acc, e):
  match ds:
    case Nil{}: {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +en = inert.dok.head(name, sig, body, rest, e)
      +eb = inert.dok.body(name, sig, body, rest, e)
      +ib = D1.inert.node(body)
      +isg = D1.inert.node(sig)
      +lst = Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, isg), [], _u => Concat.walk(ib, name, Calls.names(isg),
        [], path))
      %inert.stop(Calls.exempt(path, isg), Calls.exempt(path, sig), Concat.walk(ib, name, Calls.names(isg), [], path),
        Concat.walk(body, name, Calls.names(sig), [], path), inert.exempt(path, sig),
        Equal.trans(List<&2, F.Finding>, Concat.walk(ib, name, Calls.names(isg), [], path), Concat.walk(ib, name,
          Calls.names(sig), [], path), Concat.walk(body, name, Calls.names(sig), [], path),
          Equal.cong(List<&2, String>, List<&2, F.Finding>, z => Concat.walk(ib, name, z, [], path), Calls.names(isg),
            Calls.names(sig), inert.names(sig)),
          inert.concat.walk(body, name, Calls.names(sig), [], path, en, eb))) :
        {Concat.check.go(inert.defs(rest), path, lst <> acc) == Concat.check.go(rest, path, _ <> acc)
          : List<&2, F.Finding>}
      inert.concat.go(rest, path, lst <> acc, inert.dok.rest(name, sig, body, rest, e))

def Laws.inert_concat(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, ok, ok2, e):
  M1.inert.via(Tree.Node, z => Concat.check.go(Calls.defs(z), path, []), tree, tree2, D1.inert.node(tree),
    D1.inert.node(tree2),
    inert.lift(z => Concat.check.go(z, path, []), tree, inert.concat.go(Calls.defs(tree), path, [], inert.dok.of(tree,
      ok))),
    inert.lift(z => Concat.check.go(z, path, []), tree2, inert.concat.go(Calls.defs(tree2), path, [],
      inert.dok.of(tree2, ok2))),
    e)

# unit
# ----

# a maybe token, read that way
def inert.mtok(mm: Maybe<&2, Lex.Tok>) -> Maybe<&2, Lex.Tok>:
  match mm:
    case None{}: None{}
    case Some{tok}: Some{D1.inert.tok(tok)}

# a maybe token as the lexer makes it
def inert.mfits(mm: Maybe<&2, Lex.Tok>) -> Bool:
  match mm:
    case None{}: True{}
    case Some{tok}: D1.inert.fits(tok)

# a token read that way is the literal one it was: a number is never cut
law inert.unit.one_of:
  for mm: Maybe<&2, Lex.Tok>
  {UnitRule.one_of(inert.mtok(mm)) == UnitRule.one_of(mm) : Maybe<&2, Lex.Tok>}

def inert.unit.one_of(mm):
  match mm:
    case None{}: {==}
    case Some{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}:
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

# which literal an operator's finding points at, from the two literals
def inert.unit.whichp(+op: String, +right: Maybe<&2, Lex.Tok>, left: Maybe<&2, Lex.Tok>) -> Maybe<&2, Lex.Tok>:
  Bool.pick(Maybe<&2, Lex.Tok>, String.eq(op, "*"), UnitRule.either(right, left),
    Bool.pick(Maybe<&2, Lex.Tok>, String.eq(op, "/"), right, None{}))

# the literal an operator points at, its neighbours read that way
law inert.unit.which:
  for +op: String
  for +prev: Maybe<&2, Lex.Tok>
  for +nxt: Maybe<&2, Lex.Tok>
  {UnitRule.which(op, inert.mtok(prev), inert.mtok(nxt)) == UnitRule.which(op, prev, nxt) : Maybe<&2, Lex.Tok>}

def inert.unit.which(op, prev, nxt):
  +lhs = UnitRule.which(op, inert.mtok(prev), inert.mtok(nxt))
  %inert.unit.one_of(nxt) : {lhs == inert.unit.whichp(op, _, UnitRule.one_of(prev)) : Maybe<&2, Lex.Tok>}
  %inert.unit.one_of(prev) : {lhs == inert.unit.whichp(op, UnitRule.one_of(inert.mtok(nxt)), _) : Maybe<&2, Lex.Tok>}
  {==}

# a leaf read that way hits as it did: only an operator's text is read
law inert.unit.op_hit:
  for hot: Bool
  for tok: Lex.Tok
  for +prev: Maybe<&2, Lex.Tok>
  for +nxt: Maybe<&2, Lex.Tok>
  for +path: String
  {UnitRule.op_hit(D1.inert.tok(tok), inert.mtok(prev), inert.mtok(nxt), path, hot)
    == UnitRule.op_hit(tok, prev, nxt, path, hot) : List<&2, F.Finding>}

def inert.unit.op_hit(hot, tok, prev, nxt, path):
  match hot:
    case False{}:
      match tok:
        case Lex.Tok{k, t, l, c}: {==}
    case True{}:
      match tok:
        case Lex.Tok{k, +t, l, c}:
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
            case Lex.TOp{}:
              Equal.cong(Maybe<&2, Lex.Tok>, List<&2, F.Finding>, z => UnitRule.cite(z, path),
                UnitRule.which(t, inert.mtok(prev), inert.mtok(nxt)), UnitRule.which(t, prev, nxt),
                inert.unit.which(t, prev, nxt))
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

# the first leaf of a chain read that way is the leaf it was, read that way
law inert.unit.first_tok:
  for nn: Tree.Node
  {UnitRule.first_tok(D1.inert.node(nn)) == inert.mtok(UnitRule.first_tok(nn)) : Maybe<&2, Lex.Tok>}

def inert.unit.first_tok(nn):
  match nn:
    case Tree.NCons{h, r}:
      match h:
        case Tree.Leaf{tok}: {==}
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a token dropped or kept, read that way
law inert.mt_pick:
  for c: Bool
  for +tok: Lex.Tok
  {Bool.pick(Maybe<&2, Lex.Tok>, c, None{}, Some{D1.inert.tok(tok)})
    == inert.mtok(Bool.pick(Maybe<&2, Lex.Tok>, c, None{}, Some{tok})) : Maybe<&2, Lex.Tok>}

def inert.mt_pick(c, _tok):
  match c:
    case True{}: {==}
    case False{}: {==}

# a token dropped or kept as the lexer makes it
law inert.mf_pick:
  for c: Bool
  for +tok: Lex.Tok
  for e: {D1.inert.fits(tok) == True{} : Bool}
  {inert.mfits(Bool.pick(Maybe<&2, Lex.Tok>, c, None{}, Some{tok})) == True{} : Bool}

def inert.mf_pick(c, _tok, e):
  match c:
    case True{}: {==}
    case False{}: e

# what a leaf leaves behind, read that way
law inert.unit.after:
  for tok: Lex.Tok
  {UnitRule.after(D1.inert.tok(tok)) == inert.mtok(UnitRule.after(tok)) : Maybe<&2, Lex.Tok>}

def inert.unit.after(tok):
  match tok:
    case Lex.Tok{+k, +t, +l, +c}: inert.mt_pick(UnitRule.op_kind(k), Lex.Tok{k, t, l, c})

# what a leaf leaves behind as the lexer makes it
law inert.unit.mf_after:
  for tok: Lex.Tok
  for +e: {D1.inert.fits(tok) == True{} : Bool}
  {inert.mfits(UnitRule.after(tok)) == True{} : Bool}

def inert.unit.mf_after(tok, e):
  match tok:
    case Lex.Tok{+k, +t, +l, +c}: inert.mf_pick(UnitRule.op_kind(k), Lex.Tok{k, t, l, c}, e)

# an argument read that way is the literal one it was
law inert.unit.arg_one:
  for aa: Tree.Node
  {UnitRule.arg_one(D1.inert.node(aa)) == UnitRule.arg_one(aa) : Maybe<&2, Lex.Tok>}

def inert.unit.arg_one(aa):
  match aa:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Leaf{tok}:
          match r:
            case Tree.NNil{}: inert.unit.one_of(Some{tok})
            case Tree.Leaf{x}: {==}
            case Tree.Group{x, y, z}: {==}
            case Tree.Stmt{x, y, z}: {==}
            case Tree.NCons{x, y}: {==}
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# the last argument read that way is the literal one it was
law inert.unit.last_one:
  for as: List<&2, Tree.Node>
  {UnitRule.last_one(inert.nodes(as)) == UnitRule.last_one(as) : Maybe<&2, Lex.Tok>}

def inert.unit.last_one(as):
  match as:
    case Nil{}: {==}
    case Con{h, +rest}:
      match rest:
        case Nil{}: inert.unit.arg_one(h)
        case Con{x, y}: inert.unit.last_one(rest)

# the last argument that is the literal one, the arguments read that way
law inert.unit.any_one:
  for as: List<&2, Tree.Node>
  {UnitRule.any_one(inert.nodes(as)) == UnitRule.any_one(as) : Maybe<&2, Lex.Tok>}

def inert.unit.any_one(as):
  match as:
    case Nil{}: {==}
    case Con{+h, +rest}:
      %inert.unit.any_one(rest) : {UnitRule.any_one(inert.nodes(Con{h, rest})) == UnitRule.either(_,
        UnitRule.arg_one(h)) : Maybe<&2, Lex.Tok>}
      %inert.unit.arg_one(h) : {UnitRule.any_one(inert.nodes(Con{h, rest})) == UnitRule.either(
        UnitRule.any_one(inert.nodes(rest)), _) : Maybe<&2, Lex.Tok>}
      {==}

# a divide's divisor, the arguments read that way
law inert.unit.on_div_is:
  for d: Bool
  for +as: List<&2, Tree.Node>
  for +path: String
  {UnitRule.on_div_is(d, inert.nodes(as), path) == UnitRule.on_div_is(d, as, path) : List<&2, F.Finding>}

def inert.unit.on_div_is(d, as, path):
  match d:
    case False{}: {==}
    case True{}:
      Equal.cong(Maybe<&2, Lex.Tok>, List<&2, F.Finding>, z => UnitRule.cite(z, path),
        UnitRule.last_one(inert.nodes(as)), UnitRule.last_one(as), inert.unit.last_one(as))

# the three divides
def inert.unit.divs() -> List<&2, String>:
  ["Nat.div", "U32.div", "F32.div"]

# the three multiplies
def inert.unit.muls() -> List<&2, String>:
  ["Nat.mul", "U32.mul", "F32.mul"]

# a multiply or a divide, the name and arguments read that way
law inert.unit.on_op_is:
  for m: Bool
  for +b: Bool
  for +t: String
  for +as: List<&2, Tree.Node>
  for +path: String
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  {UnitRule.on_op_is(m, D1.inert.keep(b, t), inert.nodes(as), path) == UnitRule.on_op_is(m, t, as, path)
    : List<&2, F.Finding>}

def inert.unit.on_op_is(m, b, t, as, path, ef):
  match m:
    case True{}:
      Equal.cong(Maybe<&2, Lex.Tok>, List<&2, F.Finding>, z => UnitRule.cite(z, path),
        UnitRule.any_one(inert.nodes(as)), UnitRule.any_one(as), inert.unit.any_one(as))
    case False{}:
      +cd = List.contains(~String, ~String.eq, inert.unit.divs(), D1.inert.keep(b, t))
      %inert.contains_keep(inert.unit.divs(), b, t, ef, {==}) : {UnitRule.on_div(D1.inert.keep(b, t),
        inert.nodes(as), path) == UnitRule.on_div_is(_, as, path) : List<&2, F.Finding>}
      inert.unit.on_div_is(cd, as, path)

# a call's identity operands, the name and arguments read that way
law inert.unit.on_op:
  for +b: Bool
  for +t: String
  for +as: List<&2, Tree.Node>
  for +path: String
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  {UnitRule.on_op(D1.inert.keep(b, t), inert.nodes(as), path) == UnitRule.on_op(t, as, path) : List<&2, F.Finding>}

def inert.unit.on_op(b, t, as, path, ef):
  +kt = D1.inert.keep(b, t)
  %inert.contains_keep(inert.unit.muls(), b, t, ef, {==}) : {UnitRule.on_op(kt, inert.nodes(as), path)
    == UnitRule.on_op_is(_, t, as, path) : List<&2, F.Finding>}
  inert.unit.on_op_is(List.contains(~String, ~String.eq, inert.unit.muls(), kt), b, t, as, path, ef)

# an application's findings, the name and the group read that way
law inert.unit.own:
  for call: Bool
  for hot: Bool
  for +b: Bool
  for +t: String
  for +kids: Tree.Node
  for +path: String
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  {UnitRule.own_of(call, D1.inert.keep(b, t), D1.inert.node(kids), path, hot)
    == UnitRule.own_of(call, t, kids, path, hot) : List<&2, F.Finding>}

def inert.unit.own(call, hot, b, t, kids, path, ef):
  match call:
    case False{}: {==}
    case True{}:
      match hot:
        case False{}: {==}
        case True{}:
          %Equal.sym(List<&2, Tree.Node>, Calls.args(D1.inert.node(kids)), inert.nodes(Calls.args(kids)),
            inert.args(kids)) : {UnitRule.on_op(D1.inert.keep(b, t), _, path) == UnitRule.on_op(t, Calls.args(kids),
              path) : List<&2, F.Finding>}
          inert.unit.on_op(b, t, Calls.args(kids), path, ef)

# an application's findings, the callee and the group read that way
law inert.unit.callee:
  for +call: Bool
  for +hot: Bool
  for prev: Maybe<&2, Lex.Tok>
  for +kids: Tree.Node
  for +path: String
  for +ep: {inert.mfits(prev) == True{} : Bool}
  {UnitRule.own_of(call, UnitRule.callee(inert.mtok(prev)), D1.inert.node(kids), path, hot)
    == UnitRule.own_of(call, UnitRule.callee(prev), kids, path, hot) : List<&2, F.Finding>}

def inert.unit.callee(call, hot, prev, kids, path, ep):
  match prev:
    case None{}: inert.unit.own(call, hot, False{}, "", kids, path, {==})
    case Some{tok}:
      match tok:
        case Lex.Tok{+k, +t, l, c}: inert.unit.own(call, hot, D1.inert.blanks(k), t, kids, path, ep)

# a statement, read that way: its tokens, its body and the rest walked as
# they were, a case arm hot by its self-call as it was
law inert.unit.stmt:
  for sk: Tree.StmtKind
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +prev: Maybe<&2, Lex.Tok>
  for +self: String
  for +path: String
  for +hot: Bool
  for +es: {D1.inert.marked(self) == False{} : Bool}
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  for +eb: {D1.inert.ok(body) == True{} : Bool}
  for i1: {UnitRule.walk(D1.inert.node(kids), None{}, self, path, False{}) == UnitRule.walk(kids, None{}, self,
    path, False{}) : List<&2, F.Finding>}
  for i2: {UnitRule.walk(D1.inert.node(kids), None{}, self, path, hot) == UnitRule.walk(kids, None{}, self, path,
    hot) : List<&2, F.Finding>}
  for i3: {UnitRule.walk(D1.inert.node(body), None{}, self, path, Bool.and(hot, Calls.calls(body, self)))
    == UnitRule.walk(body, None{}, self, path, Bool.and(hot, Calls.calls(body, self))) : List<&2, F.Finding>}
  for i4: {UnitRule.walk(D1.inert.node(body), None{}, self, path, hot) == UnitRule.walk(body, None{}, self, path,
    hot) : List<&2, F.Finding>}
  for i5: {UnitRule.walk(D1.inert.node(rest), None{}, self, path, hot) == UnitRule.walk(rest, None{}, self, path,
    hot) : List<&2, F.Finding>}
  {UnitRule.walk(Tree.NCons{Tree.Stmt{sk, D1.inert.node(kids), D1.inert.node(body)}, D1.inert.node(rest)},
    inert.mtok(prev), self, path, hot)
    == UnitRule.walk(Tree.NCons{Tree.Stmt{sk, kids, body}, rest}, prev, self, path, hot) : List<&2, F.Finding>}

def inert.unit.stmt(sk, kids, body, rest, _prev, self, path, hot, es, _ek, eb, i1, i2, i3, i4, i5):
  match sk:
    case Tree.SDef{}:
      inert.cat3(UnitRule.walk(D1.inert.node(kids), None{}, self, path, hot),
        UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(D1.inert.node(body), None{}, self, path, hot),
        UnitRule.walk(body, None{}, self, path, hot), UnitRule.walk(D1.inert.node(rest), None{}, self, path, hot),
        UnitRule.walk(rest, None{}, self, path, hot), i2, i4, i5)
    case Tree.SType{}:
      inert.cat3(UnitRule.walk(D1.inert.node(kids), None{}, self, path, hot),
        UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(D1.inert.node(body), None{}, self, path, hot),
        UnitRule.walk(body, None{}, self, path, hot), UnitRule.walk(D1.inert.node(rest), None{}, self, path, hot),
        UnitRule.walk(rest, None{}, self, path, hot), i2, i4, i5)
    case Tree.SLaw{}:
      inert.cat3(UnitRule.walk(D1.inert.node(kids), None{}, self, path, hot),
        UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(D1.inert.node(body), None{}, self, path, hot),
        UnitRule.walk(body, None{}, self, path, hot), UnitRule.walk(D1.inert.node(rest), None{}, self, path, hot),
        UnitRule.walk(rest, None{}, self, path, hot), i2, i4, i5)
    case Tree.SImport{}:
      inert.cat3(UnitRule.walk(D1.inert.node(kids), None{}, self, path, hot),
        UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(D1.inert.node(body), None{}, self, path, hot),
        UnitRule.walk(body, None{}, self, path, hot), UnitRule.walk(D1.inert.node(rest), None{}, self, path, hot),
        UnitRule.walk(rest, None{}, self, path, hot), i2, i4, i5)
    case Tree.SCase{}:
      +ch = Bool.and(hot, Calls.calls(body, self))
      +ci = Bool.and(hot, Calls.calls(D1.inert.node(body), self))
      inert.cat3(UnitRule.walk(D1.inert.node(kids), None{}, self, path, False{}),
        UnitRule.walk(kids, None{}, self, path, False{}), UnitRule.walk(D1.inert.node(body), None{}, self, path, ci),
        UnitRule.walk(body, None{}, self, path, ch), UnitRule.walk(D1.inert.node(rest), None{}, self, path, hot),
        UnitRule.walk(rest, None{}, self, path, hot), i1,
        Equal.trans(List<&2, F.Finding>, UnitRule.walk(D1.inert.node(body), None{}, self, path, ci),
          UnitRule.walk(D1.inert.node(body), None{}, self, path, ch), UnitRule.walk(body, None{}, self, path, ch),
          Equal.cong(Bool, List<&2, F.Finding>, z => UnitRule.walk(D1.inert.node(body), None{}, self, path,
            Bool.and(hot, z)), Calls.calls(D1.inert.node(body), self), Calls.calls(body, self),
            inert.calls(body, self, es, eb)), i3), i5)
    case Tree.SFor{}:
      inert.cat3(UnitRule.walk(D1.inert.node(kids), None{}, self, path, hot),
        UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(D1.inert.node(body), None{}, self, path, hot),
        UnitRule.walk(body, None{}, self, path, hot), UnitRule.walk(D1.inert.node(rest), None{}, self, path, hot),
        UnitRule.walk(rest, None{}, self, path, hot), i2, i4, i5)
    case Tree.SLet{}:
      inert.cat3(UnitRule.walk(D1.inert.node(kids), None{}, self, path, hot),
        UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(D1.inert.node(body), None{}, self, path, hot),
        UnitRule.walk(body, None{}, self, path, hot), UnitRule.walk(D1.inert.node(rest), None{}, self, path, hot),
        UnitRule.walk(rest, None{}, self, path, hot), i2, i4, i5)
    case Tree.STerm{}:
      inert.cat3(UnitRule.walk(D1.inert.node(kids), None{}, self, path, hot),
        UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(D1.inert.node(body), None{}, self, path, hot),
        UnitRule.walk(body, None{}, self, path, hot), UnitRule.walk(D1.inert.node(rest), None{}, self, path, hot),
        UnitRule.walk(rest, None{}, self, path, hot), i2, i4, i5)

# unit's walk reads no string: an operator's text, a callee's against the
# multiplies and divides, and a number's against the one
law inert.unit.walk:
  for nn: Tree.Node
  for +prev: Maybe<&2, Lex.Tok>
  for +self: String
  for +path: String
  for +hot: Bool
  for +es: {D1.inert.marked(self) == False{} : Bool}
  for +ep: {inert.mfits(prev) == True{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {UnitRule.walk(D1.inert.node(nn), inert.mtok(prev), self, path, hot) == UnitRule.walk(nn, prev, self, path, hot)
    : List<&2, F.Finding>}

def inert.unit.walk(nn, prev, self, path, hot, es, ep, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              +tk = {Lex.Tok{k, t, l, c} : Lex.Tok}
              +ir = D1.inert.node(rest)
              +lhs = UnitRule.walk(D1.inert.node(Tree.NCons{Tree.Leaf{tk}, rest}), inert.mtok(prev), self, path, hot)
              %inert.unit.walk(rest, UnitRule.after(tk), self, path, hot, es, inert.unit.mf_after(tk,
                inert.ok_h(Tree.Leaf{tk}, rest, e)), inert.ok_t(Tree.Leaf{tk}, rest, e)) : {lhs
                == List.append(&2, F.Finding, UnitRule.op_hit(tk, prev, UnitRule.first_tok(rest), path, hot), _)
                : List<&2, F.Finding>}
              %inert.unit.after(tk) : {lhs == List.append(&2, F.Finding, UnitRule.op_hit(tk, prev,
                UnitRule.first_tok(rest), path, hot), UnitRule.walk(ir, _, self, path, hot)) : List<&2, F.Finding>}
              %inert.unit.op_hit(hot, tk, prev, UnitRule.first_tok(rest), path) : {lhs == List.append(&2, F.Finding, _,
                UnitRule.walk(ir, UnitRule.after(D1.inert.tok(tk)), self, path, hot)) : List<&2, F.Finding>}
              %inert.unit.first_tok(rest) : {lhs == List.append(&2, F.Finding, UnitRule.op_hit(D1.inert.tok(tk),
                inert.mtok(prev), _, path, hot), UnitRule.walk(ir, UnitRule.after(D1.inert.tok(tk)), self, path, hot))
                : List<&2, F.Finding>}
              {==}
        case Tree.Group{o, +kids, +cl}:
          match o:
            case Lex.Tok{+ok, +ot, +ol, +oc}:
              +gp = {Tree.Group{Lex.Tok{ok, ot, ol, oc}, kids, cl} : Tree.Node}
              inert.cat3(UnitRule.walk(D1.inert.node(kids), None{}, self, path, hot), UnitRule.walk(kids, None{},
                self, path, hot),
                UnitRule.own_of(String.eq(ot, "("), UnitRule.callee(inert.mtok(prev)), D1.inert.node(kids), path,
                  hot), UnitRule.own_of(String.eq(ot, "("), UnitRule.callee(prev), kids, path, hot),
                UnitRule.walk(D1.inert.node(rest), None{}, self, path, hot), UnitRule.walk(rest, None{}, self, path,
                  hot),
                inert.unit.walk(kids, None{}, self, path, hot, es, {==}, inert.ok_h(gp, rest, e)),
                inert.unit.callee(String.eq(ot, "("), hot, prev, kids, path, ep),
                inert.unit.walk(rest, None{}, self, path, hot, es, {==}, inert.ok_t(gp, rest, e)))
        case Tree.Stmt{+sk, +kids, +body}:
          +es2 = inert.ok_h(Tree.Stmt{sk, kids, body}, rest, e)
          +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)
          +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)
          +er = inert.ok_t(Tree.Stmt{sk, kids, body}, rest, e)
          inert.unit.stmt(sk, kids, body, rest, prev, self, path, hot, es, ek, eb,
            inert.unit.walk(kids, None{}, self, path, False{}, es, {==}, ek),
            inert.unit.walk(kids, None{}, self, path, hot, es, {==}, ek),
            inert.unit.walk(body, None{}, self, path, Bool.and(hot, Calls.calls(body, self)), es, {==}, eb),
            inert.unit.walk(body, None{}, self, path, hot, es, {==}, eb),
            inert.unit.walk(rest, None{}, self, path, hot, es, {==}, er))
        case Tree.NNil{}: inert.unit.walk(rest, prev, self, path, hot, es, ep, e)
        case Tree.NCons{x, y}:
          inert.unit.walk(rest, prev, self, path, hot, es, ep, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# unit over the defs read that way reports what it reports over the defs
law inert.unit.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  for +e: {inert.dok(ds) == True{} : Bool}
  {UnitRule.check.go(inert.defs(ds), path, acc) == UnitRule.check.go(ds, path, acc) : List<&2, F.Finding>}

def inert.unit.go(ds, path, acc, e):
  match ds:
    case Nil{}: {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +en = inert.dok.head(name, sig, body, rest, e)
      +eb = inert.dok.body(name, sig, body, rest, e)
      +ib = D1.inert.node(body)
      +lst = Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Calls.calls(ib, name), Bool.not(Calls.exempt(path,
        D1.inert.node(sig))))), [], _u => UnitRule.walk(ib, None{}, name, path, True{}))
      %inert.stop(Bool.not(Bool.and(Calls.calls(ib, name), Bool.not(Calls.exempt(path, D1.inert.node(sig))))),
        Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))),
        UnitRule.walk(ib, None{}, name, path, True{}), UnitRule.walk(body, None{}, name, path, True{}),
        inert.gate(path, name, sig, body, en, eb), inert.unit.walk(body, None{}, name, path, True{}, en, {==}, eb)) :
        {UnitRule.check.go(inert.defs(rest), path, lst <> acc) == UnitRule.check.go(rest, path, _ <> acc)
          : List<&2, F.Finding>}
      inert.unit.go(rest, path, lst <> acc, inert.dok.rest(name, sig, body, rest, e))

def Laws.inert_unit(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, ok, ok2, e):
  M1.inert.via(Tree.Node, z => UnitRule.check.go(Calls.defs(z), path, []), tree, tree2, D1.inert.node(tree),
    D1.inert.node(tree2),
    inert.lift(z => UnitRule.check.go(z, path, []), tree, inert.unit.go(Calls.defs(tree), path, [], inert.dok.of(tree,
      ok))),
    inert.lift(z => UnitRule.check.go(z, path, []), tree2, inert.unit.go(Calls.defs(tree2), path, [],
      inert.dok.of(tree2, ok2))),
    e)

# thunk
# -----

# a name is never cut, read in the order thunk tests it
law inert.thunk.name_code:
  for k: Lex.TokKind
  {Bool.and(Lex.is_name(k), D1.inert.blanks(k)) == False{} : Bool}

def inert.thunk.name_code(k):
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

# a node read that way reads the parameter as it did: only name leaves are
# compared, and a name is never cut
law inert.thunk.reads:
  for nn: Tree.Node
  for +pp: String
  {Thunk.reads(D1.inert.node(nn), pp) == Thunk.reads(nn, pp) : Bool}

def inert.thunk.reads(nn, pp):
  match nn:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{+k, +t, l, c}:
          inert.guard(Lex.is_name(k), D1.inert.blanks(k), t,
            z => Bool.or(String.eq(z, pp), String.starts_with(z, pp ++ ".")), inert.thunk.name_code(k))
    case Tree.Group{o, +kids, cl}:
      inert.thunk.reads(kids, pp)
    case Tree.Stmt{sk, +kids, +body}:
      %inert.thunk.reads(kids, pp) : {Bool.or(Thunk.reads(D1.inert.node(kids), pp), Thunk.reads(D1.inert.node(body),
        pp)) == Bool.or(_, Thunk.reads(body, pp)) : Bool}
      %inert.thunk.reads(body, pp) : {Bool.or(Thunk.reads(D1.inert.node(kids), pp), Thunk.reads(D1.inert.node(body),
        pp)) == Bool.or(Thunk.reads(D1.inert.node(kids), pp), _) : Bool}
      {==}
    case Tree.NCons{+h, +t}:
      %inert.thunk.reads(h, pp) : {Bool.or(Thunk.reads(D1.inert.node(h), pp), Thunk.reads(D1.inert.node(t), pp))
        == Bool.or(_, Thunk.reads(t, pp)) : Bool}
      %inert.thunk.reads(t, pp) : {Bool.or(Thunk.reads(D1.inert.node(h), pp), Thunk.reads(D1.inert.node(t), pp))
        == Bool.or(Thunk.reads(D1.inert.node(h), pp), _) : Bool}
      {==}
    case Tree.NNil{}:
      {==}

# a chain read that way ends a body as it did: kinds are kept
law inert.thunk.ends:
  for nn: Tree.Node
  {Thunk.ends(D1.inert.node(nn)) == Thunk.ends(nn) : Bool}

def inert.thunk.ends(nn):
  match nn:
    case Tree.NCons{h, t}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, s, l, c}: {==}
        case Tree.Group{a, b, c}: {==}
        case Tree.Stmt{a, b, c}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{a, b}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{a, b, c}: {==}
    case Tree.Stmt{a, b, c}: {==}
    case Tree.NNil{}: {==}

# the lead read that way is the lead: the group reads the parameter as it
# did, and a name parameter is never cut
law inert.thunk.lead:
  for +kp: Lex.TokKind
  for +pp: String
  for +kids: Tree.Node
  {Bool.and(Lex.is_name(kp), Bool.not(Thunk.reads(D1.inert.node(kids), D1.inert.keep(D1.inert.blanks(kp), pp))))
    == Bool.and(Lex.is_name(kp), Bool.not(Thunk.reads(kids, pp))) : Bool}

def inert.thunk.lead(kp, pp, kids):
  Equal.trans(Bool,
    Bool.and(Lex.is_name(kp), Bool.not(Thunk.reads(D1.inert.node(kids), D1.inert.keep(D1.inert.blanks(kp), pp)))),
    Bool.and(Lex.is_name(kp), Bool.not(Thunk.reads(kids, D1.inert.keep(D1.inert.blanks(kp), pp)))),
    Bool.and(Lex.is_name(kp), Bool.not(Thunk.reads(kids, pp))),
    Equal.cong(Bool, Bool, z => Bool.and(Lex.is_name(kp), Bool.not(z)),
      Thunk.reads(D1.inert.node(kids), D1.inert.keep(D1.inert.blanks(kp), pp)),
      Thunk.reads(kids, D1.inert.keep(D1.inert.blanks(kp), pp)),
      inert.thunk.reads(kids, D1.inert.keep(D1.inert.blanks(kp), pp))),
    inert.guard(Lex.is_name(kp), D1.inert.blanks(kp), pp, z => Bool.not(Thunk.reads(kids, z)),
      inert.thunk.name_code(kp)))

# past the name, read that way: the finding it gave
law inert.thunk.group:
  for +kp: Lex.TokKind
  for +pp: String
  for +ka: Lex.TokKind
  for +aa: String
  for +kn: Lex.TokKind
  for +nm: String
  for +ll: U32
  for +cc: U32
  for r3: Tree.Node
  for +name: String
  for +path: String
  for ea: {D1.inert.fits.go(D1.inert.blanks(ka), aa) == True{} : Bool}
  for ef: {D1.inert.fits.go(D1.inert.blanks(kn), nm) == True{} : Bool}
  for en: {D1.inert.marked(name) == False{} : Bool}
  {Thunk.site.group(kp, D1.inert.keep(D1.inert.blanks(kp), pp), D1.inert.keep(D1.inert.blanks(ka), aa),
    D1.inert.keep(D1.inert.blanks(kn), nm), ll, cc, D1.inert.node(r3), name, path)
    == Thunk.site.group(kp, pp, aa, nm, ll, cc, r3, name, path) : List<&2, F.Finding>}

def inert.thunk.group(kp, pp, ka, aa, kn, nm, ll, cc, r3, name, path, ea, ef, en):
  match r3:
    case Tree.NCons{h, +after}:
      match h:
        case Tree.Group{open, +kids, cl}:
          match open:
            case Lex.Tok{ko, +o, lo, co}:
              +f = Thunk.cite(ll, cc, name, path)
              +l1 = Bool.and(Lex.is_name(kp),
                Bool.not(Thunk.reads(D1.inert.node(kids), D1.inert.keep(D1.inert.blanks(kp), pp))))
              +a1 = String.eq(D1.inert.keep(D1.inert.blanks(ka), aa), "=>")
              +n1 = String.eq(D1.inert.keep(D1.inert.blanks(kn), nm), name)
              +e1 = Thunk.ends(D1.inert.node(after))
              +oo = String.eq(o, "(")
              %inert.thunk.lead(kp, pp, kids) : {Bool.pick(List<&2, F.Finding>, Thunk.hit(l1, a1, n1, oo, e1), [f], [])
                == Bool.pick(List<&2, F.Finding>, Thunk.hit(_, String.eq(aa, "=>"), String.eq(nm, name), oo,
                  Thunk.ends(after)), [f], []) : List<&2, F.Finding>}
              %M1.inert.eq_keep(D1.inert.blanks(ka), aa, "=>", ea, {==}) : {Bool.pick(List<&2, F.Finding>,
                Thunk.hit(l1, a1, n1, oo, e1), [f], [])
                == Bool.pick(List<&2, F.Finding>, Thunk.hit(l1, _, String.eq(nm, name), oo, Thunk.ends(after)), [f],
                  []) : List<&2, F.Finding>}
              %M1.inert.eq_keep(D1.inert.blanks(kn), nm, name, ef, en) : {Bool.pick(List<&2, F.Finding>,
                Thunk.hit(l1, a1, n1, oo, e1), [f], [])
                == Bool.pick(List<&2, F.Finding>, Thunk.hit(l1, a1, _, oo, Thunk.ends(after)), [f], [])
                  : List<&2, F.Finding>}
              %inert.thunk.ends(after) : {Bool.pick(List<&2, F.Finding>, Thunk.hit(l1, a1, n1, oo, e1), [f], [])
                == Bool.pick(List<&2, F.Finding>, Thunk.hit(l1, a1, n1, oo, _), [f], []) : List<&2, F.Finding>}
              {==}
        case Tree.Leaf{x}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# past `=>`, read that way: the finding it gave
law inert.thunk.name:
  for +kp: Lex.TokKind
  for +pp: String
  for +ka: Lex.TokKind
  for +aa: String
  for r2: Tree.Node
  for +name: String
  for +path: String
  for ea: {D1.inert.fits.go(D1.inert.blanks(ka), aa) == True{} : Bool}
  for en: {D1.inert.marked(name) == False{} : Bool}
  for e: {D1.inert.ok(r2) == True{} : Bool}
  {Thunk.site.name(kp, D1.inert.keep(D1.inert.blanks(kp), pp), D1.inert.keep(D1.inert.blanks(ka), aa),
    D1.inert.node(r2), name, path)
    == Thunk.site.name(kp, pp, aa, r2, name, path) : List<&2, F.Finding>}

def inert.thunk.name(kp, pp, ka, aa, r2, name, path, ea, en, e):
  match r2:
    case Tree.NCons{h, +r3}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+kn, +n, l, c}:
              inert.thunk.group(kp, pp, ka, aa, kn, n, l, c, r3, name, path, ea,
                M1.inert.and_l(D1.inert.fits.go(D1.inert.blanks(kn), n), D1.inert.ok(r3), e), en)
        case Tree.Group{x, y, z}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# past the parameter, read that way: the finding it gave
law inert.thunk.lam:
  for +kp: Lex.TokKind
  for +pp: String
  for rest: Tree.Node
  for +name: String
  for +path: String
  for en: {D1.inert.marked(name) == False{} : Bool}
  for +e: {D1.inert.ok(rest) == True{} : Bool}
  {Thunk.site.lam(kp, D1.inert.keep(D1.inert.blanks(kp), pp), D1.inert.node(rest), name, path)
    == Thunk.site.lam(kp, pp, rest, name, path) : List<&2, F.Finding>}

def inert.thunk.lam(kp, pp, rest, name, path, en, e):
  match rest:
    case Tree.NCons{h, +r2}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+ka, +a, l, c}:
              inert.thunk.name(kp, pp, ka, a, r2, name, path,
                M1.inert.and_l(D1.inert.fits.go(D1.inert.blanks(ka), a), D1.inert.ok(r2), e), en,
                M1.inert.and_r(D1.inert.fits.go(D1.inert.blanks(ka), a), D1.inert.ok(r2), e))
        case Tree.Group{x, y, z}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a node and the chain after it, read that way: the finding they gave
law inert.thunk.site:
  for hh: Tree.Node
  for rest: Tree.Node
  for +name: String
  for +path: String
  for en: {D1.inert.marked(name) == False{} : Bool}
  for e: {D1.inert.ok(rest) == True{} : Bool}
  {Thunk.site(D1.inert.node(hh), D1.inert.node(rest), name, path) == Thunk.site(hh, rest, name, path)
    : List<&2, F.Finding>}

def inert.thunk.site(hh, rest, name, path, en, e):
  match hh:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{+kp, +p, l, c}: inert.thunk.lam(kp, p, rest, name, path, en, e)
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# a chain read that way counts the lambda arguments it did: kinds are kept,
# and `=>` is never cut
law inert.thunk.lams:
  for nn: Tree.Node
  for +seen: Bool
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Thunk.lams(D1.inert.node(nn), seen) == Thunk.lams(nn, seen) : Nat}

def inert.thunk.lams(nn, seen, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, l, c}:
              +ef = M1.inert.and_l(D1.inert.fits.go(D1.inert.blanks(k), t), D1.inert.ok(rest), e)
              +er = M1.inert.and_r(D1.inert.fits.go(D1.inert.blanks(k), t), D1.inert.ok(rest), e)
              +p = Bool.pick(Nat, Bool.and(Lex.is_comma(k), seen), 1n, 0n)
              +s1 = Bool.and(Bool.not(Lex.is_comma(k)),
                Bool.or(seen, String.eq(D1.inert.keep(D1.inert.blanks(k), t), "=>")))
              %M1.inert.eq_keep(D1.inert.blanks(k), t, "=>", ef, {==}) : {Nat.add(p,
                Thunk.lams(D1.inert.node(rest), s1)) == Nat.add(p, Thunk.lams(rest,
                  Bool.and(Bool.not(Lex.is_comma(k)), Bool.or(seen, _)))) : Nat}
              Equal.cong(Nat, Nat, x => Nat.add(p, x), Thunk.lams(D1.inert.node(rest), s1), Thunk.lams(rest, s1),
                inert.thunk.lams(rest, s1, er))
        case Tree.Group{x, y, z}: inert.thunk.lams(rest, seen, M1.inert.and_r(D1.inert.ok(h), D1.inert.ok(rest), e))
        case Tree.Stmt{x, y, z}: inert.thunk.lams(rest, seen, M1.inert.and_r(D1.inert.ok(h), D1.inert.ok(rest), e))
        case Tree.NNil{}: inert.thunk.lams(rest, seen, M1.inert.and_r(D1.inert.ok(h), D1.inert.ok(rest), e))
        case Tree.NCons{x, y}: inert.thunk.lams(rest, seen, M1.inert.and_r(D1.inert.ok(h), D1.inert.ok(rest), e))
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# thunk's walk over a node read that way reports what it reports over the node
law inert.thunk.walk:
  for nn: Tree.Node
  for +lone: Bool
  for +name: String
  for +path: String
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Thunk.walk(D1.inert.node(nn), lone, name, path) == Thunk.walk(nn, lone, name, path) : List<&2, F.Finding>}

def inert.thunk.walk(nn, lone, name, path, en, e):
  match nn:
    case Tree.NCons{+h, +rest}:
      +eh = M1.inert.and_l(D1.inert.ok(h), D1.inert.ok(rest), e)
      +er = M1.inert.and_r(D1.inert.ok(h), D1.inert.ok(rest), e)
      +s1 = Thunk.site(D1.inert.node(h), D1.inert.node(rest), name, path)
      +w1 = Thunk.walk(D1.inert.node(h), False{}, name, path)
      +w2 = Thunk.walk(D1.inert.node(rest), lone, name, path)
      %inert.thunk.site(h, rest, name, path, en, er) : {List.concat(&2, F.Finding,
        [Bool.pick(List<&2, F.Finding>, lone, s1, []), w1, w2])
        == List.concat(&2, F.Finding, [Bool.pick(List<&2, F.Finding>, lone, _, []), Thunk.walk(h, False{}, name, path),
          Thunk.walk(rest, lone, name, path)]) : List<&2, F.Finding>}
      %inert.thunk.walk(h, False{}, name, path, en, eh) : {List.concat(&2, F.Finding,
        [Bool.pick(List<&2, F.Finding>, lone, s1, []), w1, w2])
        == List.concat(&2, F.Finding, [Bool.pick(List<&2, F.Finding>, lone, s1, []), _,
          Thunk.walk(rest, lone, name, path)]) : List<&2, F.Finding>}
      %inert.thunk.walk(rest, lone, name, path, en, er) : {List.concat(&2, F.Finding,
        [Bool.pick(List<&2, F.Finding>, lone, s1, []), w1, w2])
        == List.concat(&2, F.Finding, [Bool.pick(List<&2, F.Finding>, lone, s1, []), w1, _]) : List<&2, F.Finding>}
      {==}
    case Tree.Group{open, +kids, cl}:
      match open:
        case Lex.Tok{k, +o, l, c}:
          +l1 = Thunk.only(o, D1.inert.node(kids))
          %inert.thunk.lams(kids, False{}, e) : {Thunk.walk(D1.inert.node(kids), l1, name, path)
            == Thunk.walk(kids, Bool.and(String.eq(o, "("), Nat.is_eq(_, 1n)), name, path) : List<&2, F.Finding>}
          inert.thunk.walk(kids, l1, name, path, en, e)
    case Tree.Stmt{sk, +kids, +body}:
      +w1 = Thunk.walk(D1.inert.node(kids), False{}, name, path)
      +w2 = Thunk.walk(D1.inert.node(body), False{}, name, path)
      %inert.thunk.walk(kids, False{}, name, path, en, M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), e)) :
        {List.concat(&2, F.Finding, [w1, w2]) == List.concat(&2, F.Finding, [_, Thunk.walk(body, False{}, name, path)])
          : List<&2, F.Finding>}
      %inert.thunk.walk(body, False{}, name, path, en, M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), e)) :
        {List.concat(&2, F.Finding, [w1, w2]) == List.concat(&2, F.Finding, [w1, _]) : List<&2, F.Finding>}
      {==}
    case Tree.Leaf{tok}:
      {==}
    case Tree.NNil{}:
      {==}

# thunk over the defs read that way reports what it reports over the defs
law inert.thunk.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  for +e: {inert.dok(ds) == True{} : Bool}
  {Thunk.check.go(inert.defs(ds), path, acc) == Thunk.check.go(ds, path, acc) : List<&2, F.Finding>}

def inert.thunk.go(ds, path, acc, e):
  match ds:
    case Nil{}: {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +lst = inert.pick.stop(Calls.exempt(path, D1.inert.node(sig)), Thunk.walk(D1.inert.node(body), False{}, name,
        path))
      %inert.exempt(path, sig) : {Thunk.check.go(inert.defs(rest), path, lst <> acc) == Thunk.check.go(rest, path,
        inert.pick.stop(_, Thunk.walk(body, False{}, name, path)) <> acc) : List<&2, F.Finding>}
      %inert.thunk.walk(body, False{}, name, path, inert.dok.head(name, sig, body, rest, e),
        inert.dok.body(name, sig, body, rest, e)) : {Thunk.check.go(inert.defs(rest), path, lst <> acc)
          == Thunk.check.go(rest, path, inert.pick.stop(Calls.exempt(path, D1.inert.node(sig)), _) <> acc)
          : List<&2, F.Finding>}
      inert.thunk.go(rest, path, lst <> acc, inert.dok.rest(name, sig, body, rest, e))

def Laws.inert_thunk(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, ok, ok2, e):
  M1.inert.via(Tree.Node, z => Thunk.check.go(Calls.defs(z), path, []), tree, tree2, D1.inert.node(tree),
    D1.inert.node(tree2),
    inert.lift(z => Thunk.check.go(z, path, []), tree, inert.thunk.go(Calls.defs(tree), path, [], inert.dok.of(tree,
      ok))),
    inert.lift(z => Thunk.check.go(z, path, []), tree2, inert.thunk.go(Calls.defs(tree2), path, [],
      inert.dok.of(tree2, ok2))),
    e)

# Inert text, eager and on (laws/CodeRulesIgnoreCommentsAndStrings.bend): more rules over a file's defs,
# on the lemmas above.

# eager
# -----

# a text as the lexer makes it, read that way: cut when it starts with `"`
# or `#`, what a token read that way says whatever its kind
def inert.mk(+tt: String) -> String:
  D1.inert.keep(D1.inert.marked(tt), tt)

# the texts, each read that way
def inert.mks(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}: Nil{}
    case Con{h, t}: inert.mk(h) <> inert.mks(t)

# a text fits whatever says it is marked
law inert.fits_b:
  for b: Bool
  for +t: String
  for e: {D1.inert.marked(t) == b : Bool}
  {D1.inert.fits.go(b, t) == True{} : Bool}

def inert.fits_b(b, t, e):
  match b:
    case True{}: e
    case False{}:
      %Equal.sym(Bool, D1.inert.marked(t), False{}, e) : {Bool.not(_) == True{} : Bool}
      {==}

# a text fits its own mark
law inert.fits_mk:
  for +t: String
  {D1.inert.fits.go(D1.inert.marked(t), t) == True{} : Bool}

def inert.fits_mk(t):
  inert.fits_b(D1.inert.marked(t), t, {==})

# a token's text read that way is its text read that way, when it fits
law inert.keep_mk:
  for b: Bool
  for +t: String
  for ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  {D1.inert.keep(b, t) == inert.mk(t) : String}

def inert.keep_mk(b, t, ef):
  match b:
    case True{}:
      %Equal.sym(Bool, D1.inert.marked(t), True{}, ef) : {D1.inert.keep(True{}, t) == D1.inert.keep(_, t)
        : String}
      {==}
    case False{}:
      %Equal.sym(Bool, D1.inert.marked(t), False{}, inert.not_true(D1.inert.marked(t), ef)) :
        {D1.inert.keep(False{}, t) == D1.inert.keep(_, t) : String}
      {==}

# texts read that way, appended, are the append read that way
law inert.mks_app:
  for a: List<&2, String>
  for +b: List<&2, String>
  {inert.mks(List.append(&2, String, a, b)) == List.append(&2, String, inert.mks(a), inert.mks(b)) : List<&2, String>}

def inert.mks_app(a, b):
  match a:
    case Nil{}: {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, String>, List<&2, String>, z => inert.mk(h) <> z, inert.mks(List.append(&2, String, t, b)),
        List.append(&2, String, inert.mks(t), inert.mks(b)), inert.mks_app(t, b))

# two lists joined, read that way, are the two read that way joined
law inert.mks_cat2:
  for +a: List<&2, String>
  for +b: List<&2, String>
  {inert.mks(List.concat(&2, String, [a, b])) == List.concat(&2, String, [inert.mks(a), inert.mks(b)])
    : List<&2, String>}

def inert.mks_cat2(a, b):
  Equal.trans(List<&2, String>, inert.mks(List.append(&2, String, a, List.append(&2, String, b, []))),
    List.append(&2, String, inert.mks(a), inert.mks(List.append(&2, String, b, []))),
    List.append(&2, String, inert.mks(a), List.append(&2, String, inert.mks(b), [])),
    inert.mks_app(a, List.append(&2, String, b, [])),
    Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, inert.mks(a), z),
      inert.mks(List.append(&2, String, b, [])), List.append(&2, String, inert.mks(b), []), inert.mks_app(b, [])))

# three lists joined, read that way, are the three read that way joined
law inert.mks_cat3:
  for +a: List<&2, String>
  for +b: List<&2, String>
  for +c: List<&2, String>
  {inert.mks(List.concat(&2, String, [a, b, c])) == List.concat(&2, String, [inert.mks(a), inert.mks(b), inert.mks(c)])
    : List<&2, String>}

def inert.mks_cat3(a, b, c):
  Equal.trans(List<&2, String>, inert.mks(List.append(&2, String, a, List.concat(&2, String, [b, c]))),
    List.append(&2, String, inert.mks(a), inert.mks(List.concat(&2, String, [b, c]))),
    List.append(&2, String, inert.mks(a), List.concat(&2, String, [inert.mks(b), inert.mks(c)])),
    inert.mks_app(a, List.concat(&2, String, [b, c])),
    Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, inert.mks(a), z),
      inert.mks(List.concat(&2, String, [b, c])), List.concat(&2, String, [inert.mks(b), inert.mks(c)]),
      inert.mks_cat2(b, c)))

# a name kept or not, read that way
law inert.mks_pick:
  for c: Bool
  for +t: String
  for +m: List<&2, String>
  {inert.mks(Bool.pick(List<&2, String>, c, t <> m, m)) == Bool.pick(List<&2, String>, c, inert.mk(t) <> inert.mks(m),
    inert.mks(m)) : List<&2, String>}

def inert.mks_pick(c, _t, _m):
  match c:
    case True{}: {==}
    case False{}: {==}

# a name then a group: the names it calls, read that way
law inert.eager.called_lg:
  for +b: Bool
  for +t: String
  for +o: String
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for ik: {Eager.called(D1.inert.node(kids)) == inert.mks(Eager.called(kids)) : List<&2, String>}
  for ir: {Eager.called(D1.inert.node(r2)) == inert.mks(Eager.called(r2)) : List<&2, String>}
  {Bool.pick(List<&2, String>, String.eq(o, "("), D1.inert.keep(b, t) <> List.concat(&2, String,
    [Eager.called(D1.inert.node(kids)), Eager.called(D1.inert.node(r2))]), List.concat(&2, String,
      [Eager.called(D1.inert.node(kids)), Eager.called(D1.inert.node(r2))]))
    == inert.mks(Bool.pick(List<&2, String>, String.eq(o, "("), t <> List.concat(&2, String, [Eager.called(kids),
      Eager.called(r2)]), List.concat(&2, String, [Eager.called(kids), Eager.called(r2)]))) : List<&2, String>}

def inert.eager.called_lg(b, t, o, kids, r2, ef, ik, ir):
  +ck = Eager.called(kids)
  +cr = Eager.called(r2)
  +ci = Eager.called(D1.inert.node(kids))
  +cj = Eager.called(D1.inert.node(r2))
  +lhs = Bool.pick(List<&2, String>, String.eq(o, "("), D1.inert.keep(b, t) <> List.concat(&2, String, [ci, cj]),
    List.concat(&2, String, [ci, cj]))
  %Equal.sym(List<&2, String>, inert.mks(Bool.pick(List<&2, String>, String.eq(o, "("), t <> List.concat(&2, String,
    [ck, cr]), List.concat(&2, String, [ck, cr]))), Bool.pick(List<&2, String>, String.eq(o, "("),
      inert.mk(t) <> inert.mks(List.concat(&2, String, [ck, cr])), inert.mks(List.concat(&2, String, [ck, cr]))),
    inert.mks_pick(String.eq(o, "("), t, List.concat(&2, String, [ck, cr]))) : {lhs == _ : List<&2, String>}
  %Equal.sym(List<&2, String>, inert.mks(List.concat(&2, String, [ck, cr])), List.concat(&2, String,
    [inert.mks(ck), inert.mks(cr)]), inert.mks_cat2(ck, cr)) : {lhs == Bool.pick(List<&2, String>, String.eq(o, "("),
      inert.mk(t) <> _, _) : List<&2, String>}
  %ik : {lhs == Bool.pick(List<&2, String>, String.eq(o, "("), inert.mk(t) <> List.concat(&2, String, [_,
    inert.mks(cr)]), List.concat(&2, String, [_, inert.mks(cr)])) : List<&2, String>}
  %ir : {lhs == Bool.pick(List<&2, String>, String.eq(o, "("), inert.mk(t) <> List.concat(&2, String, [ci, _]),
    List.concat(&2, String, [ci, _])) : List<&2, String>}
  %inert.keep_mk(b, t, ef) : {lhs == Bool.pick(List<&2, String>, String.eq(o, "("), _ <> List.concat(&2, String,
    [ci, cj]), List.concat(&2, String, [ci, cj])) : List<&2, String>}
  {==}

# the names a chain read that way calls are the names it called, read that way
law inert.eager.called:
  for nn: Tree.Node
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Eager.called(D1.inert.node(nn)) == inert.mks(Eager.called(nn)) : List<&2, String>}

def inert.eager.called(nn, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{o, +kids, +cl}:
                      match o:
                        case Lex.Tok{+ok, +ot, +ol, +oc}:
                          +lf = {Tree.Leaf{Lex.Tok{k, t, l, c}} : Tree.Node}
                          +gp = {Tree.Group{Lex.Tok{ok, ot, ol, oc}, kids, cl} : Tree.Node}
                          +eg = inert.ok_t(lf, Tree.NCons{gp, r2}, e)
                          inert.eager.called_lg(D1.inert.blanks(k), t, ot, kids, r2,
                            inert.ok_h(lf, Tree.NCons{gp, r2}, e),
                            inert.eager.called(kids, inert.ok_h(gp, r2, eg)),
                            inert.eager.called(r2, inert.ok_t(gp, r2, eg)))
                    case Tree.Leaf{x}:
                      inert.eager.called(rest, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.Stmt{x, y, z}:
                      inert.eager.called(rest, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NNil{}:
                      inert.eager.called(rest, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NCons{x, y}:
                      inert.eager.called(rest, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NNil{}: {==}
        case Tree.Group{+o, +kids, +cl}:
          +ck = Eager.called(kids)
          +cr = Eager.called(rest)
          %Equal.sym(List<&2, String>, inert.mks(List.concat(&2, String, [ck, cr])), List.concat(&2, String,
            [inert.mks(ck), inert.mks(cr)]), inert.mks_cat2(ck, cr)) : {Eager.called(D1.inert.node(Tree.NCons{
              Tree.Group{o, kids, cl}, rest})) == _ : List<&2, String>}
          %inert.eager.called(kids, inert.ok_h(Tree.Group{o, kids, cl}, rest, e)) : {Eager.called(D1.inert.node(
            Tree.NCons{Tree.Group{o, kids, cl}, rest})) == List.concat(&2, String, [_, inert.mks(cr)])
              : List<&2, String>}
          %inert.eager.called(rest, inert.ok_t(Tree.Group{o, kids, cl}, rest, e)) : {Eager.called(D1.inert.node(
            Tree.NCons{Tree.Group{o, kids, cl}, rest})) == List.concat(&2, String, [Eager.called(D1.inert.node(
              kids)), _]) : List<&2, String>}
          {==}
        case Tree.Stmt{+sk, +kids, +body}:
          +es = inert.ok_h(Tree.Stmt{sk, kids, body}, rest, e)
          +ck = Eager.called(kids)
          +cb = Eager.called(body)
          +cr = Eager.called(rest)
          +lhs = Eager.called(D1.inert.node(Tree.NCons{Tree.Stmt{sk, kids, body}, rest}))
          %Equal.sym(List<&2, String>, inert.mks(List.concat(&2, String, [ck, cb, cr])), List.concat(&2, String,
            [inert.mks(ck), inert.mks(cb), inert.mks(cr)]), inert.mks_cat3(ck, cb, cr)) : {lhs == _
              : List<&2, String>}
          %inert.eager.called(kids, M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es)) : {lhs
            == List.concat(&2, String, [_, inert.mks(cb), inert.mks(cr)]) : List<&2, String>}
          %inert.eager.called(body, M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es)) : {lhs
            == List.concat(&2, String, [Eager.called(D1.inert.node(kids)), _, inert.mks(cr)]) : List<&2, String>}
          %inert.eager.called(rest, inert.ok_t(Tree.Stmt{sk, kids, body}, rest, e)) : {lhs
            == List.concat(&2, String, [Eager.called(D1.inert.node(kids)), Eager.called(D1.inert.node(body)), _])
              : List<&2, String>}
          {==}
        case Tree.NNil{}: inert.eager.called(rest, e)
        case Tree.NCons{x, y}: inert.eager.called(rest, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# the names read that way hold an unmarked name as they did
law inert.contains_mks:
  for cs: List<&2, String>
  for +x: String
  for +ex: {D1.inert.marked(x) == False{} : Bool}
  {List.contains(~String, ~String.eq, inert.mks(cs), x) == List.contains(~String, ~String.eq, cs, x) : Bool}

def inert.contains_mks(cs, x, ex):
  match cs:
    case Nil{}: {==}
    case Con{+h, +t}:
      inert.if2(String.eq(inert.mk(h), x), String.eq(h, x), List.contains(~String, ~String.eq, inert.mks(t), x),
        List.contains(~String, ~String.eq, t, x), M1.inert.eq_keep(D1.inert.marked(h), h, x, inert.fits_mk(h), ex),
        inert.contains_mks(t, x, ex))

# a list of unmarked texts holds no marked one
law inert.contains_marked:
  for xs: List<&2, String>
  for +t: String
  for +ep: {inert.plains(xs) == True{} : Bool}
  for +et: {D1.inert.marked(t) == True{} : Bool}
  {List.contains(~String, ~String.eq, xs, t) == False{} : Bool}

def inert.contains_marked(xs, t, ep, et):
  match xs:
    case Nil{}: {==}
    case Con{+h, +r}:
      %Equal.sym(Bool, String.eq(h, t), False{}, inert.neq_r(h, t, inert.not_true(D1.inert.marked(h),
        M1.inert.and_l(Bool.not(D1.inert.marked(h)), inert.plains(r), ep)), et)) :
        {List.any.if(_u => List.contains(~String, ~String.eq, r, t), _) == False{} : Bool}
      inert.contains_marked(r, t, M1.inert.and_r(Bool.not(D1.inert.marked(h)), inert.plains(r), ep), et)

# the names read that way reach the set as they did
law inert.eager.any_of:
  for cs: List<&2, String>
  for +set: List<&2, String>
  for +ep: {inert.plains(set) == True{} : Bool}
  {Eager.any_of(inert.mks(cs), set) == Eager.any_of(cs, set) : Bool}

def inert.eager.any_of(cs, set, ep):
  match cs:
    case Nil{}: {==}
    case Con{+c, +t}:
      inert.or_else(List.contains(~String, ~String.eq, set, inert.mk(c)), List.contains(~String, ~String.eq, set, c),
        Eager.any_of(inert.mks(t), set), Eager.any_of(t, set),
        inert.contains_keep(set, D1.inert.marked(c), c, inert.fits_mk(c), ep), inert.eager.any_of(t, set, ep))

# a name joins the unmarked ones or not
law inert.plains_pick:
  for deep: Bool
  for +name: String
  for +acc: List<&2, String>
  for en: {D1.inert.marked(name) == False{} : Bool}
  for ea: {inert.plains(acc) == True{} : Bool}
  {inert.plains(Bool.pick(List<&2, String>, deep, name <> acc, acc)) == True{} : Bool}

def inert.plains_pick(deep, name, acc, en, ea):
  match deep:
    case False{}: ea
    case True{}:
      %Equal.sym(Bool, D1.inert.marked(name), False{}, en) : {Bool.and(Bool.not(_), inert.plains(acc)) == True{}
        : Bool}
      ea

# does a def loop, its body read that way
law inert.eager.deep:
  for +name: String
  for +body: Tree.Node
  for +acc: List<&2, String>
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for +eb: {D1.inert.ok(body) == True{} : Bool}
  for +ea: {inert.plains(acc) == True{} : Bool}
  {Bool.or(List.contains(~String, ~String.eq, Eager.called(D1.inert.node(body)), name),
    Eager.any_of(Eager.called(D1.inert.node(body)), acc))
    == Bool.or(List.contains(~String, ~String.eq, Eager.called(body), name), Eager.any_of(Eager.called(body), acc))
    : Bool}

def inert.eager.deep(name, body, acc, en, eb, ea):
  +cs = Eager.called(body)
  +lhs = Bool.or(List.contains(~String, ~String.eq, Eager.called(D1.inert.node(body)), name),
    Eager.any_of(Eager.called(D1.inert.node(body)), acc))
  %inert.contains_mks(cs, name, en) : {lhs == Bool.or(_, Eager.any_of(cs, acc)) : Bool}
  %inert.eager.any_of(cs, acc, ea) : {lhs == Bool.or(List.contains(~String, ~String.eq, inert.mks(cs), name), _)
    : Bool}
  %inert.eager.called(body, eb) : {lhs == Bool.or(List.contains(~String, ~String.eq, _, name), Eager.any_of(_, acc))
    : Bool}
  {==}

# the looping defs, over defs read that way, are the ones they were
law inert.eager.loops:
  for ds: List<&2, Calls.Def>
  for +acc: List<&2, String>
  for +e: {inert.dok(ds) == True{} : Bool}
  for +ea: {inert.plains(acc) == True{} : Bool}
  {Eager.loops.go(inert.defs(ds), acc) == Eager.loops.go(ds, acc) : List<&2, String>}

def inert.eager.loops(ds, acc, e, ea):
  match ds:
    case Nil{}: {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +en = inert.dok.head(name, sig, body, rest, e)
      +ib = D1.inert.node(body)
      +di = Bool.or(List.contains(~String, ~String.eq, Eager.called(ib), name), Eager.any_of(Eager.called(ib), acc))
      +nx = Bool.pick(List<&2, String>, di, name <> acc, acc)
      %inert.eager.deep(name, body, acc, en, inert.dok.body(name, sig, body, rest, e), ea) : {Eager.loops.go(
        inert.defs(rest), nx) == Eager.loops.go(rest, Bool.pick(List<&2, String>, _, name <> acc, acc))
          : List<&2, String>}
      inert.eager.loops(rest, nx, inert.dok.rest(name, sig, body, rest, e), inert.plains_pick(di, name, acc, en, ea))

# the looping defs are named as the lexer makes names
law inert.eager.loops_plain:
  for ds: List<&2, Calls.Def>
  for +acc: List<&2, String>
  for +e: {inert.dok(ds) == True{} : Bool}
  for +ea: {inert.plains(acc) == True{} : Bool}
  {inert.plains(Eager.loops.go(ds, acc)) == True{} : Bool}

def inert.eager.loops_plain(ds, acc, e, ea):
  match ds:
    case Nil{}: ea
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +cs = Eager.called(body)
      +di = Bool.or(List.contains(~String, ~String.eq, cs, name), Eager.any_of(cs, acc))
      inert.eager.loops_plain(rest, Bool.pick(List<&2, String>, di, name <> acc, acc), inert.dok.rest(name, sig, body,
        rest, e), inert.plains_pick(di, name, acc, inert.dok.head(name, sig, body, rest, e), ea))

# a pick whose test is False gives what it gives otherwise, whatever it would
# have given
law inert.pick_off:
  for c: Bool
  for -x: List<&2, F.Finding>
  for -y: List<&2, F.Finding>
  for -m: List<&2, F.Finding>
  for e: {c == False{} : Bool}
  {Bool.pick(List<&2, F.Finding>, c, x, m) == Bool.pick(List<&2, F.Finding>, c, y, m) : List<&2, F.Finding>}

def inert.pick_off(c, x, y, m, e):
  %Equal.sym(Bool, c, False{}, e) : {Bool.pick(List<&2, F.Finding>, _, x, m) == Bool.pick(List<&2, F.Finding>, _, y,
    m) : List<&2, F.Finding>}
  {==}

# three ands whose last is False
law inert.and3_false:
  for a: Bool
  for b: Bool
  for c: Bool
  for -d: Bool
  for e: {d == False{} : Bool}
  {Bool.and(a, Bool.and(b, Bool.and(c, d))) == False{} : Bool}

def inert.and3_false(a, b, c, _d, e):
  match a:
    case False{}: {==}
    case True{}:
      match b:
        case False{}: {==}
        case True{}:
          match c:
            case False{}: {==}
            case True{}: e

# what eager reads of a call: whether it is one of the file's looping defs,
# its name, and what the group and the rest report
def inert.eager.at(
  +now: Bool,
  +call: Bool,
  mine: Bool,
  +tt: String,
  +l: U32,
  +c: U32,
  wk: List<&2, F.Finding>,
  wr: List<&2, F.Finding>,
  +path: String
) -> List<&2, F.Finding>:
  +more = List.concat(&2, F.Finding, [wk, wr])
  Bool.pick(List<&2, F.Finding>, Bool.and(now, Bool.and(call, mine)),
    F.Finding{path, l, c, U32.from_nat(String.length(tt)), "eager",
      tt ++ " is called in a branch of Bool.pick, which evaluates both branches, so it runs whatever the condition; bind it above the pick, or branch with `match` on the condition."}
      <> more,
    more)

# a call's name read that way: what it cites is what it cited
law inert.eager.fin:
  for +now: Bool
  for +call: Bool
  for b: Bool
  for +t: String
  for +l: U32
  for +c: U32
  for +wk: List<&2, F.Finding>
  for +wr: List<&2, F.Finding>
  for +ns: List<&2, String>
  for +self: String
  for +path: String
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +ep: {inert.plains(ns) == True{} : Bool}
  {inert.eager.at(now, call, Bool.and(Bool.not(String.eq(D1.inert.keep(b, t), self)),
    List.contains(~String, ~String.eq, ns, D1.inert.keep(b, t))), D1.inert.keep(b, t), l, c, wk, wr, path)
    == inert.eager.at(now, call, Bool.and(Bool.not(String.eq(D1.inert.keep(b, t), self)),
      List.contains(~String, ~String.eq, ns, D1.inert.keep(b, t))), t, l, c, wk, wr, path) : List<&2, F.Finding>}

def inert.eager.fin(now, call, b, t, l, c, wk, wr, ns, self, path, ef, ep):
  match b:
    case False{}: {==}
    case True{}:
      +ct = D1.inert.cut(t)
      +more = List.concat(&2, F.Finding, [wk, wr])
      inert.pick_off(Bool.and(now, Bool.and(call, Bool.and(Bool.not(String.eq(ct, self)), List.contains(~String,
        ~String.eq, ns, ct)))),
        F.Finding{path, l, c, U32.from_nat(String.length(ct)), "eager",
          ct ++ " is called in a branch of Bool.pick, which evaluates both branches, so it runs whatever the condition; bind it above the pick, or branch with `match` on the condition."}
          <> more,
        F.Finding{path, l, c, U32.from_nat(String.length(t)), "eager",
          t ++ " is called in a branch of Bool.pick, which evaluates both branches, so it runs whatever the condition; bind it above the pick, or branch with `match` on the condition."}
          <> more, more,
        inert.and3_false(now, call, Bool.not(String.eq(ct, self)), List.contains(~String, ~String.eq, ns, ct),
          inert.contains_marked(ns, ct, ep, M1.inert.cut_marked(t, ef))))

# a call's name read that way is one of the file's looping defs as it was
law inert.eager.mine:
  for +b: Bool
  for +t: String
  for +ns: List<&2, String>
  for +self: String
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +es: {D1.inert.marked(self) == False{} : Bool}
  for +ep: {inert.plains(ns) == True{} : Bool}
  {Bool.and(Bool.not(String.eq(D1.inert.keep(b, t), self)), List.contains(~String, ~String.eq, ns,
    D1.inert.keep(b, t)))
    == Bool.and(Bool.not(String.eq(t, self)), List.contains(~String, ~String.eq, ns, t)) : Bool}

def inert.eager.mine(b, t, ns, self, ef, es, ep):
  +kt = D1.inert.keep(b, t)
  +lhs = Bool.and(Bool.not(String.eq(kt, self)), List.contains(~String, ~String.eq, ns, kt))
  %M1.inert.eq_keep(b, t, self, ef, es) : {lhs == Bool.and(Bool.not(_), List.contains(~String, ~String.eq, ns, t))
    : Bool}
  %inert.contains_keep(ns, b, t, ef, ep) : {lhs == Bool.and(Bool.not(String.eq(kt, self)), _) : Bool}
  {==}

# a name then a group, read that way: the call reported as it was, the group
# and the rest walked as they were
law inert.eager.lg:
  for +now: Bool
  for +call: Bool
  for +b: Bool
  for +t: String
  for +l: U32
  for +c: U32
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +ns: List<&2, String>
  for +self: String
  for +path: String
  for +sg: U32
  for +keep: Bool
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +es: {D1.inert.marked(self) == False{} : Bool}
  for +ep: {inert.plains(ns) == True{} : Bool}
  for ik: {Eager.work(D1.inert.node(kids), ns, self, path, Bool.and(now, Bool.not(Bool.and(call, String.eq(t,
    "Bool.pick")))), Bool.pick(U32, Bool.and(call, String.eq(t, "Bool.pick")), 0, 9), Bool.and(now,
      Bool.not(Bool.and(call, String.eq(t, "Bool.pick")))))
    == Eager.work(kids, ns, self, path, Bool.and(now, Bool.not(Bool.and(call, String.eq(t, "Bool.pick")))),
      Bool.pick(U32, Bool.and(call, String.eq(t, "Bool.pick")), 0, 9), Bool.and(now, Bool.not(Bool.and(call,
        String.eq(t, "Bool.pick"))))) : List<&2, F.Finding>}
  for ir: {Eager.work(D1.inert.node(r2), ns, self, path, now, sg, keep) == Eager.work(r2, ns, self, path, now, sg,
    keep) : List<&2, F.Finding>}
  {inert.eager.at(now, call, Bool.and(Bool.not(String.eq(D1.inert.keep(b, t), self)), List.contains(~String,
    ~String.eq, ns, D1.inert.keep(b, t))), D1.inert.keep(b, t), l, c, Eager.work(D1.inert.node(kids), ns, self,
      path, Bool.and(now, Bool.not(Bool.and(call, String.eq(D1.inert.keep(b, t), "Bool.pick")))), Bool.pick(U32,
        Bool.and(call, String.eq(D1.inert.keep(b, t), "Bool.pick")), 0, 9), Bool.and(now, Bool.not(Bool.and(call,
          String.eq(D1.inert.keep(b, t), "Bool.pick"))))), Eager.work(D1.inert.node(r2), ns, self, path, now, sg,
            keep), path)
    == inert.eager.at(now, call, Bool.and(Bool.not(String.eq(t, self)), List.contains(~String, ~String.eq, ns, t)), t,
      l, c, Eager.work(kids, ns, self, path, Bool.and(now, Bool.not(Bool.and(call, String.eq(t, "Bool.pick")))),
        Bool.pick(U32, Bool.and(call, String.eq(t, "Bool.pick")), 0, 9), Bool.and(now, Bool.not(Bool.and(call,
          String.eq(t, "Bool.pick"))))), Eager.work(r2, ns, self, path, now, sg, keep), path) : List<&2, F.Finding>}

def inert.eager.lg(now, call, b, t, l, c, kids, r2, ns, self, path, sg, keep, ef, es, ep, ik, ir):
  +kt = D1.inert.keep(b, t)
  +ip = Bool.and(call, String.eq(t, "Bool.pick"))
  +pl = Bool.and(call, String.eq(kt, "Bool.pick"))
  +mo = Bool.and(Bool.not(String.eq(t, self)), List.contains(~String, ~String.eq, ns, t))
  +mi = Bool.and(Bool.not(String.eq(kt, self)), List.contains(~String, ~String.eq, ns, kt))
  +wki = Eager.work(D1.inert.node(kids), ns, self, path, Bool.and(now, Bool.not(pl)), Bool.pick(U32, pl, 0, 9),
    Bool.and(now, Bool.not(pl)))
  +wri = Eager.work(D1.inert.node(r2), ns, self, path, now, sg, keep)
  +lhs = inert.eager.at(now, call, mi, kt, l, c, wki, wri, path)
  %ik : {lhs == inert.eager.at(now, call, mo, t, l, c, _, Eager.work(r2, ns, self, path, now, sg, keep), path)
    : List<&2, F.Finding>}
  %ir : {lhs == inert.eager.at(now, call, mo, t, l, c, Eager.work(D1.inert.node(kids), ns, self, path, Bool.and(now,
    Bool.not(ip)), Bool.pick(U32, ip, 0, 9), Bool.and(now, Bool.not(ip))), _, path) : List<&2, F.Finding>}
  %Equal.cong(Bool, Bool, z => Bool.and(call, z), String.eq(kt, "Bool.pick"), String.eq(t, "Bool.pick"),
    M1.inert.eq_keep(b, t, "Bool.pick", ef, {==})) : {lhs == inert.eager.at(now, call, mo, t, l, c,
      Eager.work(D1.inert.node(kids), ns, self, path, Bool.and(now, Bool.not(_)), Bool.pick(U32, _, 0, 9),
        Bool.and(now, Bool.not(_))), wri, path) : List<&2, F.Finding>}
  %inert.eager.mine(b, t, ns, self, ef, es, ep) : {lhs == inert.eager.at(now, call, _, t, l, c, wki, wri, path)
    : List<&2, F.Finding>}
  inert.eager.fin(now, call, b, t, l, c, wki, wri, ns, self, path, ef, ep)

# eager's walk reads no string: a leaf's text is compared with `Bool.pick`,
# the def's name and the file's looping defs, which no string equals
law inert.eager.work:
  for nn: Tree.Node
  for +ns: List<&2, String>
  for +self: String
  for +path: String
  for +hot: Bool
  for +seg: U32
  for +keep: Bool
  for +es: {D1.inert.marked(self) == False{} : Bool}
  for +ep: {inert.plains(ns) == True{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Eager.work(D1.inert.node(nn), ns, self, path, hot, seg, keep) == Eager.work(nn, ns, self, path, hot, seg, keep)
    : List<&2, F.Finding>}

def inert.eager.work(nn, ns, self, path, hot, seg, keep, es, ep, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{o, +kids, +cl}:
                      match o:
                        case Lex.Tok{+ok, +ot, +ol, +oc}:
                          +lf = {Tree.Leaf{Lex.Tok{k, t, l, c}} : Tree.Node}
                          +gp = {Tree.Group{Lex.Tok{ok, ot, ol, oc}, kids, cl} : Tree.Node}
                          +eg = inert.ok_t(lf, Tree.NCons{gp, r2}, e)
                          +now = Eager.work.hot(k, hot, seg, keep)
                          +call = Bool.and(Eager.work.name(k), String.eq(ot, "("))
                          +ip = Bool.and(call, String.eq(t, "Bool.pick"))
                          +sg = Eager.work.seg(k, seg)
                          inert.eager.lg(now, call, D1.inert.blanks(k), t, l, c, kids, r2, ns, self, path, sg, keep,
                            inert.ok_h(lf, Tree.NCons{gp, r2}, e), es, ep,
                            inert.eager.work(kids, ns, self, path, Bool.and(now, Bool.not(ip)), Bool.pick(U32, ip, 0,
                              9), Bool.and(now, Bool.not(ip)), es, ep, inert.ok_h(gp, r2, eg)),
                            inert.eager.work(r2, ns, self, path, now, sg, keep, es, ep, inert.ok_t(gp, r2, eg)))
                    case Tree.Leaf{x}:
                      inert.eager.work(rest, ns, self, path, Eager.work.hot(k, hot, seg, keep), Eager.work.seg(k, seg),
                        keep, es, ep, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.Stmt{x, y, z}:
                      inert.eager.work(rest, ns, self, path, Eager.work.hot(k, hot, seg, keep), Eager.work.seg(k, seg),
                        keep, es, ep, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NNil{}:
                      inert.eager.work(rest, ns, self, path, Eager.work.hot(k, hot, seg, keep), Eager.work.seg(k, seg),
                        keep, es, ep, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NCons{x, y}:
                      inert.eager.work(rest, ns, self, path, Eager.work.hot(k, hot, seg, keep), Eager.work.seg(k, seg),
                        keep, es, ep, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NNil{}: {==}
        case Tree.Group{+o, +kids, +cl}:
          inert.cat2(Eager.work(D1.inert.node(kids), ns, self, path, hot, 9, hot), Eager.work(kids, ns, self, path,
            hot, 9, hot), Eager.work(D1.inert.node(rest), ns, self, path, hot, seg, keep), Eager.work(rest, ns, self,
              path, hot, seg, keep),
            inert.eager.work(kids, ns, self, path, hot, 9, hot, es, ep, inert.ok_h(Tree.Group{o, kids, cl}, rest, e)),
            inert.eager.work(rest, ns, self, path, hot, seg, keep, es, ep, inert.ok_t(Tree.Group{o, kids, cl}, rest,
              e)))
        case Tree.Stmt{+sk, +kids, +body}:
          +es2 = inert.ok_h(Tree.Stmt{sk, kids, body}, rest, e)
          inert.cat3(Eager.work(D1.inert.node(kids), ns, self, path, False{}, 9, False{}), Eager.work(kids, ns, self,
            path, False{}, 9, False{}), Eager.work(D1.inert.node(body), ns, self, path, False{}, 9, False{}),
            Eager.work(body, ns, self, path, False{}, 9, False{}), Eager.work(D1.inert.node(rest), ns, self, path,
              hot, seg, keep), Eager.work(rest, ns, self, path, hot, seg, keep),
            inert.eager.work(kids, ns, self, path, False{}, 9, False{}, es, ep, M1.inert.and_l(D1.inert.ok(kids),
              D1.inert.ok(body), es2)),
            inert.eager.work(body, ns, self, path, False{}, 9, False{}, es, ep, M1.inert.and_r(D1.inert.ok(kids),
              D1.inert.ok(body), es2)),
            inert.eager.work(rest, ns, self, path, hot, seg, keep, es, ep, inert.ok_t(Tree.Stmt{sk, kids, body}, rest,
              e)))
        case Tree.NNil{}: inert.eager.work(rest, ns, self, path, hot, seg, keep, es, ep, e)
        case Tree.NCons{x, y}:
          inert.eager.work(rest, ns, self, path, hot, seg, keep, es, ep, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# eager over the defs read that way reports what it reports over the defs
law inert.eager.go:
  for ds: List<&2, Calls.Def>
  for +ns: List<&2, String>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  for +ep: {inert.plains(ns) == True{} : Bool}
  for +e: {inert.dok(ds) == True{} : Bool}
  {Eager.check.go(inert.defs(ds), ns, path, acc) == Eager.check.go(ds, ns, path, acc) : List<&2, F.Finding>}

def inert.eager.go(ds, ns, path, acc, ep, e):
  match ds:
    case Nil{}: {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +ib = D1.inert.node(body)
      +isg = D1.inert.node(sig)
      +lst = Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, isg), [], _u => Eager.work(ib, ns, name, path, False{},
        9, False{}))
      %inert.stop(Calls.exempt(path, isg), Calls.exempt(path, sig), Eager.work(ib, ns, name, path, False{}, 9, False{}),
        Eager.work(body, ns, name, path, False{}, 9, False{}), inert.exempt(path, sig),
        inert.eager.work(body, ns, name, path, False{}, 9, False{}, inert.dok.head(name, sig, body, rest, e), ep,
          inert.dok.body(name, sig, body, rest, e))) :
        {Eager.check.go(inert.defs(rest), ns, path, lst <> acc) == Eager.check.go(rest, ns, path, _ <> acc)
          : List<&2, F.Finding>}
      inert.eager.go(rest, ns, path, lst <> acc, ep, inert.dok.rest(name, sig, body, rest, e))

# eager over the defs read that way, their looping defs read that way too
law inert.eager.all:
  for +ds: List<&2, Calls.Def>
  for +path: String
  for +e: {inert.dok(ds) == True{} : Bool}
  {Eager.check.go(inert.defs(ds), Eager.loops(inert.defs(ds)), path, [])
    == Eager.check.go(ds, Eager.loops(ds), path, []) : List<&2, F.Finding>}

def inert.eager.all(ds, path, e):
  %inert.eager.loops(ds, [], e, {==}) : {Eager.check.go(inert.defs(ds), Eager.loops(inert.defs(ds)), path, [])
    == Eager.check.go(ds, _, path, []) : List<&2, F.Finding>}
  inert.eager.go(ds, Eager.loops(inert.defs(ds)), path, [], Equal.trans(Bool,
    inert.plains(Eager.loops.go(inert.defs(ds), [])), inert.plains(Eager.loops.go(ds, [])), True{},
    Equal.cong(List<&2, String>, Bool, z => inert.plains(z),
      Eager.loops.go(inert.defs(ds), []), Eager.loops.go(ds, []), inert.eager.loops(ds, [], e, {==})),
    inert.eager.loops_plain(ds, [], e, {==})), e)

def Laws.inert_eager(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, ok, ok2, e):
  M1.inert.via(Tree.Node, z => Eager.check.go(Calls.defs(z), Eager.loops(Calls.defs(z)), path, []), tree, tree2,
    D1.inert.node(tree), D1.inert.node(tree2),
    inert.lift(z => Eager.check.go(z, Eager.loops(z), path, []), tree, inert.eager.all(Calls.defs(tree), path,
      inert.dok.of(tree, ok))),
    inert.lift(z => Eager.check.go(z, Eager.loops(z), path, []), tree2, inert.eager.all(Calls.defs(tree2), path,
      inert.dok.of(tree2, ok2))),
    e)

# fuel
# ----

# a name is never cut
law inert.fuel.name_code:
  for k: Lex.TokKind
  {Bool.and(D1.inert.blanks(k), Lex.is_name(k)) == False{} : Bool}

def inert.fuel.name_code(k):
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

# the parameters of a signature read that way are its parameters, each read
# that way
law inert.params:
  for +sig: Tree.Node
  {Calls.params(D1.inert.node(sig)) == inert.nodes(Calls.params(sig)) : List<&2, Tree.Node>}

def inert.params(sig):
  Equal.trans(List<&2, Tree.Node>, Calls.args(Calls.params.of(D1.inert.node(sig))),
    Calls.args(D1.inert.node(Calls.params.of(sig))), inert.nodes(Calls.args(Calls.params.of(sig))),
    Equal.cong(Tree.Node, List<&2, Tree.Node>, z => Calls.args(z), Calls.params.of(D1.inert.node(sig)),
      D1.inert.node(Calls.params.of(sig)), inert.params.of(sig)),
    inert.args(Calls.params.of(sig)))

# the fuel parameters among parameters read that way are the ones they were
law inert.fuel.params:
  for ps: List<&2, Tree.Node>
  for +name: String
  for +ii: Nat
  {FuelRule.fuels.params(inert.nodes(ps), name, ii) == FuelRule.fuels.params(ps, name, ii) : List<&2, FuelRule.Fuel>}

def inert.fuel.params(ps, name, ii):
  match ps:
    case Nil{}: {==}
    case Con{+p, +rest}:
      +mi = FuelRule.fuels.params(inert.nodes(rest), name, 1n+ii)
      +lhs = FuelRule.fuels.params(inert.nodes(Con{p, rest}), name, ii)
      %inert.fuel.params(rest, name, 1n+ii) : {lhs == Bool.pick(List<&2, FuelRule.Fuel>,
        FuelRule.is_fuel(Calls.param_name(p)), FuelRule.Fuel{name, ii} <> _, _) : List<&2, FuelRule.Fuel>}
      %inert.param_name(p) : {lhs == Bool.pick(List<&2, FuelRule.Fuel>, FuelRule.is_fuel(_),
        FuelRule.Fuel{name, ii} <> mi, mi) : List<&2, FuelRule.Fuel>}
      {==}

# a capitalized name after an arrow, read that way, is the name it was
law inert.fuel.io:
  for nn: Tree.Node
  {FuelRule.effect.io(D1.inert.node(nn)) == FuelRule.effect.io(nn) : Bool}

def inert.fuel.io(nn):
  match nn:
    case Tree.NCons{h, r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
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
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# an arrow read that way is an arrow as it was
law inert.fuel.arrow:
  for h: Tree.Node
  {Calls.kind.leaf(~Calls.kind.arrow, D1.inert.node(h)) == Calls.kind.leaf(~Calls.kind.arrow, h) : Bool}

def inert.fuel.arrow(h):
  match h:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# the first line under a def, read that way, is that line read that way
law inert.fuel.under:
  for body: Tree.Node
  {FuelRule.under(D1.inert.node(body)) == D1.inert.node(FuelRule.under(body)) : Tree.Node}

def inert.fuel.under(body):
  match body:
    case Tree.NCons{h, r}:
      match h:
        case Tree.Stmt{k, kids, inner}: {==}
        case Tree.Leaf{tok}: {==}
        case Tree.Group{o, gk, cl}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# what follows an arrow, read that way, is `IO` when it was
law inert.fuel.next:
  for rest: Tree.Node
  for +below: Tree.Node
  {FuelRule.effect.next(D1.inert.node(rest), D1.inert.node(below)) == FuelRule.effect.next(rest, below) : Bool}

def inert.fuel.next(rest, below):
  match rest:
    case Tree.NCons{h, t}: inert.fuel.io(Tree.NCons{h, t})
    case Tree.Leaf{tok}: inert.fuel.io(below)
    case Tree.Group{o, gk, cl}: inert.fuel.io(below)
    case Tree.Stmt{sk, sks, sb}: inert.fuel.io(below)
    case Tree.NNil{}: inert.fuel.io(below)

# a header read that way returns an effect when it did
law inert.fuel.effect:
  for sig: Tree.Node
  for +below: Tree.Node
  {FuelRule.effect(D1.inert.node(sig), D1.inert.node(below)) == FuelRule.effect(sig, below) : Bool}

def inert.fuel.effect(sig, below):
  match sig:
    case Tree.NCons{+h, +rest}:
      +lhs = FuelRule.effect(D1.inert.node(Tree.NCons{h, rest}), D1.inert.node(below))
      +ir = D1.inert.node(rest)
      +ib = D1.inert.node(below)
      %inert.fuel.effect(rest, below) : {lhs == Bool.or(Bool.and(Calls.kind.leaf(~Calls.kind.arrow, h),
        FuelRule.effect.next(rest, below)), _) : Bool}
      %inert.fuel.next(rest, below) : {lhs == Bool.or(Bool.and(Calls.kind.leaf(~Calls.kind.arrow, h), _),
        FuelRule.effect(ir, ib)) : Bool}
      %inert.fuel.arrow(h) : {lhs == Bool.or(Bool.and(_, FuelRule.effect.next(ir, ib)), FuelRule.effect(ir, ib))
        : Bool}
      {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# the fuel parameters among parameters read that way, or none, are the ones
# they were
law inert.fuel.pick:
  for b: Bool
  for +ps: List<&2, Tree.Node>
  for +name: String
  {FuelRule.fuels.params(Bool.pick(List<&2, Tree.Node>, b, [], inert.nodes(ps)), name, 0n)
    == FuelRule.fuels.params(Bool.pick(List<&2, Tree.Node>, b, [], ps), name, 0n) : List<&2, FuelRule.Fuel>}

def inert.fuel.pick(b, ps, name):
  match b:
    case True{}: {==}
    case False{}: inert.fuel.params(ps, name, 0n)

# the fuel parameters of defs read that way are the ones they were
law inert.fuel.fuels:
  for ds: List<&2, Calls.Def>
  {FuelRule.fuels(inert.defs(ds)) == FuelRule.fuels(ds) : List<&2, FuelRule.Fuel>}

def inert.fuel.fuels(ds):
  match ds:
    case Nil{}: {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +lhs = FuelRule.fuels(inert.defs(Con{Calls.Def{name, sig, body}, rest}))
      +isig = D1.inert.node(sig)
      +iu = FuelRule.under(D1.inert.node(body))
      +ps = Calls.params(sig)
      +more = FuelRule.fuels(inert.defs(rest))
      %inert.fuel.fuels(rest) : {lhs == List.append(&2, FuelRule.Fuel, FuelRule.fuels.params(FuelRule.slots(sig, body),
        name, 0n), _) : List<&2, FuelRule.Fuel>}
      %inert.fuel.effect(sig, FuelRule.under(body)) : {lhs == List.append(&2, FuelRule.Fuel,
        FuelRule.fuels.params(Bool.pick(List<&2, Tree.Node>, _, [], ps), name, 0n), more) : List<&2, FuelRule.Fuel>}
      %inert.fuel.under(body) : {lhs == List.append(&2, FuelRule.Fuel,
        FuelRule.fuels.params(Bool.pick(List<&2, Tree.Node>, FuelRule.effect(isig, _), [], ps), name, 0n), more)
        : List<&2, FuelRule.Fuel>}
      %inert.fuel.pick(FuelRule.effect(isig, iu), ps, name) : {lhs == List.append(&2, FuelRule.Fuel, _, more)
        : List<&2, FuelRule.Fuel>}
      %inert.params(sig) : {lhs == List.append(&2, FuelRule.Fuel, FuelRule.fuels.params(Bool.pick(List<&2, Tree.Node>,
        FuelRule.effect(isig, iu), [], _), name, 0n), more) : List<&2, FuelRule.Fuel>}
      {==}

# a `U32.to_nat(..)` group read that way fixes the fuel it fixed
law inert.fuel.conv:
  for kids: Tree.Node
  for ok: Bool
  for +ll: U32
  for +cc: U32
  for +path: String
  {FuelRule.converted(D1.inert.node(kids), ok, ll, cc, path) == FuelRule.converted(kids, ok, ll, cc, path)
    : List<&2, F.Finding>}

def inert.fuel.conv(kids, _ok, _ll, _cc, _path):
  match kids:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}: {==}
                case Lex.TUpper{}: {==}
                case Lex.TDotted{}: {==}
                case Lex.TWild{}: {==}
                case Lex.TKey{}: {==}
                case Lex.TNum{}:
                  match r:
                    case Tree.NNil{}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NCons{x, y}: {==}
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
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# an argument read that way is the Nat literal it was: a number is never cut
law inert.fuel.literal:
  for aa: Tree.Node
  for +path: String
  {FuelRule.literal(D1.inert.node(aa), path) == FuelRule.literal(aa, path) : List<&2, F.Finding>}

def inert.fuel.literal(aa, _path):
  match aa:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}: {==}
                case Lex.TUpper{}: {==}
                case Lex.TDotted{}:
                  match r:
                    case Tree.NCons{g, y}:
                      match g:
                        case Tree.Group{o, gk, cl}:
                          match o:
                            case Lex.Tok{ok, ot, ol, oc}:
                              match y:
                                case Tree.NNil{}:
                                  inert.fuel.conv(gk, Bool.and(String.eq(t, "U32.to_nat"), String.eq(ot, "(")), l, c,
                                    _path)
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, w, z}: {==}
                                case Tree.Stmt{x, w, z}: {==}
                                case Tree.NCons{x, w}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, w, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, w}: {==}
                    case Tree.NNil{}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, w, z}: {==}
                    case Tree.Stmt{x, w, z}: {==}
                case Lex.TWild{}: {==}
                case Lex.TKey{}: {==}
                case Lex.TNum{}:
                  match r:
                    case Tree.NNil{}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NCons{x, y}: {==}
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
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a call's arguments read that way fix the fuel they fixed
law inert.fuel.call:
  for fs: List<&2, FuelRule.Fuel>
  for +name: String
  for +as: List<&2, Tree.Node>
  for +path: String
  {FuelRule.call(fs, name, inert.nodes(as), path) == FuelRule.call(fs, name, as, path) : List<&2, F.Finding>}

def inert.fuel.call(fs, name, as, path):
  match fs:
    case Nil{}: {==}
    case Con{FuelRule.Fuel{+fn, +at}, +rest}:
      +mi = FuelRule.call(rest, name, inert.nodes(as), path)
      +lhs = FuelRule.call(Con{FuelRule.Fuel{fn, at}, rest}, name, inert.nodes(as), path)
      %inert.fuel.call(rest, name, as, path) : {lhs == Lazy.stop(List<&2, F.Finding>, Bool.not(String.eq(fn, name)), _,
        _u => List.append(&2, F.Finding, FuelRule.literal(Calls.arg(as, at), path), _)) : List<&2, F.Finding>}
      %inert.fuel.literal(Calls.arg(as, at), path) : {lhs == Lazy.stop(List<&2, F.Finding>, Bool.not(String.eq(fn,
        name)), mi, _u => List.append(&2, F.Finding, _, mi)) : List<&2, F.Finding>}
      %inert.arg(as, at) : {lhs == Lazy.stop(List<&2, F.Finding>, Bool.not(String.eq(fn, name)), mi,
        _u => List.append(&2, F.Finding, FuelRule.literal(_, path), mi)) : List<&2, F.Finding>}
      {==}

# a name then a group, read that way: the call checked as it was
law inert.fuel.hit:
  for x: Bool
  for +oo: Bool
  for +b: Bool
  for +t: String
  for +self: String
  for +fs: List<&2, FuelRule.Fuel>
  for +kids: Tree.Node
  for +path: String
  for +m: List<&2, F.Finding>
  for e: {Bool.and(b, x) == False{} : Bool}
  {Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Bool.and(x, oo), Bool.not(String.eq(D1.inert.keep(b, t),
    self)))), m, _u => List.append(&2, F.Finding, FuelRule.call(fs, D1.inert.keep(b, t),
      Calls.args(D1.inert.node(kids)), path), m))
    == Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Bool.and(x, oo), Bool.not(String.eq(t, self)))), m,
      _u => List.append(&2, F.Finding, FuelRule.call(fs, t, Calls.args(kids), path), m)) : List<&2, F.Finding>}

def inert.fuel.hit(x, oo, b, t, self, fs, kids, path, m, e):
  match b:
    case False{}:
      +lhs = Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Bool.and(x, oo), Bool.not(String.eq(t, self)))), m,
        _u => List.append(&2, F.Finding, FuelRule.call(fs, t, Calls.args(D1.inert.node(kids)), path), m))
      %inert.fuel.call(fs, t, Calls.args(kids), path) : {lhs == Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(
        Bool.and(x, oo), Bool.not(String.eq(t, self)))), m, _u => List.append(&2, F.Finding, _, m))
          : List<&2, F.Finding>}
      %inert.args(kids) : {lhs == Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Bool.and(x, oo),
        Bool.not(String.eq(t, self)))), m, _u => List.append(&2, F.Finding, FuelRule.call(fs, t, _, path), m))
          : List<&2, F.Finding>}
      {==}
    case True{}:
      %Equal.sym(Bool, x, False{}, e) : {Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Bool.and(_, oo),
        Bool.not(String.eq(D1.inert.cut(t), self)))), m, _u => List.append(&2, F.Finding, FuelRule.call(fs,
          D1.inert.cut(t), Calls.args(D1.inert.node(kids)), path), m))
        == Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Bool.and(_, oo), Bool.not(String.eq(t, self)))), m,
          _u => List.append(&2, F.Finding, FuelRule.call(fs, t, Calls.args(kids), path), m)) : List<&2, F.Finding>}
      {==}

# a name then a group, read that way: the group and the rest walked as they
# were, the call checked as it was
law inert.fuel.lg:
  for +k: Lex.TokKind
  for +t: String
  for +oo: Bool
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +fs: List<&2, FuelRule.Fuel>
  for +self: String
  for +path: String
  for ik: {FuelRule.calls(D1.inert.node(kids), fs, self, path) == FuelRule.calls(kids, fs, self, path)
    : List<&2, F.Finding>}
  for ir: {FuelRule.calls(D1.inert.node(r2), fs, self, path) == FuelRule.calls(r2, fs, self, path)
    : List<&2, F.Finding>}
  {Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Bool.and(Lex.is_name(k), oo), Bool.not(String.eq(
    D1.inert.keep(D1.inert.blanks(k), t), self)))), List.concat(&2, F.Finding, [FuelRule.calls(
      D1.inert.node(kids), fs, self, path), FuelRule.calls(D1.inert.node(r2), fs, self, path)]),
    _u => List.append(&2, F.Finding, FuelRule.call(fs, D1.inert.keep(D1.inert.blanks(k), t),
      Calls.args(D1.inert.node(kids)), path), List.concat(&2, F.Finding, [FuelRule.calls(D1.inert.node(kids), fs,
        self, path), FuelRule.calls(D1.inert.node(r2), fs, self, path)])))
    == Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Bool.and(Lex.is_name(k), oo), Bool.not(String.eq(t, self)))),
      List.concat(&2, F.Finding, [FuelRule.calls(kids, fs, self, path), FuelRule.calls(r2, fs, self, path)]),
      _u => List.append(&2, F.Finding, FuelRule.call(fs, t, Calls.args(kids), path), List.concat(&2, F.Finding,
        [FuelRule.calls(kids, fs, self, path), FuelRule.calls(r2, fs, self, path)]))) : List<&2, F.Finding>}

def inert.fuel.lg(k, t, oo, kids, r2, fs, self, path, ik, ir):
  +mi = List.concat(&2, F.Finding, [FuelRule.calls(D1.inert.node(kids), fs, self, path),
    FuelRule.calls(D1.inert.node(r2), fs, self, path)])
  +hn = Bool.and(Bool.and(Lex.is_name(k), oo), Bool.not(String.eq(t, self)))
  +lhs = Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Bool.and(Lex.is_name(k), oo), Bool.not(String.eq(
    D1.inert.keep(D1.inert.blanks(k), t), self)))), mi, _u => List.append(&2, F.Finding, FuelRule.call(fs,
      D1.inert.keep(D1.inert.blanks(k), t), Calls.args(D1.inert.node(kids)), path), mi))
  %ik : {lhs == Lazy.stop(List<&2, F.Finding>, Bool.not(hn), List.concat(&2, F.Finding, [_, FuelRule.calls(r2, fs,
    self, path)]), _u => List.append(&2, F.Finding, FuelRule.call(fs, t, Calls.args(kids), path),
      List.concat(&2, F.Finding, [_, FuelRule.calls(r2, fs, self, path)]))) : List<&2, F.Finding>}
  %ir : {lhs == Lazy.stop(List<&2, F.Finding>, Bool.not(hn), List.concat(&2, F.Finding, [FuelRule.calls(
    D1.inert.node(kids), fs, self, path), _]), _u => List.append(&2, F.Finding, FuelRule.call(fs, t,
      Calls.args(kids), path), List.concat(&2, F.Finding, [FuelRule.calls(D1.inert.node(kids), fs, self, path), _])))
    : List<&2, F.Finding>}
  inert.fuel.hit(Lex.is_name(k), oo, D1.inert.blanks(k), t, self, fs, kids, path, mi, inert.fuel.name_code(k))

# fuel's walk reads no string: a call's name is read only when it is a name
law inert.fuel.calls:
  for nn: Tree.Node
  for +fs: List<&2, FuelRule.Fuel>
  for +self: String
  for +path: String
  {FuelRule.calls(D1.inert.node(nn), fs, self, path) == FuelRule.calls(nn, fs, self, path) : List<&2, F.Finding>}

def inert.fuel.calls(nn, fs, self, path):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, l, c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{o, +kids, cl}:
                      match o:
                        case Lex.Tok{ok, +ot, ol, oc}:
                          inert.fuel.lg(k, t, String.eq(ot, "("), kids, r2, fs, self, path,
                            inert.fuel.calls(kids, fs, self, path), inert.fuel.calls(r2, fs, self, path))
                    case Tree.Leaf{x}: inert.fuel.calls(rest, fs, self, path)
                    case Tree.Stmt{x, y, z}: inert.fuel.calls(rest, fs, self, path)
                    case Tree.NNil{}: inert.fuel.calls(rest, fs, self, path)
                    case Tree.NCons{x, y}: inert.fuel.calls(rest, fs, self, path)
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NNil{}: {==}
        case Tree.Group{o, +kids, cl}:
          inert.cat2(FuelRule.calls(D1.inert.node(kids), fs, self, path), FuelRule.calls(kids, fs, self, path),
            FuelRule.calls(D1.inert.node(rest), fs, self, path), FuelRule.calls(rest, fs, self, path),
            inert.fuel.calls(kids, fs, self, path), inert.fuel.calls(rest, fs, self, path))
        case Tree.Stmt{sk, +kids, +body}:
          inert.cat3(FuelRule.calls(D1.inert.node(kids), fs, self, path), FuelRule.calls(kids, fs, self, path),
            FuelRule.calls(D1.inert.node(body), fs, self, path), FuelRule.calls(body, fs, self, path),
            FuelRule.calls(D1.inert.node(rest), fs, self, path), FuelRule.calls(rest, fs, self, path),
            inert.fuel.calls(kids, fs, self, path), inert.fuel.calls(body, fs, self, path),
            inert.fuel.calls(rest, fs, self, path))
        case Tree.NNil{}: inert.fuel.calls(rest, fs, self, path)
        case Tree.NCons{x, y}: inert.fuel.calls(rest, fs, self, path)
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# fuel over each top-level statement read that way reports what it reported
law inert.fuel.go:
  for root: Tree.Node
  for +fs: List<&2, FuelRule.Fuel>
  for +path: String
  {FuelRule.check.go(D1.inert.node(root), fs, path) == FuelRule.check.go(root, fs, path) : List<&2, F.Finding>}

def inert.fuel.go(root, fs, path):
  match root:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{sk, +kids, +body}:
          +si = FuelRule.own(Bind.declared(D1.inert.node(kids)))
          %inert.declared(kids) : {FuelRule.check.go(D1.inert.node(Tree.NCons{Tree.Stmt{sk, kids, body}, rest}), fs,
            path) == List.concat(&2, F.Finding, [FuelRule.calls(kids, fs, FuelRule.own(_), path), FuelRule.calls(body,
              fs, FuelRule.own(_), path), FuelRule.check.go(rest, fs, path)]) : List<&2, F.Finding>}
          inert.cat3(FuelRule.calls(D1.inert.node(kids), fs, si, path), FuelRule.calls(kids, fs, si, path),
            FuelRule.calls(D1.inert.node(body), fs, si, path), FuelRule.calls(body, fs, si, path),
            FuelRule.check.go(D1.inert.node(rest), fs, path), FuelRule.check.go(rest, fs, path),
            inert.fuel.calls(kids, fs, si, path), inert.fuel.calls(body, fs, si, path), inert.fuel.go(rest, fs, path))
        case Tree.Leaf{tok}: inert.fuel.go(rest, fs, path)
        case Tree.Group{o, gk, cl}: inert.fuel.go(rest, fs, path)
        case Tree.NNil{}: inert.fuel.go(rest, fs, path)
        case Tree.NCons{x, y}: inert.fuel.go(rest, fs, path)
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# fuel over a tree read that way, its fuel parameters read that way too
law inert.fuel.all:
  for +tree: Tree.Node
  for +path: String
  {FuelRule.check.go(D1.inert.node(tree), FuelRule.fuels(Calls.defs(D1.inert.node(tree))), path)
    == FuelRule.check.go(tree, FuelRule.fuels(Calls.defs(tree)), path) : List<&2, F.Finding>}

def inert.fuel.all(tree, path):
  +ds = Calls.defs(tree)
  %inert.fuel.fuels(ds) : {FuelRule.check.go(D1.inert.node(tree), FuelRule.fuels(Calls.defs(D1.inert.node(tree))),
    path) == FuelRule.check.go(tree, _, path) : List<&2, F.Finding>}
  %inert.defs.of(tree) : {FuelRule.check.go(D1.inert.node(tree), FuelRule.fuels(Calls.defs(D1.inert.node(tree))),
    path) == FuelRule.check.go(tree, FuelRule.fuels(_), path) : List<&2, F.Finding>}
  inert.fuel.go(tree, FuelRule.fuels(Calls.defs(D1.inert.node(tree))), path)

def Laws.inert_fuel(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, _ok, _ok2, e):
  M1.inert.via(Tree.Node, z => FuelRule.check.go(z, FuelRule.fuels(Calls.defs(z)), path), tree, tree2,
    D1.inert.node(tree), D1.inert.node(tree2), inert.fuel.all(tree, path), inert.fuel.all(tree2, path), e)

# ring
# ----

# a chain read that way is one number as it was
law inert.ring.is_num:
  for nn: Tree.Node
  {Ring.is_num(D1.inert.node(nn)) == Ring.is_num(nn) : Bool}

def inert.ring.is_num(nn):
  match nn:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}: {==}
                case Lex.TUpper{}: {==}
                case Lex.TDotted{}: {==}
                case Lex.TWild{}: {==}
                case Lex.TKey{}: {==}
                case Lex.TNum{}:
                  match r:
                    case Tree.NNil{}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NCons{x, y}: {==}
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
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a chain read that way is the one name it was
law inert.ring.name_text:
  for nn: Tree.Node
  {Ring.name_text(D1.inert.node(nn)) == Ring.name_text(nn) : String}

def inert.ring.name_text(nn):
  match nn:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}:
                  match r:
                    case Tree.NNil{}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NCons{x, y}: {==}
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
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# arguments read that way name a window as they did
law inert.ring.has_name:
  for as: List<&2, Tree.Node>
  for +wins: List<&2, String>
  {Ring.has_name(inert.nodes(as), wins) == Ring.has_name(as, wins) : Bool}

def inert.ring.has_name(as, wins):
  match as:
    case Nil{}: {==}
    case Con{+h, +rest}:
      +lhs = Ring.has_name(inert.nodes(Con{h, rest}), wins)
      %inert.ring.has_name(rest, wins) : {lhs == Bool.or(Ring.win_name(h, wins), _) : Bool}
      %inert.ring.name_text(h) : {lhs == Bool.or(Bool.and(Bool.not(String.is_empty(_)), List.contains(~String,
        ~String.eq, wins, _)), Ring.has_name(inert.nodes(rest), wins)) : Bool}
      {==}

# arguments read that way end with a number as they did
law inert.ring.last_num:
  for as: List<&2, Tree.Node>
  {Ring.last_num(inert.nodes(as)) == Ring.last_num(as) : Bool}

def inert.ring.last_num(as):
  match as:
    case Nil{}: {==}
    case Con{h, +rest}:
      match rest:
        case Nil{}: inert.ring.is_num(h)
        case Con{x, y}: inert.ring.last_num(rest)

# what drop_ok reads: the name among the drops and tails, the window named,
# the name a tail, the count a number
def inert.ring.dparts(kd: Bool, hn: Bool, +tl: Bool, ln: Bool) -> Bool:
  Bool.and(kd, Bool.and(hn, Bool.or(tl, ln)))

# the drops and tails
def inert.ring.drops() -> List<&2, String>:
  ["List.drop", "String.drop", "List.tail", "String.tail"]

# a call's name and arguments read that way are the fixed drop they were
law inert.ring.drop_ok:
  for +b: Bool
  for +t: String
  for +as: List<&2, Tree.Node>
  for +wins: List<&2, String>
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  {Ring.drop_ok(D1.inert.keep(b, t), inert.nodes(as), wins) == Ring.drop_ok(t, as, wins) : Bool}

def inert.ring.drop_ok(b, t, as, wins, ef):
  +kt = D1.inert.keep(b, t)
  +lhs = Ring.drop_ok(kt, inert.nodes(as), wins)
  %inert.contains_keep(inert.ring.drops(), b, t, ef, {==}) : {lhs == inert.ring.dparts(_, Ring.has_name(as, wins),
    Bool.or(String.eq(t, "List.tail"), String.eq(t, "String.tail")), Ring.last_num(as)) : Bool}
  %M1.inert.eq_keep(b, t, "List.tail", ef, {==}) : {lhs == inert.ring.dparts(List.contains(~String, ~String.eq,
    inert.ring.drops(), kt), Ring.has_name(as, wins), Bool.or(_, String.eq(t, "String.tail")), Ring.last_num(as))
    : Bool}
  %M1.inert.eq_keep(b, t, "String.tail", ef, {==}) : {lhs == inert.ring.dparts(List.contains(~String, ~String.eq,
    inert.ring.drops(), kt), Ring.has_name(as, wins), Bool.or(String.eq(kt, "List.tail"), _), Ring.last_num(as))
    : Bool}
  %inert.ring.has_name(as, wins) : {lhs == inert.ring.dparts(List.contains(~String, ~String.eq, inert.ring.drops(),
    kt), _, Bool.or(String.eq(kt, "List.tail"), String.eq(kt, "String.tail")), Ring.last_num(as)) : Bool}
  %inert.ring.last_num(as) : {lhs == inert.ring.dparts(List.contains(~String, ~String.eq, inert.ring.drops(), kt),
    Ring.has_name(inert.nodes(as), wins), Bool.or(String.eq(kt, "List.tail"), String.eq(kt, "String.tail")), _)
    : Bool}
  {==}

# a drop's token is kept only for a drop's name, which is never cut
law inert.ring.drop_pick:
  for b: Bool
  for +t: String
  for +k: Lex.TokKind
  for +l: U32
  for +c: U32
  for +as: List<&2, Tree.Node>
  for +wins: List<&2, String>
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  {Bool.pick(Maybe<&2, Lex.Tok>, Ring.drop_ok(t, as, wins), Some{Lex.Tok{k, D1.inert.keep(b, t), l, c}}, None{})
    == Bool.pick(Maybe<&2, Lex.Tok>, Ring.drop_ok(t, as, wins), Some{Lex.Tok{k, t, l, c}}, None{})
    : Maybe<&2, Lex.Tok>}

def inert.ring.drop_pick(b, t, k, l, c, as, wins, ef):
  match b:
    case False{}: {==}
    case True{}:
      +tl = Bool.or(String.eq(t, "List.tail"), String.eq(t, "String.tail"))
      %Equal.sym(Bool, List.contains(~String, ~String.eq, inert.ring.drops(), t), False{},
        inert.contains_marked(inert.ring.drops(), t, {==}, ef)) : {Bool.pick(Maybe<&2, Lex.Tok>,
          inert.ring.dparts(_, Ring.has_name(as, wins), tl, Ring.last_num(as)), Some{Lex.Tok{k, D1.inert.cut(t), l,
            c}}, None{}) == Bool.pick(Maybe<&2, Lex.Tok>, inert.ring.dparts(_, Ring.has_name(as, wins), tl,
              Ring.last_num(as)), Some{Lex.Tok{k, t, l, c}}, None{}) : Maybe<&2, Lex.Tok>}
      {==}

# a call read that way is the fixed drop it was
law inert.ring.drop_tok:
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +kids: Tree.Node
  for +wins: List<&2, String>
  for +ef: {D1.inert.fits.go(D1.inert.blanks(k), t) == True{} : Bool}
  {Ring.drop_tok(k, D1.inert.keep(D1.inert.blanks(k), t), l, c, D1.inert.node(kids), wins)
    == Ring.drop_tok(k, t, l, c, kids, wins) : Maybe<&2, Lex.Tok>}

def inert.ring.drop_tok(k, t, l, c, kids, wins, ef):
  +b = D1.inert.blanks(k)
  +kt = D1.inert.keep(b, t)
  +aa = Calls.args(kids)
  +lhs = Ring.drop_tok(k, kt, l, c, D1.inert.node(kids), wins)
  %inert.ring.drop_pick(b, t, k, l, c, aa, wins, ef) : {lhs == _ : Maybe<&2, Lex.Tok>}
  %inert.ring.drop_ok(b, t, aa, wins, ef) : {lhs == Bool.pick(Maybe<&2, Lex.Tok>, _, Some{Lex.Tok{k, kt, l, c}},
    None{}) : Maybe<&2, Lex.Tok>}
  %inert.args(kids) : {lhs == Bool.pick(Maybe<&2, Lex.Tok>, Ring.drop_ok(kt, _, wins), Some{Lex.Tok{k, kt, l, c}},
    None{}) : Maybe<&2, Lex.Tok>}
  {==}

# an application read that way is the drop it was
law inert.ring.here_of:
  for open: Bool
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +kids: Tree.Node
  for +wins: List<&2, String>
  for +ef: {D1.inert.fits.go(D1.inert.blanks(k), t) == True{} : Bool}
  {Ring.here_of(open, k, D1.inert.keep(D1.inert.blanks(k), t), l, c, D1.inert.node(kids), wins)
    == Ring.here_of(open, k, t, l, c, kids, wins) : Maybe<&2, Lex.Tok>}

def inert.ring.here_of(open, k, t, l, c, kids, wins, ef):
  match open:
    case False{}: {==}
    case True{}: inert.ring.drop_tok(k, t, l, c, kids, wins, ef)

# two maybes read as they did give the first of them as it did
law inert.ring.or2:
  for -a1: Maybe<&2, Lex.Tok>
  for -a2: Maybe<&2, Lex.Tok>
  for -b1: Maybe<&2, Lex.Tok>
  for -b2: Maybe<&2, Lex.Tok>
  for ea: {a1 == a2 : Maybe<&2, Lex.Tok>}
  for eb: {b1 == b2 : Maybe<&2, Lex.Tok>}
  {Ring.or_tok(a1, b1) == Ring.or_tok(a2, b2) : Maybe<&2, Lex.Tok>}

def inert.ring.or2(a1, _a2, b1, b2, ea, eb):
  %ea : {Ring.or_tok(a1, b1) == Ring.or_tok(_, b2) : Maybe<&2, Lex.Tok>}
  %eb : {Ring.or_tok(a1, b1) == Ring.or_tok(a1, _) : Maybe<&2, Lex.Tok>}
  {==}

# a drop anywhere under a node read that way is the drop it was
law inert.ring.drop_in:
  for nn: Tree.Node
  for +wins: List<&2, String>
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Ring.drop_in(D1.inert.node(nn), wins) == Ring.drop_in(nn, wins) : Maybe<&2, Lex.Tok>}

def inert.ring.drop_in(nn, wins, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{o, +kids, +cl}:
                      match o:
                        case Lex.Tok{+ok, +ot, +ol, +oc}:
                          +lf = {Tree.Leaf{Lex.Tok{k, t, l, c}} : Tree.Node}
                          +gp = {Tree.Group{Lex.Tok{ok, ot, ol, oc}, kids, cl} : Tree.Node}
                          +eg = inert.ok_t(lf, Tree.NCons{gp, r2}, e)
                          inert.ring.or2(Ring.here_of(String.eq(ot, "("), k, D1.inert.keep(D1.inert.blanks(k), t), l,
                            c, D1.inert.node(kids), wins), Ring.here_of(String.eq(ot, "("), k, t, l, c, kids, wins),
                            Ring.or_tok(Ring.drop_in(D1.inert.node(kids), wins), Ring.drop_in(D1.inert.node(r2),
                              wins)), Ring.or_tok(Ring.drop_in(kids, wins), Ring.drop_in(r2, wins)),
                            inert.ring.here_of(String.eq(ot, "("), k, t, l, c, kids, wins, inert.ok_h(lf,
                              Tree.NCons{gp, r2}, e)),
                            inert.ring.or2(Ring.drop_in(D1.inert.node(kids), wins), Ring.drop_in(kids, wins),
                              Ring.drop_in(D1.inert.node(r2), wins), Ring.drop_in(r2, wins),
                              inert.ring.drop_in(kids, wins, inert.ok_h(gp, r2, eg)),
                              inert.ring.drop_in(r2, wins, inert.ok_t(gp, r2, eg))))
                    case Tree.Leaf{x}:
                      inert.ring.drop_in(rest, wins, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.Stmt{x, y, z}:
                      inert.ring.drop_in(rest, wins, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NNil{}:
                      inert.ring.drop_in(rest, wins, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NCons{x, y}:
                      inert.ring.drop_in(rest, wins, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NNil{}: {==}
        case Tree.Group{+o, +kids, +cl}:
          inert.ring.or2(Ring.drop_in(D1.inert.node(kids), wins), Ring.drop_in(kids, wins),
            Ring.drop_in(D1.inert.node(rest), wins), Ring.drop_in(rest, wins),
            inert.ring.drop_in(kids, wins, inert.ok_h(Tree.Group{o, kids, cl}, rest, e)),
            inert.ring.drop_in(rest, wins, inert.ok_t(Tree.Group{o, kids, cl}, rest, e)))
        case Tree.Stmt{+sk, +kids, +body}:
          +es = inert.ok_h(Tree.Stmt{sk, kids, body}, rest, e)
          inert.ring.or2(Ring.drop_in(D1.inert.node(kids), wins), Ring.drop_in(kids, wins),
            Ring.or_tok(Ring.drop_in(D1.inert.node(body), wins), Ring.drop_in(D1.inert.node(rest), wins)),
            Ring.or_tok(Ring.drop_in(body, wins), Ring.drop_in(rest, wins)),
            inert.ring.drop_in(kids, wins, M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es)),
            inert.ring.or2(Ring.drop_in(D1.inert.node(body), wins), Ring.drop_in(body, wins),
              Ring.drop_in(D1.inert.node(rest), wins), Ring.drop_in(rest, wins),
              inert.ring.drop_in(body, wins, M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es)),
              inert.ring.drop_in(rest, wins, inert.ok_t(Tree.Stmt{sk, kids, body}, rest, e))))
        case Tree.NNil{}: inert.ring.drop_in(rest, wins, e)
        case Tree.NCons{x, y}: inert.ring.drop_in(rest, wins, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# the receiver of an append, its arguments read that way
law inert.ring.receiver_is:
  for list: Bool
  for str: Bool
  for +as: List<&2, Tree.Node>
  for +wins: List<&2, String>
  for +ea: {inert.noks(as) == True{} : Bool}
  {Ring.receiver_is(list, str, inert.nodes(as), wins) == Ring.receiver_is(list, str, as, wins) : Maybe<&2, Lex.Tok>}

def inert.ring.receiver_is(list, str, as, wins, ea):
  match list str:
    case True{} s:
      %Equal.sym(Tree.Node, Calls.arg(inert.nodes(as), 2n), D1.inert.node(Calls.arg(as, 2n)), inert.arg(as, 2n)) :
        {Ring.drop_in(_, wins) == Ring.drop_in(Calls.arg(as, 2n), wins) : Maybe<&2, Lex.Tok>}
      inert.ring.drop_in(Calls.arg(as, 2n), wins, inert.ok.nth(as, 2n, ea))
    case False{} True{}:
      %Equal.sym(Tree.Node, Calls.arg(inert.nodes(as), 0n), D1.inert.node(Calls.arg(as, 0n)), inert.arg(as, 0n)) :
        {Ring.drop_in(_, wins) == Ring.drop_in(Calls.arg(as, 0n), wins) : Maybe<&2, Lex.Tok>}
      inert.ring.drop_in(Calls.arg(as, 0n), wins, inert.ok.nth(as, 0n, ea))
    case False{} False{}: {==}

# the receiver of an append, the call's name and arguments read that way
law inert.ring.receiver:
  for +b: Bool
  for +t: String
  for +kids: Tree.Node
  for +wins: List<&2, String>
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  {Ring.receiver(D1.inert.keep(b, t), D1.inert.node(kids), wins) == Ring.receiver(t, kids, wins)
    : Maybe<&2, Lex.Tok>}

def inert.ring.receiver(b, t, kids, wins, ef, ek):
  +kt = D1.inert.keep(b, t)
  +aa = Calls.args(kids)
  +lhs = Ring.receiver(kt, D1.inert.node(kids), wins)
  %inert.ring.receiver_is(String.eq(t, "List.append"), String.eq(t, "String.append"), aa, wins,
    inert.ok.args.go(kids, Tree.NNil{}, [], ek, {==}, {==})) : {lhs == _ : Maybe<&2, Lex.Tok>}
  %M1.inert.eq_keep(b, t, "List.append", ef, {==}) : {lhs == Ring.receiver_is(_, String.eq(t, "String.append"),
    inert.nodes(aa), wins) : Maybe<&2, Lex.Tok>}
  %M1.inert.eq_keep(b, t, "String.append", ef, {==}) : {lhs == Ring.receiver_is(String.eq(kt, "List.append"), _,
    inert.nodes(aa), wins) : Maybe<&2, Lex.Tok>}
  %inert.args(kids) : {lhs == Ring.receiver_is(String.eq(kt, "List.append"), String.eq(kt, "String.append"), _, wins)
    : Maybe<&2, Lex.Tok>}
  {==}

# an application's receiver, read that way
law inert.ring.call_recv:
  for open: Bool
  for +b: Bool
  for +t: String
  for +kids: Tree.Node
  for +wins: List<&2, String>
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  {Ring.call_recv(open, D1.inert.keep(b, t), D1.inert.node(kids), wins) == Ring.call_recv(open, t, kids, wins)
    : Maybe<&2, Lex.Tok>}

def inert.ring.call_recv(open, b, t, kids, wins, ef, ek):
  match open:
    case False{}: {==}
    case True{}: inert.ring.receiver(b, t, kids, wins, ef, ek)

# the drop a call or a bracket is, read that way
law inert.ring.call_drop:
  for open: Bool
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +kids: Tree.Node
  for +wins: List<&2, String>
  for +ef: {D1.inert.fits.go(D1.inert.blanks(k), t) == True{} : Bool}
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  {Ring.call_drop(open, k, D1.inert.keep(D1.inert.blanks(k), t), l, c, D1.inert.node(kids), wins)
    == Ring.call_drop(open, k, t, l, c, kids, wins) : Maybe<&2, Lex.Tok>}

def inert.ring.call_drop(open, k, t, l, c, kids, wins, ef, ek):
  match open:
    case False{}: inert.ring.drop_in(kids, wins, ek)
    case True{}: inert.ring.drop_tok(k, t, l, c, kids, wins, ef)

# a leaf, a group and the rest as the lexer makes them: each fits
law inert.ok3:
  for +a: Tree.Node
  for +g: Tree.Node
  for +r: Tree.Node
  for e: {D1.inert.ok(Tree.NCons{a, Tree.NCons{g, r}}) == True{} : Bool}
  {Bool.and(D1.inert.ok(a), Bool.and(D1.inert.ok(g), D1.inert.ok(r))) == True{} : Bool}

def inert.ok3(_a, _g, _r, e):
  e

# a name then a group, read that way: the scan finds the drop it found
law inert.ring.ps_lg:
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +o: String
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +seen: Maybe<&2, Lex.Tok>
  for +wins: List<&2, String>
  for +ef: {D1.inert.fits.go(D1.inert.blanks(k), t) == True{} : Bool}
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  for ik: {Ring.plus_scan(D1.inert.node(kids), None{}, wins) == Ring.plus_scan(kids, None{}, wins)
    : Maybe<&2, Lex.Tok>}
  for ir: {Ring.plus_scan(D1.inert.node(r2), Ring.or_tok(seen, Ring.call_drop(String.eq(o, "("), k, t, l, c, kids,
    wins)), wins) == Ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(o, "("), k, t, l, c, kids, wins)),
      wins) : Maybe<&2, Lex.Tok>}
  {Ring.or_tok(Ring.call_recv(String.eq(o, "("), D1.inert.keep(D1.inert.blanks(k), t), D1.inert.node(kids),
    wins), Ring.or_tok(Ring.plus_scan(D1.inert.node(kids), None{}, wins), Ring.plus_scan(D1.inert.node(r2),
      Ring.or_tok(seen, Ring.call_drop(String.eq(o, "("), k, D1.inert.keep(D1.inert.blanks(k), t), l, c,
        D1.inert.node(kids), wins)), wins)))
    == Ring.or_tok(Ring.call_recv(String.eq(o, "("), t, kids, wins), Ring.or_tok(Ring.plus_scan(kids, None{}, wins),
      Ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(o, "("), k, t, l, c, kids, wins)), wins)))
    : Maybe<&2, Lex.Tok>}

def inert.ring.ps_lg(k, t, l, c, o, kids, r2, seen, wins, ef, ek, ik, ir):
  +op = String.eq(o, "(")
  +kt = D1.inert.keep(D1.inert.blanks(k), t)
  +ki = D1.inert.node(kids)
  +di = Ring.call_drop(op, k, kt, l, c, ki, wins)
  +lhs = Ring.or_tok(Ring.call_recv(op, kt, ki, wins), Ring.or_tok(Ring.plus_scan(ki, None{}, wins),
    Ring.plus_scan(D1.inert.node(r2), Ring.or_tok(seen, di), wins)))
  %ir : {lhs == Ring.or_tok(Ring.call_recv(op, t, kids, wins), Ring.or_tok(Ring.plus_scan(kids, None{}, wins), _))
    : Maybe<&2, Lex.Tok>}
  %inert.ring.call_drop(op, k, t, l, c, kids, wins, ef, ek) : {lhs == Ring.or_tok(Ring.call_recv(op, t, kids, wins),
    Ring.or_tok(Ring.plus_scan(kids, None{}, wins), Ring.plus_scan(D1.inert.node(r2), Ring.or_tok(seen, _), wins)))
    : Maybe<&2, Lex.Tok>}
  %ik : {lhs == Ring.or_tok(Ring.call_recv(op, t, kids, wins), Ring.or_tok(_, Ring.plus_scan(D1.inert.node(r2),
    Ring.or_tok(seen, di), wins))) : Maybe<&2, Lex.Tok>}
  %inert.ring.call_recv(op, D1.inert.blanks(k), t, kids, wins, ef, ek) : {lhs == Ring.or_tok(_, Ring.or_tok(
    Ring.plus_scan(ki, None{}, wins), Ring.plus_scan(D1.inert.node(r2), Ring.or_tok(seen, di), wins)))
    : Maybe<&2, Lex.Tok>}
  {==}

# an operator: the scan past it, read that way, finds what it found
law inert.ring.ps_op:
  for +t: String
  for +seen: Maybe<&2, Lex.Tok>
  for +rest: Tree.Node
  for +wins: List<&2, String>
  for ih: {Ring.plus_scan(D1.inert.node(rest), Ring.pp_seen(String.eq(t, "++"), seen), wins)
    == Ring.plus_scan(rest, Ring.pp_seen(String.eq(t, "++"), seen), wins) : Maybe<&2, Lex.Tok>}
  {Ring.or_tok(Ring.pp_found(String.eq(t, "++"), seen), Ring.plus_scan(D1.inert.node(rest),
    Ring.pp_seen(String.eq(t, "++"), seen), wins))
    == Ring.or_tok(Ring.pp_found(String.eq(t, "++"), seen), Ring.plus_scan(rest, Ring.pp_seen(String.eq(t, "++"),
      seen), wins)) : Maybe<&2, Lex.Tok>}

def inert.ring.ps_op(t, seen, rest, wins, ih):
  Equal.cong(Maybe<&2, Lex.Tok>, Maybe<&2, Lex.Tok>, z => Ring.or_tok(Ring.pp_found(String.eq(t, "++"), seen), z),
    Ring.plus_scan(D1.inert.node(rest), Ring.pp_seen(String.eq(t, "++"), seen), wins),
    Ring.plus_scan(rest, Ring.pp_seen(String.eq(t, "++"), seen), wins), ih)

# ring's scan reads no string: an operator's text, a drop's or an append's
# name against the few it knows, a window's name
law inert.ring.plus_scan:
  for nn: Tree.Node
  for +seen: Maybe<&2, Lex.Tok>
  for +wins: List<&2, String>
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Ring.plus_scan(D1.inert.node(nn), seen, wins) == Ring.plus_scan(nn, seen, wins) : Maybe<&2, Lex.Tok>}

def inert.ring.plus_scan(nn, seen, wins, e):
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
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TName{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TName{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TUpper{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TUpper{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TUpper{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TDotted{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TDotted{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TDotted{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TWild{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TWild{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TWild{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TWild{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TWild{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TWild{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TWild{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TWild{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TWild{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TWild{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TKey{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TKey{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TKey{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TKey{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TKey{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TKey{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TKey{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TKey{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TKey{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TKey{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TNum{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TNum{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TNum{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TStr{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TStr{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TStr{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TStr{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TStr{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TStr{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TStr{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TStr{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TStr{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TStr{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TChar{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TChar{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TChar{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TChar{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TChar{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TChar{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TChar{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TChar{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TChar{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TChar{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TComment{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TComment{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TComment{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TComment{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TComment{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TComment{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TComment{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TComment{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TComment{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TComment{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TSpace{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TSpace{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TSpace{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TSpace{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TSpace{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TSpace{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TSpace{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TSpace{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TSpace{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TSpace{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TNewline{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TNewline{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TNewline{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TNewline{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TNewline{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TNewline{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TNewline{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TNewline{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TNewline{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TNewline{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TOp{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Leaf{x}:
                          inert.ring.ps_op(t, seen, rest, wins, inert.ring.plus_scan(rest,
                            Ring.pp_seen(String.eq(t, "++"), seen), wins,
                            inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOp{}, t, l, c}}, rest, e)))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.ps_op(t, seen, rest, wins, inert.ring.plus_scan(rest,
                            Ring.pp_seen(String.eq(t, "++"), seen), wins,
                            inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOp{}, t, l, c}}, rest, e)))
                        case Tree.NNil{}:
                          inert.ring.ps_op(t, seen, rest, wins, inert.ring.plus_scan(rest,
                            Ring.pp_seen(String.eq(t, "++"), seen), wins,
                            inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOp{}, t, l, c}}, rest, e)))
                        case Tree.NCons{x, y}:
                          inert.ring.ps_op(t, seen, rest, wins, inert.ring.plus_scan(rest,
                            Ring.pp_seen(String.eq(t, "++"), seen), wins,
                            inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOp{}, t, l, c}}, rest, e)))
                        case Tree.Group{x, y, z}:
                          match x:
                            case Lex.Tok{a1, a2, a3, a4}:
                              inert.ring.ps_op(t, seen, rest, wins, inert.ring.plus_scan(rest,
                                Ring.pp_seen(String.eq(t, "++"), seen), wins,
                                inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOp{}, t, l, c}}, rest, e)))
                    case Tree.Leaf{x}:
                      inert.ring.ps_op(t, seen, rest, wins, inert.ring.plus_scan(rest,
                        Ring.pp_seen(String.eq(t, "++"), seen), wins,
                        inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOp{}, t, l, c}}, rest, e)))
                    case Tree.Group{x, y, z}:
                      inert.ring.ps_op(t, seen, rest, wins, inert.ring.plus_scan(rest,
                        Ring.pp_seen(String.eq(t, "++"), seen), wins,
                        inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOp{}, t, l, c}}, rest, e)))
                    case Tree.Stmt{x, y, z}:
                      inert.ring.ps_op(t, seen, rest, wins, inert.ring.plus_scan(rest,
                        Ring.pp_seen(String.eq(t, "++"), seen), wins,
                        inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOp{}, t, l, c}}, rest, e)))
                    case Tree.NNil{}:
                      inert.ring.ps_op(t, seen, rest, wins, inert.ring.plus_scan(rest,
                        Ring.pp_seen(String.eq(t, "++"), seen), wins,
                        inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOp{}, t, l, c}}, rest, e)))
                case Lex.TColon{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TColon{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TColon{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TEq{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TEq{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TEq{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TBind{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TBind{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TBind{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TArrow{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TArrow{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TArrow{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TArrow{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TArrow{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TArrow{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TArrow{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TArrow{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TArrow{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TArrow{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TLam{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TLam{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TLam{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TAll{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TAll{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TAll{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TAll{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TAll{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TAll{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TAll{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TAll{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TAll{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TAll{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TAmp{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TAmp{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TAmp{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TAmp{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TAmp{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TAmp{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TAmp{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TAmp{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TAmp{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TAmp{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TOpen{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TOpen{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TOpen{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TOpen{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TOpen{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TOpen{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOpen{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOpen{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOpen{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOpen{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TClose{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TClose{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TClose{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TClose{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TClose{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TClose{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TClose{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TClose{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TClose{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TClose{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TComma{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{o, +kids, +cl}:
                          match o:
                            case Lex.Tok{+a, +ot, +b, +d}:
                              +e3 = inert.ok3(Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, Tree.Group{Lex.Tok{a, ot, b,
                                d}, kids, cl}, r2, e)
                              +ea = M1.inert.and_l(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +eg = M1.inert.and_r(D1.inert.ok(Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}),
                                Bool.and(D1.inert.ok(kids), D1.inert.ok(r2)), e3)
                              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(r2), eg)
                              inert.ring.ps_lg(Lex.TComma{}, t, l, c, ot, kids, r2, seen, wins, ea, ek,
                                inert.ring.plus_scan(kids, None{}, wins, ek),
                                inert.ring.plus_scan(r2, Ring.or_tok(seen, Ring.call_drop(String.eq(ot, "("),
                                  Lex.TComma{}, t, l, c, kids, wins)), wins, M1.inert.and_r(D1.inert.ok(kids),
                                    D1.inert.ok(r2), eg)))
                        case Tree.Leaf{x}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}},
                            rest, e))
                        case Tree.Stmt{x, y, z}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}},
                            rest, e))
                        case Tree.NNil{}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}},
                            rest, e))
                        case Tree.NCons{x, y}:
                          inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}},
                            rest, e))
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
        case Tree.Group{+o, +kids, +cl}:
          inert.ring.or2(Ring.plus_scan(D1.inert.node(kids), None{}, wins), Ring.plus_scan(kids, None{}, wins),
            Ring.plus_scan(D1.inert.node(rest), Ring.or_tok(seen, Ring.drop_in(D1.inert.node(kids), wins)), wins),
            Ring.plus_scan(rest, Ring.or_tok(seen, Ring.drop_in(kids, wins)), wins),
            inert.ring.plus_scan(kids, None{}, wins, inert.ok_h(Tree.Group{o, kids, cl}, rest, e)),
            Equal.trans(Maybe<&2, Lex.Tok>, Ring.plus_scan(D1.inert.node(rest), Ring.or_tok(seen,
              Ring.drop_in(D1.inert.node(kids), wins)), wins), Ring.plus_scan(D1.inert.node(rest),
                Ring.or_tok(seen, Ring.drop_in(kids, wins)), wins), Ring.plus_scan(rest, Ring.or_tok(seen,
                  Ring.drop_in(kids, wins)), wins),
              Equal.cong(Maybe<&2, Lex.Tok>, Maybe<&2, Lex.Tok>, z => Ring.plus_scan(D1.inert.node(rest),
                Ring.or_tok(seen, z), wins), Ring.drop_in(D1.inert.node(kids), wins), Ring.drop_in(kids, wins),
                inert.ring.drop_in(kids, wins, inert.ok_h(Tree.Group{o, kids, cl}, rest, e))),
              inert.ring.plus_scan(rest, Ring.or_tok(seen, Ring.drop_in(kids, wins)), wins,
                inert.ok_t(Tree.Group{o, kids, cl}, rest, e))))
        case Tree.Stmt{+sk, +kids, +body}:
          +es = inert.ok_h(Tree.Stmt{sk, kids, body}, rest, e)
          inert.ring.or2(Ring.plus_scan(D1.inert.node(kids), None{}, wins), Ring.plus_scan(kids, None{}, wins),
            Ring.or_tok(Ring.plus_scan(D1.inert.node(body), None{}, wins), Ring.plus_scan(D1.inert.node(rest),
              seen, wins)), Ring.or_tok(Ring.plus_scan(body, None{}, wins), Ring.plus_scan(rest, seen, wins)),
            inert.ring.plus_scan(kids, None{}, wins, M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es)),
            inert.ring.or2(Ring.plus_scan(D1.inert.node(body), None{}, wins), Ring.plus_scan(body, None{}, wins),
              Ring.plus_scan(D1.inert.node(rest), seen, wins), Ring.plus_scan(rest, seen, wins),
              inert.ring.plus_scan(body, None{}, wins, M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es)),
              inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.Stmt{sk, kids, body}, rest, e))))
        case Tree.NNil{}: inert.ring.plus_scan(rest, seen, wins, e)
        case Tree.NCons{x, y}: inert.ring.plus_scan(rest, seen, wins, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# every self-call argument that slides a window, the arguments read that way
law inert.ring.slides:
  for as: List<&2, Tree.Node>
  for +params: List<&2, String>
  for +path: String
  for +wins: List<&2, String>
  for +e: {inert.noks(as) == True{} : Bool}
  {Ring.slides(inert.nodes(as), params, path, wins) == Ring.slides(as, params, path, wins) : List<&2, F.Finding>}

def inert.ring.slides(as, params, path, wins, e):
  match as:
    case Nil{}: {==}
    case Con{+h, +rest}:
      +sw = Ring.slot_wins(Maybe.default(&2, String, List.head(&2, String, params), ""), wins)
      +pt = List.tail(&2, String, params)
      +lhs = Ring.slides(inert.nodes(Con{h, rest}), params, path, wins)
      %inert.ring.slides(rest, pt, path, wins, M1.inert.and_r(D1.inert.ok(h), inert.noks(rest), e)) : {lhs
        == List.append(&2, F.Finding, Ring.slide(h, path, sw), _) : List<&2, F.Finding>}
      %inert.ring.plus_scan(h, None{}, sw, M1.inert.and_l(D1.inert.ok(h), inert.noks(rest), e)) : {lhs
        == List.append(&2, F.Finding, Ring.slide_at(_, path), Ring.slides(inert.nodes(rest), pt, path, wins))
          : List<&2, F.Finding>}
      {==}

# a name then a group: a self-call's sliding arguments, the group and the rest
# walked as they were
law inert.ring.lg:
  for +b: Bool
  for +t: String
  for +o: String
  for +self: String
  for +params: List<&2, String>
  for +path: String
  for +wins: List<&2, String>
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +es: {D1.inert.marked(self) == False{} : Bool}
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  for ik: {Ring.walk(D1.inert.node(kids), self, params, path, wins) == Ring.walk(kids, self, params, path, wins)
    : List<&2, F.Finding>}
  for ir: {Ring.walk(D1.inert.node(r2), self, params, path, wins) == Ring.walk(r2, self, params, path, wins)
    : List<&2, F.Finding>}
  {List.concat(&2, F.Finding, [Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(String.eq(o, "("),
    String.eq(D1.inert.keep(b, t), self))), [], _u => Ring.slides(Calls.args(D1.inert.node(kids)), params, path,
      wins)), Ring.walk(D1.inert.node(kids), self, params, path, wins), Ring.walk(D1.inert.node(r2), self, params,
        path, wins)])
    == List.concat(&2, F.Finding, [Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(String.eq(o, "("),
      String.eq(t, self))), [], _u => Ring.slides(Calls.args(kids), params, path, wins)), Ring.walk(kids, self, params,
        path, wins), Ring.walk(r2, self, params, path, wins)]) : List<&2, F.Finding>}

def inert.ring.lg(b, t, o, self, params, path, wins, kids, r2, ef, es, ek, ik, ir):
  +aa = Calls.args(kids)
  +hi = Ring.slides(Calls.args(D1.inert.node(kids)), params, path, wins)
  +eh = Equal.trans(List<&2, F.Finding>, hi, Ring.slides(inert.nodes(aa), params, path, wins), Ring.slides(aa, params,
    path, wins), Equal.cong(List<&2, Tree.Node>, List<&2, F.Finding>, z => Ring.slides(z, params, path, wins),
      Calls.args(D1.inert.node(kids)), inert.nodes(aa), inert.args(kids)),
    inert.ring.slides(aa, params, path, wins, inert.ok.args.go(kids, Tree.NNil{}, [], ek, {==}, {==})))
  inert.cat3(Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(String.eq(o, "("), String.eq(D1.inert.keep(b, t),
    self))), [], _u => hi), Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(String.eq(o, "("), String.eq(t, self))),
      [], _u => Ring.slides(aa, params, path, wins)),
    Ring.walk(D1.inert.node(kids), self, params, path, wins), Ring.walk(kids, self, params, path, wins),
    Ring.walk(D1.inert.node(r2), self, params, path, wins), Ring.walk(r2, self, params, path, wins),
    inert.stop(Bool.not(Bool.and(String.eq(o, "("), String.eq(D1.inert.keep(b, t), self))), Bool.not(Bool.and(
      String.eq(o, "("), String.eq(t, self))), hi, Ring.slides(aa, params, path, wins),
      Equal.cong(Bool, Bool, z => Bool.not(Bool.and(String.eq(o, "("), z)), String.eq(D1.inert.keep(b, t), self),
        String.eq(t, self), M1.inert.eq_keep(b, t, self, ef, es)), eh),
    ik, ir)

# ring's walk reads no string: a leaf's text is compared with the def's name,
# which no string equals
law inert.ring.walk:
  for nn: Tree.Node
  for +self: String
  for +params: List<&2, String>
  for +path: String
  for +wins: List<&2, String>
  for +es: {D1.inert.marked(self) == False{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Ring.walk(D1.inert.node(nn), self, params, path, wins) == Ring.walk(nn, self, params, path, wins)
    : List<&2, F.Finding>}

def inert.ring.walk(nn, self, params, path, wins, es, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{o, +kids, +cl}:
                      match o:
                        case Lex.Tok{+ok, +ot, +ol, +oc}:
                          +lf = {Tree.Leaf{Lex.Tok{k, t, l, c}} : Tree.Node}
                          +gp = {Tree.Group{Lex.Tok{ok, ot, ol, oc}, kids, cl} : Tree.Node}
                          +eg = inert.ok_t(lf, Tree.NCons{gp, r2}, e)
                          +ec = inert.ok_h(gp, r2, eg)
                          inert.ring.lg(D1.inert.blanks(k), t, ot, self, params, path, wins, kids, r2,
                            inert.ok_h(lf, Tree.NCons{gp, r2}, e), es, ec,
                            inert.ring.walk(kids, self, params, path, wins, es, ec),
                            inert.ring.walk(r2, self, params, path, wins, es, inert.ok_t(gp, r2, eg)))
                    case Tree.Leaf{x}:
                      inert.ring.walk(rest, self, params, path, wins, es, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}},
                        rest, e))
                    case Tree.Stmt{x, y, z}:
                      inert.ring.walk(rest, self, params, path, wins, es, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}},
                        rest, e))
                    case Tree.NNil{}:
                      inert.ring.walk(rest, self, params, path, wins, es, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}},
                        rest, e))
                    case Tree.NCons{x, y}:
                      inert.ring.walk(rest, self, params, path, wins, es, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}},
                        rest, e))
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NNil{}: {==}
        case Tree.Group{+o, +kids, +cl}:
          inert.cat2(Ring.walk(D1.inert.node(kids), self, params, path, wins), Ring.walk(kids, self, params, path,
            wins), Ring.walk(D1.inert.node(rest), self, params, path, wins), Ring.walk(rest, self, params, path,
              wins),
            inert.ring.walk(kids, self, params, path, wins, es, inert.ok_h(Tree.Group{o, kids, cl}, rest, e)),
            inert.ring.walk(rest, self, params, path, wins, es, inert.ok_t(Tree.Group{o, kids, cl}, rest, e)))
        case Tree.Stmt{+sk, +kids, +body}:
          +es2 = inert.ok_h(Tree.Stmt{sk, kids, body}, rest, e)
          inert.cat3(Ring.walk(D1.inert.node(kids), self, params, path, wins), Ring.walk(kids, self, params, path,
            wins), Ring.walk(D1.inert.node(body), self, params, path, wins), Ring.walk(body, self, params, path,
              wins), Ring.walk(D1.inert.node(rest), self, params, path, wins), Ring.walk(rest, self, params, path,
                wins),
            inert.ring.walk(kids, self, params, path, wins, es, M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body),
              es2)),
            inert.ring.walk(body, self, params, path, wins, es, M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body),
              es2)),
            inert.ring.walk(rest, self, params, path, wins, es, inert.ok_t(Tree.Stmt{sk, kids, body}, rest, e)))
        case Tree.NNil{}: inert.ring.walk(rest, self, params, path, wins, es, e)
        case Tree.NCons{x, y}:
          inert.ring.walk(rest, self, params, path, wins, es, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# the top-level names of a chain read that way are the ones it had
law inert.ring.names_in:
  for nn: Tree.Node
  for +acc: List<&2, String>
  {Ring.names_in(D1.inert.node(nn), acc) == Ring.names_in(nn, acc) : List<&2, String>}

def inert.ring.names_in(nn, acc):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, l, c}:
              match k:
                case Lex.TName{}:
                  Equal.cong(List<&2, String>, List<&2, String>, z => t <> z, Ring.names_in(D1.inert.node(rest),
                    acc), Ring.names_in(rest, acc), inert.ring.names_in(rest, acc))
                case Lex.TUpper{}: inert.ring.names_in(rest, acc)
                case Lex.TDotted{}: inert.ring.names_in(rest, acc)
                case Lex.TWild{}: inert.ring.names_in(rest, acc)
                case Lex.TKey{}: inert.ring.names_in(rest, acc)
                case Lex.TNum{}: inert.ring.names_in(rest, acc)
                case Lex.TStr{}: inert.ring.names_in(rest, acc)
                case Lex.TChar{}: inert.ring.names_in(rest, acc)
                case Lex.TComment{}: inert.ring.names_in(rest, acc)
                case Lex.TSpace{}: inert.ring.names_in(rest, acc)
                case Lex.TNewline{}: inert.ring.names_in(rest, acc)
                case Lex.TOp{}: inert.ring.names_in(rest, acc)
                case Lex.TColon{}: inert.ring.names_in(rest, acc)
                case Lex.TEq{}: inert.ring.names_in(rest, acc)
                case Lex.TBind{}: inert.ring.names_in(rest, acc)
                case Lex.TArrow{}: inert.ring.names_in(rest, acc)
                case Lex.TLam{}: inert.ring.names_in(rest, acc)
                case Lex.TAll{}: inert.ring.names_in(rest, acc)
                case Lex.TAmp{}: inert.ring.names_in(rest, acc)
                case Lex.TOpen{}: inert.ring.names_in(rest, acc)
                case Lex.TClose{}: inert.ring.names_in(rest, acc)
                case Lex.TComma{}: inert.ring.names_in(rest, acc)
        case Tree.Group{o, gk, cl}: inert.ring.names_in(rest, acc)
        case Tree.Stmt{sk, sks, sb}: inert.ring.names_in(rest, acc)
        case Tree.NNil{}: inert.ring.names_in(rest, acc)
        case Tree.NCons{x, y}: inert.ring.names_in(rest, acc)
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# the scrutinees of a statement read that way are the ones it had: only a
# keyword's text is read
law inert.ring.match_names:
  for kids: Tree.Node
  for +acc: List<&2, String>
  {Ring.match_names(D1.inert.node(kids), acc) == Ring.match_names(kids, acc) : List<&2, String>}

def inert.ring.match_names(kids, acc):
  match kids:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +kw, l, c}:
              match k:
                case Lex.TName{}: {==}
                case Lex.TUpper{}: {==}
                case Lex.TDotted{}: {==}
                case Lex.TWild{}: {==}
                case Lex.TKey{}:
                  Equal.cong(List<&2, String>, List<&2, String>, z => Lazy.stop(List<&2, String>,
                    Bool.not(String.eq(kw, "match")), acc, _u => z), Ring.names_in(D1.inert.node(rest), acc),
                    Ring.names_in(rest, acc), inert.ring.names_in(rest, acc))
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
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# three chains matched in turn, each read as it did
law inert.ring.m3:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +a0: List<&2, String>
  for ik: {Ring.matched(D1.inert.node(kids), a0) == Ring.matched(kids, a0) : List<&2, String>}
  for ib: {Ring.matched(D1.inert.node(body), Ring.matched(kids, a0)) == Ring.matched(body, Ring.matched(kids, a0))
    : List<&2, String>}
  for ir: {Ring.matched(D1.inert.node(rest), Ring.matched(body, Ring.matched(kids, a0))) == Ring.matched(rest,
    Ring.matched(body, Ring.matched(kids, a0))) : List<&2, String>}
  {Ring.matched(D1.inert.node(rest), Ring.matched(D1.inert.node(body), Ring.matched(D1.inert.node(kids), a0)))
    == Ring.matched(rest, Ring.matched(body, Ring.matched(kids, a0))) : List<&2, String>}

def inert.ring.m3(kids, body, rest, a0, ik, ib, ir):
  +lhs = Ring.matched(D1.inert.node(rest), Ring.matched(D1.inert.node(body), Ring.matched(D1.inert.node(kids),
    a0)))
  %ir : {lhs == _ : List<&2, String>}
  %ib : {lhs == Ring.matched(D1.inert.node(rest), _) : List<&2, String>}
  %ik : {lhs == Ring.matched(D1.inert.node(rest), Ring.matched(D1.inert.node(body), _)) : List<&2, String>}
  {==}

# the names a def matches, its body read that way, are the ones it matched
law inert.ring.matched:
  for nn: Tree.Node
  for +acc: List<&2, String>
  {Ring.matched(D1.inert.node(nn), acc) == Ring.matched(nn, acc) : List<&2, String>}

def inert.ring.matched(nn, acc):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{sk, +kids, +body}:
          match sk:
            case Tree.STerm{}:
              %inert.ring.match_names(kids, acc) : {Ring.matched(D1.inert.node(Tree.NCons{Tree.Stmt{Tree.STerm{},
                kids, body}, rest}), acc) == Ring.matched(rest, Ring.matched(body, Ring.matched(kids, _)))
                : List<&2, String>}
              inert.ring.m3(kids, body, rest, Ring.match_names(D1.inert.node(kids), acc),
                inert.ring.matched(kids, Ring.match_names(D1.inert.node(kids), acc)),
                inert.ring.matched(body, Ring.matched(kids, Ring.match_names(D1.inert.node(kids), acc))),
                inert.ring.matched(rest, Ring.matched(body, Ring.matched(kids, Ring.match_names(D1.inert.node(kids),
                  acc)))))
            case Tree.SDef{}: inert.ring.m3(kids, body, rest, acc, inert.ring.matched(kids, acc),
              inert.ring.matched(body, Ring.matched(kids, acc)), inert.ring.matched(rest, Ring.matched(body,
                Ring.matched(kids, acc))))
            case Tree.SType{}: inert.ring.m3(kids, body, rest, acc, inert.ring.matched(kids, acc),
              inert.ring.matched(body, Ring.matched(kids, acc)), inert.ring.matched(rest, Ring.matched(body,
                Ring.matched(kids, acc))))
            case Tree.SLaw{}: inert.ring.m3(kids, body, rest, acc, inert.ring.matched(kids, acc),
              inert.ring.matched(body, Ring.matched(kids, acc)), inert.ring.matched(rest, Ring.matched(body,
                Ring.matched(kids, acc))))
            case Tree.SImport{}: inert.ring.m3(kids, body, rest, acc, inert.ring.matched(kids, acc),
              inert.ring.matched(body, Ring.matched(kids, acc)), inert.ring.matched(rest, Ring.matched(body,
                Ring.matched(kids, acc))))
            case Tree.SCase{}: inert.ring.m3(kids, body, rest, acc, inert.ring.matched(kids, acc),
              inert.ring.matched(body, Ring.matched(kids, acc)), inert.ring.matched(rest, Ring.matched(body,
                Ring.matched(kids, acc))))
            case Tree.SFor{}: inert.ring.m3(kids, body, rest, acc, inert.ring.matched(kids, acc),
              inert.ring.matched(body, Ring.matched(kids, acc)), inert.ring.matched(rest, Ring.matched(body,
                Ring.matched(kids, acc))))
            case Tree.SLet{}: inert.ring.m3(kids, body, rest, acc, inert.ring.matched(kids, acc),
              inert.ring.matched(body, Ring.matched(kids, acc)), inert.ring.matched(rest, Ring.matched(body,
                Ring.matched(kids, acc))))
        case Tree.Group{o, +kids, cl}:
          %inert.ring.matched(rest, Ring.matched(kids, acc)) : {Ring.matched(D1.inert.node(rest),
            Ring.matched(D1.inert.node(kids), acc)) == _ : List<&2, String>}
          %inert.ring.matched(kids, acc) : {Ring.matched(D1.inert.node(rest), Ring.matched(D1.inert.node(kids),
            acc)) == Ring.matched(D1.inert.node(rest), _) : List<&2, String>}
          {==}
        case Tree.Leaf{tok}: inert.ring.matched(rest, acc)
        case Tree.NNil{}: inert.ring.matched(rest, acc)
        case Tree.NCons{x, y}: inert.ring.matched(rest, acc)
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# the windows of a def read that way are the ones they were
law inert.ring.windows:
  for +sig: Tree.Node
  for +body: Tree.Node
  {Ring.windows(D1.inert.node(sig), D1.inert.node(body)) == Ring.windows(sig, body) : List<&2, String>}

def inert.ring.windows(sig, body):
  +lhs = Ring.windows(D1.inert.node(sig), D1.inert.node(body))
  %inert.names(sig) : {lhs == Ring.windows.go(_, Ring.matched(body, []), []) : List<&2, String>}
  %inert.ring.matched(body, []) : {lhs == Ring.windows.go(Calls.names(D1.inert.node(sig)), _, []) : List<&2, String>}
  {==}

# ring over the defs read that way reports what it reports over the defs
law inert.ring.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  for +e: {inert.dok(ds) == True{} : Bool}
  {Ring.check.go(inert.defs(ds), path, acc) == Ring.check.go(ds, path, acc) : List<&2, F.Finding>}

def inert.ring.go(ds, path, acc, e):
  match ds:
    case Nil{}: {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +en = inert.dok.head(name, sig, body, rest, e)
      +eb = inert.dok.body(name, sig, body, rest, e)
      +ib = D1.inert.node(body)
      +isg = D1.inert.node(sig)
      +wi = Ring.walk(ib, name, Calls.names(isg), path, Ring.windows(isg, ib))
      +wo = Ring.walk(body, name, Calls.names(sig), path, Ring.windows(sig, body))
      +lst = Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Calls.calls(ib, name), Bool.not(Calls.exempt(path,
        isg)))), [], _u => wi)
      +ew = Equal.trans(List<&2, F.Finding>, wi, Ring.walk(ib, name, Calls.names(sig), path, Ring.windows(sig, body)),
        wo, Equal.trans(List<&2, F.Finding>, wi, Ring.walk(ib, name, Calls.names(sig), path, Ring.windows(isg, ib)),
          Ring.walk(ib, name, Calls.names(sig), path, Ring.windows(sig, body)),
          Equal.cong(List<&2, String>, List<&2, F.Finding>, z => Ring.walk(ib, name, z, path, Ring.windows(isg, ib)),
            Calls.names(isg), Calls.names(sig), inert.names(sig)),
          Equal.cong(List<&2, String>, List<&2, F.Finding>, z => Ring.walk(ib, name, Calls.names(sig), path, z),
            Ring.windows(isg, ib), Ring.windows(sig, body), inert.ring.windows(sig, body))),
        inert.ring.walk(body, name, Calls.names(sig), path, Ring.windows(sig, body), en, eb))
      %inert.stop(Bool.not(Bool.and(Calls.calls(ib, name), Bool.not(Calls.exempt(path, isg)))),
        Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))), wi, wo,
        inert.gate(path, name, sig, body, en, eb), ew) :
        {Ring.check.go(inert.defs(rest), path, lst <> acc) == Ring.check.go(rest, path, _ <> acc)
          : List<&2, F.Finding>}
      inert.ring.go(rest, path, lst <> acc, inert.dok.rest(name, sig, body, rest, e))

def Laws.inert_ring(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, ok, ok2, e):
  M1.inert.via(Tree.Node, z => Ring.check.go(Calls.defs(z), path, []), tree, tree2, D1.inert.node(tree),
    D1.inert.node(tree2),
    inert.lift(z => Ring.check.go(z, path, []), tree, inert.ring.go(Calls.defs(tree), path, [], inert.dok.of(tree,
      ok))),
    inert.lift(z => Ring.check.go(z, path, []), tree2, inert.ring.go(Calls.defs(tree2), path, [],
      inert.dok.of(tree2, ok2))),
    e)

# Inert text, arms and on (laws/CodeRulesIgnoreCommentsAndStrings.bend): the tree rules not over a
# file's defs, on the lemmas above.

# arms
# ----

# a case statement's pattern read that way is the pattern it had, read that way
law inert.pattern:
  for kids: Tree.Node
  {T.pattern(D1.inert.node(kids)) == D1.inert.node(T.pattern(kids)) : Tree.Node}

def inert.pattern(kids):
  match kids:
    case Tree.NCons{h, rest}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a from-k-up arm whose binder is read that way: a binder is never cut
law inert.arms.bpick:
  for x: Bool
  for b: Lex.TokKind
  for +p: String
  for -f: String -> Arms.Arm
  {Bool.pick(Arms.Arm, Bool.and(x, Arms.binder(b)), f(D1.inert.keep(D1.inert.blanks(b), p)), Arms.AOther{})
    == Bool.pick(Arms.Arm, Bool.and(x, Arms.binder(b)), f(p), Arms.AOther{}) : Arms.Arm}

def inert.arms.bpick(x, b, _p, _f):
  match x:
    case False{}: {==}
    case True{}:
      match b:
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

# what follows a Nat literal read that way makes the arm it made
law inert.arms.shape:
  for rest: Tree.Node
  for +kk: U32
  for +tt: String
  for +line: U32
  for +col: U32
  {Arms.lit.shape(D1.inert.node(rest), kk, tt, line, col) == Arms.lit.shape(rest, kk, tt, line, col) : Arms.Arm}

def inert.arms.shape(rest, kk, tt, line, col):
  match rest:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +o, l, c}:
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
                case Lex.TOp{}:
                  match r:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Leaf{tok2}:
                          match tok2:
                            case Lex.Tok{+b, +p, l2, c2}:
                              match r2:
                                case Tree.NCons{h3, r3}:
                                  match h3:
                                    case Tree.Leaf{tok3}:
                                      match tok3:
                                        case Lex.Tok{k3, s, l3, c3}:
                                          match k3:
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
                                            case Lex.TColon{}:
                                              inert.arms.bpick(String.eq(o, "+"), b, p, z => Arms.APlus{kk,
                                                tt ++ "+" ++ z, line, col, T.width(tt)})
                                            case Lex.TEq{}: {==}
                                            case Lex.TBind{}: {==}
                                            case Lex.TArrow{}: {==}
                                            case Lex.TLam{}: {==}
                                            case Lex.TAll{}: {==}
                                            case Lex.TAmp{}: {==}
                                            case Lex.TOpen{}: {==}
                                            case Lex.TClose{}: {==}
                                            case Lex.TComma{}: {==}
                                    case Tree.Group{x, y, z}: {==}
                                    case Tree.Stmt{x, y, z}: {==}
                                    case Tree.NNil{}: {==}
                                    case Tree.NCons{x, y}: {==}
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NNil{}: {==}
                        case Tree.Group{x, y, z}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
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
        case Tree.Group{x, y, z}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a Nat literal's arm, what follows it read that way
law inert.arms.lit:
  for mm: Maybe<&2, U32>
  for +tt: String
  for +rest: Tree.Node
  for +line: U32
  for +col: U32
  {Arms.lit.of(mm, tt, D1.inert.node(rest), line, col) == Arms.lit.of(mm, tt, rest, line, col) : Arms.Arm}

def inert.arms.lit(mm, tt, rest, line, col):
  match mm:
    case None{}: {==}
    case Some{+k}: inert.arms.shape(rest, k, tt, line, col)

# a case pattern read that way makes the arm it made: a Nat literal, a capital
# name and a binder are never cut
law inert.arms.arm:
  for pat: Tree.Node
  {Arms.arm(D1.inert.node(pat)) == Arms.arm(pat) : Arms.Arm}

def inert.arms.arm(pat):
  match pat:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, +l, +c}:
              match k:
                case Lex.TName{}: {==}
                case Lex.TUpper{}:
                  match rest:
                    case Tree.NCons{g, more}:
                      match g:
                        case Tree.Group{op, gk, cl}:
                          match gk:
                            case Tree.NCons{h3, +r3}:
                              match h3:
                                case Tree.Leaf{tok3}:
                                  match tok3:
                                    case Lex.Tok{+k3, +p, l2, c2}:
                                      match r3:
                                        case Tree.NNil{}:
                                          inert.arms.bpick(String.eq(t, "Succ"), k3, p, z => Arms.APlus{1,
                                            "Succ{" ++ z ++ "}", l, c, 4})
                                        case Tree.Leaf{x}: {==}
                                        case Tree.Group{x, y, z}: {==}
                                        case Tree.Stmt{x, y, z}: {==}
                                        case Tree.NCons{x, y}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NNil{}: {==}
                                case Tree.NCons{x, y}: {==}
                            case Tree.Leaf{x}: {==}
                            case Tree.Group{x, y, z}: {==}
                            case Tree.Stmt{x, y, z}: {==}
                            case Tree.NNil{}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TDotted{}: {==}
                case Lex.TWild{}: {==}
                case Lex.TKey{}: {==}
                case Lex.TNum{}: inert.arms.lit(T.nat_value(t), t, rest, l, c)
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
        case Tree.Group{x, y, z}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a match statement read that way has one scrutinee as it had: only a
# keyword's text is read
law inert.arms.single:
  for kids: Tree.Node
  {Arms.single(D1.inert.node(kids)) == Arms.single(kids) : Bool}

def inert.arms.single(kids):
  match kids:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}: {==}
                case Lex.TUpper{}: {==}
                case Lex.TDotted{}: {==}
                case Lex.TWild{}: {==}
                case Lex.TKey{}:
                  match r:
                    case Tree.NCons{x, +r2}:
                      match r2:
                        case Tree.NCons{h3, +r3}:
                          match h3:
                            case Tree.Leaf{tok3}:
                              match tok3:
                                case Lex.Tok{k3, s, l3, c3}:
                                  match k3:
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
                                    case Lex.TColon{}:
                                      match r3:
                                        case Tree.NNil{}: {==}
                                        case Tree.Leaf{y}: {==}
                                        case Tree.Group{y, z, w}: {==}
                                        case Tree.Stmt{y, z, w}: {==}
                                        case Tree.NCons{y, z}: {==}
                                    case Lex.TEq{}: {==}
                                    case Lex.TBind{}: {==}
                                    case Lex.TArrow{}: {==}
                                    case Lex.TLam{}: {==}
                                    case Lex.TAll{}: {==}
                                    case Lex.TAmp{}: {==}
                                    case Lex.TOpen{}: {==}
                                    case Lex.TClose{}: {==}
                                    case Lex.TComma{}: {==}
                            case Tree.Group{y, z, w}: {==}
                            case Tree.Stmt{y, z, w}: {==}
                            case Tree.NNil{}: {==}
                            case Tree.NCons{y, z}: {==}
                        case Tree.Leaf{y}: {==}
                        case Tree.Group{y, z, w}: {==}
                        case Tree.Stmt{y, z, w}: {==}
                        case Tree.NNil{}: {==}
                    case Tree.Leaf{y}: {==}
                    case Tree.Group{y, z, w}: {==}
                    case Tree.Stmt{y, z, w}: {==}
                    case Tree.NNil{}: {==}
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
        case Tree.Group{x, y, z}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a case's arm, its tokens read that way
law inert.arms.case:
  for +kids: Tree.Node
  {Arms.arm(T.pattern(D1.inert.node(kids))) == Arms.arm(T.pattern(kids)) : Arms.Arm}

def inert.arms.case(kids):
  Equal.trans(Arms.Arm, Arms.arm(T.pattern(D1.inert.node(kids))), Arms.arm(D1.inert.node(T.pattern(kids))),
    Arms.arm(T.pattern(kids)), Equal.cong(Tree.Node, Arms.Arm, z => Arms.arm(z), T.pattern(D1.inert.node(kids)),
      D1.inert.node(T.pattern(kids)), inert.pattern(kids)), inert.arms.arm(T.pattern(kids)))

# a match's arms read that way are judged as they were
law inert.arms.arms:
  for body: Tree.Node
  for +wide: Maybe<&2, Arms.Wide>
  for +path: String
  {Arms.arms(D1.inert.node(body), wide, path) == Arms.arms(body, wide, path) : List<&2, F.Finding>}

def inert.arms.arms(body, wide, path):
  match body:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{sk, +kids, b}:
          match sk:
            case Tree.SCase{}:
              +ao = Arms.arm(T.pattern(kids))
              +ai = Arms.arm(T.pattern(D1.inert.node(kids)))
              +lhs = Arms.verdict(wide, ai, path, Arms.arms(D1.inert.node(rest), Arms.widen(wide, ai), path))
              %inert.arms.arms(rest, Arms.widen(wide, ao), path) : {lhs == Arms.verdict(wide, ao, path, _)
                : List<&2, F.Finding>}
              %inert.arms.case(kids) : {lhs == Arms.verdict(wide, _, path, Arms.arms(D1.inert.node(rest),
                Arms.widen(wide, _), path)) : List<&2, F.Finding>}
              {==}
            case Tree.SDef{}: inert.arms.arms(rest, wide, path)
            case Tree.SType{}: inert.arms.arms(rest, wide, path)
            case Tree.SLaw{}: inert.arms.arms(rest, wide, path)
            case Tree.SImport{}: inert.arms.arms(rest, wide, path)
            case Tree.SFor{}: inert.arms.arms(rest, wide, path)
            case Tree.SLet{}: inert.arms.arms(rest, wide, path)
            case Tree.STerm{}: inert.arms.arms(rest, wide, path)
        case Tree.Leaf{x}: inert.arms.arms(rest, wide, path)
        case Tree.Group{x, y, z}: inert.arms.arms(rest, wide, path)
        case Tree.NNil{}: inert.arms.arms(rest, wide, path)
        case Tree.NCons{x, y}: inert.arms.arms(rest, wide, path)
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# arms reads no string: a Nat literal, `Succ`, `match` and `+` are read by
# their kind, and a binder by its
law inert.arms.walk:
  for nn: Tree.Node
  for +path: String
  {Arms.walk(D1.inert.node(nn), path) == Arms.walk(nn, path) : List<&2, F.Finding>}

def inert.arms.walk(nn, path):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{sk, +kids, +body}:
          inert.cat3(Lazy.stop(List<&2, F.Finding>, Bool.not(Arms.single(D1.inert.node(kids))), [],
            _u => Arms.arms(D1.inert.node(body), None{}, path)), Lazy.stop(List<&2, F.Finding>,
              Bool.not(Arms.single(kids)), [], _u => Arms.arms(body, None{}, path)),
            Arms.walk(D1.inert.node(body), path), Arms.walk(body, path), Arms.walk(D1.inert.node(rest), path),
            Arms.walk(rest, path),
            inert.stop(Bool.not(Arms.single(D1.inert.node(kids))), Bool.not(Arms.single(kids)),
              Arms.arms(D1.inert.node(body), None{}, path), Arms.arms(body, None{}, path),
              Equal.cong(Bool, Bool, z => Bool.not(z), Arms.single(D1.inert.node(kids)), Arms.single(kids),
                inert.arms.single(kids)), inert.arms.arms(body, None{}, path)),
            inert.arms.walk(body, path), inert.arms.walk(rest, path))
        case Tree.Leaf{x}: inert.arms.walk(rest, path)
        case Tree.Group{x, y, z}: inert.arms.walk(rest, path)
        case Tree.NNil{}: inert.arms.walk(rest, path)
        case Tree.NCons{x, y}: inert.arms.walk(rest, path)
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

def Laws.inert_arms(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, _ok, _ok2, e):
  M1.inert.via(Tree.Node, z => Arms.walk(z, path), tree, tree2, D1.inert.node(tree), D1.inert.node(tree2),
    inert.arms.walk(tree, path), inert.arms.walk(tree2, path), e)

# unused
# ------

# a token by where it stands only
def inert.canon(tok: Lex.Tok) -> Lex.Tok:
  match tok:
    case Lex.Tok{k, t, l, c}: Lex.Tok{Lex.TSpace{}, "", l, c}

# the tokens, each by where it stands only
def inert.canons(ts: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match ts:
    case Nil{}: Nil{}
    case Con{h, t}: inert.canon(h) <> inert.canons(t)

# a token read that way stands where it stood
law inert.canon_tok:
  for tok: Lex.Tok
  {inert.canon(D1.inert.tok(tok)) == inert.canon(tok) : Lex.Tok}

def inert.canon_tok(tok):
  match tok:
    case Lex.Tok{k, t, l, c}: {==}

# a group's close onto tokens that stand alike
law inert.canon_close:
  for close: Maybe<&2, Lex.Tok>
  for -x: List<&2, Lex.Tok>
  for -y: List<&2, Lex.Tok>
  for e: {inert.canons(x) == inert.canons(y) : List<&2, Lex.Tok>}
  {inert.canons(Tree.leaf_close(close, x)) == inert.canons(Tree.leaf_close(close, y)) : List<&2, Lex.Tok>}

def inert.canon_close(close, x, y, e):
  match close:
    case None{}: e
    case Some{+tok}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => inert.canon(tok) <> z, inert.canons(x), inert.canons(y),
        e)

# the leaves of a node read that way stand where they stood
law inert.canon_leaves:
  for nn: Tree.Node
  for -a: List<&2, Lex.Tok>
  for -b: List<&2, Lex.Tok>
  for e: {inert.canons(a) == inert.canons(b) : List<&2, Lex.Tok>}
  {inert.canons(Tree.leaves.go(D1.inert.node(nn), a)) == inert.canons(Tree.leaves.go(nn, b)) : List<&2, Lex.Tok>}

def inert.canon_leaves(nn, a, b, e):
  match nn:
    case Tree.Leaf{+tok}:
      %inert.canon_tok(tok) : {inert.canon(D1.inert.tok(tok)) <> inert.canons(a) == _ <> inert.canons(b)
        : List<&2, Lex.Tok>}
      %e : {inert.canon(D1.inert.tok(tok)) <> inert.canons(a) == inert.canon(D1.inert.tok(tok)) <> _
        : List<&2, Lex.Tok>}
      {==}
    case Tree.Group{+open, kids, close}:
      inert.canon_close(close, Tree.leaves.go(D1.inert.node(kids), open <> a), Tree.leaves.go(kids, open <> b),
        inert.canon_leaves(kids, open <> a, open <> b, Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
          z => inert.canon(open) <> z, inert.canons(a), inert.canons(b), e)))
    case Tree.Stmt{sk, kids, body}:
      inert.canon_leaves(body, Tree.leaves.go(D1.inert.node(kids), a), Tree.leaves.go(kids, b),
        inert.canon_leaves(kids, a, b, e))
    case Tree.NNil{}: e
    case Tree.NCons{h, t}:
      inert.canon_leaves(t, Tree.leaves.go(D1.inert.node(h), a), Tree.leaves.go(h, b), inert.canon_leaves(h, a, b, e))

# reversing, by where they stand
law inert.canon_rev:
  for xs: List<&2, Lex.Tok>
  for +acc: List<&2, Lex.Tok>
  {inert.canons(List.reverse.go(&2, Lex.Tok, xs, acc)) == List.reverse.go(&2, Lex.Tok, inert.canons(xs),
    inert.canons(acc)) : List<&2, Lex.Tok>}

def inert.canon_rev(xs, acc):
  match xs:
    case Nil{}: {==}
    case Con{+h, t}: inert.canon_rev(t, h <> acc)

# the lines of tokens are the lines of where they stand
law inert.canon_lines:
  for ts: List<&2, Lex.Tok>
  for +acc: List<&2, U32>
  {Unused.lines(ts, acc) == Unused.lines(inert.canons(ts), acc) : List<&2, U32>}

def inert.canon_lines(ts, acc):
  match ts:
    case Nil{}: {==}
    case Con{h, +t}:
      match h:
        case Lex.Tok{k, x, +l, c}:
          Equal.cong(List<&2, U32>, List<&2, U32>, z => l <> z, Unused.lines(t, acc),
            Unused.lines(inert.canons(t), acc), inert.canon_lines(t, acc))

# the lines of a node's leaves read that way are the lines they were
law inert.unused.lines:
  for +kids: Tree.Node
  for +acc: List<&2, U32>
  {Unused.lines(Tree.leaves(D1.inert.node(kids)), acc) == Unused.lines(Tree.leaves(kids), acc) : List<&2, U32>}

def inert.unused.lines(kids, acc):
  +li = Tree.leaves.go(D1.inert.node(kids), [])
  +lo = Tree.leaves.go(kids, [])
  +ec = Equal.trans(List<&2, Lex.Tok>, inert.canons(List.reverse.go(&2, Lex.Tok, li, [])), List.reverse.go(&2, Lex.Tok,
    inert.canons(li), []), inert.canons(List.reverse.go(&2, Lex.Tok, lo, [])), inert.canon_rev(li, []),
    Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, inert.canons(li), []), List.reverse.go(&2, Lex.Tok,
      inert.canons(lo), []), inert.canons(List.reverse.go(&2, Lex.Tok, lo, [])),
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => List.reverse.go(&2, Lex.Tok, z, []), inert.canons(li),
        inert.canons(lo), inert.canon_leaves(kids, [], [], {==})),
      Equal.sym(List<&2, Lex.Tok>, inert.canons(List.reverse.go(&2, Lex.Tok, lo, [])), List.reverse.go(&2, Lex.Tok,
        inert.canons(lo), []), inert.canon_rev(lo, []))))
  Equal.trans(List<&2, U32>, Unused.lines(List.reverse.go(&2, Lex.Tok, li, []), acc),
    Unused.lines(inert.canons(List.reverse.go(&2, Lex.Tok, li, [])), acc),
    Unused.lines(List.reverse.go(&2, Lex.Tok, lo, []), acc),
    inert.canon_lines(List.reverse.go(&2, Lex.Tok, li, []), acc),
    Equal.trans(List<&2, U32>, Unused.lines(inert.canons(List.reverse.go(&2, Lex.Tok, li, [])), acc),
      Unused.lines(inert.canons(List.reverse.go(&2, Lex.Tok, lo, [])), acc),
      Unused.lines(List.reverse.go(&2, Lex.Tok, lo, []), acc),
      Equal.cong(List<&2, Lex.Tok>, List<&2, U32>, z => Unused.lines(z, acc),
        inert.canons(List.reverse.go(&2, Lex.Tok, li, [])), inert.canons(List.reverse.go(&2, Lex.Tok, lo, [])), ec),
      Equal.sym(List<&2, U32>, Unused.lines(List.reverse.go(&2, Lex.Tok, lo, []), acc),
        Unused.lines(inert.canons(List.reverse.go(&2, Lex.Tok, lo, [])), acc),
        inert.canon_lines(List.reverse.go(&2, Lex.Tok, lo, []), acc))))

# a node's `:` test, the node read that way, is the one it was
law inert.unused.colon:
  for nn: Tree.Node
  {Unused.colon(D1.inert.node(nn)) == Unused.colon(nn) : Bool}

def inert.unused.colon(nn):
  match nn:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# a statement's `:` ending, its chain read that way, is the one it was
law inert.unused.ends:
  for kids: Tree.Node
  for last: Bool
  {Unused.foreign.ends(D1.inert.node(kids), last) == Unused.foreign.ends(kids, last) : Bool}

def inert.unused.ends(kids, _last):
  match kids:
    case Tree.NCons{+h, +t}:
      Equal.trans(Bool, Unused.foreign.ends(D1.inert.node(t), Unused.colon(D1.inert.node(h))),
        Unused.foreign.ends(D1.inert.node(t), Unused.colon(h)), Unused.foreign.ends(t, Unused.colon(h)),
        Equal.cong(Bool, Bool, z => Unused.foreign.ends(D1.inert.node(t), z), Unused.colon(D1.inert.node(h)),
          Unused.colon(h), inert.unused.colon(h)),
        inert.unused.ends(t, Unused.colon(h)))
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a body's opening import, the body read that way, is the one it was
law inert.unused.opens:
  for body: Tree.Node
  for open: Bool
  {Unused.foreign.opens(D1.inert.node(body), open) == Unused.foreign.opens(body, open) : Bool}

def inert.unused.opens(body, open):
  match body:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{sk, +kids, b}:
          match open:
            case True{}:
              Equal.trans(Bool,
                Unused.foreign.opens(D1.inert.node(rest),
                  Bool.not(Unused.foreign.ends(D1.inert.node(kids), False{}))),
                Unused.foreign.opens(D1.inert.node(rest), Bool.not(Unused.foreign.ends(kids, False{}))),
                Unused.foreign.opens(rest, Bool.not(Unused.foreign.ends(kids, False{}))),
                Equal.cong(Bool, Bool, z => Unused.foreign.opens(D1.inert.node(rest), Bool.not(z)),
                  Unused.foreign.ends(D1.inert.node(kids), False{}), Unused.foreign.ends(kids, False{}),
                  inert.unused.ends(kids, False{})),
                inert.unused.opens(rest, Bool.not(Unused.foreign.ends(kids, False{}))))
            case False{}: {==}
        case Tree.Leaf{x}: {==}
        case Tree.Group{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a def's lines onto the lines after it, the tree read that way, are the ones
# they were
law inert.unused.def:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +ih: {Unused.foreign(D1.inert.node(rest)) == Unused.foreign(rest) : List<&2, U32>}
  {Bool.pick(List<&2, U32>,
    Unused.foreign.opens(D1.inert.node(body), Bool.not(Unused.foreign.ends(D1.inert.node(kids), False{}))),
    Unused.lines(Tree.leaves(D1.inert.node(kids)), Unused.foreign(D1.inert.node(rest))),
    Unused.foreign(D1.inert.node(rest)))
    == Bool.pick(List<&2, U32>, Unused.foreign.opens(body, Bool.not(Unused.foreign.ends(kids, False{}))),
      Unused.lines(Tree.leaves(kids), Unused.foreign(rest)), Unused.foreign(rest)) : List<&2, U32>}

def inert.unused.def(kids, body, rest, ih):
  +fi = Unused.foreign(D1.inert.node(rest))
  +fo = Unused.foreign(rest)
  +ra = Unused.lines(Tree.leaves(D1.inert.node(kids)), fi)
  +rb = Unused.lines(Tree.leaves(kids), fo)
  +c1 = Unused.foreign.opens(D1.inert.node(body), Bool.not(Unused.foreign.ends(D1.inert.node(kids), False{})))
  +c2 = Unused.foreign.opens(body, Bool.not(Unused.foreign.ends(kids, False{})))
  +ec = Equal.trans(Bool, c1,
    Unused.foreign.opens(D1.inert.node(body), Bool.not(Unused.foreign.ends(kids, False{}))), c2,
    Equal.cong(Bool, Bool, z => Unused.foreign.opens(D1.inert.node(body), Bool.not(z)),
      Unused.foreign.ends(D1.inert.node(kids), False{}), Unused.foreign.ends(kids, False{}),
      inert.unused.ends(kids, False{})),
    inert.unused.opens(body, Bool.not(Unused.foreign.ends(kids, False{}))))
  +ea = Equal.trans(List<&2, U32>, ra, Unused.lines(Tree.leaves(kids), fi), rb, inert.unused.lines(kids, fi),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => Unused.lines(Tree.leaves(kids), z), fi, fo, ih))
  Equal.trans(List<&2, U32>, Bool.pick(List<&2, U32>, c1, ra, fi), Bool.pick(List<&2, U32>, c2, ra, fi),
    Bool.pick(List<&2, U32>, c2, rb, fo),
    Equal.cong(Bool, List<&2, U32>, z => Bool.pick(List<&2, U32>, z, ra, fi), c1, c2, ec),
    M2.unused.pick(c2, ra, rb, fi, fo, ea, ih))

# the foreign defs' header lines, the tree read that way, are the ones they were
law inert.unused.foreign:
  for root: Tree.Node
  {Unused.foreign(D1.inert.node(root)) == Unused.foreign(root) : List<&2, U32>}

def inert.unused.foreign(root):
  match root:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{sk, +kids, +body}:
          match sk:
            case Tree.SDef{}: inert.unused.def(kids, body, rest, inert.unused.foreign(rest))
            case Tree.SType{}: inert.unused.foreign(rest)
            case Tree.SLaw{}: inert.unused.foreign(rest)
            case Tree.SImport{}: inert.unused.foreign(rest)
            case Tree.SCase{}: inert.unused.foreign(rest)
            case Tree.SFor{}: inert.unused.foreign(rest)
            case Tree.SLet{}: inert.unused.foreign(rest)
            case Tree.STerm{}: inert.unused.foreign(rest)
        case Tree.Leaf{x}: inert.unused.foreign(rest)
        case Tree.Group{x, y, z}: inert.unused.foreign(rest)
        case Tree.NNil{}: inert.unused.foreign(rest)
        case Tree.NCons{x, y}: inert.unused.foreign(rest)
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# does a binder of this kind count, its note read as unused reads it
def inert.unused.rep(kk: Bind.BindKind, +note: String, +line: U32, +fl: List<&2, U32>) -> Bool:
  match kk:
    case Bind.KLocal{}:
      True{}
    case Bind.KParam{}:
      Bool.and(Bool.not(String.starts_with(note, "-")), Bool.not(List.contains(~U32, ~U32.is_eq, fl, line)))
    case other:
      False{}

# unused over binders as it reads them
def inert.unused.go(
  binds: List<&2, Bind.Bind>,
  +hh: Unused.Hits,
  +uses: List<&2, Bind.Use>,
  +fl: List<&2, U32>,
  +path: String
) -> List<&2, F.Finding>:
  match binds:
    case Nil{}:
      Nil{}
    case Con{Bind.Bind{+name, +line, +col, +kind, +note}, rest}:
      +more = inert.unused.go(rest, hh, uses, fl, path)
      +hit = Bool.and(inert.unused.rep(kind, note, line, fl), Bool.not(String.starts_with(name, "_")))
      Bool.pick(List<&2, F.Finding>, Lazy.and_then(hit, _u => Bool.not(Unused.seen(hh, uses, line, col))),
        F.Finding{path, line, col, U32.from_nat(String.length(name)), "unused",
          Unused.what(kind) ++ " " ++ name ++ " is never used."} <> more, more)

# a leading `-`, kept as unused reads a note
law inert.unused.dash:
  for s: Bool
  {String.starts_with(Bool.pick(String, s, "-", ""), "-") == s : Bool}

def inert.unused.dash(s):
  match s:
    case True{}: {==}
    case False{}: {==}

# a binder kept as unused reads it
law inert.unused.one:
  for kind: Bind.BindKind
  for +note: String
  for +line: U32
  for +fl: List<&2, U32>
  {Unused.reportable(kind, note, line, fl) == inert.unused.rep(kind, Bool.pick(String, String.starts_with(note, "-"),
    "-", ""), line, fl) : Bool}

def inert.unused.one(kind, note, line, fl):
  match kind:
    case Bind.KParam{}:
      %Equal.sym(Bool, String.starts_with(Bool.pick(String, String.starts_with(note, "-"), "-", ""), "-"),
        String.starts_with(note, "-"), inert.unused.dash(String.starts_with(note, "-"))) :
        {Bool.and(Bool.not(String.starts_with(note, "-")),
        Bool.not(List.contains(~U32, ~U32.is_eq, fl, line))) == Bool.and(Bool.not(_), Bool.not(List.contains(~U32,
          ~U32.is_eq, fl, line))) : Bool}
      {==}
    case Bind.KItem{}: {==}
    case Bind.KCtor{}: {==}
    case Bind.KTypeParam{}: {==}
    case Bind.KField{}: {==}
    case Bind.KLocal{}: {==}
    case Bind.KPat{}: {==}
    case Bind.KFor{}: {==}
    case Bind.KTypeVar{}: {==}

# unused over binders is unused over the binders as it reads them
law inert.unused.via:
  for binds: List<&2, Bind.Bind>
  for +hh: Unused.Hits
  for +uses: List<&2, Bind.Use>
  for +fl: List<&2, U32>
  for +path: String
  {Unused.check.go(binds, hh, uses, fl, path) == inert.unused.go(Laws.inert.ubinds(binds), hh, uses, fl, path)
    : List<&2, F.Finding>}

def inert.unused.via(binds, hh, uses, fl, path):
  match binds:
    case Nil{}: {==}
    case Con{Bind.Bind{+name, +line, +col, +kind, +note}, +rest}:
      +mo = Unused.check.go(rest, hh, uses, fl, path)
      +x = {F.Finding{path, line, col, U32.from_nat(String.length(name)), "unused",
        Unused.what(kind) ++ " " ++ name ++ " is never used."} : F.Finding}
      +lhs = Unused.check.go(Con{Bind.Bind{name, line, col, kind, note}, rest}, hh, uses, fl, path)
      %inert.unused.via(rest, hh, uses, fl, path) : {lhs == Bool.pick(List<&2, F.Finding>, Lazy.and_then(Bool.and(
        inert.unused.rep(kind, Bool.pick(String, String.starts_with(note, "-"), "-", ""), line, fl),
          Bool.not(String.starts_with(name, "_"))), _u => Bool.not(Unused.seen(hh, uses, line, col))), x <> _, _)
          : List<&2, F.Finding>}
      %inert.unused.one(kind, note, line, fl) : {lhs == Bool.pick(List<&2, F.Finding>, Lazy.and_then(Bool.and(_,
        Bool.not(String.starts_with(name, "_"))), _u => Bool.not(Unused.seen(hh, uses, line, col))), x <> mo, mo)
          : List<&2, F.Finding>}
      {==}

# unused over binders and lines that read alike
law inert.unused.cong:
  for -x1: List<&2, Bind.Bind>
  for -x2: List<&2, Bind.Bind>
  for -f1: List<&2, U32>
  for -f2: List<&2, U32>
  for +hh: Unused.Hits
  for +uses: List<&2, Bind.Use>
  for +path: String
  for e1: {x1 == x2 : List<&2, Bind.Bind>}
  for e2: {f1 == f2 : List<&2, U32>}
  {inert.unused.go(x1, hh, uses, f1, path) == inert.unused.go(x2, hh, uses, f2, path) : List<&2, F.Finding>}

def inert.unused.cong(x1, _x2, f1, f2, hh, uses, path, e1, e2):
  %e1 : {inert.unused.go(x1, hh, uses, f1, path) == inert.unused.go(_, hh, uses, f2, path) : List<&2, F.Finding>}
  %e2 : {inert.unused.go(x1, hh, uses, f1, path) == inert.unused.go(x1, hh, uses, _, path) : List<&2, F.Finding>}
  {==}

def Laws.inert_unused(
  path,
  _text,
  _toks,
  tree,
  binds,
  uses,
  _scopes,
  _items,
  _text2,
  _toks2,
  tree2,
  binds2,
  _scopes2,
  _items2,
  et,
  eb
):
  +f1 = Unused.foreign(tree)
  +f2 = Unused.foreign(tree2)
  +ef = Equal.trans(List<&2, U32>, f1, Unused.foreign(D1.inert.node(tree)), f2,
    Equal.sym(List<&2, U32>, Unused.foreign(D1.inert.node(tree)), f1, inert.unused.foreign(tree)),
    Equal.trans(List<&2, U32>, Unused.foreign(D1.inert.node(tree)), Unused.foreign(D1.inert.node(tree2)), f2,
      Equal.cong(Tree.Node, List<&2, U32>, z => Unused.foreign(z), D1.inert.node(tree), D1.inert.node(tree2), et),
      inert.unused.foreign(tree2)))
  +hh = Unused.index(uses)
  Equal.trans(List<&2, F.Finding>, Unused.check.go(binds, hh, uses, f1, path),
    inert.unused.go(Laws.inert.ubinds(binds), hh, uses, f1, path), Unused.check.go(binds2, hh, uses, f2, path),
    inert.unused.via(binds, hh, uses, f1, path),
    Equal.trans(List<&2, F.Finding>, inert.unused.go(Laws.inert.ubinds(binds), hh, uses, f1, path),
      inert.unused.go(Laws.inert.ubinds(binds2), hh, uses, f2, path), Unused.check.go(binds2, hh, uses, f2, path),
      inert.unused.cong(Laws.inert.ubinds(binds), Laws.inert.ubinds(binds2), f1, f2, hh, uses, path, eb, ef),
      Equal.sym(List<&2, F.Finding>, Unused.check.go(binds2, hh, uses, f2, path),
        inert.unused.go(Laws.inert.ubinds(binds2), hh, uses, f2, path), inert.unused.via(binds2, hh, uses, f2, path))))

# Inert text, hoist (laws/CodeRulesIgnoreCommentsAndStrings.bend): a def's self-calls, its carried
# parameters, the tables it builds and the names it indexes, each read the
# way the lemmas above read a tree.

# hoist
# -----

# self-calls' argument lists, each argument read that way
def inert.hoist.css(cs: List<&2, List<&2, Tree.Node>>) -> List<&2, List<&2, Tree.Node>>:
  match cs:
    case Nil{}: Nil{}
    case Con{h, t}: inert.nodes(h) <> inert.hoist.css(t)

# argument lists appended, then read that way, are each read that way, appended
law inert.hoist.css_app:
  for a: List<&2, List<&2, Tree.Node>>
  for +b: List<&2, List<&2, Tree.Node>>
  {inert.hoist.css(List.append(&2, List<&2, Tree.Node>, a, b)) == List.append(&2, List<&2, Tree.Node>,
    inert.hoist.css(a), inert.hoist.css(b)) : List<&2, List<&2, Tree.Node>>}

def inert.hoist.css_app(a, b):
  match a:
    case Nil{}: {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, List<&2, Tree.Node>>, List<&2, List<&2, Tree.Node>>, z => inert.nodes(h) <> z,
        inert.hoist.css(List.append(&2, List<&2, Tree.Node>, t, b)),
        List.append(&2, List<&2, Tree.Node>, inert.hoist.css(t), inert.hoist.css(b)), inert.hoist.css_app(t, b))

# two runs of argument lists joined, each read that way, are the join read that way
law inert.hoist.cat2:
  for +a: List<&2, List<&2, Tree.Node>>
  for +b: List<&2, List<&2, Tree.Node>>
  {List.concat(&2, List<&2, Tree.Node>, [inert.hoist.css(a), inert.hoist.css(b)]) == inert.hoist.css(List.concat(&2,
    List<&2, Tree.Node>, [a, b]))
    : List<&2, List<&2, Tree.Node>>}

def inert.hoist.cat2(a, b):
  +lhs = List.concat(&2, List<&2, Tree.Node>, [inert.hoist.css(a), inert.hoist.css(b)])
  %Equal.sym(List<&2, List<&2, Tree.Node>>, inert.hoist.css(List.append(&2, List<&2, Tree.Node>, a, List.append(&2,
    List<&2, Tree.Node>, b, []))),
    List.append(&2, List<&2, Tree.Node>, inert.hoist.css(a), inert.hoist.css(List.append(&2, List<&2, Tree.Node>, b,
      []))),
    inert.hoist.css_app(a, List.append(&2, List<&2, Tree.Node>, b, []))) : {lhs == _ : List<&2, List<&2, Tree.Node>>}
  %Equal.sym(List<&2, List<&2, Tree.Node>>, inert.hoist.css(List.append(&2, List<&2, Tree.Node>, b, [])),
    List.append(&2, List<&2, Tree.Node>, inert.hoist.css(b),
    inert.hoist.css([])), inert.hoist.css_app(b, [])) : {lhs == List.append(&2, List<&2, Tree.Node>,
      inert.hoist.css(a), _) : List<&2, List<&2, Tree.Node>>}
  {==}

# three runs of argument lists joined, each read that way, are the join read that way
law inert.hoist.cat3:
  for +a: List<&2, List<&2, Tree.Node>>
  for +b: List<&2, List<&2, Tree.Node>>
  for +c: List<&2, List<&2, Tree.Node>>
  {List.concat(&2, List<&2, Tree.Node>, [inert.hoist.css(a), inert.hoist.css(b), inert.hoist.css(c)])
    == inert.hoist.css(List.concat(&2, List<&2, Tree.Node>, [a, b, c])) : List<&2, List<&2, Tree.Node>>}

def inert.hoist.cat3(a, b, c):
  +lhs = List.concat(&2, List<&2, Tree.Node>, [inert.hoist.css(a), inert.hoist.css(b), inert.hoist.css(c)])
  +bc = List.append(&2, List<&2, Tree.Node>, b, List.append(&2, List<&2, Tree.Node>, c, []))
  %Equal.sym(List<&2, List<&2, Tree.Node>>, inert.hoist.css(List.append(&2, List<&2, Tree.Node>, a, bc)),
    List.append(&2, List<&2, Tree.Node>, inert.hoist.css(a), inert.hoist.css(bc)),
    inert.hoist.css_app(a, bc)) : {lhs == _ : List<&2, List<&2, Tree.Node>>}
  %Equal.sym(List<&2, List<&2, Tree.Node>>, inert.hoist.css(bc), List.append(&2, List<&2, Tree.Node>,
    inert.hoist.css(b),
    inert.hoist.css(List.append(&2, List<&2, Tree.Node>, c, []))), inert.hoist.css_app(b, List.append(&2, List<&2,
      Tree.Node>, c, []))) :
    {lhs == List.append(&2, List<&2, Tree.Node>, inert.hoist.css(a), _) : List<&2, List<&2, Tree.Node>>}
  %Equal.sym(List<&2, List<&2, Tree.Node>>, inert.hoist.css(List.append(&2, List<&2, Tree.Node>, c, [])),
    List.append(&2, List<&2, Tree.Node>, inert.hoist.css(c),
    inert.hoist.css([])), inert.hoist.css_app(c, [])) :
    {lhs == List.append(&2, List<&2, Tree.Node>, inert.hoist.css(a), List.append(&2, List<&2, Tree.Node>,
      inert.hoist.css(b), _)) : List<&2, List<&2, Tree.Node>>}
  {==}

# a self-call picked onto the rest, each read that way
law inert.hoist.pick:
  for me: Bool
  for +as: List<&2, Tree.Node>
  for +more: List<&2, List<&2, Tree.Node>>
  {Bool.pick(List<&2, List<&2, Tree.Node>>, me, inert.nodes(as) <> inert.hoist.css(more), inert.hoist.css(more))
    == inert.hoist.css(Bool.pick(List<&2, List<&2, Tree.Node>>, me, as <> more, more)) : List<&2, List<&2, Tree.Node>>}

def inert.hoist.pick(me, _as, _more):
  match me:
    case True{}: {==}
    case False{}: {==}

# two runs that read as others read that way join as their join does
law inert.hoist.pcat2:
  for -x1: List<&2, List<&2, Tree.Node>>
  for +x2: List<&2, List<&2, Tree.Node>>
  for -y1: List<&2, List<&2, Tree.Node>>
  for +y2: List<&2, List<&2, Tree.Node>>
  for ix: {x1 == inert.hoist.css(x2) : List<&2, List<&2, Tree.Node>>}
  for iy: {y1 == inert.hoist.css(y2) : List<&2, List<&2, Tree.Node>>}
  {List.concat(&2, List<&2, Tree.Node>, [x1, y1]) == inert.hoist.css(List.concat(&2, List<&2, Tree.Node>, [x2,
    y2])) : List<&2, List<&2, Tree.Node>>}

def inert.hoist.pcat2(x1, x2, y1, y2, ix, iy):
  %Equal.sym(List<&2, List<&2, Tree.Node>>, x1, inert.hoist.css(x2), ix) :
    {List.concat(&2, List<&2, Tree.Node>, [_, y1]) == inert.hoist.css(List.concat(&2, List<&2, Tree.Node>, [x2,
      y2])) : List<&2, List<&2, Tree.Node>>}
  %Equal.sym(List<&2, List<&2, Tree.Node>>, y1, inert.hoist.css(y2), iy) :
    {List.concat(&2, List<&2, Tree.Node>, [inert.hoist.css(x2), _]) == inert.hoist.css(List.concat(&2, List<&2,
      Tree.Node>, [x2, y2])) : List<&2, List<&2, Tree.Node>>}
  inert.hoist.cat2(x2, y2)

# three runs that read as others read that way join as their join does
law inert.hoist.pcat3:
  for -x1: List<&2, List<&2, Tree.Node>>
  for +x2: List<&2, List<&2, Tree.Node>>
  for -y1: List<&2, List<&2, Tree.Node>>
  for +y2: List<&2, List<&2, Tree.Node>>
  for -z1: List<&2, List<&2, Tree.Node>>
  for +z2: List<&2, List<&2, Tree.Node>>
  for ix: {x1 == inert.hoist.css(x2) : List<&2, List<&2, Tree.Node>>}
  for iy: {y1 == inert.hoist.css(y2) : List<&2, List<&2, Tree.Node>>}
  for iz: {z1 == inert.hoist.css(z2) : List<&2, List<&2, Tree.Node>>}
  {List.concat(&2, List<&2, Tree.Node>, [x1, y1, z1]) == inert.hoist.css(List.concat(&2, List<&2, Tree.Node>, [x2, y2,
    z2])) : List<&2, List<&2, Tree.Node>>}

def inert.hoist.pcat3(x1, x2, y1, y2, z1, z2, ix, iy, iz):
  +rhs = inert.hoist.css(List.concat(&2, List<&2, Tree.Node>, [x2, y2, z2]))
  %Equal.sym(List<&2, List<&2, Tree.Node>>, x1, inert.hoist.css(x2), ix) : {List.concat(&2, List<&2, Tree.Node>, [_,
    y1, z1]) == rhs : List<&2, List<&2, Tree.Node>>}
  %Equal.sym(List<&2, List<&2, Tree.Node>>, y1, inert.hoist.css(y2), iy) : {List.concat(&2, List<&2, Tree.Node>,
    [inert.hoist.css(x2), _, z1]) == rhs : List<&2, List<&2, Tree.Node>>}
  %Equal.sym(List<&2, List<&2, Tree.Node>>, z1, inert.hoist.css(z2), iz) :
    {List.concat(&2, List<&2, Tree.Node>, [inert.hoist.css(x2), inert.hoist.css(y2), _]) == rhs : List<&2, List<&2,
      Tree.Node>>}
  inert.hoist.cat3(x2, y2, z2)

# a name then a group, both read that way: a self-call as it was, and the
# calls under the group and after it read that way
law inert.hoist.pushes_lg:
  for +b: Bool
  for +t: String
  for +o: String
  for +self: String
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +es: {D1.inert.marked(self) == False{} : Bool}
  for ik: {Hoist.pushes(D1.inert.node(kids), self) == inert.hoist.css(Hoist.pushes(kids, self)) : List<&2, List<&2,
    Tree.Node>>}
  for ir: {Hoist.pushes(D1.inert.node(r2), self) == inert.hoist.css(Hoist.pushes(r2, self)) : List<&2, List<&2,
    Tree.Node>>}
  {Bool.pick(List<&2, List<&2, Tree.Node>>, Bool.and(String.eq(o, "("), String.eq(D1.inert.keep(b, t), self)),
    Calls.args(D1.inert.node(kids)) <> List.concat(&2, List<&2, Tree.Node>, [Hoist.pushes(D1.inert.node(kids),
      self), Hoist.pushes(D1.inert.node(r2), self)]),
    List.concat(&2, List<&2, Tree.Node>, [Hoist.pushes(D1.inert.node(kids), self), Hoist.pushes(D1.inert.node(r2),
      self)]))
    == inert.hoist.css(Bool.pick(List<&2, List<&2, Tree.Node>>, Bool.and(String.eq(o, "("), String.eq(t, self)),
      Calls.args(kids) <> List.concat(&2, List<&2, Tree.Node>, [Hoist.pushes(kids, self), Hoist.pushes(r2, self)]),
      List.concat(&2, List<&2, Tree.Node>, [Hoist.pushes(kids, self), Hoist.pushes(r2, self)]))) : List<&2, List<&2,
        Tree.Node>>}

def inert.hoist.pushes_lg(b, t, o, self, kids, r2, ef, es, ik, ir):
  +m = List.concat(&2, List<&2, Tree.Node>, [Hoist.pushes(kids, self), Hoist.pushes(r2, self)])
  +im = List.concat(&2, List<&2, Tree.Node>, [Hoist.pushes(D1.inert.node(kids), self),
    Hoist.pushes(D1.inert.node(r2), self)])
  +rhs = inert.hoist.css(Bool.pick(List<&2, List<&2, Tree.Node>>, Bool.and(String.eq(o, "("), String.eq(t, self)),
    Calls.args(kids) <> m, m))
  %Equal.sym(Bool, String.eq(D1.inert.keep(b, t), self), String.eq(t, self), M1.inert.eq_keep(b, t, self, ef, es)) :
    {Bool.pick(List<&2, List<&2, Tree.Node>>, Bool.and(String.eq(o, "("), _), Calls.args(D1.inert.node(kids)) <> im,
      im) == rhs : List<&2, List<&2, Tree.Node>>}
  %Equal.sym(List<&2, List<&2, Tree.Node>>, im, inert.hoist.css(m),
    inert.hoist.pcat2(Hoist.pushes(D1.inert.node(kids), self), Hoist.pushes(kids, self),
    Hoist.pushes(D1.inert.node(r2), self), Hoist.pushes(r2, self), ik, ir)) :
    {Bool.pick(List<&2, List<&2, Tree.Node>>, Bool.and(String.eq(o, "("), String.eq(t, self)),
      Calls.args(D1.inert.node(kids)) <> _, _) == rhs : List<&2, List<&2, Tree.Node>>}
  %Equal.sym(List<&2, Tree.Node>, Calls.args(D1.inert.node(kids)), inert.nodes(Calls.args(kids)), inert.args(kids)) :
    {Bool.pick(List<&2, List<&2, Tree.Node>>, Bool.and(String.eq(o, "("), String.eq(t, self)),
      _ <> inert.hoist.css(m), inert.hoist.css(m))
      == rhs : List<&2, List<&2, Tree.Node>>}
  inert.hoist.pick(Bool.and(String.eq(o, "("), String.eq(t, self)), Calls.args(kids), m)

# the self-calls under a node read that way are its self-calls, each argument
# read that way: a string is never the def's name
law inert.hoist.pushes:
  for nn: Tree.Node
  for +self: String
  for +es: {D1.inert.marked(self) == False{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Hoist.pushes(D1.inert.node(nn), self) == inert.hoist.css(Hoist.pushes(nn, self)) : List<&2, List<&2, Tree.Node>>}

def inert.hoist.pushes(nn, self, es, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{go, +kids, +gcl}:
                      match go:
                        case Lex.Tok{+gk, +o, +gl, +gc}:
                          +lf = {Tree.Leaf{Lex.Tok{k, t, l, c}} : Tree.Node}
                          +gp = {Tree.Group{Lex.Tok{gk, o, gl, gc}, kids, gcl} : Tree.Node}
                          +eg = inert.ok_t(lf, Tree.NCons{gp, r2}, e)
                          inert.hoist.pushes_lg(D1.inert.blanks(k), t, o, self, kids, r2,
                            inert.ok_h(lf, Tree.NCons{gp, r2}, e), es,
                            inert.hoist.pushes(kids, self, es, inert.ok_h(gp, r2, eg)),
                            inert.hoist.pushes(r2, self, es, inert.ok_t(gp, r2, eg)))
                    case Tree.Leaf{x}:
                      inert.hoist.pushes(rest, self, es, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.Stmt{x, y, z}:
                      inert.hoist.pushes(rest, self, es, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NNil{}:
                      inert.hoist.pushes(rest, self, es, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NCons{x, y}:
                      inert.hoist.pushes(rest, self, es, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Leaf{x}:
                  inert.hoist.pushes(rest, self, es, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Group{x, y, z}:
                  inert.hoist.pushes(rest, self, es, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Stmt{x, y, z}:
                  inert.hoist.pushes(rest, self, es, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.NNil{}:
                  inert.hoist.pushes(rest, self, es, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
        case Tree.Group{+o, +kids, +cl}:
          inert.hoist.pcat2(Hoist.pushes(D1.inert.node(kids), self), Hoist.pushes(kids, self),
            Hoist.pushes(D1.inert.node(rest), self),
            Hoist.pushes(rest, self), inert.hoist.pushes(kids, self, es, inert.ok_h(Tree.Group{o, kids, cl}, rest, e)),
            inert.hoist.pushes(rest, self, es, inert.ok_t(Tree.Group{o, kids, cl}, rest, e)))
        case Tree.Stmt{+sk, +kids, +body}:
          +es2 = inert.ok_h(Tree.Stmt{sk, kids, body}, rest, e)
          inert.hoist.pcat3(Hoist.pushes(D1.inert.node(kids), self), Hoist.pushes(kids, self),
            Hoist.pushes(D1.inert.node(body), self),
            Hoist.pushes(body, self), Hoist.pushes(D1.inert.node(rest), self), Hoist.pushes(rest, self),
            inert.hoist.pushes(kids, self, es, M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)),
            inert.hoist.pushes(body, self, es, M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)),
            inert.hoist.pushes(rest, self, es, inert.ok_t(Tree.Stmt{sk, kids, body}, rest, e)))
        case Tree.NNil{}: inert.hoist.pushes(rest, self, es, e)
        case Tree.NCons{x, y}: inert.hoist.pushes(rest, self, es, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a chain read that way is exactly the name as it was: only a name's text is read
law inert.hoist.lone_eq:
  for nn: Tree.Node
  for +name: String
  {Hoist.lone_eq(D1.inert.node(nn), name) == Hoist.lone_eq(nn, name) : Bool}

def inert.hoist.lone_eq(nn, _name):
  match nn:
    case Tree.NCons{h, r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}:
                  match r:
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                    case Tree.NCons{x, y}: {==}
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
        case Tree.Group{x, y, z}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# every self-call, its arguments read that way, passes the name at the
# argument as it did
law inert.hoist.all_same:
  for cs: List<&2, List<&2, Tree.Node>>
  for +ii: Nat
  for +name: String
  {Hoist.all_same(inert.hoist.css(cs), ii, name) == Hoist.all_same(cs, ii, name) : Bool}

def inert.hoist.all_same(cs, ii, name):
  match cs:
    case Nil{}: {==}
    case Con{+as, +rest}:
      +lhs = Hoist.all_same(inert.hoist.css(Con{as, rest}), ii, name)
      %inert.hoist.all_same(rest, ii, name) :
        {lhs == Bool.and(Hoist.lone_eq(Calls.arg(as, ii), name), _) : Bool}
      %inert.hoist.lone_eq(Calls.arg(as, ii), name) :
        {lhs == Bool.and(_, Hoist.all_same(inert.hoist.css(rest), ii, name)) : Bool}
      %inert.arg(as, ii) :
        {lhs == Bool.and(Hoist.lone_eq(_, name), Hoist.all_same(inert.hoist.css(rest), ii, name)) : Bool}
      {==}

# the parameters every self-call passes unchanged, parameters and calls read
# that way
law inert.hoist.carried.go:
  for ps: List<&2, Tree.Node>
  for +cs: List<&2, List<&2, Tree.Node>>
  for +ii: Nat
  for +acc: List<&2, String>
  {Hoist.carried.go(inert.nodes(ps), inert.hoist.css(cs), ii, acc) == Hoist.carried.go(ps, cs, ii, acc) : List<&2,
    String>}

def inert.hoist.carried.go(ps, cs, ii, acc):
  match ps:
    case Nil{}: {==}
    case Con{+p, +rest}:
      +nm = Calls.param_name(p)
      +lhs = Hoist.carried.go(inert.nodes(Con{p, rest}), inert.hoist.css(cs), ii, acc)
      %inert.hoist.all_same(cs, ii, nm) :
        {lhs == Hoist.carried.go(rest, cs, (ii + 1n : Nat), Bool.pick(List<&2, String>,
          Bool.and(Bool.not(String.is_empty(nm)),
          _), nm <> acc, acc)) : List<&2, String>}
      %inert.hoist.carried.go(rest, cs, (ii + 1n : Nat),
          Bool.pick(List<&2, String>, Bool.and(Bool.not(String.is_empty(nm)), Hoist.all_same(inert.hoist.css(cs), ii,
            nm)),
            nm <> acc, acc)) :
        {lhs == _ : List<&2, String>}
      %Equal.sym(String, Calls.param_name(D1.inert.node(p)), nm, inert.param_name(p)) :
        {Hoist.carried.go(inert.nodes(rest), inert.hoist.css(cs), (ii + 1n : Nat),
          Bool.pick(List<&2, String>, Bool.and(Bool.not(String.is_empty(_)), Hoist.all_same(inert.hoist.css(cs), ii,
            _)),
            _ <> acc, acc))
          == Hoist.carried.go(inert.nodes(rest), inert.hoist.css(cs), (ii + 1n : Nat),
            Bool.pick(List<&2, String>, Bool.and(Bool.not(String.is_empty(nm)), Hoist.all_same(inert.hoist.css(cs),
              ii, nm)),
              nm <> acc, acc)) : List<&2, String>}
      {==}

# parameters passed through unchanged, calls and signature read that way
law inert.hoist.carried_of:
  for cs: List<&2, List<&2, Tree.Node>>
  for +sig: Tree.Node
  {Hoist.carried_of(inert.hoist.css(cs), D1.inert.node(sig)) == Hoist.carried_of(cs, sig) : List<&2, String>}

def inert.hoist.carried_of(cs, sig):
  match cs:
    case Nil{}: {==}
    case Con{+h, +t}:
      +rhs = Hoist.carried_of(Con{h, t}, sig)
      %Equal.sym(Tree.Node, Calls.params.of(D1.inert.node(sig)), D1.inert.node(Calls.params.of(sig)),
        inert.params.of(sig)) :
        {Hoist.carried.go(Calls.args(_), inert.hoist.css(h <> t), 0n, []) == rhs : List<&2, String>}
      %Equal.sym(List<&2, Tree.Node>, Calls.args(D1.inert.node(Calls.params.of(sig))), inert.nodes(Calls.params(sig)),
        inert.args(Calls.params.of(sig))) :
        {Hoist.carried.go(_, inert.hoist.css(h <> t), 0n, []) == rhs : List<&2, String>}
      inert.hoist.carried.go(Calls.params(sig), h <> t, 0n, [])

# the parameters a def carries, its signature and body read that way
law inert.hoist.carried:
  for +sig: Tree.Node
  for +body: Tree.Node
  for +self: String
  for +es: {D1.inert.marked(self) == False{} : Bool}
  for +eb: {D1.inert.ok(body) == True{} : Bool}
  {Hoist.carried(D1.inert.node(sig), D1.inert.node(body), self) == Hoist.carried(sig, body, self) : List<&2,
    String>}

def inert.hoist.carried(sig, body, self, es, eb):
  %Equal.sym(List<&2, List<&2, Tree.Node>>, Hoist.pushes(D1.inert.node(body), self),
    inert.hoist.css(Hoist.pushes(body, self)),
    inert.hoist.pushes(body, self, es, eb)) : {Hoist.carried_of(_, D1.inert.node(sig)) == Hoist.carried(sig, body,
      self) : List<&2, String>}
  inert.hoist.carried_of(Hoist.pushes(body, self), sig)

# two ands whose sides read alike read alike
law inert.hoist.and2:
  for -a1: Bool
  for -a2: Bool
  for -b1: Bool
  for -b2: Bool
  for ea: {a1 == a2 : Bool}
  for eb: {b1 == b2 : Bool}
  {Bool.and(a1, b1) == Bool.and(a2, b2) : Bool}

def inert.hoist.and2(a1, _a2, b1, b2, ea, eb):
  %ea : {Bool.and(a1, b1) == Bool.and(_, b2) : Bool}
  %eb : {Bool.and(a1, b1) == Bool.and(a1, _) : Bool}
  {==}

# two ors whose sides read alike read alike
law inert.hoist.or2:
  for -a1: Bool
  for -a2: Bool
  for -b1: Bool
  for -b2: Bool
  for ea: {a1 == a2 : Bool}
  for eb: {b1 == b2 : Bool}
  {Bool.or(a1, b1) == Bool.or(a2, b2) : Bool}

def inert.hoist.or2(a1, _a2, b1, b2, ea, eb):
  %ea : {Bool.or(a1, b1) == Bool.or(_, b2) : Bool}
  %eb : {Bool.or(a1, b1) == Bool.or(a1, _) : Bool}
  {==}

# a token read that way names a carried parameter as it did: only a name's
# text is read
law inert.hoist.name_ok:
  for k: Lex.TokKind
  for +t: String
  for +carried: List<&2, String>
  {Hoist.name_ok(k, D1.inert.keep(D1.inert.blanks(k), t), carried) == Hoist.name_ok(k, t, carried) : Bool}

def inert.hoist.name_ok(k, _t, _carried):
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

# a token after an operator, read that way, is closed as it was
law inert.hoist.leaf_ok:
  for skip: Bool
  for tok: Lex.Tok
  for +carried: List<&2, String>
  {Hoist.leaf_ok(skip, D1.inert.tok(tok), carried) == Hoist.leaf_ok(skip, tok, carried) : Bool}

def inert.hoist.leaf_ok(skip, tok, carried):
  match skip:
    case True{}: {==}
    case False{}:
      match tok:
        case Lex.Tok{k, +t, l, c}: inert.hoist.name_ok(k, t, carried)

# a token before a group, read that way, is closed as it was
law inert.hoist.value_ok:
  for app: Bool
  for k: Lex.TokKind
  for +t: String
  for +carried: List<&2, String>
  {Hoist.value_ok(app, k, D1.inert.keep(D1.inert.blanks(k), t), carried) == Hoist.value_ok(app, k, t, carried)
    : Bool}

def inert.hoist.value_ok(app, k, t, carried):
  match app:
    case True{}: {==}
    case False{}: inert.hoist.name_ok(k, t, carried)

# a token then a group, read that way: closed as it was, the group and the
# rest too
law inert.hoist.closed_lg:
  for k: Lex.TokKind
  for +t: String
  for +o: String
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +carried: List<&2, String>
  for ik: {Hoist.closed(D1.inert.node(kids), carried) == Hoist.closed(kids, carried) : Bool}
  for ir: {Hoist.closed(D1.inert.node(r2), carried) == Hoist.closed(r2, carried) : Bool}
  {Bool.and(Hoist.value_ok(String.eq(o, "("), k, D1.inert.keep(D1.inert.blanks(k), t), carried),
    Bool.and(Hoist.closed(D1.inert.node(kids), carried), Hoist.closed(D1.inert.node(r2), carried)))
    == Bool.and(Hoist.value_ok(String.eq(o, "("), k, t, carried), Bool.and(Hoist.closed(kids, carried),
      Hoist.closed(r2, carried))) : Bool}

def inert.hoist.closed_lg(k, t, o, kids, r2, carried, ik, ir):
  inert.hoist.and2(Hoist.value_ok(String.eq(o, "("), k, D1.inert.keep(D1.inert.blanks(k), t), carried),
    Hoist.value_ok(String.eq(o, "("), k, t, carried), Bool.and(Hoist.closed(D1.inert.node(kids), carried),
      Hoist.closed(D1.inert.node(r2), carried)), Bool.and(Hoist.closed(kids, carried), Hoist.closed(r2, carried)),
    inert.hoist.value_ok(String.eq(o, "("), k, t, carried),
    inert.hoist.and2(Hoist.closed(D1.inert.node(kids), carried), Hoist.closed(kids, carried),
      Hoist.closed(D1.inert.node(r2), carried),
      Hoist.closed(r2, carried), ik, ir))

# a chain read that way is closed over the carried parameters as it was: a
# string is never a value name
law inert.hoist.closed:
  for nn: Tree.Node
  for +carried: List<&2, String>
  {Hoist.closed(D1.inert.node(nn), carried) == Hoist.closed(nn, carried) : Bool}

def inert.hoist.closed(nn, carried):
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
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TName{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}:
                          Equal.cong(Bool, Bool, z => Bool.and(List.contains(~String, ~String.eq, carried, t), z),
                            Hoist.closed(D1.inert.node(rest), carried), Hoist.closed(rest, carried),
                            inert.hoist.closed(rest, carried))
                        case Tree.Stmt{x, y, z}:
                          Equal.cong(Bool, Bool, z => Bool.and(List.contains(~String, ~String.eq, carried, t), z),
                            Hoist.closed(D1.inert.node(rest), carried), Hoist.closed(rest, carried),
                            inert.hoist.closed(rest, carried))
                        case Tree.NNil{}:
                          Equal.cong(Bool, Bool, z => Bool.and(List.contains(~String, ~String.eq, carried, t), z),
                            Hoist.closed(D1.inert.node(rest), carried), Hoist.closed(rest, carried),
                            inert.hoist.closed(rest, carried))
                        case Tree.NCons{x, y}:
                          Equal.cong(Bool, Bool, z => Bool.and(List.contains(~String, ~String.eq, carried, t), z),
                            Hoist.closed(D1.inert.node(rest), carried), Hoist.closed(rest, carried),
                            inert.hoist.closed(rest, carried))
                    case Tree.Leaf{x}:
                      Equal.cong(Bool, Bool, z => Bool.and(List.contains(~String, ~String.eq, carried, t), z),
                        Hoist.closed(D1.inert.node(rest), carried), Hoist.closed(rest, carried),
                        inert.hoist.closed(rest, carried))
                    case Tree.Group{x, y, z}:
                      Equal.cong(Bool, Bool, z => Bool.and(List.contains(~String, ~String.eq, carried, t), z),
                        Hoist.closed(D1.inert.node(rest), carried), Hoist.closed(rest, carried),
                        inert.hoist.closed(rest, carried))
                    case Tree.Stmt{x, y, z}:
                      Equal.cong(Bool, Bool, z => Bool.and(List.contains(~String, ~String.eq, carried, t), z),
                        Hoist.closed(D1.inert.node(rest), carried), Hoist.closed(rest, carried),
                        inert.hoist.closed(rest, carried))
                    case Tree.NNil{}:
                      Equal.cong(Bool, Bool, z => Bool.and(List.contains(~String, ~String.eq, carried, t), z),
                        Hoist.closed(D1.inert.node(rest), carried), Hoist.closed(rest, carried),
                        inert.hoist.closed(rest, carried))
                case Lex.TUpper{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TUpper{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TDotted{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TDotted{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TWild{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TWild{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TKey{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TKey{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TNum{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TNum{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TStr{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TStr{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TChar{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TChar{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TComment{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TComment{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TSpace{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TSpace{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TNewline{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TNewline{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TOp{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}: inert.hoist.closed(rest, carried)
                        case Tree.Leaf{+tok2}:
                          inert.hoist.and2(Hoist.leaf_ok(String.eq(t, "~"), D1.inert.tok(tok2), carried),
                            Hoist.leaf_ok(String.eq(t, "~"), tok2, carried), Hoist.closed(D1.inert.node(r2),
                            carried), Hoist.closed(r2, carried), inert.hoist.leaf_ok(String.eq(t, "~"), tok2,
                            carried), inert.hoist.closed(r2, carried))
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TColon{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TColon{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TEq{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TEq{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TBind{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TBind{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TArrow{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TArrow{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TLam{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TLam{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TAll{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TAll{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TAmp{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TAmp{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TOpen{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TOpen{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TClose{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TClose{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
                case Lex.TComma{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{go, +kids, gcl}:
                          match go:
                            case Lex.Tok{gk, +o, gl, gc}:
                              inert.hoist.closed_lg(Lex.TComma{}, t, o, kids, r2, carried, inert.hoist.closed(kids,
                                carried), inert.hoist.closed(r2, carried))
                        case Tree.Leaf{+tok2}: inert.hoist.closed(rest, carried)
                        case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                        case Tree.NNil{}: inert.hoist.closed(rest, carried)
                        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
                    case Tree.Leaf{x}: inert.hoist.closed(rest, carried)
                    case Tree.Group{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.Stmt{x, y, z}: inert.hoist.closed(rest, carried)
                    case Tree.NNil{}: inert.hoist.closed(rest, carried)
        case Tree.Group{o, +kids, cl}:
          inert.hoist.and2(Hoist.closed(D1.inert.node(kids), carried), Hoist.closed(kids, carried),
            Hoist.closed(D1.inert.node(rest), carried),
            Hoist.closed(rest, carried), inert.hoist.closed(kids, carried), inert.hoist.closed(rest, carried))
        case Tree.Stmt{sk, +kids, +body}:
          inert.hoist.and2(Hoist.closed(D1.inert.node(kids), carried), Hoist.closed(kids, carried),
            Bool.and(Hoist.closed(D1.inert.node(body), carried), Hoist.closed(D1.inert.node(rest), carried)),
            Bool.and(Hoist.closed(body, carried), Hoist.closed(rest, carried)), inert.hoist.closed(kids, carried),
            inert.hoist.and2(Hoist.closed(D1.inert.node(body), carried), Hoist.closed(body, carried),
              Hoist.closed(D1.inert.node(rest), carried), Hoist.closed(rest, carried), inert.hoist.closed(body,
                carried),
              inert.hoist.closed(rest, carried)))
        case Tree.NNil{}: inert.hoist.closed(rest, carried)
        case Tree.NCons{x, y}: inert.hoist.closed(rest, carried)
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}:
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
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a chain read that way holds a top-level token of an unmarked text as it did
law inert.hoist.top_mark:
  for nn: Tree.Node
  for +want: String
  for +ew: {D1.inert.marked(want) == False{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Hoist.top_mark(D1.inert.node(nn), want) == Hoist.top_mark(nn, want) : Bool}

def inert.hoist.top_mark(nn, want, ew, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              inert.or2(String.eq(D1.inert.keep(D1.inert.blanks(k), t), want), String.eq(t, want),
                Hoist.top_mark(D1.inert.node(rest), want), Hoist.top_mark(rest, want),
                M1.inert.eq_keep(D1.inert.blanks(k), t, want, inert.ok_h(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e), ew),
                inert.hoist.top_mark(rest, want, ew, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e)))
        case Tree.Group{o, gk, cl}: inert.hoist.top_mark(rest, want, ew, inert.ok_t(Tree.Group{o, gk, cl}, rest, e))
        case Tree.Stmt{sk, sks, sb}: inert.hoist.top_mark(rest, want, ew, inert.ok_t(Tree.Stmt{sk, sks, sb}, rest, e))
        case Tree.NNil{}: inert.hoist.top_mark(rest, want, ew, e)
        case Tree.NCons{x, y}: inert.hoist.top_mark(rest, want, ew, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a chain read that way holds as many top-level tokens of an unmarked text as
# it did
law inert.hoist.top_count:
  for nn: Tree.Node
  for +want: String
  for +got: Nat
  for +ew: {D1.inert.marked(want) == False{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Hoist.top_count(D1.inert.node(nn), want, got) == Hoist.top_count(nn, want, got) : Nat}

def inert.hoist.top_count(nn, want, got, ew, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              +lf = {Tree.Leaf{Lex.Tok{k, t, l, c}} : Tree.Node}
              +lhs = Hoist.top_count(D1.inert.node(Tree.NCons{lf, rest}), want, got)
              %inert.hoist.top_count(rest, want, Bool.pick(Nat, String.eq(t, want), (got + 1n : Nat), got), ew,
                inert.ok_t(lf, rest, e)) : {lhs == _ : Nat}
              %M1.inert.eq_keep(D1.inert.blanks(k), t, want, inert.ok_h(lf, rest, e), ew) :
                {lhs == Hoist.top_count(D1.inert.node(rest), want, Bool.pick(Nat, _, (got + 1n : Nat), got)) : Nat}
              {==}
        case Tree.Group{o, gk, cl}:
          inert.hoist.top_count(rest, want, got, ew, inert.ok_t(Tree.Group{o, gk, cl}, rest, e))
        case Tree.Stmt{sk, sks, sb}:
          inert.hoist.top_count(rest, want, got, ew, inert.ok_t(Tree.Stmt{sk, sks, sb}, rest, e))
        case Tree.NNil{}: inert.hoist.top_count(rest, want, got, ew, e)
        case Tree.NCons{x, y}: inert.hoist.top_count(rest, want, got, ew, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a bracket's kids read that way are an array as they were
law inert.hoist.is_array:
  for +kids: Tree.Node
  for +e: {D1.inert.ok(kids) == True{} : Bool}
  {Hoist.is_array(D1.inert.node(kids)) == Hoist.is_array(kids) : Bool}

def inert.hoist.is_array(kids, e):
  +lhs = Hoist.is_array(D1.inert.node(kids))
  %inert.hoist.top_mark(kids, ":", {==}, e) :
    {lhs == Bool.and(_, Bool.or(Hoist.top_mark(kids, "*"), Hoist.top_mark(kids, "^"))) : Bool}
  %inert.hoist.top_mark(kids, "*", {==}, e) :
    {lhs == Bool.and(Hoist.top_mark(D1.inert.node(kids), ":"), Bool.or(_, Hoist.top_mark(kids, "^"))) : Bool}
  %inert.hoist.top_mark(kids, "^", {==}, e) :
    {lhs == Bool.and(Hoist.top_mark(D1.inert.node(kids), ":"), Bool.or(Hoist.top_mark(D1.inert.node(kids), "*"),
      _)) : Bool}
  {==}

# a chain read that way is sized small as it was: an operator's and a
# number's text are read, never a string's
law inert.hoist.small_size:
  for nn: Tree.Node
  {Hoist.small_size(D1.inert.node(nn)) == Hoist.small_size(nn) : Bool}

def inert.hoist.small_size(nn):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, op, l, c}:
              match k:
                case Lex.TName{}: inert.hoist.small_size(rest)
                case Lex.TUpper{}: inert.hoist.small_size(rest)
                case Lex.TDotted{}: inert.hoist.small_size(rest)
                case Lex.TWild{}: inert.hoist.small_size(rest)
                case Lex.TKey{}: inert.hoist.small_size(rest)
                case Lex.TNum{}: inert.hoist.small_size(rest)
                case Lex.TStr{}: inert.hoist.small_size(rest)
                case Lex.TChar{}: inert.hoist.small_size(rest)
                case Lex.TComment{}: inert.hoist.small_size(rest)
                case Lex.TSpace{}: inert.hoist.small_size(rest)
                case Lex.TNewline{}: inert.hoist.small_size(rest)
                case Lex.TOp{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Leaf{tok2}:
                          match tok2:
                            case Lex.Tok{k2, t2, l2, c2}:
                              match k2:
                                case Lex.TName{}: inert.hoist.small_size(rest)
                                case Lex.TUpper{}: inert.hoist.small_size(rest)
                                case Lex.TDotted{}: inert.hoist.small_size(rest)
                                case Lex.TWild{}: inert.hoist.small_size(rest)
                                case Lex.TKey{}: inert.hoist.small_size(rest)
                                case Lex.TNum{}:
                                  Equal.cong(Bool, Bool, z => Bool.or(Bool.or(Bool.and(String.eq(op, "*"),
                                    Hoist.small_num(t2)), Bool.and(String.eq(op, "^"), List.contains(~String,
                                    ~String.eq, ["0", "1", "2", "3", "0n", "1n", "2n", "3n"], t2))), z),
                                    Hoist.small_size(D1.inert.node(r2)), Hoist.small_size(r2),
                                    inert.hoist.small_size(r2))
                                case Lex.TStr{}: inert.hoist.small_size(rest)
                                case Lex.TChar{}: inert.hoist.small_size(rest)
                                case Lex.TComment{}: inert.hoist.small_size(rest)
                                case Lex.TSpace{}: inert.hoist.small_size(rest)
                                case Lex.TNewline{}: inert.hoist.small_size(rest)
                                case Lex.TOp{}: inert.hoist.small_size(rest)
                                case Lex.TColon{}: inert.hoist.small_size(rest)
                                case Lex.TEq{}: inert.hoist.small_size(rest)
                                case Lex.TBind{}: inert.hoist.small_size(rest)
                                case Lex.TArrow{}: inert.hoist.small_size(rest)
                                case Lex.TLam{}: inert.hoist.small_size(rest)
                                case Lex.TAll{}: inert.hoist.small_size(rest)
                                case Lex.TAmp{}: inert.hoist.small_size(rest)
                                case Lex.TOpen{}: inert.hoist.small_size(rest)
                                case Lex.TClose{}: inert.hoist.small_size(rest)
                                case Lex.TComma{}: inert.hoist.small_size(rest)
                        case Tree.Group{x, y, z}: inert.hoist.small_size(rest)
                        case Tree.Stmt{x, y, z}: inert.hoist.small_size(rest)
                        case Tree.NNil{}: inert.hoist.small_size(rest)
                        case Tree.NCons{x, y}: inert.hoist.small_size(rest)
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TColon{}: inert.hoist.small_size(rest)
                case Lex.TEq{}: inert.hoist.small_size(rest)
                case Lex.TBind{}: inert.hoist.small_size(rest)
                case Lex.TArrow{}: inert.hoist.small_size(rest)
                case Lex.TLam{}: inert.hoist.small_size(rest)
                case Lex.TAll{}: inert.hoist.small_size(rest)
                case Lex.TAmp{}: inert.hoist.small_size(rest)
                case Lex.TOpen{}: inert.hoist.small_size(rest)
                case Lex.TClose{}: inert.hoist.small_size(rest)
                case Lex.TComma{}: inert.hoist.small_size(rest)
        case Tree.Group{o, gk, cl}: inert.hoist.small_size(rest)
        case Tree.Stmt{sk, sks, sb}: inert.hoist.small_size(rest)
        case Tree.NNil{}: inert.hoist.small_size(rest)
        case Tree.NCons{x, y}: inert.hoist.small_size(rest)
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a table's kids read that way are as wide as they were
law inert.hoist.wide_shape:
  for arr: Bool
  for +kids: Tree.Node
  for +e: {D1.inert.ok(kids) == True{} : Bool}
  {Hoist.wide_shape(arr, D1.inert.node(kids)) == Hoist.wide_shape(arr, kids) : Bool}

def inert.hoist.wide_shape(arr, kids, e):
  match arr:
    case True{}:
      Equal.cong(Bool, Bool, z => Bool.not(z), Hoist.small_size(D1.inert.node(kids)), Hoist.small_size(kids),
        inert.hoist.small_size(kids))
    case False{}:
      Equal.cong(Nat, Bool, z => Nat.is_gt(z, 7n), Hoist.top_count(D1.inert.node(kids), ",", 0n),
        Hoist.top_count(kids, ",", 0n),
        inert.hoist.top_count(kids, ",", 0n, {==}, e))

# a chain read that way is the number it was: only a number's text is read
law inert.hoist.num_text:
  for nn: Tree.Node
  {Hoist.num_text(D1.inert.node(nn)) == Hoist.num_text(nn) : String}

def inert.hoist.num_text(nn):
  match nn:
    case Tree.NCons{h, r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}: {==}
                case Lex.TUpper{}: {==}
                case Lex.TDotted{}: {==}
                case Lex.TWild{}: {==}
                case Lex.TKey{}: {==}
                case Lex.TNum{}:
                  match r:
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                    case Tree.NCons{x, y}: {==}
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
        case Tree.Group{x, y, z}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a count read that way is wide as it was
law inert.hoist.count_wide:
  for +aa: Tree.Node
  {Hoist.count_wide(D1.inert.node(aa)) == Hoist.count_wide(aa) : Bool}

def inert.hoist.count_wide(aa):
  Equal.cong(String, Bool, z => Bool.not(Hoist.small_num(z)), Hoist.num_text(D1.inert.node(aa)), Hoist.num_text(aa),
    inert.hoist.num_text(aa))

# the last of the arguments read that way is the last read that way
law inert.hoist.last_node:
  for as: List<&2, Tree.Node>
  {Hoist.last_node(inert.nodes(as)) == D1.inert.node(Hoist.last_node(as)) : Tree.Node}

def inert.hoist.last_node(as):
  match as:
    case Nil{}: {==}
    case Con{h, +rest}:
      match rest:
        case Nil{}: {==}
        case Con{x, y}: inert.hoist.last_node(rest)

# a builder's count read that way is wide as it was
law inert.hoist.call_arm:
  for rep: Bool
  for +as: List<&2, Tree.Node>
  for +end: Tree.Node
  for +range: Bool
  {Hoist.call_arm(rep, inert.nodes(as), D1.inert.node(end), range) == Hoist.call_arm(rep, as, end, range) : Bool}

def inert.hoist.call_arm(rep, as, end, range):
  match rep:
    case True{}:
      %Equal.sym(Tree.Node, Calls.arg(inert.nodes(as), 2n), D1.inert.node(Calls.arg(as, 2n)), inert.arg(as, 2n)) :
        {Hoist.count_wide(_) == Hoist.count_wide(Calls.arg(as, 2n)) : Bool}
      inert.hoist.count_wide(Calls.arg(as, 2n))
    case False{}:
      Equal.cong(Bool, Bool, z => Bool.pick(Bool, range, z, True{}), Hoist.count_wide(D1.inert.node(end)),
        Hoist.count_wide(end),
        inert.hoist.count_wide(end))

# a builder call read that way is wide as it was: a string names no builder
law inert.hoist.call_wide:
  for +b: Bool
  for +t: String
  for +kids: Tree.Node
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  {Hoist.call_wide(D1.inert.keep(b, t), D1.inert.node(kids)) == Hoist.call_wide(t, kids) : Bool}

def inert.hoist.call_wide(b, t, kids, ef):
  +kt = D1.inert.keep(b, t)
  +lhs = Hoist.call_wide(kt, D1.inert.node(kids))
  +aa = Calls.args(kids)
  +rp = Bool.or(String.eq(kt, "List.replicate"), String.eq(kt, "Array.new"))
  +rg = String.eq(kt, "List.range")
  %M1.inert.eq_keep(b, t, "List.replicate", ef, {==}) :
    {lhs == Hoist.call_arm(Bool.or(_, String.eq(t, "Array.new")), aa, Hoist.last_node(aa), String.eq(t, "List.range"))
      : Bool}
  %M1.inert.eq_keep(b, t, "Array.new", ef, {==}) :
    {lhs == Hoist.call_arm(Bool.or(String.eq(kt, "List.replicate"), _), aa, Hoist.last_node(aa),
      String.eq(t, "List.range")) : Bool}
  %M1.inert.eq_keep(b, t, "List.range", ef, {==}) : {lhs == Hoist.call_arm(rp, aa, Hoist.last_node(aa), _) : Bool}
  %inert.hoist.call_arm(rp, aa, Hoist.last_node(aa), rg) : {lhs == _ : Bool}
  %inert.hoist.last_node(aa) : {lhs == Hoist.call_arm(rp, inert.nodes(aa), _, rg) : Bool}
  %inert.args(kids) : {lhs == Hoist.call_arm(rp, _, Hoist.last_node(_), rg) : Bool}
  {==}

# a table's cells read that way are as wide as they were
law inert.hoist.wide_of:
  for nn: Tree.Node
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Hoist.wide_of(D1.inert.node(nn)) == Hoist.wide_of(nn) : Bool}

def inert.hoist.wide_of(nn, e):
  match nn:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Group{go, +kids, cl}:
          match go:
            case Lex.Tok{gk, +o, gl, gc}:
              match r:
                case Tree.NNil{}:
                  +ek = M1.inert.and_l(D1.inert.ok(kids), True{}, e)
                  +lhs = Hoist.wide_shape(Hoist.is_array(D1.inert.node(kids)), D1.inert.node(kids))
                  %inert.hoist.wide_shape(Hoist.is_array(kids), kids, ek) : {lhs == _ : Bool}
                  %inert.hoist.is_array(kids, ek) : {lhs == Hoist.wide_shape(_, D1.inert.node(kids)) : Bool}
                  {==}
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NCons{x, y}: {==}
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match r:
                case Tree.NCons{g, +r2}:
                  match g:
                    case Tree.Group{go, +gkids, gcl}:
                      match go:
                        case Lex.Tok{gk, +o, gl, gc}:
                          match r2:
                            case Tree.NNil{}:
                              inert.hoist.call_wide(D1.inert.blanks(k), t, gkids,
                                inert.ok_h(Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc},
                                  gkids, gcl}, Tree.NNil{}}, e))
                            case Tree.Leaf{x}: {==}
                            case Tree.Group{x, y, z}: {==}
                            case Tree.Stmt{x, y, z}: {==}
                            case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                    case Tree.NCons{x, y}: {==}
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NNil{}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a def's body read that way is one wide table as it was
law inert.hoist.wide_one:
  for body: Tree.Node
  for +name: String
  for +acc: List<&2, String>
  for +e: {D1.inert.ok(body) == True{} : Bool}
  {Hoist.wide_one(D1.inert.node(body), name, acc) == Hoist.wide_one(body, name, acc) : List<&2, String>}

def inert.hoist.wide_one(body, name, acc, e):
  match body:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Stmt{sk, +kids, +inn}:
          match r:
            case Tree.NNil{}:
              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(inn), M1.inert.and_l(Bool.and(D1.inert.ok(kids),
                D1.inert.ok(inn)), True{}, e))
              +lhs = Hoist.wide_one(D1.inert.node(Tree.NCons{Tree.Stmt{sk, kids, inn}, Tree.NNil{}}), name, acc)
              %inert.table.built(kids, ek) : {lhs == Bool.pick(List<&2, String>, Bool.and(_, Hoist.wide_of(kids)),
                name <> acc, acc)
                : List<&2, String>}
              %inert.hoist.wide_of(kids, ek) : {lhs == Bool.pick(List<&2, String>,
                Bool.and(Table.built(D1.inert.node(kids)), _), name <> acc,
                acc) : List<&2, String>}
              {==}
            case Tree.Leaf{x}: {==}
            case Tree.Group{x, y, z}: {==}
            case Tree.Stmt{x, y, z}: {==}
            case Tree.NCons{x, y}: {==}
        case Tree.Leaf{x}: {==}
        case Tree.Group{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# the defs read that way whose body is one wide table are the ones they were
law inert.hoist.wide_defs:
  for ds: List<&2, Calls.Def>
  for +acc: List<&2, String>
  for +e: {inert.dok(ds) == True{} : Bool}
  {Hoist.wide_defs(inert.defs(ds), acc) == Hoist.wide_defs(ds, acc) : List<&2, String>}

def inert.hoist.wide_defs(ds, acc, e):
  match ds:
    case Nil{}: {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +lhs = Hoist.wide_defs(inert.defs(Calls.Def{name, sig, body} <> rest), acc)
      %inert.hoist.wide_defs(rest, Hoist.wide_one(body, name, acc), inert.dok.rest(name, sig, body, rest, e)) :
        {lhs == _ : List<&2, String>}
      %inert.hoist.wide_one(body, name, acc, inert.dok.body(name, sig, body, rest, e)) :
        {lhs == Hoist.wide_defs(inert.defs(rest), _) : List<&2, String>}
      {==}

# a call's name read that way picks the slot it did: a string names no get or set
law inert.hoist.slot_of:
  for +b: Bool
  for +t: String
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  {Hoist.slot_of(D1.inert.keep(b, t)) == Hoist.slot_of(t) : Hoist.Slot}

def inert.hoist.slot_of(b, t, ef):
  +kt = D1.inert.keep(b, t)
  +lhs = Hoist.slot_of(kt)
  %M1.inert.eq_keep(b, t, "List.get", ef, {==}) : {lhs == Hoist.slot_pick(Bool.or(_, String.eq(t, "List.set")),
    String.eq(t, "String.get"), Bool.or(String.eq(t, "Array.get"), String.eq(t, "Array.set"))) : Hoist.Slot}
  %M1.inert.eq_keep(b, t, "List.set", ef, {==}) : {lhs == Hoist.slot_pick(Bool.or(String.eq(kt, "List.get"), _),
    String.eq(t, "String.get"), Bool.or(String.eq(t, "Array.get"), String.eq(t, "Array.set"))) : Hoist.Slot}
  %M1.inert.eq_keep(b, t, "String.get", ef, {==}) : {lhs == Hoist.slot_pick(Bool.or(String.eq(kt, "List.get"),
    String.eq(kt, "List.set")), _, Bool.or(String.eq(t, "Array.get"), String.eq(t, "Array.set"))) : Hoist.Slot}
  %M1.inert.eq_keep(b, t, "Array.get", ef, {==}) : {lhs == Hoist.slot_pick(Bool.or(String.eq(kt, "List.get"),
    String.eq(kt, "List.set")), String.eq(kt, "String.get"), Bool.or(_, String.eq(t, "Array.set"))) : Hoist.Slot}
  %M1.inert.eq_keep(b, t, "Array.set", ef, {==}) : {lhs == Hoist.slot_pick(Bool.or(String.eq(kt, "List.get"),
    String.eq(kt, "List.set")), String.eq(kt, "String.get"), Bool.or(String.eq(kt, "Array.get"), _)) : Hoist.Slot}
  {==}

# a bracket group read that way is a closed wide table as it was
law inert.hoist.table_group:
  for brack: Bool
  for +kids: Tree.Node
  for +carried: List<&2, String>
  for +e: {D1.inert.ok(kids) == True{} : Bool}
  {Hoist.table_group(brack, D1.inert.node(kids), carried) == Hoist.table_group(brack, kids, carried) : Bool}

def inert.hoist.table_group(brack, kids, carried, e):
  match brack:
    case False{}: {==}
    case True{}:
      +ia = Hoist.is_array(D1.inert.node(kids))
      +lhs = Hoist.group_yes(ia, D1.inert.node(kids), carried)
      %inert.hoist.is_array(kids, e) : {lhs == Hoist.group_yes(_, kids, carried) : Bool}
      %inert.hoist.top_mark(kids, ",", {==}, e) : {lhs == Bool.and(Bool.or(_, ia), Bool.and(Hoist.closed(kids, carried),
        Hoist.wide_shape(ia, kids))) : Bool}
      %inert.hoist.closed(kids, carried) : {lhs == Bool.and(Bool.or(Hoist.top_mark(D1.inert.node(kids), ","), ia),
        Bool.and(_,
        Hoist.wide_shape(ia, kids))) : Bool}
      %inert.hoist.wide_shape(ia, kids, e) : {lhs == Bool.and(Bool.or(Hoist.top_mark(D1.inert.node(kids), ","), ia),
        Bool.and(Hoist.closed(D1.inert.node(kids), carried), _)) : Bool}
      {==}

# a builder's closed arguments read that way are closed as they were
law inert.hoist.tb2:
  for o: Bool
  for w: Bool
  for +kids: Tree.Node
  for +carried: List<&2, String>
  {Hoist.table_built(o, w, D1.inert.node(kids), carried) == Hoist.table_built(o, w, kids, carried) : Bool}

def inert.hoist.tb2(o, w, kids, carried):
  match o w:
    case True{} True{}: inert.hoist.closed(kids, carried)
    case True{} False{}: {==}
    case False{} True{}: {==}
    case False{} False{}: {==}

# a builder's arguments read that way are a closed wide table as they were
law inert.hoist.tb:
  for +o: Bool
  for +t: String
  for +kids: Tree.Node
  for +carried: List<&2, String>
  for +ef: {D1.inert.fits.go(False{}, t) == True{} : Bool}
  {Hoist.table_built(o, Hoist.call_wide(t, D1.inert.node(kids)), D1.inert.node(kids), carried)
    == Hoist.table_built(o, Hoist.call_wide(t, kids), kids, carried) : Bool}

def inert.hoist.tb(o, t, kids, carried, ef):
  +lhs = Hoist.table_built(o, Hoist.call_wide(t, D1.inert.node(kids)), D1.inert.node(kids), carried)
  %inert.hoist.call_wide(False{}, t, kids, ef) : {lhs == Hoist.table_built(o, _, kids, carried) : Bool}
  inert.hoist.tb2(o, Hoist.call_wide(t, D1.inert.node(kids)), kids, carried)

# a call read that way builds a table as it did: a string names no builder
law inert.hoist.table_call:
  for app: Bool
  for k: Lex.TokKind
  for +t: String
  for +kids: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +ef: {D1.inert.fits.go(D1.inert.blanks(k), t) == True{} : Bool}
  {Hoist.table_call(app, k, D1.inert.keep(D1.inert.blanks(k), t), D1.inert.node(kids), self, wides, carried)
    == Hoist.table_call(app, k, t, kids, self, wides, carried) : Bool}

def inert.hoist.table_call(app, k, t, kids, self, wides, carried, ef):
  match app:
    case False{}: {==}
    case True{}:
      match k:
        case Lex.TName{}: inert.hoist.tb(Hoist.builder(Lex.TName{}, t, self, wides), t, kids, carried, ef)
        case Lex.TUpper{}: inert.hoist.tb(Hoist.builder(Lex.TUpper{}, t, self, wides), t, kids, carried, ef)
        case Lex.TDotted{}: inert.hoist.tb(Hoist.builder(Lex.TDotted{}, t, self, wides), t, kids, carried, ef)
        case Lex.TWild{}: inert.hoist.tb(Hoist.builder(Lex.TWild{}, t, self, wides), t, kids, carried, ef)
        case Lex.TKey{}: inert.hoist.tb(Hoist.builder(Lex.TKey{}, t, self, wides), t, kids, carried, ef)
        case Lex.TNum{}: inert.hoist.tb(Hoist.builder(Lex.TNum{}, t, self, wides), t, kids, carried, ef)
        case Lex.TStr{}: {==}
        case Lex.TChar{}: inert.hoist.tb(Hoist.builder(Lex.TChar{}, t, self, wides), t, kids, carried, ef)
        case Lex.TComment{}: {==}
        case Lex.TSpace{}: inert.hoist.tb(Hoist.builder(Lex.TSpace{}, t, self, wides), t, kids, carried, ef)
        case Lex.TNewline{}: inert.hoist.tb(Hoist.builder(Lex.TNewline{}, t, self, wides), t, kids, carried, ef)
        case Lex.TOp{}: inert.hoist.tb(Hoist.builder(Lex.TOp{}, t, self, wides), t, kids, carried, ef)
        case Lex.TColon{}: inert.hoist.tb(Hoist.builder(Lex.TColon{}, t, self, wides), t, kids, carried, ef)
        case Lex.TEq{}: inert.hoist.tb(Hoist.builder(Lex.TEq{}, t, self, wides), t, kids, carried, ef)
        case Lex.TBind{}: inert.hoist.tb(Hoist.builder(Lex.TBind{}, t, self, wides), t, kids, carried, ef)
        case Lex.TArrow{}: inert.hoist.tb(Hoist.builder(Lex.TArrow{}, t, self, wides), t, kids, carried, ef)
        case Lex.TLam{}: inert.hoist.tb(Hoist.builder(Lex.TLam{}, t, self, wides), t, kids, carried, ef)
        case Lex.TAll{}: inert.hoist.tb(Hoist.builder(Lex.TAll{}, t, self, wides), t, kids, carried, ef)
        case Lex.TAmp{}: inert.hoist.tb(Hoist.builder(Lex.TAmp{}, t, self, wides), t, kids, carried, ef)
        case Lex.TOpen{}: inert.hoist.tb(Hoist.builder(Lex.TOpen{}, t, self, wides), t, kids, carried, ef)
        case Lex.TClose{}: inert.hoist.tb(Hoist.builder(Lex.TClose{}, t, self, wides), t, kids, carried, ef)
        case Lex.TComma{}: inert.hoist.tb(Hoist.builder(Lex.TComma{}, t, self, wides), t, kids, carried, ef)

# a call named by a string is no table, whatever it says
law inert.hoist.tc_TStr:
  for app: Bool
  for -t1: String
  for -t2: String
  for -k1: Tree.Node
  for -k2: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for -n1: Tree.Node
  for -n2: Tree.Node
  for +path: String
  {Hoist.one_yes(Hoist.table_call(app, Lex.TStr{}, t1, k1, self, wides, carried), n1, path)
    == Hoist.one_yes(Hoist.table_call(app, Lex.TStr{}, t2, k2, self, wides, carried), n2, path) : List<&2, F.Finding>}

def inert.hoist.tc_TStr(app, _t1, _t2, _k1, _k2, _self, _wides, _carried, _n1, _n2, _path):
  match app:
    case True{}: {==}
    case False{}: {==}

# a call named by a comment is no table, whatever it says
law inert.hoist.tc_TComment:
  for app: Bool
  for -t1: String
  for -t2: String
  for -k1: Tree.Node
  for -k2: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for -n1: Tree.Node
  for -n2: Tree.Node
  for +path: String
  {Hoist.one_yes(Hoist.table_call(app, Lex.TComment{}, t1, k1, self, wides, carried), n1, path)
    == Hoist.one_yes(Hoist.table_call(app, Lex.TComment{}, t2, k2, self, wides, carried), n2, path) : List<&2,
      F.Finding>}

def inert.hoist.tc_TComment(app, _t1, _t2, _k1, _k2, _self, _wides, _carried, _n1, _n2, _path):
  match app:
    case True{}: {==}
    case False{}: {==}

# a finding that is there or not, on two nodes it cites alike
law inert.hoist.one:
  for yes: Bool
  for -n1: Tree.Node
  for -n2: Tree.Node
  for +path: String
  for ec: {Hoist.cite(n1, path) == Hoist.cite(n2, path) : List<&2, F.Finding>}
  {Hoist.one_yes(yes, n1, path) == Hoist.one_yes(yes, n2, path) : List<&2, F.Finding>}

def inert.hoist.one(yes, _n1, _n2, _path, ec):
  match yes:
    case True{}: ec
    case False{}: {==}

# a table read that way is the table it was, cited where it was: a table
# starts with a bracket or a builder's name, never a string
law inert.hoist.yes:
  for nn: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Hoist.one_yes(Hoist.is_table(D1.inert.node(nn), self, wides, carried), D1.inert.node(nn), path)
    == Hoist.one_yes(Hoist.is_table(nn, self, wides, carried), nn, path) : List<&2, F.Finding>}

def inert.hoist.yes(nn, self, wides, carried, path, e):
  match nn:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Group{go, +kids, +gcl}:
          match go:
            case Lex.Tok{+gk, +o, +gl, +gc}:
              match r:
                case Tree.NNil{}:
                  +n1 = D1.inert.node(Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, kids, gcl}, Tree.NNil{}})
                  +n2 = {Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, kids, gcl}, Tree.NNil{}} : Tree.Node}
                  +tg = Hoist.table_group(String.eq(o, "["), D1.inert.node(kids), carried)
                  %inert.hoist.table_group(String.eq(o, "["), kids, carried, M1.inert.and_l(D1.inert.ok(kids), True{},
                    e)) : {Hoist.one_yes(tg, n1, path) == Hoist.one_yes(_, n2, path) : List<&2, F.Finding>}
                  inert.hoist.one(tg, n1, n2, path, {==})
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NCons{x, y}: {==}
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, +l, +c}:
              match k:
                case Lex.TName{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TName{}, t, gkids, self, wides,
                                    carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TName{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TName{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TUpper{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TUpper{}, t, gkids, self, wides,
                                    carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TUpper{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TUpper{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TDotted{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TDotted{}, t, gkids, self, wides,
                                    carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TDotted{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TDotted{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TWild{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TWild{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TWild{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TWild{}, t, gkids, self, wides,
                                    carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TWild{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TWild{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TWild{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TKey{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TKey{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TKey{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TKey{}, t, gkids, self, wides, carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TKey{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TKey{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TKey{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TNum{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TNum{}, t, gkids, self, wides, carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TNum{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TNum{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TStr{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  inert.hoist.tc_TStr(String.eq(o, "("), D1.inert.cut(t), t, D1.inert.node(gkids),
                                    gkids, self, wides, carried,
                                    D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TStr{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}}),
                                      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TStr{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}}, path)
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TChar{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TChar{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TChar{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TChar{}, t, gkids, self, wides,
                                    carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TChar{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TChar{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TChar{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TComment{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  inert.hoist.tc_TComment(String.eq(o, "("), D1.inert.cut(t), t,
                                    D1.inert.node(gkids), gkids, self, wides, carried,
                                    D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComment{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}}),
                                      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComment{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}}, path)
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TSpace{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TSpace{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TSpace{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TSpace{}, t, gkids, self, wides,
                                    carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TSpace{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TSpace{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TSpace{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TNewline{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNewline{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNewline{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TNewline{}, t, gkids, self, wides,
                                    carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TNewline{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TNewline{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TNewline{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TOp{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TOp{}, t, gkids, self, wides, carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TOp{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TOp{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TOp{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TColon{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TColon{}, t, gkids, self, wides,
                                    carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TColon{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TColon{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TEq{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TEq{}, t, gkids, self, wides, carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TEq{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TEq{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TBind{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TBind{}, t, gkids, self, wides,
                                    carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TBind{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TBind{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TArrow{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TArrow{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TArrow{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TArrow{}, t, gkids, self, wides,
                                    carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TArrow{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TArrow{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TArrow{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TLam{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TLam{}, t, gkids, self, wides, carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TLam{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TLam{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TAll{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TAll{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TAll{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TAll{}, t, gkids, self, wides, carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TAll{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TAll{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TAll{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TAmp{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TAmp{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TAmp{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TAmp{}, t, gkids, self, wides, carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TAmp{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TAmp{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TAmp{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TOpen{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOpen{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOpen{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TOpen{}, t, gkids, self, wides,
                                    carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TOpen{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TOpen{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TOpen{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TClose{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TClose{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TClose{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TClose{}, t, gkids, self, wides,
                                    carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TClose{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TClose{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TClose{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                case Lex.TComma{}:
                  match r:
                    case Tree.NCons{g, +r2}:
                      match g:
                        case Tree.Group{go, +gkids, +gcl}:
                          match go:
                            case Lex.Tok{+gk, +o, +gl, +gc}:
                              match r2:
                                case Tree.NNil{}:
                                  +n1 = D1.inert.node(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}})
                                  +n2 = {Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}},
                                    Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl},
                                    Tree.NNil{}}} : Tree.Node}
                                  %inert.hoist.table_call(String.eq(o, "("), Lex.TComma{}, t, gkids, self, wides,
                                    carried,
                                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}},
                                      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, gkids, gcl}, Tree.NNil{}}, e)) :
                                    {Hoist.one_yes(Hoist.table_call(String.eq(o, "("), Lex.TComma{}, t,
                                      D1.inert.node(gkids), self, wides, carried), n1, path) == Hoist.one_yes(_, n2,
                                      path) : List<&2, F.Finding>}
                                  inert.hoist.one(Hoist.table_call(String.eq(o, "("), Lex.TComma{}, t,
                                    D1.inert.node(gkids), self, wides, carried), n1, n2, path, {==})
                                case Tree.Leaf{x}: {==}
                                case Tree.Group{x, y, z}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NCons{x, y}: {==}
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a let's table cited when it is indexed: a choice on the index of the table's
# finding
law inert.hoist.use_pick:
  for tab: Bool
  for used: Bool
  for +expr: Tree.Node
  for +path: String
  {Hoist.let_use(tab, used, expr, path) == Bool.pick(List<&2, F.Finding>, used, Hoist.one_yes(tab, expr, path),
    []) : List<&2, F.Finding>}

def inert.hoist.use_pick(tab, used, _expr, _path):
  match tab used:
    case True{} True{}: {==}
    case True{} False{}: {==}
    case False{} True{}: {==}
    case False{} False{}: {==}

# a let's table read that way, indexed as it was, is cited as it was
law inert.hoist.use:
  for +expr: Tree.Node
  for +used: Bool
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +e: {D1.inert.ok(expr) == True{} : Bool}
  {Hoist.let_use(Hoist.is_table(D1.inert.node(expr), self, wides, carried), used, D1.inert.node(expr), path)
    == Hoist.let_use(Hoist.is_table(expr, self, wides, carried), used, expr, path) : List<&2, F.Finding>}

def inert.hoist.use(expr, used, self, wides, carried, path, e):
  +t1 = Hoist.is_table(D1.inert.node(expr), self, wides, carried)
  +t2 = Hoist.is_table(expr, self, wides, carried)
  Equal.trans(List<&2, F.Finding>, Hoist.let_use(t1, used, D1.inert.node(expr), path), Bool.pick(List<&2,
    F.Finding>, used, Hoist.one_yes(t1, D1.inert.node(expr), path), []),
    Hoist.let_use(t2, used, expr, path), inert.hoist.use_pick(t1, used, D1.inert.node(expr), path),
    Equal.trans(List<&2, F.Finding>, Bool.pick(List<&2, F.Finding>, used, Hoist.one_yes(t1, D1.inert.node(expr),
      path), []),
      Bool.pick(List<&2, F.Finding>, used, Hoist.one_yes(t2, expr, path), []), Hoist.let_use(t2, used, expr, path),
      Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>, z => Bool.pick(List<&2, F.Finding>, used, z, []),
        Hoist.one_yes(t1, D1.inert.node(expr), path),
        Hoist.one_yes(t2, expr, path), inert.hoist.yes(expr, self, wides, carried, path, e)),
      Equal.sym(List<&2, F.Finding>, Hoist.let_use(t2, used, expr, path), Bool.pick(List<&2, F.Finding>, used,
        Hoist.one_yes(t2, expr, path), []),
        inert.hoist.use_pick(t2, used, expr, path))))

# a chain read that way is exactly the name as it was: only a name's text is read
law inert.hoist.wrapped_inside:
  for nn: Tree.Node
  for +binder: String
  {Hoist.wrapped_inside(D1.inert.node(nn), binder) == Hoist.wrapped_inside(nn, binder) : Bool}

def inert.hoist.wrapped_inside(nn, _binder):
  match nn:
    case Tree.NCons{h, r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}:
                  match r:
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                    case Tree.NCons{x, y}: {==}
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
        case Tree.Group{x, y, z}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a paren's kids read that way are the name as they were
law inert.hoist.wrapped_open:
  for paren: Bool
  for +kids: Tree.Node
  for +binder: String
  {Hoist.wrapped_open(paren, D1.inert.node(kids), binder) == Hoist.wrapped_open(paren, kids, binder) : Bool}

def inert.hoist.wrapped_open(paren, kids, binder):
  match paren:
    case True{}: inert.hoist.wrapped_inside(kids, binder)
    case False{}: {==}

# a chain read that way is the name, or the name in parentheses, as it was
law inert.hoist.wrapped:
  for nn: Tree.Node
  for +binder: String
  {Hoist.wrapped(D1.inert.node(nn), binder) == Hoist.wrapped(nn, binder) : Bool}

def inert.hoist.wrapped(nn, binder):
  match nn:
    case Tree.NCons{h, r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}:
                  match r:
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                    case Tree.NCons{x, y}: {==}
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
        case Tree.Group{go, +kids, gcl}:
          match go:
            case Lex.Tok{gk, +o, gl, gc}:
              match r:
                case Tree.NNil{}: inert.hoist.wrapped_open(String.eq(o, "("), kids, binder)
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NCons{x, y}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a get's or set's collection argument, the arguments read that way, is the
# name as it was
law inert.hoist.uses_arg:
  for ss: Hoist.Slot
  for +as: List<&2, Tree.Node>
  for +binder: String
  {Hoist.uses_arg(ss, inert.nodes(as), binder) == Hoist.uses_arg(ss, as, binder) : Bool}

def inert.hoist.uses_arg(ss, as, binder):
  match ss:
    case Hoist.Slot{on, +at}:
      match on:
        case False{}: {==}
        case True{}:
          %Equal.sym(Tree.Node, Calls.arg(inert.nodes(as), at), D1.inert.node(Calls.arg(as, at)), inert.arg(as, at)) :
            {Hoist.wrapped(_, binder) == Hoist.wrapped(Calls.arg(as, at), binder) : Bool}
          inert.hoist.wrapped(Calls.arg(as, at), binder)

# a name then a group, read that way, indexes the name as it did: a string is
# never the name nor a get or set
law inert.hoist.uses_here:
  for brack: Bool
  for call: Bool
  for +b: Bool
  for +t: String
  for +kids: Tree.Node
  for +binder: String
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +eb: {D1.inert.marked(binder) == False{} : Bool}
  {Hoist.uses_here(brack, call, D1.inert.keep(b, t), D1.inert.node(kids), binder) == Hoist.uses_here(brack, call,
    t, kids, binder)
    : Bool}

def inert.hoist.uses_here(brack, call, b, t, kids, binder, ef, eb):
  match brack:
    case True{}: M1.inert.eq_keep(b, t, binder, ef, eb)
    case False{}:
      match call:
        case False{}: {==}
        case True{}:
          +lhs = Hoist.uses_arg(Hoist.slot_of(D1.inert.keep(b, t)), Calls.args(D1.inert.node(kids)), binder)
          %inert.hoist.uses_arg(Hoist.slot_of(t), Calls.args(kids), binder) : {lhs == _ : Bool}
          %inert.args(kids) : {lhs == Hoist.uses_arg(Hoist.slot_of(t), _, binder) : Bool}
          %inert.hoist.slot_of(b, t, ef) : {lhs == Hoist.uses_arg(_, Calls.args(D1.inert.node(kids)), binder) : Bool}
          {==}

# a name then a group: the index here, under the group and after it read as
# they were
law inert.hoist.uses_lg:
  for +b: Bool
  for +t: String
  for +o: String
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +binder: String
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +eb: {D1.inert.marked(binder) == False{} : Bool}
  for ik: {Hoist.uses_name(D1.inert.node(kids), binder) == Hoist.uses_name(kids, binder) : Bool}
  for ir: {Hoist.uses_name(D1.inert.node(r2), binder) == Hoist.uses_name(r2, binder) : Bool}
  {Bool.or(Hoist.uses_here(String.eq(o, "["), String.eq(o, "("), D1.inert.keep(b, t), D1.inert.node(kids), binder),
    Bool.or(Hoist.uses_name(D1.inert.node(kids), binder), Hoist.uses_name(D1.inert.node(r2), binder)))
    == Bool.or(Hoist.uses_here(String.eq(o, "["), String.eq(o, "("), t, kids, binder),
      Bool.or(Hoist.uses_name(kids, binder), Hoist.uses_name(r2, binder))) : Bool}

def inert.hoist.uses_lg(b, t, o, kids, r2, binder, ef, eb, ik, ir):
  inert.hoist.or2(Hoist.uses_here(String.eq(o, "["), String.eq(o, "("), D1.inert.keep(b, t), D1.inert.node(kids),
    binder),
    Hoist.uses_here(String.eq(o, "["), String.eq(o, "("), t, kids, binder),
    Bool.or(Hoist.uses_name(D1.inert.node(kids), binder), Hoist.uses_name(D1.inert.node(r2), binder)),
    Bool.or(Hoist.uses_name(kids, binder), Hoist.uses_name(r2, binder)),
    inert.hoist.uses_here(String.eq(o, "["), String.eq(o, "("), b, t, kids, binder, ef, eb),
    inert.hoist.or2(Hoist.uses_name(D1.inert.node(kids), binder), Hoist.uses_name(kids, binder),
      Hoist.uses_name(D1.inert.node(r2), binder),
      Hoist.uses_name(r2, binder), ik, ir))

# a chain read that way indexes the name as it did
law inert.hoist.uses_name:
  for nn: Tree.Node
  for +binder: String
  for +eb: {D1.inert.marked(binder) == False{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Hoist.uses_name(D1.inert.node(nn), binder) == Hoist.uses_name(nn, binder) : Bool}

def inert.hoist.uses_name(nn, binder, eb, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{go, +kids, +gcl}:
                      match go:
                        case Lex.Tok{+gk, +o, +gl, +gc}:
                          +lf = {Tree.Leaf{Lex.Tok{k, t, l, c}} : Tree.Node}
                          +gp = {Tree.Group{Lex.Tok{gk, o, gl, gc}, kids, gcl} : Tree.Node}
                          +eg = inert.ok_t(lf, Tree.NCons{gp, r2}, e)
                          inert.hoist.uses_lg(D1.inert.blanks(k), t, o, kids, r2, binder,
                            inert.ok_h(lf, Tree.NCons{gp, r2}, e), eb,
                            inert.hoist.uses_name(kids, binder, eb, inert.ok_h(gp, r2, eg)),
                            inert.hoist.uses_name(r2, binder, eb, inert.ok_t(gp, r2, eg)))
                    case Tree.Leaf{x}:
                      inert.hoist.uses_name(rest, binder, eb, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.Stmt{x, y, z}:
                      inert.hoist.uses_name(rest, binder, eb, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NNil{}:
                      inert.hoist.uses_name(rest, binder, eb, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NCons{x, y}:
                      inert.hoist.uses_name(rest, binder, eb, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Leaf{x}:
                  inert.hoist.uses_name(rest, binder, eb, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Group{x, y, z}:
                  inert.hoist.uses_name(rest, binder, eb, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Stmt{x, y, z}:
                  inert.hoist.uses_name(rest, binder, eb, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.NNil{}:
                  inert.hoist.uses_name(rest, binder, eb, inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
        case Tree.Group{+o, +kids, +cl}:
          inert.hoist.or2(Hoist.uses_name(D1.inert.node(kids), binder), Hoist.uses_name(kids, binder),
            Hoist.uses_name(D1.inert.node(rest), binder),
            Hoist.uses_name(rest, binder), inert.hoist.uses_name(kids, binder, eb, inert.ok_h(Tree.Group{o, kids, cl},
              rest, e)),
            inert.hoist.uses_name(rest, binder, eb, inert.ok_t(Tree.Group{o, kids, cl}, rest, e)))
        case Tree.Stmt{+sk, +kids, +body}:
          +es = inert.ok_h(Tree.Stmt{sk, kids, body}, rest, e)
          inert.hoist.or2(Hoist.uses_name(D1.inert.node(kids), binder), Hoist.uses_name(kids, binder),
            Bool.or(Hoist.uses_name(D1.inert.node(body), binder), Hoist.uses_name(D1.inert.node(rest), binder)),
            Bool.or(Hoist.uses_name(body, binder), Hoist.uses_name(rest, binder)),
            inert.hoist.uses_name(kids, binder, eb, M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es)),
            inert.hoist.or2(Hoist.uses_name(D1.inert.node(body), binder), Hoist.uses_name(body, binder),
              Hoist.uses_name(D1.inert.node(rest), binder), Hoist.uses_name(rest, binder),
              inert.hoist.uses_name(body, binder, eb, M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es)),
              inert.hoist.uses_name(rest, binder, eb, inert.ok_t(Tree.Stmt{sk, kids, body}, rest, e))))
        case Tree.NNil{}: inert.hoist.uses_name(rest, binder, eb, e)
        case Tree.NCons{x, y}: inert.hoist.uses_name(rest, binder, eb, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a let's name and table, the table read that way
def inert.hoist.got(mm: Maybe<&2, Hoist.Got>) -> Maybe<&2, Hoist.Got>:
  match mm:
    case None{}: None{}
    case Some{Hoist.Got{nm, expr}}: Some{Hoist.Got{nm, D1.inert.node(expr)}}

# a let's name plain and its table's leaves fitting, or no let
def inert.hoist.gok(mm: Maybe<&2, Hoist.Got>) -> Bool:
  match mm:
    case None{}: True{}
    case Some{Hoist.Got{nm, expr}}: Bool.and(Bool.not(D1.inert.marked(nm)), D1.inert.ok(expr))

# a Bool that is False has a negation that holds
law inert.hoist.not_f:
  for -x: Bool
  for e: {x == False{} : Bool}
  {Bool.not(x) == True{} : Bool}

def inert.hoist.not_f(x, e):
  %Equal.sym(Bool, x, False{}, e) : {Bool.not(_) == True{} : Bool}
  {==}

# the chain after `=`, read that way, is the table it was
law inert.hoist.got_at:
  for seen: Bool
  for bad: Bool
  for +nm: String
  for +expr: Tree.Node
  {Hoist.got_at(seen, bad, nm, D1.inert.node(expr)) == inert.hoist.got(Hoist.got_at(seen, bad, nm,
    expr)) : Maybe<&2, Hoist.Got>}

def inert.hoist.got_at(seen, bad, _nm, _expr):
  match seen:
    case False{}: {==}
    case True{}:
      match bad:
        case True{}: {==}
        case False{}: {==}

# the chain after `=` of a plain name fits
law inert.hoist.got_at_ok:
  for seen: Bool
  for bad: Bool
  for +nm: String
  for +expr: Tree.Node
  for +en: {D1.inert.marked(nm) == False{} : Bool}
  for +ee: {D1.inert.ok(expr) == True{} : Bool}
  {inert.hoist.gok(Hoist.got_at(seen, bad, nm, expr)) == True{} : Bool}

def inert.hoist.got_at_ok(seen, bad, nm, expr, en, ee):
  match seen:
    case False{}: {==}
    case True{}:
      match bad:
        case True{}: {==}
        case False{}:
          M1.inert.and_both(Bool.not(D1.inert.marked(nm)), D1.inert.ok(expr),
            inert.hoist.not_f(D1.inert.marked(nm), en), ee)

# a let read that way binds the name it did to its table read that way: only
# a name's text is read
law inert.hoist.eat:
  for nn: Tree.Node
  for +seen: Bool
  for +bad: Bool
  for +nm: String
  {Hoist.eat(D1.inert.node(nn), seen, bad, nm) == inert.hoist.got(Hoist.eat(nn, seen, bad, nm)) : Maybe<&2,
    Hoist.Got>}

def inert.hoist.eat(nn, seen, bad, nm):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}: inert.hoist.eat(rest, True{}, Bool.or(bad, seen), t)
                case Lex.TUpper{}: inert.hoist.eat(rest, seen, True{}, nm)
                case Lex.TDotted{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TWild{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TKey{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TNum{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TStr{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TChar{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TComment{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TSpace{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TNewline{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TOp{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TColon{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TEq{}: inert.hoist.got_at(seen, bad, nm, rest)
                case Lex.TBind{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TArrow{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TLam{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TAll{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TAmp{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TOpen{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TClose{}: inert.hoist.eat(rest, seen, bad, nm)
                case Lex.TComma{}: inert.hoist.eat(rest, seen, bad, nm)
        case Tree.Group{o, gk, cl}: inert.hoist.eat(rest, seen, True{}, nm)
        case Tree.Stmt{sk, sks, sb}: inert.hoist.eat(rest, seen, bad, nm)
        case Tree.NNil{}: inert.hoist.eat(rest, seen, bad, nm)
        case Tree.NCons{x, y}: inert.hoist.eat(rest, seen, bad, nm)
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a let of a source as the lexer makes it binds a plain name to leaves that fit
law inert.hoist.eat_ok:
  for nn: Tree.Node
  for +seen: Bool
  for +bad: Bool
  for +nm: String
  for +en: {D1.inert.marked(nm) == False{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {inert.hoist.gok(Hoist.eat(nn, seen, bad, nm)) == True{} : Bool}

def inert.hoist.eat_ok(nn, seen, bad, nm, en, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, +l, +c}:
              match k:
                case Lex.TName{}:
                  inert.hoist.eat_ok(rest, True{}, Bool.or(bad, seen), t, inert.not_true(D1.inert.marked(t),
                    inert.ok_h(Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, rest, e)),
                    inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, rest, e))
                case Lex.TUpper{}:
                  inert.hoist.eat_ok(rest, seen, True{}, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}},
                    rest, e))
                case Lex.TDotted{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}},
                    rest, e))
                case Lex.TWild{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TWild{}, t, l, c}},
                    rest, e))
                case Lex.TKey{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TKey{}, t, l, c}},
                    rest, e))
                case Lex.TNum{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}},
                    rest, e))
                case Lex.TStr{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TStr{}, t, l, c}},
                    rest, e))
                case Lex.TChar{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TChar{}, t, l, c}},
                    rest, e))
                case Lex.TComment{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TComment{}, t, l, c}},
                    rest, e))
                case Lex.TSpace{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TSpace{}, t, l, c}},
                    rest, e))
                case Lex.TNewline{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TNewline{}, t, l, c}},
                    rest, e))
                case Lex.TOp{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOp{}, t, l, c}}, rest,
                    e))
                case Lex.TColon{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}},
                    rest, e))
                case Lex.TEq{}:
                  inert.hoist.got_at_ok(seen, bad, nm, rest, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}},
                    rest, e))
                case Lex.TBind{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}},
                    rest, e))
                case Lex.TArrow{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TArrow{}, t, l, c}},
                    rest, e))
                case Lex.TLam{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}},
                    rest, e))
                case Lex.TAll{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TAll{}, t, l, c}},
                    rest, e))
                case Lex.TAmp{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TAmp{}, t, l, c}},
                    rest, e))
                case Lex.TOpen{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOpen{}, t, l, c}},
                    rest, e))
                case Lex.TClose{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TClose{}, t, l, c}},
                    rest, e))
                case Lex.TComma{}:
                  inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}},
                    rest, e))
        case Tree.Group{o, gk, cl}:
          inert.hoist.eat_ok(rest, seen, True{}, nm, en, inert.ok_t(Tree.Group{o, gk, cl}, rest, e))
        case Tree.Stmt{sk, sks, sb}:
          inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.Stmt{sk, sks, sb}, rest, e))
        case Tree.NNil{}: inert.hoist.eat_ok(rest, seen, bad, nm, en, e)
        case Tree.NCons{x, y}: inert.hoist.eat_ok(rest, seen, bad, nm, en, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# the let's body and what follows, read that way, index the name as they did
law inert.hoist.uses_or:
  for +body: Tree.Node
  for +rest: Tree.Node
  for +binder: String
  for +eb: {D1.inert.marked(binder) == False{} : Bool}
  for +ebd: {D1.inert.ok(body) == True{} : Bool}
  for +er: {D1.inert.ok(rest) == True{} : Bool}
  {Hoist.uses_or(D1.inert.node(body), D1.inert.node(rest), binder) == Hoist.uses_or(body, rest, binder) : Bool}

def inert.hoist.uses_or(body, rest, binder, eb, ebd, er):
  inert.hoist.or2(Hoist.uses_name(D1.inert.node(body), binder), Hoist.uses_name(body, binder),
    Hoist.uses_name(D1.inert.node(rest), binder),
    Hoist.uses_name(rest, binder), inert.hoist.uses_name(body, binder, eb, ebd),
    inert.hoist.uses_name(rest, binder, eb, er))

# a plain let read that way is judged as it was
law inert.hoist.let_of:
  for mm: Maybe<&2, Hoist.Got>
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +eg: {inert.hoist.gok(mm) == True{} : Bool}
  for +eb: {D1.inert.ok(body) == True{} : Bool}
  for +er: {D1.inert.ok(rest) == True{} : Bool}
  {Hoist.let_of(inert.hoist.got(mm), D1.inert.node(body), D1.inert.node(rest), self, wides, carried, path)
    == Hoist.let_of(mm, body, rest, self, wides, carried, path) : List<&2, F.Finding>}

def inert.hoist.let_of(mm, body, rest, self, wides, carried, path, eg, eb, er):
  match mm:
    case None{}: {==}
    case Some{Hoist.Got{+nm, +expr}}:
      +en = inert.not_true(D1.inert.marked(nm), M1.inert.and_l(Bool.not(D1.inert.marked(nm)), D1.inert.ok(expr), eg))
      +ee = M1.inert.and_r(Bool.not(D1.inert.marked(nm)), D1.inert.ok(expr), eg)
      +lhs = Hoist.let_use(Hoist.is_table(D1.inert.node(expr), self, wides, carried),
        Hoist.uses_or(D1.inert.node(body), D1.inert.node(rest), nm), D1.inert.node(expr),
        path)
      %inert.hoist.uses_or(body, rest, nm, en, eb, er) :
        {lhs == Hoist.let_use(Hoist.is_table(expr, self, wides, carried), _, expr, path) : List<&2, F.Finding>}
      inert.hoist.use(expr, Hoist.uses_or(D1.inert.node(body), D1.inert.node(rest), nm), self, wides, carried,
        path, ee)

# a hot let read that way is judged as it was
law inert.hoist.let_hit:
  for hot: Bool
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  for +eb: {D1.inert.ok(body) == True{} : Bool}
  for +er: {D1.inert.ok(rest) == True{} : Bool}
  {Hoist.let_hit(hot, D1.inert.node(kids), D1.inert.node(body), D1.inert.node(rest), self, wides, carried, path)
    == Hoist.let_hit(hot, kids, body, rest, self, wides, carried, path) : List<&2, F.Finding>}

def inert.hoist.let_hit(hot, kids, body, rest, self, wides, carried, path, ek, eb, er):
  match hot:
    case False{}: {==}
    case True{}:
      %Equal.sym(Maybe<&2, Hoist.Got>, Hoist.eat(D1.inert.node(kids), False{}, False{}, ""),
        inert.hoist.got(Hoist.eat(kids, False{}, False{}, "")), inert.hoist.eat(kids, False{}, False{}, "")) :
        {Hoist.let_of(_, D1.inert.node(body), D1.inert.node(rest), self, wides, carried, path)
          == Hoist.let_of(Hoist.eat(kids, False{}, False{}, ""), body, rest, self, wides, carried, path) : List<&2,
            F.Finding>}
      inert.hoist.let_of(Hoist.eat(kids, False{}, False{}, ""), body, rest, self, wides, carried, path,
        inert.hoist.eat_ok(kids, False{}, False{}, "", {==}, ek), eb, er)

# a get's or set's collection argument, the arguments read that way, is the
# table it was
law inert.hoist.arg_table:
  for ss: Hoist.Slot
  for +as: List<&2, Tree.Node>
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +ea: {inert.noks(as) == True{} : Bool}
  {Hoist.arg_table(ss, inert.nodes(as), self, wides, carried, path)
    == Hoist.arg_table(ss, as, self, wides, carried, path) : List<&2, F.Finding>}

def inert.hoist.arg_table(ss, as, self, wides, carried, path, ea):
  match ss:
    case Hoist.Slot{on, +at}:
      match on:
        case False{}: {==}
        case True{}:
          %Equal.sym(Tree.Node, Calls.arg(inert.nodes(as), at), D1.inert.node(Calls.arg(as, at)), inert.arg(as, at)) :
            {Hoist.one_yes(Hoist.is_table(_, self, wides, carried), _, path)
              == Hoist.one_yes(Hoist.is_table(Calls.arg(as, at), self, wides, carried), Calls.arg(as, at),
                path) : List<&2, F.Finding>}
          inert.hoist.yes(Calls.arg(as, at), self, wides, carried, path, inert.ok.nth(as, at, ea))

# a get or set read that way, its table passed inline, is judged as it was
law inert.hoist.call_table:
  for hot: Bool
  for open: Bool
  for +b: Bool
  for +t: String
  for +kids: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  {Hoist.call_table(hot, open, D1.inert.keep(b, t), D1.inert.node(kids), self, wides, carried, path)
    == Hoist.call_table(hot, open, t, kids, self, wides, carried, path) : List<&2, F.Finding>}

def inert.hoist.call_table(hot, open, b, t, kids, self, wides, carried, path, ef, ek):
  match hot:
    case False{}: {==}
    case True{}:
      match open:
        case False{}: {==}
        case True{}:
          +lhs = Hoist.arg_table(Hoist.slot_of(D1.inert.keep(b, t)), Calls.args(D1.inert.node(kids)), self, wides,
            carried, path)
          %inert.hoist.arg_table(Hoist.slot_of(t), Calls.args(kids), self, wides, carried, path,
            inert.ok.args.go(kids, Tree.NNil{}, [], ek, {==}, {==})) : {lhs == _ : List<&2, F.Finding>}
          %inert.args(kids) : {lhs == Hoist.arg_table(Hoist.slot_of(t), _, self, wides, carried, path) : List<&2,
            F.Finding>}
          %inert.hoist.slot_of(b, t, ef) :
            {lhs == Hoist.arg_table(_, Calls.args(D1.inert.node(kids)), self, wides, carried, path) : List<&2,
              F.Finding>}
          {==}

# four finding lists that read alike join alike
law inert.hoist.cat4:
  for -a1: List<&2, F.Finding>
  for -a2: List<&2, F.Finding>
  for -b1: List<&2, F.Finding>
  for -b2: List<&2, F.Finding>
  for -c1: List<&2, F.Finding>
  for -c2: List<&2, F.Finding>
  for -d1: List<&2, F.Finding>
  for -d2: List<&2, F.Finding>
  for ea: {a1 == a2 : List<&2, F.Finding>}
  for eb: {b1 == b2 : List<&2, F.Finding>}
  for ec: {c1 == c2 : List<&2, F.Finding>}
  for ed: {d1 == d2 : List<&2, F.Finding>}
  {List.concat(&2, F.Finding, [a1, b1, c1, d1]) == List.concat(&2, F.Finding, [a2, b2, c2, d2]) : List<&2, F.Finding>}

def inert.hoist.cat4(a1, _a2, b1, b2, c1, c2, d1, d2, ea, eb, ec, ed):
  %ea : {List.concat(&2, F.Finding, [a1, b1, c1, d1]) == List.concat(&2, F.Finding, [_, b2, c2, d2]) : List<&2,
    F.Finding>}
  %eb : {List.concat(&2, F.Finding, [a1, b1, c1, d1]) == List.concat(&2, F.Finding, [a1, _, c2, d2]) : List<&2,
    F.Finding>}
  %ec : {List.concat(&2, F.Finding, [a1, b1, c1, d1]) == List.concat(&2, F.Finding, [a1, b1, _, d2]) : List<&2,
    F.Finding>}
  %ed : {List.concat(&2, F.Finding, [a1, b1, c1, d1]) == List.concat(&2, F.Finding, [a1, b1, c1, _]) : List<&2,
    F.Finding>}
  {==}

# a name then a group: its inline table, the group and the rest walked as
# they were
law inert.hoist.walk_lg:
  for +k: Lex.TokKind
  for +t: String
  for +o: String
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +hot: Bool
  for +ef: {D1.inert.fits.go(D1.inert.blanks(k), t) == True{} : Bool}
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  for ik: {Hoist.walk(D1.inert.node(kids), self, wides, carried, path, Hoist.warm(hot, k))
    == Hoist.walk(kids, self, wides, carried, path, Hoist.warm(hot, k)) : List<&2, F.Finding>}
  for ir: {Hoist.walk(D1.inert.node(r2), self, wides, carried, path, Hoist.warm(hot, k))
    == Hoist.walk(r2, self, wides, carried, path, Hoist.warm(hot, k)) : List<&2, F.Finding>}
  {List.concat(&2, F.Finding, [Hoist.call_table(Hoist.warm(hot, k), String.eq(o, "("),
    D1.inert.keep(D1.inert.blanks(k), t), D1.inert.node(kids), self, wides, carried, path),
    Hoist.walk(D1.inert.node(kids), self, wides, carried, path, Hoist.warm(hot, k)),
    Hoist.walk(D1.inert.node(r2), self, wides, carried, path, Hoist.warm(hot, k))])
    == List.concat(&2, F.Finding, [Hoist.call_table(Hoist.warm(hot, k), String.eq(o, "("), t, kids, self, wides,
      carried, path), Hoist.walk(kids, self, wides, carried, path, Hoist.warm(hot, k)),
      Hoist.walk(r2, self, wides, carried, path, Hoist.warm(hot, k))]) : List<&2, F.Finding>}

def inert.hoist.walk_lg(k, t, o, kids, r2, self, wides, carried, path, hot, ef, ek, ik, ir):
  +w = Hoist.warm(hot, k)
  inert.cat3(Hoist.call_table(w, String.eq(o, "("), D1.inert.keep(D1.inert.blanks(k), t), D1.inert.node(kids),
    self, wides,
    carried, path), Hoist.call_table(w, String.eq(o, "("), t, kids, self, wides, carried, path),
    Hoist.walk(D1.inert.node(kids), self, wides, carried, path, w), Hoist.walk(kids, self, wides, carried, path, w),
    Hoist.walk(D1.inert.node(r2), self, wides, carried, path, w), Hoist.walk(r2, self, wides, carried, path, w),
    inert.hoist.call_table(w, String.eq(o, "("), D1.inert.blanks(k), t, kids, self, wides, carried, path, ef, ek),
    ik, ir)

# a case arm read that way: hot as it was, and its pattern, body and the rest
# walked as they were
law inert.hoist.walk_case:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +hot: Bool
  for +es: {D1.inert.marked(self) == False{} : Bool}
  for +eb: {D1.inert.ok(body) == True{} : Bool}
  for ik: {Hoist.walk(D1.inert.node(kids), self, wides, carried, path, False{})
    == Hoist.walk(kids, self, wides, carried, path, False{}) : List<&2, F.Finding>}
  for ib: {Hoist.walk(D1.inert.node(body), self, wides, carried, path, Bool.and(hot,
    Calls.calls(D1.inert.node(body), self)))
    == Hoist.walk(body, self, wides, carried, path, Bool.and(hot, Calls.calls(D1.inert.node(body),
      self))) : List<&2, F.Finding>}
  for ir: {Hoist.walk(D1.inert.node(rest), self, wides, carried, path, hot) == Hoist.walk(rest, self, wides,
    carried, path, hot)
    : List<&2, F.Finding>}
  {List.concat(&2, F.Finding, [Hoist.walk(D1.inert.node(kids), self, wides, carried, path, False{}),
    Hoist.walk(D1.inert.node(body), self, wides, carried, path, Bool.and(hot, Calls.calls(D1.inert.node(body),
      self))),
    Hoist.walk(D1.inert.node(rest), self, wides, carried, path, hot)])
    == List.concat(&2, F.Finding, [Hoist.walk(kids, self, wides, carried, path, False{}),
      Hoist.walk(body, self, wides, carried, path, Bool.and(hot, Calls.calls(body, self))),
      Hoist.walk(rest, self, wides, carried, path, hot)]) : List<&2, F.Finding>}

def inert.hoist.walk_case(kids, body, rest, self, wides, carried, path, hot, es, eb, ik, ib, ir):
  +arm = Bool.and(hot, Calls.calls(D1.inert.node(body), self))
  +lhs = List.concat(&2, F.Finding, [Hoist.walk(D1.inert.node(kids), self, wides, carried, path, False{}),
    Hoist.walk(D1.inert.node(body), self, wides, carried, path, arm), Hoist.walk(D1.inert.node(rest), self, wides,
      carried, path, hot)])
  %inert.calls(body, self, es, eb) : {lhs == List.concat(&2, F.Finding, [Hoist.walk(kids, self, wides, carried, path,
    False{}), Hoist.walk(body, self, wides, carried, path, Bool.and(hot, _)), Hoist.walk(rest, self, wides, carried,
    path, hot)]) : List<&2, F.Finding>}
  inert.cat3(Hoist.walk(D1.inert.node(kids), self, wides, carried, path, False{}), Hoist.walk(kids, self, wides,
    carried, path,
    False{}), Hoist.walk(D1.inert.node(body), self, wides, carried, path, arm), Hoist.walk(body, self, wides,
      carried, path, arm),
    Hoist.walk(D1.inert.node(rest), self, wides, carried, path, hot), Hoist.walk(rest, self, wides, carried, path,
      hot), ik, ib, ir)

# any other statement read that way: its let, its kids, body and the rest
# walked as they were
law inert.hoist.walk_st:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +hot: Bool
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  for +eb: {D1.inert.ok(body) == True{} : Bool}
  for +er: {D1.inert.ok(rest) == True{} : Bool}
  for ik: {Hoist.walk(D1.inert.node(kids), self, wides, carried, path, hot) == Hoist.walk(kids, self, wides,
    carried, path, hot)
    : List<&2, F.Finding>}
  for ib: {Hoist.walk(D1.inert.node(body), self, wides, carried, path, hot) == Hoist.walk(body, self, wides,
    carried, path, hot)
    : List<&2, F.Finding>}
  for ir: {Hoist.walk(D1.inert.node(rest), self, wides, carried, path, hot) == Hoist.walk(rest, self, wides,
    carried, path, hot)
    : List<&2, F.Finding>}
  {List.concat(&2, F.Finding, [Hoist.let_hit(hot, D1.inert.node(kids), D1.inert.node(body), D1.inert.node(rest),
    self, wides, carried, path),
    Hoist.walk(D1.inert.node(kids), self, wides, carried, path, hot), Hoist.walk(D1.inert.node(body), self, wides,
      carried, path, hot),
    Hoist.walk(D1.inert.node(rest), self, wides, carried, path, hot)])
    == List.concat(&2, F.Finding, [Hoist.let_hit(hot, kids, body, rest, self, wides, carried, path),
      Hoist.walk(kids, self, wides, carried, path, hot), Hoist.walk(body, self, wides, carried, path, hot),
      Hoist.walk(rest, self, wides, carried, path, hot)]) : List<&2, F.Finding>}

def inert.hoist.walk_st(kids, body, rest, self, wides, carried, path, hot, ek, eb, er, ik, ib, ir):
  inert.hoist.cat4(Hoist.let_hit(hot, D1.inert.node(kids), D1.inert.node(body), D1.inert.node(rest), self,
    wides, carried, path),
    Hoist.let_hit(hot, kids, body, rest, self, wides, carried, path),
    Hoist.walk(D1.inert.node(kids), self, wides, carried, path, hot), Hoist.walk(kids, self, wides, carried, path,
      hot),
    Hoist.walk(D1.inert.node(body), self, wides, carried, path, hot), Hoist.walk(body, self, wides, carried, path,
      hot),
    Hoist.walk(D1.inert.node(rest), self, wides, carried, path, hot), Hoist.walk(rest, self, wides, carried, path,
      hot),
    inert.hoist.let_hit(hot, kids, body, rest, self, wides, carried, path, ek, eb, er), ik, ib, ir)

# hoist's walk reads no string: a string names no builder, no get or set, no
# carried parameter and no let, and a table never starts with one
law inert.hoist.walk:
  for nn: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +hot: Bool
  for +es: {D1.inert.marked(self) == False{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Hoist.walk(D1.inert.node(nn), self, wides, carried, path, hot) == Hoist.walk(nn, self, wides, carried, path,
    hot) : List<&2, F.Finding>}

def inert.hoist.walk(nn, self, wides, carried, path, hot, es, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{go, +kids, +gcl}:
                      match go:
                        case Lex.Tok{+gk, +o, +gl, +gc}:
                          +lf = {Tree.Leaf{Lex.Tok{k, t, l, c}} : Tree.Node}
                          +gp = {Tree.Group{Lex.Tok{gk, o, gl, gc}, kids, gcl} : Tree.Node}
                          +eg = inert.ok_t(lf, Tree.NCons{gp, r2}, e)
                          inert.hoist.walk_lg(k, t, o, kids, r2, self, wides, carried, path, hot,
                            inert.ok_h(lf, Tree.NCons{gp, r2}, e), inert.ok_h(gp, r2, eg),
                            inert.hoist.walk(kids, self, wides, carried, path, Hoist.warm(hot, k), es, inert.ok_h(gp,
                              r2,
                              eg)),
                            inert.hoist.walk(r2, self, wides, carried, path, Hoist.warm(hot, k), es, inert.ok_t(gp, r2,
                              eg)))
                    case Tree.Leaf{x}:
                      inert.hoist.walk(rest, self, wides, carried, path, Hoist.warm(hot, k), es,
                        inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.Stmt{x, y, z}:
                      inert.hoist.walk(rest, self, wides, carried, path, Hoist.warm(hot, k), es,
                        inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NNil{}:
                      inert.hoist.walk(rest, self, wides, carried, path, Hoist.warm(hot, k), es,
                        inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NCons{x, y}:
                      inert.hoist.walk(rest, self, wides, carried, path, Hoist.warm(hot, k), es,
                        inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Leaf{x}:
                  inert.hoist.walk(rest, self, wides, carried, path, Hoist.warm(hot, k), es,
                    inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Group{x, y, z}:
                  inert.hoist.walk(rest, self, wides, carried, path, Hoist.warm(hot, k), es,
                    inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Stmt{x, y, z}:
                  inert.hoist.walk(rest, self, wides, carried, path, Hoist.warm(hot, k), es,
                    inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.NNil{}:
                  inert.hoist.walk(rest, self, wides, carried, path, Hoist.warm(hot, k), es,
                    inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
        case Tree.Group{+o, +kids, +cl}:
          inert.cat2(Hoist.walk(D1.inert.node(kids), self, wides, carried, path, hot), Hoist.walk(kids, self, wides,
            carried, path,
            hot), Hoist.walk(D1.inert.node(rest), self, wides, carried, path, hot), Hoist.walk(rest, self, wides,
              carried, path, hot),
            inert.hoist.walk(kids, self, wides, carried, path, hot, es, inert.ok_h(Tree.Group{o, kids, cl}, rest, e)),
            inert.hoist.walk(rest, self, wides, carried, path, hot, es, inert.ok_t(Tree.Group{o, kids, cl}, rest, e)))
        case Tree.Stmt{sk, +kids, +body}:
          match sk:
            case Tree.SDef{}:
              +es2 = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +er = M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              inert.hoist.walk_st(kids, body, rest, self, wides, carried, path, hot, ek, eb, er,
                inert.hoist.walk(kids, self, wides, carried, path, hot, es, ek),
                inert.hoist.walk(body, self, wides, carried, path, hot, es, eb),
                inert.hoist.walk(rest, self, wides, carried, path, hot, es, er))
            case Tree.SType{}:
              +es2 = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +er = M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              inert.hoist.walk_st(kids, body, rest, self, wides, carried, path, hot, ek, eb, er,
                inert.hoist.walk(kids, self, wides, carried, path, hot, es, ek),
                inert.hoist.walk(body, self, wides, carried, path, hot, es, eb),
                inert.hoist.walk(rest, self, wides, carried, path, hot, es, er))
            case Tree.SLaw{}:
              +es2 = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +er = M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              inert.hoist.walk_st(kids, body, rest, self, wides, carried, path, hot, ek, eb, er,
                inert.hoist.walk(kids, self, wides, carried, path, hot, es, ek),
                inert.hoist.walk(body, self, wides, carried, path, hot, es, eb),
                inert.hoist.walk(rest, self, wides, carried, path, hot, es, er))
            case Tree.SImport{}:
              +es2 = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +er = M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              inert.hoist.walk_st(kids, body, rest, self, wides, carried, path, hot, ek, eb, er,
                inert.hoist.walk(kids, self, wides, carried, path, hot, es, ek),
                inert.hoist.walk(body, self, wides, carried, path, hot, es, eb),
                inert.hoist.walk(rest, self, wides, carried, path, hot, es, er))
            case Tree.SCase{}:
              +es2 = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +er = M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              inert.hoist.walk_case(kids, body, rest, self, wides, carried, path, hot, es, eb,
                inert.hoist.walk(kids, self, wides, carried, path, False{}, es, ek),
                inert.hoist.walk(body, self, wides, carried, path, Bool.and(hot, Calls.calls(D1.inert.node(body),
                  self)), es, eb),
                inert.hoist.walk(rest, self, wides, carried, path, hot, es, er))
            case Tree.SFor{}:
              +es2 = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +er = M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              inert.hoist.walk_st(kids, body, rest, self, wides, carried, path, hot, ek, eb, er,
                inert.hoist.walk(kids, self, wides, carried, path, hot, es, ek),
                inert.hoist.walk(body, self, wides, carried, path, hot, es, eb),
                inert.hoist.walk(rest, self, wides, carried, path, hot, es, er))
            case Tree.SLet{}:
              +es2 = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +er = M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              inert.hoist.walk_st(kids, body, rest, self, wides, carried, path, hot, ek, eb, er,
                inert.hoist.walk(kids, self, wides, carried, path, hot, es, ek),
                inert.hoist.walk(body, self, wides, carried, path, hot, es, eb),
                inert.hoist.walk(rest, self, wides, carried, path, hot, es, er))
            case Tree.STerm{}:
              +es2 = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +er = M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              inert.hoist.walk_st(kids, body, rest, self, wides, carried, path, hot, ek, eb, er,
                inert.hoist.walk(kids, self, wides, carried, path, hot, es, ek),
                inert.hoist.walk(body, self, wides, carried, path, hot, es, eb),
                inert.hoist.walk(rest, self, wides, carried, path, hot, es, er))
        case Tree.NNil{}: inert.hoist.walk(rest, self, wides, carried, path, hot, es, e)
        case Tree.NCons{x, y}:
          inert.hoist.walk(rest, self, wides, carried, path, hot, es, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# hoist over the defs read that way reports what it reports over the defs
law inert.hoist.go:
  for ds: List<&2, Calls.Def>
  for +wide: List<&2, String>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  for +e: {inert.dok(ds) == True{} : Bool}
  {Hoist.check.go(inert.defs(ds), wide, path, acc) == Hoist.check.go(ds, wide, path, acc) : List<&2, F.Finding>}

def inert.hoist.go(ds, wide, path, acc, e):
  match ds:
    case Nil{}: {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +en = inert.dok.head(name, sig, body, rest, e)
      +eb = inert.dok.body(name, sig, body, rest, e)
      +ib = D1.inert.node(body)
      +isg = D1.inert.node(sig)
      +cr = Hoist.carried(isg, ib, name)
      +lst = Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Calls.calls(ib, name), Bool.not(Calls.exempt(path,
        isg)))), [],
        _u => Hoist.walk(ib, name, wide, cr, path, True{}))
      %inert.hoist.carried(sig, body, name, en, eb) : {Hoist.check.go(inert.defs(rest), wide, path, lst <> acc)
        == Hoist.check.go(rest, wide, path, Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Calls.calls(body, name),
          Bool.not(Calls.exempt(path, sig)))), [], _u => Hoist.walk(body, name, wide, _, path,
            True{})) <> acc) : List<&2, F.Finding>}
      %inert.stop(Bool.not(Bool.and(Calls.calls(ib, name), Bool.not(Calls.exempt(path, isg)))),
        Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))),
        Hoist.walk(ib, name, wide, cr, path, True{}), Hoist.walk(body, name, wide, cr, path, True{}),
        inert.gate(path, name, sig, body, en, eb), inert.hoist.walk(body, name, wide, cr, path, True{}, en, eb)) :
        {Hoist.check.go(inert.defs(rest), wide, path, lst <> acc) == Hoist.check.go(rest, wide, path,
          _ <> acc) : List<&2, F.Finding>}
      inert.hoist.go(rest, wide, path, lst <> acc, inert.dok.rest(name, sig, body, rest, e))

# hoist over the defs read that way, their wide tables read that way too
law inert.hoist.all:
  for +ds: List<&2, Calls.Def>
  for +path: String
  for +e: {inert.dok(ds) == True{} : Bool}
  {Hoist.check.go(inert.defs(ds), Hoist.wide_defs(inert.defs(ds), []), path, [])
    == Hoist.check.go(ds, Hoist.wide_defs(ds, []), path, []) : List<&2, F.Finding>}

def inert.hoist.all(ds, path, e):
  %inert.hoist.wide_defs(ds, [], e) : {Hoist.check.go(inert.defs(ds), Hoist.wide_defs(inert.defs(ds), []), path, [])
    == Hoist.check.go(ds, _, path, []) : List<&2, F.Finding>}
  inert.hoist.go(ds, Hoist.wide_defs(inert.defs(ds), []), path, [], e)

def Laws.inert_hoist(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, ok, ok2, e):
  M1.inert.via(Tree.Node, z => Hoist.check.go(Calls.defs(z), Hoist.wide_defs(Calls.defs(z), []), path, []), tree, tree2,
    D1.inert.node(tree), D1.inert.node(tree2),
    inert.lift(z => Hoist.check.go(z, Hoist.wide_defs(z, []), path, []), tree, inert.hoist.all(Calls.defs(tree), path,
      inert.dok.of(tree, ok))),
    inert.lift(z => Hoist.check.go(z, Hoist.wide_defs(z, []), path, []), tree2, inert.hoist.all(Calls.defs(tree2), path,
      inert.dok.of(tree2, ok2))),
    e)

# wrap
# ----

# a token's share of the width reads a string's kind only, and a comment has
# none
law inert.wrap.cost:
  for k: Lex.TokKind
  for +t: String
  {Wrap.check.cost(k, t) == Wrap.check.cost(k, D1.inert.keep(D1.inert.blanks(k), t)) : U32}

def inert.wrap.cost(k, _t):
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

# the width walk reads no comment or string
law inert.wrap.width:
  for ts: List<&2, Lex.Tok>
  for +acc: U32
  for +upto: U32
  for +seen: Bool
  {Wrap.check.width.go(D1.inert.toks(ts), acc, upto, seen) == Wrap.check.width.go(ts, acc, upto, seen) : U32}

def inert.wrap.width(ts, acc, upto, seen):
  match ts:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k, +t, l, c}, +rest}:
      +nx = Wrap.check.add(acc, k, t)
      +co = Wrap.check.is_colon(k)
      %inert.wrap.cost(k, t) : {Wrap.check.width.go(D1.inert.toks(rest), (acc + _ : U32),
        Bool.pick(U32, co, (acc + _ : U32), upto), Bool.or(co, seen))
          == Wrap.check.width.go(rest, nx, Bool.pick(U32, co, nx, upto), Bool.or(co, seen)) : U32}
      inert.wrap.width(rest, nx, Bool.pick(U32, co, nx, upto), Bool.or(co, seen))

# the line test reads kinds only
law inert.wrap.broken:
  for ts: List<&2, Lex.Tok>
  {Wrap.check.broken(D1.inert.toks(ts)) == Wrap.check.broken(ts) : Bool}

def inert.wrap.broken(ts):
  match ts:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k, t, l, c}, +rest}:
      %inert.wrap.broken(rest) : {Lazy.or_else(Lex.is_nl(k), _u => Wrap.check.broken(D1.inert.toks(rest)))
        == Lazy.or_else(Lex.is_nl(k), _u => _) : Bool}
      {==}

# a string moves nothing, whatever the walk's phase: its text is read only
# for the angles a `>` run closes, and a string is no such run
law inert.wrap.str:
  for +wk: Wrap.Walk
  for +t: String
  for +l: U32
  for +c: U32
  for glued: Bool
  {Wrap.check.step_hit(wk, Lex.Tok{Lex.TStr{}, D1.inert.cut(t), l, c}, glued)
    == Wrap.check.step_hit(wk, Lex.Tok{Lex.TStr{}, t, l, c}, glued) : Wrap.Walk}

def inert.wrap.str(wk, _t, _l, _c, _glued):
  match wk:
    case Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans}:
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

# one token of the header moves the walk as it did: a comment moves nothing,
# a string as above, and any other token keeps its text
law inert.wrap.step:
  for k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +wk: Wrap.Walk
  for glued: Bool
  {Wrap.check.step(D1.inert.tok(Lex.Tok{k, t, l, c}), wk, glued) == Wrap.check.step(Lex.Tok{k, t, l, c}, wk, glued)
    : Wrap.Walk}

def inert.wrap.step(k, t, l, c, wk, glued):
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
      inert.wrap.str(wk, t, l, c, glued)
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

# the shape walk reads no comment or string
law inert.wrap.walk:
  for ts: List<&2, Lex.Tok>
  for +wk: Wrap.Walk
  for +glued: Bool
  {Wrap.check.walk(D1.inert.toks(ts), wk, glued) == Wrap.check.walk(ts, wk, glued) : Wrap.Walk}

def inert.wrap.walk(ts, wk, glued):
  match ts:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      +s1 = Wrap.check.step(D1.inert.tok(Lex.Tok{k, t, l, c}), wk, glued)
      +s2 = Wrap.check.step(Lex.Tok{k, t, l, c}, wk, glued)
      Equal.trans(Wrap.Walk, Wrap.check.walk(D1.inert.toks(rest), s1, Lex.is_name(k)),
        Wrap.check.walk(rest, s1, Lex.is_name(k)), Wrap.check.walk(rest, s2, Lex.is_name(k)),
        inert.wrap.walk(rest, s1, Lex.is_name(k)),
        Equal.cong(Wrap.Walk, Wrap.Walk, w => Wrap.check.walk(rest, w, Lex.is_name(k)), s1, s2,
          inert.wrap.step(k, t, l, c, wk, glued)))

# a header, broken or not, is judged alike with its comments and strings cut
law inert.wrap.header:
  for b: Bool
  for +ts: List<&2, Lex.Tok>
  for +line: U32
  for +path: String
  for +more: List<&2, F.Finding>
  {Wrap.check.header(b, line, D1.inert.toks(ts), path, more) == Wrap.check.header(b, line, ts, path, more)
    : List<&2, F.Finding>}

def inert.wrap.header(b, ts, line, path, more):
  match b:
    case True{}:
      Equal.cong(Wrap.Walk, List<&2, F.Finding>, wk => Wrap.check.place(Wrap.check.jam_span(wk),
        Wrap.check.empty_span(wk), Wrap.check.shut_span(wk), Wrap.check.loose_span(wk), line, path, more),
        Wrap.check.walk(D1.inert.toks(ts), Wrap.check.start(), False{}),
        Wrap.check.walk(ts, Wrap.check.start(), False{}), inert.wrap.walk(ts, Wrap.check.start(), False{}))
    case False{}:
      Equal.cong(U32, List<&2, F.Finding>, ww => Lazy.stop(List<&2, F.Finding>, U32.is_gt(ww, 120),
        F.Finding{path, line, 120, 0, "wrap",
          "This def header is longer than 120 characters; wrap it with one parameter per line."} <> more,
        _u => more), Wrap.check.width.go(D1.inert.toks(ts), 0, 0, False{}), Wrap.check.width.go(ts, 0, 0, False{}),
        inert.wrap.width(ts, 0, 0, False{}))

# a def header's tokens are judged alike with their comments and strings cut
law inert.wrap.lexed:
  for +ts: List<&2, Lex.Tok>
  for +line: U32
  for +path: String
  for +more: List<&2, F.Finding>
  {Wrap.check.lexed(line, D1.inert.toks(ts), path, more) == Wrap.check.lexed(line, ts, path, more)
    : List<&2, F.Finding>}

def inert.wrap.lexed(ts, line, path, more):
  %Equal.sym(Bool, Wrap.check.broken(D1.inert.toks(ts)), Wrap.check.broken(ts), inert.wrap.broken(ts)) :
    {Wrap.check.header(_, line, D1.inert.toks(ts), path, more)
    == Wrap.check.header(Wrap.check.broken(ts), line, ts, path, more) : List<&2, F.Finding>}
  inert.wrap.header(Wrap.check.broken(ts), ts, line, path, more)

# one item as wrap reads it: its kind and line, and its header's tokens
def inert.wrap.head(
  it: Outline.Item,
  ts: List<&2, Lex.Tok>,
  +path: String,
  +more: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  match it:
    case Outline.Item{kk, _n, +line, _s, _d, _p}:
      Lazy.stop(List<&2, F.Finding>, Bool.not(Outline.is_def(kk)), more, _u => Wrap.check.lexed(line, ts, path, more))

# wrap over the items read that way: each item with its header's tokens
def inert.wrap.go(
  hs: List<&2, Outline.Item>,
  ss: List<&2, List<&2, Lex.Tok>>,
  +path: String
) -> List<&2, F.Finding>:
  match hs ss:
    case Nil{} ss:
      Nil{}
    case Con{h, t} Nil{}:
      Nil{}
    case Con{h, t} Con{ts, st}:
      inert.wrap.head(h, ts, path, inert.wrap.go(t, st, path))

# wrap's walk over the items is its walk over them read that way
law inert.wrap.items:
  for items: List<&2, Outline.Item>
  for +path: String
  {Wrap.check.go(items, path) == inert.wrap.go(Laws.inert.items(items), Laws.inert.sigs(items), path)
    : List<&2, F.Finding>}

def inert.wrap.items(items, path):
  match items:
    case Nil{}:
      {==}
    case Con{Outline.Item{+kk, n, +line, +sig, d, p}, +rest}:
      +more = Wrap.check.go(rest, path)
      +ts = Lex.tokens(sig)
      %inert.wrap.items(rest, path) : {Lazy.stop(List<&2, F.Finding>, Bool.not(Outline.is_def(kk)), more,
        _u => Wrap.check.lexed(line, ts, path, more))
          == Lazy.stop(List<&2, F.Finding>, Bool.not(Outline.is_def(kk)), _,
            _u => Wrap.check.lexed(line, D1.inert.toks(ts), path, _)) : List<&2, F.Finding>}
      %Equal.sym(List<&2, F.Finding>, Wrap.check.lexed(line, D1.inert.toks(ts), path, more),
        Wrap.check.lexed(line, ts, path, more), inert.wrap.lexed(ts, line, path, more)) :
        {Lazy.stop(List<&2, F.Finding>, Bool.not(Outline.is_def(kk)), more,
          _u => Wrap.check.lexed(line, ts, path, more))
            == Lazy.stop(List<&2, F.Finding>, Bool.not(Outline.is_def(kk)), more, _u => _) : List<&2, F.Finding>}
      {==}

def Laws.inert_wrap(path, _text, _toks, _tree, _bound, items, _text2, _toks2, _tree2, _bound2, items2, ei, es):
  +i1 = Laws.inert.items(items)
  +s1 = Laws.inert.sigs(items)
  %Equal.sym(List<&2, F.Finding>, Wrap.check.go(items, path), inert.wrap.go(i1, s1, path),
    inert.wrap.items(items, path)) : {_ == Wrap.check.go(items2, path) : List<&2, F.Finding>}
  %Equal.sym(List<&2, F.Finding>, Wrap.check.go(items2, path),
    inert.wrap.go(Laws.inert.items(items2), Laws.inert.sigs(items2), path), inert.wrap.items(items2, path)) :
    {inert.wrap.go(i1, s1, path) == _ : List<&2, F.Finding>}
  %ei : {inert.wrap.go(i1, s1, path) == inert.wrap.go(_, Laws.inert.sigs(items2), path) : List<&2, F.Finding>}
  %es : {inert.wrap.go(i1, s1, path) == inert.wrap.go(i1, _, path) : List<&2, F.Finding>}
  {==}

# scan reads no string: a string is never a callee or a lone name, so each
# walk and each call reads the same over a tree read that way

# a lone name read that way is the name it was
law inert.scan.name_tok:
  for tok: Lex.Tok
  {Scan.name_tok(D1.inert.tok(tok)) == Scan.name_tok(tok) : Maybe<&2, String>}

def inert.scan.name_tok(tok):
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

# an argument read that way is the lone name it was
law inert.scan.name_of:
  for nn: Tree.Node
  {Scan.name_of(D1.inert.node(nn)) == Scan.name_of(nn) : Maybe<&2, String>}

def inert.scan.name_of(nn):
  match nn:
    case Tree.NCons{h, r}:
      match h:
        case Tree.Leaf{tok}:
          match r:
            case Tree.NNil{}:
              inert.scan.name_tok(tok)
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

# the walked argument of arguments read that way is the lone name it was
law inert.scan.arg_name:
  for +as: List<&2, Tree.Node>
  for +at: Nat
  {Scan.name_of(Calls.arg(inert.nodes(as), at)) == Scan.name_of(Calls.arg(as, at)) : Maybe<&2, String>}

def inert.scan.arg_name(as, at):
  %Equal.sym(Tree.Node, Calls.arg(inert.nodes(as), at), D1.inert.node(Calls.arg(as, at)), inert.arg(as, at)) :
    {Scan.name_of(_) == Scan.name_of(Calls.arg(as, at)) : Maybe<&2, String>}
  inert.scan.name_of(Calls.arg(as, at))

# the first carried name among arguments read that way is the one it was
law inert.scan.found:
  for ss: List<&2, Nat>
  for +as: List<&2, Tree.Node>
  for +carried: List<&2, String>
  {Scan.found(ss, inert.nodes(as), carried) == Scan.found(ss, as, carried) : Maybe<&2, String>}

def inert.scan.found(ss, as, carried):
  match ss:
    case Nil{}:
      {==}
    case Con{+at, +rest}:
      %inert.scan.arg_name(as, at) : {Scan.first(Scan.keep_in(Scan.name_of(Calls.arg(inert.nodes(as), at)), carried),
        Scan.found(rest, inert.nodes(as), carried)) == Scan.first(Scan.keep_in(_, carried), Scan.found(rest, as,
          carried)) : Maybe<&2, String>}
      %inert.scan.found(rest, as, carried) : {Scan.first(Scan.keep_in(Scan.name_of(Calls.arg(inert.nodes(as), at)),
        carried), Scan.found(rest, inert.nodes(as), carried)) == Scan.first(Scan.keep_in(Scan.name_of(Calls.arg(
          inert.nodes(as), at)), carried), _) : Maybe<&2, String>}
      {==}

# a named call whose arguments are read that way reports what it did
law inert.scan.on_name:
  for +hot: Bool
  for +open: Bool
  for +tt: String
  for +line: U32
  for +col: U32
  for +kids: Tree.Node
  for +self: String
  for +ws: List<&2, Scan.Walk>
  for +carried: List<&2, String>
  for +lead: String
  for +path: String
  {Scan.on_name(hot, open, tt, line, col, D1.inert.node(kids), self, ws, carried, lead, path)
    == Scan.on_name(hot, open, tt, line, col, kids, self, ws, carried, lead, path) : List<&2, F.Finding>}

def inert.scan.on_name(hot, open, tt, line, col, kids, self, ws, carried, lead, path):
  +g = Bool.not(Bool.and(hot, Bool.and(open, Bool.not(String.eq(tt, self)))))
  +lhs = Scan.on_name(hot, open, tt, line, col, D1.inert.node(kids), self, ws, carried, lead, path)
  %inert.scan.found(Scan.slots(tt, ws), Calls.args(kids), carried) : {lhs == Lazy.stop(List<&2, F.Finding>, g, [],
    _u => Scan.cite(_, tt, line, col, self, lead, path)) : List<&2, F.Finding>}
  %inert.args(kids) : {lhs == Lazy.stop(List<&2, F.Finding>, g, [],
    _u => Scan.cite(Scan.found(Scan.slots(tt, ws), _, carried), tt, line, col, self, lead, path))
      : List<&2, F.Finding>}
  {==}

# a call read that way reports what it did: only a name is a callee, and a
# name is never cut
law inert.scan.call_hit:
  for kk: Lex.TokKind
  for +hot: Bool
  for +open: Bool
  for +tt: String
  for +line: U32
  for +col: U32
  for +kids: Tree.Node
  for +self: String
  for +ws: List<&2, Scan.Walk>
  for +carried: List<&2, String>
  for +lead: String
  for +path: String
  {Scan.call_hit(kk, hot, open, D1.inert.keep(D1.inert.blanks(kk), tt), line, col, D1.inert.node(kids), self,
    ws, carried, lead, path)
    == Scan.call_hit(kk, hot, open, tt, line, col, kids, self, ws, carried, lead, path) : List<&2, F.Finding>}

def inert.scan.call_hit(kk, hot, open, tt, line, col, kids, self, ws, carried, lead, path):
  match kk:
    case Lex.TName{}:
      inert.scan.on_name(hot, open, tt, line, col, kids, self, ws, carried, lead, path)
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      inert.scan.on_name(hot, open, tt, line, col, kids, self, ws, carried, lead, path)
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

# a name then a group read that way: its call, the group and the rest walked
# as they were
law inert.scan.walk_lg:
  for +k: Lex.TokKind
  for +t: String
  for +o: String
  for +l: U32
  for +c: U32
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +self: String
  for +ws: List<&2, Scan.Walk>
  for +carried: List<&2, String>
  for +lead: String
  for +path: String
  for +hot: Bool
  for ik: {Scan.walk(D1.inert.node(kids), self, ws, carried, lead, path, Hoist.warm(hot, k)) == Scan.walk(kids, self,
      ws, carried, lead, path, Hoist.warm(hot, k)) : List<&2, F.Finding>}
  for ir: {Scan.walk(D1.inert.node(r2), self, ws, carried, lead, path, Hoist.warm(hot, k)) == Scan.walk(r2, self, ws,
      carried, lead, path, Hoist.warm(hot, k)) : List<&2, F.Finding>}
  {List.concat(&2, F.Finding, [Scan.call_hit(k, Hoist.warm(hot, k), String.eq(o, "("),
      D1.inert.keep(D1.inert.blanks(k), t),
    l, c, D1.inert.node(kids), self, ws, carried, lead, path), Scan.walk(D1.inert.node(kids), self, ws, carried,
        lead, path, Hoist.warm(hot, k)), Scan.walk(D1.inert.node(r2), self, ws, carried, lead, path, Hoist.warm(hot,
        k))])
    == List.concat(&2, F.Finding, [Scan.call_hit(k, Hoist.warm(hot, k), String.eq(o, "("), t, l, c, kids, self, ws,
        carried, lead,
      path), Scan.walk(kids, self, ws, carried, lead, path, Hoist.warm(hot,
          k)), Scan.walk(r2, self, ws, carried, lead, path, Hoist.warm(hot, k))]) : List<&2, F.Finding>}

def inert.scan.walk_lg(k, t, o, l, c, kids, r2, self, ws, carried, lead, path, hot, ik, ir):
  +w = Hoist.warm(hot, k)
  inert.cat3(Scan.call_hit(k, w, String.eq(o, "("), D1.inert.keep(D1.inert.blanks(k), t), l, c,
      D1.inert.node(kids), self,
    ws, carried, lead, path), Scan.call_hit(k, w, String.eq(o, "("), t, l, c, kids, self, ws, carried, lead, path),
    Scan.walk(D1.inert.node(kids), self, ws, carried, lead, path, w), Scan.walk(kids, self, ws, carried, lead, path,
        w),
    Scan.walk(D1.inert.node(r2), self, ws, carried, lead, path, w), Scan.walk(r2, self, ws, carried, lead, path, w),
    inert.scan.call_hit(k, w, String.eq(o, "("), t, l, c, kids, self, ws, carried, lead, path), ik, ir)

# a case arm read that way: hot as it was, and its pattern, body and the rest
# walked as they were
law inert.scan.walk_case:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +ws: List<&2, Scan.Walk>
  for +carried: List<&2, String>
  for +lead: String
  for +path: String
  for +hot: Bool
  for +es: {D1.inert.marked(self) == False{} : Bool}
  for +eb: {D1.inert.ok(body) == True{} : Bool}
  for ik: {Scan.walk(D1.inert.node(kids), self, ws, carried, lead, path, False{}) == Scan.walk(kids, self, ws,
      carried, lead, path, False{}) : List<&2, F.Finding>}
  for ib: {Scan.walk(D1.inert.node(body), self, ws, carried, lead, path, Bool.and(hot,
      Calls.calls(D1.inert.node(body),
      self))) == Scan.walk(body, self, ws, carried, lead, path, Bool.and(hot, Calls.calls(D1.inert.node(body),
          self))) : List<&2, F.Finding>}
  for ir: {Scan.walk(D1.inert.node(rest), self, ws, carried, lead, path, hot) == Scan.walk(rest, self, ws, carried,
      lead, path, hot) : List<&2, F.Finding>}
  {List.concat(&2, F.Finding, [Scan.walk(D1.inert.node(kids), self, ws, carried, lead, path, False{}),
      Scan.walk(D1.inert.node(body), self, ws, carried, lead, path, Bool.and(hot, Calls.calls(D1.inert.node(body),
      self))), Scan.walk(D1.inert.node(rest), self, ws, carried, lead, path, hot)])
    == List.concat(&2, F.Finding, [Scan.walk(kids, self, ws, carried, lead, path, False{}), Scan.walk(body, self, ws,
        carried, lead, path, Bool.and(hot, Calls.calls(body,
        self))), Scan.walk(rest, self, ws, carried, lead, path, hot)])
      : List<&2, F.Finding>}

def inert.scan.walk_case(kids, body, rest, self, ws, carried, lead, path, hot, es, eb, ik, ib, ir):
  +arm = Bool.and(hot, Calls.calls(D1.inert.node(body), self))
  +lhs = List.concat(&2, F.Finding, [Scan.walk(D1.inert.node(kids), self, ws, carried, lead, path, False{}),
      Scan.walk(D1.inert.node(body), self, ws, carried, lead, path, arm), Scan.walk(D1.inert.node(rest), self, ws,
      carried, lead, path, hot)])
  %inert.calls(body, self, es, eb) : {lhs == List.concat(&2, F.Finding, [Scan.walk(kids, self, ws, carried, lead, path,
      False{}),
    Scan.walk(body, self, ws, carried, lead, path, Bool.and(hot, _)), Scan.walk(rest, self, ws, carried, lead, path,
        hot)]) : List<&2, F.Finding>}
  inert.cat3(Scan.walk(D1.inert.node(kids), self, ws, carried, lead, path, False{}), Scan.walk(kids, self, ws,
      carried, lead, path, False{}), Scan.walk(D1.inert.node(body), self, ws, carried, lead, path, arm),
          Scan.walk(body, self, ws, carried, lead, path, arm),
    Scan.walk(D1.inert.node(rest), self, ws, carried, lead, path, hot), Scan.walk(rest, self, ws, carried, lead,
        path, hot), ik, ib, ir)

# scan's walk reads no string: a string is never a callee or a lone name
law inert.scan.walk:
  for nn: Tree.Node
  for +self: String
  for +ws: List<&2, Scan.Walk>
  for +carried: List<&2, String>
  for +lead: String
  for +path: String
  for +hot: Bool
  for +es: {D1.inert.marked(self) == False{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Scan.walk(D1.inert.node(nn), self, ws, carried, lead, path, hot) == Scan.walk(nn, self, ws, carried, lead, path,
      hot) : List<&2, F.Finding>}

def inert.scan.walk(nn, self, ws, carried, lead, path, hot, es, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{go, +kids, +gcl}:
                      match go:
                        case Lex.Tok{+gk, +o, +gl, +gc}:
                          +lf = {Tree.Leaf{Lex.Tok{k, t, l, c}} : Tree.Node}
                          +gp = {Tree.Group{Lex.Tok{gk, o, gl, gc}, kids, gcl} : Tree.Node}
                          +eg = inert.ok_t(lf, Tree.NCons{gp, r2}, e)
                          inert.scan.walk_lg(k, t, o, l, c, kids, r2, self, ws, carried, lead, path, hot,
                            inert.scan.walk(kids, self, ws, carried, lead, path, Hoist.warm(hot, k), es, inert.ok_h(gp,
                                r2, eg)),
                            inert.scan.walk(r2, self, ws, carried, lead, path, Hoist.warm(hot, k), es, inert.ok_t(gp,
                                r2, eg)))
                    case Tree.Leaf{x}:
                      inert.scan.walk(rest, self, ws, carried, lead, path, Hoist.warm(hot, k), es,
                          inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.Stmt{x, y, z}:
                      inert.scan.walk(rest, self, ws, carried, lead, path, Hoist.warm(hot, k), es,
                          inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NNil{}:
                      inert.scan.walk(rest, self, ws, carried, lead, path, Hoist.warm(hot, k), es,
                          inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NCons{x, y}:
                      inert.scan.walk(rest, self, ws, carried, lead, path, Hoist.warm(hot, k), es,
                          inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Leaf{x}:
                  inert.scan.walk(rest, self, ws, carried, lead, path, Hoist.warm(hot, k), es,
                      inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Group{x, y, z}:
                  inert.scan.walk(rest, self, ws, carried, lead, path, Hoist.warm(hot, k), es,
                      inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Stmt{x, y, z}:
                  inert.scan.walk(rest, self, ws, carried, lead, path, Hoist.warm(hot, k), es,
                      inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.NNil{}:
                  inert.scan.walk(rest, self, ws, carried, lead, path, Hoist.warm(hot, k), es,
                      inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
        case Tree.Group{+o, +kids, +cl}:
          inert.cat2(Scan.walk(D1.inert.node(kids), self, ws, carried, lead, path, hot), Scan.walk(kids, self, ws,
              carried, lead, path, hot), Scan.walk(D1.inert.node(rest), self, ws, carried, lead, path, hot),
                  Scan.walk(rest, self, ws, carried, lead, path, hot),
            inert.scan.walk(kids, self, ws, carried, lead, path, hot, es, inert.ok_h(Tree.Group{o, kids, cl}, rest, e)),
            inert.scan.walk(rest, self, ws, carried, lead, path, hot, es, inert.ok_t(Tree.Group{o, kids, cl}, rest, e)))
        case Tree.Stmt{sk, +kids, +body}:
          match sk:
            case Tree.SDef{}:
              +es2 = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +er = M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              inert.cat3(Scan.walk(D1.inert.node(kids), self, ws, carried, lead, path, hot), Scan.walk(kids, self,
                  ws, carried, lead, path, hot), Scan.walk(D1.inert.node(body), self, ws, carried, lead, path, hot),
                      Scan.walk(body, self, ws, carried, lead, path, hot),
                Scan.walk(D1.inert.node(rest), self, ws, carried, lead, path, hot), Scan.walk(rest, self, ws,
                    carried, lead, path, hot),
                inert.scan.walk(kids, self, ws, carried, lead, path, hot, es, ek), inert.scan.walk(body, self, ws,
                    carried, lead, path, hot, es, eb), inert.scan.walk(rest, self, ws, carried, lead, path, hot, es,
                        er))
            case Tree.SType{}:
              +es2 = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +er = M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              inert.cat3(Scan.walk(D1.inert.node(kids), self, ws, carried, lead, path, hot), Scan.walk(kids, self,
                  ws, carried, lead, path, hot), Scan.walk(D1.inert.node(body), self, ws, carried, lead, path, hot),
                      Scan.walk(body, self, ws, carried, lead, path, hot),
                Scan.walk(D1.inert.node(rest), self, ws, carried, lead, path, hot), Scan.walk(rest, self, ws,
                    carried, lead, path, hot),
                inert.scan.walk(kids, self, ws, carried, lead, path, hot, es, ek), inert.scan.walk(body, self, ws,
                    carried, lead, path, hot, es, eb), inert.scan.walk(rest, self, ws, carried, lead, path, hot, es,
                        er))
            case Tree.SLaw{}:
              +es2 = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +er = M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              inert.cat3(Scan.walk(D1.inert.node(kids), self, ws, carried, lead, path, hot), Scan.walk(kids, self,
                  ws, carried, lead, path, hot), Scan.walk(D1.inert.node(body), self, ws, carried, lead, path, hot),
                      Scan.walk(body, self, ws, carried, lead, path, hot),
                Scan.walk(D1.inert.node(rest), self, ws, carried, lead, path, hot), Scan.walk(rest, self, ws,
                    carried, lead, path, hot),
                inert.scan.walk(kids, self, ws, carried, lead, path, hot, es, ek), inert.scan.walk(body, self, ws,
                    carried, lead, path, hot, es, eb), inert.scan.walk(rest, self, ws, carried, lead, path, hot, es,
                        er))
            case Tree.SImport{}:
              +es2 = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +er = M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              inert.cat3(Scan.walk(D1.inert.node(kids), self, ws, carried, lead, path, hot), Scan.walk(kids, self,
                  ws, carried, lead, path, hot), Scan.walk(D1.inert.node(body), self, ws, carried, lead, path, hot),
                      Scan.walk(body, self, ws, carried, lead, path, hot),
                Scan.walk(D1.inert.node(rest), self, ws, carried, lead, path, hot), Scan.walk(rest, self, ws,
                    carried, lead, path, hot),
                inert.scan.walk(kids, self, ws, carried, lead, path, hot, es, ek), inert.scan.walk(body, self, ws,
                    carried, lead, path, hot, es, eb), inert.scan.walk(rest, self, ws, carried, lead, path, hot, es,
                        er))
            case Tree.SCase{}:
              +es2 = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +er = M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              inert.scan.walk_case(kids, body, rest, self, ws, carried, lead, path, hot, es, eb,
                inert.scan.walk(kids, self, ws, carried, lead, path, False{}, es, ek),
                inert.scan.walk(body, self, ws, carried, lead, path, Bool.and(hot, Calls.calls(D1.inert.node(body),
                    self)), es, eb),
                inert.scan.walk(rest, self, ws, carried, lead, path, hot, es, er))
            case Tree.SFor{}:
              +es2 = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +er = M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              inert.cat3(Scan.walk(D1.inert.node(kids), self, ws, carried, lead, path, hot), Scan.walk(kids, self,
                  ws, carried, lead, path, hot), Scan.walk(D1.inert.node(body), self, ws, carried, lead, path, hot),
                      Scan.walk(body, self, ws, carried, lead, path, hot),
                Scan.walk(D1.inert.node(rest), self, ws, carried, lead, path, hot), Scan.walk(rest, self, ws,
                    carried, lead, path, hot),
                inert.scan.walk(kids, self, ws, carried, lead, path, hot, es, ek), inert.scan.walk(body, self, ws,
                    carried, lead, path, hot, es, eb), inert.scan.walk(rest, self, ws, carried, lead, path, hot, es,
                        er))
            case Tree.SLet{}:
              +es2 = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +er = M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              inert.cat3(Scan.walk(D1.inert.node(kids), self, ws, carried, lead, path, hot), Scan.walk(kids, self,
                  ws, carried, lead, path, hot), Scan.walk(D1.inert.node(body), self, ws, carried, lead, path, hot),
                      Scan.walk(body, self, ws, carried, lead, path, hot),
                Scan.walk(D1.inert.node(rest), self, ws, carried, lead, path, hot), Scan.walk(rest, self, ws,
                    carried, lead, path, hot),
                inert.scan.walk(kids, self, ws, carried, lead, path, hot, es, ek), inert.scan.walk(body, self, ws,
                    carried, lead, path, hot, es, eb), inert.scan.walk(rest, self, ws, carried, lead, path, hot, es,
                        er))
            case Tree.STerm{}:
              +es2 = M1.inert.and_l(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +eb = M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es2)
              +er = M1.inert.and_r(Bool.and(D1.inert.ok(kids), D1.inert.ok(body)), D1.inert.ok(rest), e)
              inert.cat3(Scan.walk(D1.inert.node(kids), self, ws, carried, lead, path, hot), Scan.walk(kids, self,
                  ws, carried, lead, path, hot), Scan.walk(D1.inert.node(body), self, ws, carried, lead, path, hot),
                      Scan.walk(body, self, ws, carried, lead, path, hot),
                Scan.walk(D1.inert.node(rest), self, ws, carried, lead, path, hot), Scan.walk(rest, self, ws,
                    carried, lead, path, hot),
                inert.scan.walk(kids, self, ws, carried, lead, path, hot, es, ek), inert.scan.walk(body, self, ws,
                    carried, lead, path, hot, es, eb), inert.scan.walk(rest, self, ws, carried, lead, path, hot, es,
                        er))
        case Tree.NNil{}:
          inert.scan.walk(rest, self, ws, carried, lead, path, hot, es, e)
        case Tree.NCons{x, y}:
          inert.scan.walk(rest, self, ws, carried, lead, path, hot, es, inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{x, y, z}:
      {==}
    case Tree.Stmt{x, y, z}:
      {==}
    case Tree.NNil{}:
      {==}

# three lists of numbers that read alike join alike
law scan.ncat3:
  for -a1: List<&2, Nat>
  for -a2: List<&2, Nat>
  for -b1: List<&2, Nat>
  for -b2: List<&2, Nat>
  for -c1: List<&2, Nat>
  for -c2: List<&2, Nat>
  for ea: {a1 == a2 : List<&2, Nat>}
  for eb: {b1 == b2 : List<&2, Nat>}
  for ec: {c1 == c2 : List<&2, Nat>}
  {List.concat(&2, Nat, [a1, b1, c1]) == List.concat(&2, Nat, [a2, b2, c2]) : List<&2, Nat>}

def scan.ncat3(a1, _a2, b1, b2, c1, c2, ea, eb, ec):
  %ea : {List.concat(&2, Nat, [a1, b1, c1]) == List.concat(&2, Nat, [_, b2, c2]) : List<&2, Nat>}
  %eb : {List.concat(&2, Nat, [a1, b1, c1]) == List.concat(&2, Nat, [a1, _, c2]) : List<&2, Nat>}
  %ec : {List.concat(&2, Nat, [a1, b1, c1]) == List.concat(&2, Nat, [a1, b1, _]) : List<&2, Nat>}
  {==}

# two lists of numbers that read alike join alike
law scan.ncat2:
  for -a1: List<&2, Nat>
  for -a2: List<&2, Nat>
  for -b1: List<&2, Nat>
  for -b2: List<&2, Nat>
  for ea: {a1 == a2 : List<&2, Nat>}
  for eb: {b1 == b2 : List<&2, Nat>}
  {List.concat(&2, Nat, [a1, b1]) == List.concat(&2, Nat, [a2, b2]) : List<&2, Nat>}

def scan.ncat2(a1, _a2, b1, b2, ea, eb):
  %ea : {List.concat(&2, Nat, [a1, b1]) == List.concat(&2, Nat, [_, b2]) : List<&2, Nat>}
  %eb : {List.concat(&2, Nat, [a1, b1]) == List.concat(&2, Nat, [a1, _]) : List<&2, Nat>}
  {==}

# the parameters at walked arguments read that way are the ones they were
law inert.scan.params_at:
  for ss: List<&2, Nat>
  for +as: List<&2, Tree.Node>
  for +ps: List<&2, String>
  {Scan.params_at(ss, inert.nodes(as), ps) == Scan.params_at(ss, as, ps) : List<&2, Nat>}

def inert.scan.params_at(ss, as, ps):
  match ss:
    case Nil{}:
      {==}
    case Con{+at, +rest}:
      %inert.scan.arg_name(as, at) : {List.append(&2, Nat,
          Scan.opt(Scan.index_in(Scan.name_of(Calls.arg(inert.nodes(as),
        at)), ps)), Scan.params_at(rest, inert.nodes(as), ps)) == List.append(&2, Nat, Scan.opt(Scan.index_in(_, ps)),
          Scan.params_at(rest, as, ps)) : List<&2, Nat>}
      %inert.scan.params_at(rest, as, ps) : {List.append(&2, Nat, Scan.opt(Scan.index_in(Scan.name_of(Calls.arg(
        inert.nodes(as), at)), ps)), Scan.params_at(rest, inert.nodes(as), ps)) == List.append(&2, Nat,
          Scan.opt(Scan.index_in(Scan.name_of(Calls.arg(inert.nodes(as), at)), ps)), _) : List<&2, Nat>}
      {==}

# a named call's walked parameters, its arguments read that way
law inert.scan.pass_name:
  for +open: Bool
  for +tt: String
  for +kids: Tree.Node
  for +ps: List<&2, String>
  for +ws: List<&2, Scan.Walk>
  {Lazy.stop(List<&2, Nat>, Bool.not(open), [], _u => Scan.params_at(Scan.slots(tt, ws),
      Calls.args(D1.inert.node(kids)), ps))
    == Lazy.stop(List<&2, Nat>, Bool.not(open), [], _u => Scan.params_at(Scan.slots(tt, ws), Calls.args(kids),
        ps)) : List<&2, Nat>}

def inert.scan.pass_name(open, tt, kids, ps, ws):
  +lhs = Lazy.stop(List<&2, Nat>, Bool.not(open), [], _u => Scan.params_at(Scan.slots(tt, ws),
      Calls.args(D1.inert.node(kids)), ps))
  %inert.scan.params_at(Scan.slots(tt, ws), Calls.args(kids), ps) : {lhs == Lazy.stop(List<&2, Nat>, Bool.not(open), [],
    _u => _) : List<&2, Nat>}
  %inert.args(kids) : {lhs == Lazy.stop(List<&2, Nat>, Bool.not(open), [], _u => Scan.params_at(Scan.slots(tt, ws), _,
      ps))
    : List<&2, Nat>}
  {==}

# a call read that way passes what it passed: only a name is a callee
law inert.scan.pass_hit:
  for kk: Lex.TokKind
  for +open: Bool
  for +tt: String
  for +kids: Tree.Node
  for +ps: List<&2, String>
  for +ws: List<&2, Scan.Walk>
  {Scan.pass_hit(kk, open, D1.inert.keep(D1.inert.blanks(kk), tt), D1.inert.node(kids), ps, ws)
    == Scan.pass_hit(kk, open, tt, kids, ps, ws) : List<&2, Nat>}

def inert.scan.pass_hit(kk, open, tt, kids, ps, ws):
  match kk:
    case Lex.TName{}:
      inert.scan.pass_name(open, tt, kids, ps, ws)
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      inert.scan.pass_name(open, tt, kids, ps, ws)
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

# what a body read that way passes is what it passed
law inert.scan.passes:
  for nn: Tree.Node
  for +ps: List<&2, String>
  for +ws: List<&2, Scan.Walk>
  {Scan.passes(D1.inert.node(nn), ps, ws) == Scan.passes(nn, ps, ws) : List<&2, Nat>}

def inert.scan.passes(nn, ps, ws):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{go, +kids, +gcl}:
                      match go:
                        case Lex.Tok{+gk, +o, +gl, +gc}:
                          scan.ncat3(Scan.pass_hit(k, String.eq(o, "("), D1.inert.keep(D1.inert.blanks(k), t),
                            D1.inert.node(kids), ps, ws), Scan.pass_hit(k, String.eq(o, "("), t, kids, ps, ws),
                            Scan.passes(D1.inert.node(kids), ps, ws), Scan.passes(kids, ps, ws),
                            Scan.passes(D1.inert.node(r2), ps, ws), Scan.passes(r2, ps, ws),
                            inert.scan.pass_hit(k, String.eq(o, "("), t, kids, ps, ws),
                            inert.scan.passes(kids, ps, ws), inert.scan.passes(r2, ps, ws))
                    case Tree.Leaf{x}:
                      inert.scan.passes(rest, ps, ws)
                    case Tree.Stmt{x, y, z}:
                      inert.scan.passes(rest, ps, ws)
                    case Tree.NNil{}:
                      inert.scan.passes(rest, ps, ws)
                    case Tree.NCons{x, y}:
                      inert.scan.passes(rest, ps, ws)
                case Tree.Leaf{x}:
                  inert.scan.passes(rest, ps, ws)
                case Tree.Group{x, y, z}:
                  inert.scan.passes(rest, ps, ws)
                case Tree.Stmt{x, y, z}:
                  inert.scan.passes(rest, ps, ws)
                case Tree.NNil{}:
                  inert.scan.passes(rest, ps, ws)
        case Tree.Group{o, +kids, cl}:
          scan.ncat2(Scan.passes(D1.inert.node(kids), ps, ws), Scan.passes(kids, ps, ws),
              Scan.passes(D1.inert.node(rest), ps, ws),
            Scan.passes(rest, ps, ws), inert.scan.passes(kids, ps, ws), inert.scan.passes(rest, ps, ws))
        case Tree.Stmt{sk, +kids, +body}:
          scan.ncat3(Scan.passes(D1.inert.node(kids), ps, ws), Scan.passes(kids, ps, ws),
              Scan.passes(D1.inert.node(body), ps, ws),
            Scan.passes(body, ps, ws), Scan.passes(D1.inert.node(rest), ps, ws), Scan.passes(rest, ps, ws),
            inert.scan.passes(kids, ps, ws), inert.scan.passes(body, ps, ws), inert.scan.passes(rest, ps, ws))
        case Tree.NNil{}:
          inert.scan.passes(rest, ps, ws)
        case Tree.NCons{x, y}:
          inert.scan.passes(rest, ps, ws)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{x, y, z}:
      {==}
    case Tree.Stmt{x, y, z}:
      {==}
    case Tree.NNil{}:
      {==}

# a parameter read that way moves as it did
law inert.scan.moves:
  for +pp: Tree.Node
  for +carried: List<&2, String>
  {Scan.moves(D1.inert.node(pp), carried) == Scan.moves(pp, carried) : Bool}

def inert.scan.moves(pp, carried):
  +lhs = Scan.moves(D1.inert.node(pp), carried)
  %inert.is_live(pp) : {lhs == Bool.and(_, Bool.not(List.contains(~String, ~String.eq, carried, Calls.param_name(pp))))
    : Bool}
  %inert.param_name(pp) : {lhs == Bool.and(Calls.is_live(D1.inert.node(pp)), Bool.not(List.contains(~String,
      ~String.eq,
    carried, _))) : Bool}
  {==}

# a parameter read that way is a count or a text as it was
law inert.scan.place:
  for +pp: Tree.Node
  for +ii: Nat
  {Scan.place(D1.inert.node(pp), ii) == Scan.place(pp, ii) : Maybe<&2, Nat>}

def inert.scan.place(pp, ii):
  %inert.type_head(pp, False{}) : {Scan.place(D1.inert.node(pp), ii) == Bool.pick(Maybe<&2, Nat>,
    Bool.or(String.eq(_, "Nat"), String.eq(_, "String")), None{}, Some{ii}) : Maybe<&2, Nat>}
  {==}

# the parameter shrunk, among parameters read that way, sits where it sat
law inert.scan.own.go:
  for ps: List<&2, Tree.Node>
  for +carried: List<&2, String>
  for +ii: Nat
  {Scan.own.go(inert.nodes(ps), carried, ii) == Scan.own.go(ps, carried, ii) : Maybe<&2, Nat>}

def inert.scan.own.go(ps, carried, ii):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      +lhs = Scan.own.go(inert.nodes(p <> rest), carried, ii)
      %inert.scan.moves(p, carried) : {lhs == Lazy.stop(Maybe<&2, Nat>, _, Scan.place(p, ii),
        _u => Scan.own.go(rest, carried, 1n+ii)) : Maybe<&2, Nat>}
      %inert.scan.place(p, ii) : {lhs == Lazy.stop(Maybe<&2, Nat>, Scan.moves(D1.inert.node(p), carried), _,
        _u => Scan.own.go(rest, carried, 1n+ii)) : Maybe<&2, Nat>}
      %inert.scan.own.go(rest, carried, 1n+ii) : {lhs == Lazy.stop(Maybe<&2, Nat>, Scan.moves(D1.inert.node(p),
        carried), Scan.place(D1.inert.node(p), ii), _u => _) : Maybe<&2, Nat>}
      {==}

# the name of the parameter shrunk, among parameters read that way, is the one it was
law inert.scan.lead.go:
  for ps: List<&2, Tree.Node>
  for +carried: List<&2, String>
  {Scan.lead.go(inert.nodes(ps), carried) == Scan.lead.go(ps, carried) : String}

def inert.scan.lead.go(ps, carried):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      +lhs = Scan.lead.go(inert.nodes(p <> rest), carried)
      %inert.scan.moves(p, carried) : {lhs == Lazy.stop(String, _, Calls.param_name(p), _u => Scan.lead.go(rest,
        carried)) : String}
      %inert.param_name(p) : {lhs == Lazy.stop(String, Scan.moves(D1.inert.node(p), carried), _,
          _u => Scan.lead.go(rest,
        carried)) : String}
      %inert.scan.lead.go(rest, carried) : {lhs == Lazy.stop(String, Scan.moves(D1.inert.node(p), carried),
        Calls.param_name(D1.inert.node(p)), _u => _) : String}
      {==}

# a signature read that way has its parameters read that way
law inert.scan.params:
  for +sig: Tree.Node
  {Calls.params(D1.inert.node(sig)) == inert.nodes(Calls.params(sig)) : List<&2, Tree.Node>}

def inert.scan.params(sig):
  %Equal.sym(Tree.Node, Calls.params.of(D1.inert.node(sig)), D1.inert.node(Calls.params.of(sig)),
    inert.params.of(sig)) : {Calls.args(_) == inert.nodes(Calls.params(sig)) : List<&2, Tree.Node>}
  inert.args(Calls.params.of(sig))

# the parameter a def read that way shrinks is the one it shrank
law inert.scan.own:
  for +sig: Tree.Node
  for +body: Tree.Node
  for +name: String
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for +eb: {D1.inert.ok(body) == True{} : Bool}
  {Scan.own(D1.inert.node(sig), D1.inert.node(body), name) == Scan.own(sig, body, name) : Maybe<&2, Nat>}

def inert.scan.own(sig, body, name, en, eb):
  +isg = D1.inert.node(sig)
  +ib = D1.inert.node(body)
  +lhs = Scan.own(isg, ib, name)
  %inert.calls(body, name, en, eb) : {lhs == Lazy.stop(Maybe<&2, Nat>, Bool.not(_), None{},
    _u => Scan.own.go(Calls.params(sig), Hoist.carried(sig, body, name), 0n)) : Maybe<&2, Nat>}
  %inert.hoist.carried(sig, body, name, en, eb) : {lhs == Lazy.stop(Maybe<&2, Nat>, Bool.not(Calls.calls(ib, name)),
    None{}, _u => Scan.own.go(Calls.params(sig), _, 0n)) : Maybe<&2, Nat>}
  %inert.scan.own.go(Calls.params(sig), Hoist.carried(isg, ib, name), 0n) : {lhs == Lazy.stop(Maybe<&2, Nat>,
    Bool.not(Calls.calls(ib, name)), None{}, _u => _) : Maybe<&2, Nat>}
  %inert.scan.params(sig) : {lhs == Lazy.stop(Maybe<&2, Nat>, Bool.not(Calls.calls(ib, name)), None{},
    _u => Scan.own.go(_, Hoist.carried(isg, ib, name), 0n)) : Maybe<&2, Nat>}
  {==}

# a def read that way records the walks it recorded
law inert.scan.walks.go:
  for ds: List<&2, Calls.Def>
  for +ws: List<&2, Scan.Walk>
  for +e: {inert.dok(ds) == True{} : Bool}
  {Scan.walks.go(inert.defs(ds), ws) == Scan.walks.go(ds, ws) : List<&2, Scan.Walk>}

def inert.scan.walks.go(ds, ws, e):
  match ds:
    case Nil{}:
      {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +en = inert.dok.head(name, sig, body, rest, e)
      +eb = inert.dok.body(name, sig, body, rest, e)
      +isg = D1.inert.node(sig)
      +ib = D1.inert.node(body)
      +lhs = Scan.walks.go(inert.defs(Calls.Def{name, sig, body} <> rest), ws)
      %inert.scan.own(sig, body, name, en, eb) : {lhs == Scan.walks.go(rest, Scan.tag(List.append(&2, Nat,
        Scan.opt(_), Scan.passes(body, Calls.names(sig), ws)), name, ws)) : List<&2, Scan.Walk>}
      %inert.scan.passes(body, Calls.names(sig), ws) : {lhs == Scan.walks.go(rest, Scan.tag(List.append(&2, Nat,
        Scan.opt(Scan.own(isg, ib, name)), _), name, ws)) : List<&2, Scan.Walk>}
      %inert.names(sig) : {lhs == Scan.walks.go(rest, Scan.tag(List.append(&2, Nat,
        Scan.opt(Scan.own(isg, ib, name)), Scan.passes(ib, _, ws)), name, ws)) : List<&2, Scan.Walk>}
      inert.scan.walks.go(rest, Scan.tag(List.append(&2, Nat, Scan.opt(Scan.own(isg, ib, name)),
        Scan.passes(ib, Calls.names(isg), ws)), name, ws), inert.dok.rest(name, sig, body, rest, e))

# a def read that way is walked as it was
law inert.scan.run:
  for +sig: Tree.Node
  for +body: Tree.Node
  for +name: String
  for +ws: List<&2, Scan.Walk>
  for +path: String
  for +en: {D1.inert.marked(name) == False{} : Bool}
  for +eb: {D1.inert.ok(body) == True{} : Bool}
  {Scan.run(D1.inert.node(sig), D1.inert.node(body), name, ws, path) == Scan.run(sig, body, name, ws,
      path) : List<&2, F.Finding>}

def inert.scan.run(sig, body, name, ws, path, en, eb):
  +isg = D1.inert.node(sig)
  +ib = D1.inert.node(body)
  +cr = Hoist.carried(isg, ib, name)
  +lhs = Scan.run(isg, ib, name, ws, path)
  %inert.hoist.carried(sig, body, name, en, eb) : {lhs == Scan.walk(body, name, ws, _, Scan.lead.go(Calls.params(sig),
    _), path, True{}) : List<&2, F.Finding>}
  %inert.scan.lead.go(Calls.params(sig), cr) : {lhs == Scan.walk(body, name, ws, cr, _, path, True{})
    : List<&2, F.Finding>}
  %inert.scan.params(sig) : {lhs == Scan.walk(body, name, ws, cr, Scan.lead.go(_, cr), path, True{})
    : List<&2, F.Finding>}
  inert.scan.walk(body, name, ws, cr, Scan.lead.go(Calls.params(isg), cr), path, True{}, en, eb)

# scan over the defs read that way reports what it reports over the defs
law inert.scan.go:
  for ds: List<&2, Calls.Def>
  for +ws: List<&2, Scan.Walk>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  for +e: {inert.dok(ds) == True{} : Bool}
  {Scan.check.go(inert.defs(ds), ws, path, acc) == Scan.check.go(ds, ws, path, acc) : List<&2, F.Finding>}

def inert.scan.go(ds, ws, path, acc, e):
  match ds:
    case Nil{}:
      {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +en = inert.dok.head(name, sig, body, rest, e)
      +eb = inert.dok.body(name, sig, body, rest, e)
      +ib = D1.inert.node(body)
      +isg = D1.inert.node(sig)
      +lst = Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Calls.calls(ib, name), Bool.not(Calls.exempt(path,
        isg)))), [], _u => Scan.run(isg, ib, name, ws, path))
      %inert.stop(Bool.not(Bool.and(Calls.calls(ib, name), Bool.not(Calls.exempt(path, isg)))),
        Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))),
        Scan.run(isg, ib, name, ws, path), Scan.run(sig, body, name, ws, path),
        inert.gate(path, name, sig, body, en, eb), inert.scan.run(sig, body, name, ws, path, en, eb)) :
        {Scan.check.go(inert.defs(rest), ws, path, lst <> acc) == Scan.check.go(rest, ws, path, _ <> acc)
          : List<&2, F.Finding>}
      inert.scan.go(rest, ws, path, lst <> acc, inert.dok.rest(name, sig, body, rest, e))

# scan over the defs read that way, their walks read that way too
law inert.scan.on:
  for +ds: List<&2, Calls.Def>
  for +path: String
  for +e: {inert.dok(ds) == True{} : Bool}
  {Scan.check.on(inert.defs(ds), path) == Scan.check.on(ds, path) : List<&2, F.Finding>}

def inert.scan.on(ds, path, e):
  %inert.scan.walks.go(ds, [], e) : {Scan.check.go(inert.defs(ds), Scan.walks(inert.defs(ds)), path, [])
    == Scan.check.go(ds, _, path, []) : List<&2, F.Finding>}
  inert.scan.go(ds, Scan.walks(inert.defs(ds)), path, [], e)

# the rule's law-file gate over the defs read that way
law inert.scan.gated:
  for +ds: List<&2, Calls.Def>
  for +path: String
  for +e: {inert.dok(ds) == True{} : Bool}
  {Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path), [], _u => Scan.check.on(inert.defs(ds), path))
    == Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path), [], _v => Scan.check.on(ds, path))
      : List<&2, F.Finding>}

def inert.scan.gated(ds, path, e):
  inert.stop(Paths.is_law_file(path), Paths.is_law_file(path), Scan.check.on(inert.defs(ds), path),
    Scan.check.on(ds, path), {==}, inert.scan.on(ds, path, e))

def Laws.inert_scan(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, ok, ok2, e):
  M1.inert.via(Tree.Node, z => Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path), [],
    _u => Scan.check.on(Calls.defs(z), path)), tree, tree2, D1.inert.node(tree), D1.inert.node(tree2),
    inert.lift(z => Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path), [], _u => Scan.check.on(z, path)), tree,
      inert.scan.gated(Calls.defs(tree), path, inert.dok.of(tree, ok))),
    inert.lift(z => Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path), [], _u => Scan.check.on(z, path)), tree2,
      inert.scan.gated(Calls.defs(tree2), path, inert.dok.of(tree2, ok2))),
    e)
