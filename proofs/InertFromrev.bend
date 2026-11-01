# proofs of laws/InertFromrev.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/suspicious/fromrev.bend as Fromrev
import ../laws/InertFromrev.bend as Laws
import ../laws/defs/InertText.bend as D1
import ./lemmas/InertTextFacts.bend as M1

# fromrev
# -------

# four texts, each read that way: tested for the shape as they were
law inert.fromrev.shape:
  for +b1: Bool
  for +t: String
  for +b2: Bool
  for +a: String
  for +b3: Bool
  for +b: String
  for +b4: Bool
  for +d: String
  for +e1: {D1.inert.fits.go(b1, t) == True{} : Bool}
  for +e2: {D1.inert.fits.go(b2, a) == True{} : Bool}
  for +e3: {D1.inert.fits.go(b3, b) == True{} : Bool}
  for +e4: {D1.inert.fits.go(b4, d) == True{} : Bool}
  {Fromrev.shape(D1.inert.keep(b1, t), D1.inert.keep(b2, a), D1.inert.keep(b3, b), D1.inert.keep(b4, d))
    == Fromrev.shape(t, a, b, d) : Bool}

def inert.fromrev.shape(b1, t, b2, a, b3, b, b4, d, e1, e2, e3, e4):
  +k1 = D1.inert.keep(b1, t)
  +k2 = D1.inert.keep(b2, a)
  +k3 = D1.inert.keep(b3, b)
  +k4 = D1.inert.keep(b4, d)
  +lhs = Fromrev.shape(k1, k2, k3, k4)
  %M1.inert.eq_keep(b1, t, "String.from_list", e1, {==}) : {lhs == Bool.and(_,
    Bool.and(String.eq(a, "("), Bool.and(String.eq(b, "List.reverse"), String.eq(d, "(")))) : Bool}
  %M1.inert.eq_keep(b2, a, "(", e2, {==}) : {lhs == Bool.and(String.eq(k1, "String.from_list"),
    Bool.and(_, Bool.and(String.eq(b, "List.reverse"), String.eq(d, "(")))) : Bool}
  %M1.inert.eq_keep(b3, b, "List.reverse", e3, {==}) : {lhs == Bool.and(String.eq(k1, "String.from_list"),
    Bool.and(String.eq(k2, "("), Bool.and(_, String.eq(d, "(")))) : Bool}
  %M1.inert.eq_keep(b4, d, "(", e4, {==}) : {lhs == Bool.and(String.eq(k1, "String.from_list"),
    Bool.and(String.eq(k2, "("), Bool.and(String.eq(k3, "List.reverse"), _))) : Bool}
  {==}

# a token's text, then tokens as the lexer makes them, each read that way:
# they open the shape as they did
law inert.fromrev.at:
  for +b1: Bool
  for +t: String
  for ts: List<&2, Lex.Tok>
  for +e1: {D1.inert.fits.go(b1, t) == True{} : Bool}
  for +e: {D1.inert.oks(ts) == True{} : Bool}
  {Fromrev.at(D1.inert.keep(b1, t), D1.inert.toks(ts)) == Fromrev.at(t, ts) : Bool}

def inert.fromrev.at(b1, t, ts, e1, e):
  match ts:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k1, +a, +l1, +c1}, +r1}:
      match r1:
        case Nil{}:
          {==}
        case Con{Lex.Tok{+k2, +b, +l2, +c2}, +r2}:
          match r2:
            case Nil{}:
              {==}
            case Con{Lex.Tok{+k3, +d, +l3, +c3}, +r3}:
              +h1 = {Lex.Tok{k1, a, l1, c1} : Lex.Tok}
              +h2 = {Lex.Tok{k2, b, l2, c2} : Lex.Tok}
              +h3 = {Lex.Tok{k3, d, l3, c3} : Lex.Tok}
              +er1 = M1.inert.and_r(D1.inert.fits(h1), D1.inert.oks(r1), e)
              +er2 = M1.inert.and_r(D1.inert.fits(h2), D1.inert.oks(r2), er1)
              inert.fromrev.shape(b1, t, D1.inert.blanks(k1), a, D1.inert.blanks(k2), b, D1.inert.blanks(k3), d,
                e1, M1.inert.and_l(D1.inert.fits(h1), D1.inert.oks(r1), e),
                M1.inert.and_l(D1.inert.fits(h2), D1.inert.oks(r2), er1),
                M1.inert.and_l(D1.inert.fits(h3), D1.inert.oks(r3), er2))

# fromrev's walk reads no comment or string: it compares texts with the shape's
law inert.fromrev.walk:
  for ts: List<&2, Lex.Tok>
  for +path: String
  for +e: {D1.inert.oks(ts) == True{} : Bool}
  {Fromrev.walk(D1.inert.toks(ts), path) == Fromrev.walk(ts, path) : List<&2, F.Finding>}

def inert.fromrev.walk(ts, path, e):
  match ts:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      +h = {Lex.Tok{k, t, l, c} : Lex.Tok}
      +er = M1.inert.and_r(D1.inert.fits(h), D1.inert.oks(rest), e)
      +x = {F.Finding{path, l, c, 16, "fromrev",
          "String.from_list(List.reverse(..)) walks the list twice and builds one it throws away; fold it onto a String with SCon in one pass."}
        : F.Finding}
      +tt = D1.inert.keep(D1.inert.blanks(k), t)
      +cr = D1.inert.toks(rest)
      +lhs = Bool.pick(List<&2, F.Finding>, Fromrev.at(tt, cr), x <> Fromrev.walk(cr, path), Fromrev.walk(cr, path))
      %inert.fromrev.walk(rest, path, er) : {lhs == Bool.pick(List<&2, F.Finding>, Fromrev.at(t, rest),
        x <> _, _) : List<&2, F.Finding>}
      %inert.fromrev.at(D1.inert.blanks(k), t, rest, M1.inert.and_l(D1.inert.fits(h), D1.inert.oks(rest), e), er) :
        {lhs == Bool.pick(List<&2, F.Finding>, _, x <> Fromrev.walk(cr, path), Fromrev.walk(cr, path))
        : List<&2, F.Finding>}
      {==}

# fromrev's walk of the significant tokens reads no comment or string
law inert.fromrev.on:
  for +ts: List<&2, Lex.Tok>
  for +path: String
  for +e: {D1.inert.oks(ts) == True{} : Bool}
  {Fromrev.walk(T.sig(D1.inert.toks(ts)), path) == Fromrev.walk(T.sig(ts), path) : List<&2, F.Finding>}

def inert.fromrev.on(ts, path, e):
  +s = T.sig(ts)
  +cs = D1.inert.toks(s)
  %Equal.sym(List<&2, Lex.Tok>, T.sig(D1.inert.toks(ts)), cs, M1.inert.put.sig(ts)) :
    {Fromrev.walk(_, path) == Fromrev.walk(s, path) : List<&2, F.Finding>}
  inert.fromrev.walk(s, path, M1.inert.put.sig_ok(ts, e))

def Laws.inert_fromrev(path, _text, toks, _tree, _bound, _items, _text2, toks2, _tree2, _bound2, _items2, ok, ok2, e):
  M1.inert.via(List<&2, Lex.Tok>, z => Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path), [],
    _u => Fromrev.walk(T.sig(z), path)), toks, toks2, D1.inert.toks(toks), D1.inert.toks(toks2),
    Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>, w => Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path),
      [], _u => w), Fromrev.walk(T.sig(D1.inert.toks(toks)), path), Fromrev.walk(T.sig(toks), path),
      inert.fromrev.on(toks, path, ok)),
    Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>, w => Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path),
      [], _u => w), Fromrev.walk(T.sig(D1.inert.toks(toks2)), path), Fromrev.walk(T.sig(toks2), path),
      inert.fromrev.on(toks2, path, ok2)),
    e)
