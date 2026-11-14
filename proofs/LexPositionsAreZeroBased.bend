# proofs of laws/LexPositionsAreZeroBased.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/lazy/lazy.bend as Lazy
import ../laws/LexPositionsAreZeroBased.bend as Laws
import ../laws/defs/LineBreakChar.bend as D1
import ./lemmas/LexAndTreeFacts.bend as M1

# the line reading a reversed token list's texts ends on, from line 0
def rline(toks: List<&2, Lex.Tok>) -> U32:
  Laws.line_after(M1.rspell(toks), 0)

# the column reading a reversed token list's texts ends on, from column 0
def rcol(toks: List<&2, Lex.Tok>) -> U32:
  Laws.col_after(M1.rspell(toks), 0)

# a reversed token list, each token moved to where the texts under it end
def rplaced(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      []
    case Con{Lex.Tok{k, t, _l, _c}, +rest}:
      Lex.Tok{k, t, rline(rest), rcol(rest)} <> rplaced(rest)

# the state with its positions recomputed from what it read: the machine's
# state always equals it
def ghost(st: Lex.St) -> Lex.St:
  match st:
    case Lex.St{m, k, _l, _c, _sl, _sc, +buf, +toks}:
      Lex.St{m, k, Laws.line_after(M1.rword(buf), rline(toks)), Laws.col_after(M1.rword(buf), rcol(toks)),
        rline(toks), rcol(toks), buf, rplaced(toks)}

# the line the buffer ends on, over moved tokens
def la(buf: List<&2, Char>, toks: List<&2, Lex.Tok>) -> U32:
  Laws.line_after(M1.rword(buf), rline(toks))

# the column the buffer ends on, over moved tokens
def ca(buf: List<&2, Char>, toks: List<&2, Lex.Tok>) -> U32:
  Laws.col_after(M1.rword(buf), rcol(toks))

# reading two texts one after the other ends on the same line as reading both
law line.app:
  for +a: String
  for +b: String
  for +l: U32
  {Laws.line_after(String.append(a, b), l) == Laws.line_after(b, Laws.line_after(a, l)) : U32}

def line.app(a, b, l):
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      line.app(t, b, Bool.pick(U32, D1.breaks(h), (l + 1 : U32), l))

# reading two texts one after the other ends on the same column as reading both
law col.app:
  for +a: String
  for +b: String
  for +c: U32
  {Laws.col_after(String.append(a, b), c) == Laws.col_after(b, Laws.col_after(a, c)) : U32}

def col.app(a, b, c):
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      col.app(t, b, Bool.pick(U32, D1.breaks(h), 0, (c + 1 : U32)))

# moving tokens keeps their texts
law rplaced.spell:
  for +xs: List<&2, Lex.Tok>
  {M1.rspell(rplaced(xs)) == M1.rspell(xs) : String}

def rplaced.spell(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, t, l, c}, rest}:
      Equal.cong(String, String, x => String.append(x, t), M1.rspell(rplaced(rest)), M1.rspell(rest),
        rplaced.spell(rest))

# moving tokens twice moves them once
law rplaced.idem:
  for +xs: List<&2, Lex.Tok>
  {rplaced(rplaced(xs)) == rplaced(xs) : List<&2, Lex.Tok>}

def rplaced.idem(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, t, l, c}, rest}:
      %Equal.sym(String, M1.rspell(rplaced(rest)), M1.rspell(rest), rplaced.spell(rest)) :
        {Lex.Tok{k, t, Laws.line_after(_, 0), Laws.col_after(_, 0)} <> rplaced(rplaced(rest))
          == Lex.Tok{k, t, rline(rest), rcol(rest)} <> rplaced(rest) : List<&2, Lex.Tok>}
      %rplaced.idem(rest) :
        {Lex.Tok{k, t, rline(rest), rcol(rest)} <> rplaced(rplaced(rest))
          == Lex.Tok{k, t, rline(rest), rcol(rest)} <> _ : List<&2, Lex.Tok>}
      {==}

# flushing onto moved tokens starts the new token on the line the buffer ends on
law pos.flush.line:
  for +k: Lex.TokKind
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {rline(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))) == la(buf, toks) : U32}

def pos.flush.line(k, buf, toks):
  %Equal.sym(String, M1.rspell(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))),
    String.append(M1.rspell(rplaced(toks)), M1.rword(buf)), M1.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))) :
    {Laws.line_after(_, 0) == la(buf, toks) : U32}
  %Equal.sym(U32, Laws.line_after(String.append(M1.rspell(rplaced(toks)), M1.rword(buf)), 0),
    Laws.line_after(M1.rword(buf), rline(rplaced(toks))), line.app(M1.rspell(rplaced(toks)), M1.rword(buf), 0)) :
    {_ == la(buf, toks) : U32}
  %Equal.sym(String, M1.rspell(rplaced(toks)), M1.rspell(toks), rplaced.spell(toks)) :
    {Laws.line_after(M1.rword(buf), Laws.line_after(_, 0)) == la(buf, toks) : U32}
  {==}

# flushing onto moved tokens starts the new token on the column the buffer ends on
law pos.flush.col:
  for +k: Lex.TokKind
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {rcol(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))) == ca(buf, toks) : U32}

def pos.flush.col(k, buf, toks):
  %Equal.sym(String, M1.rspell(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))),
    String.append(M1.rspell(rplaced(toks)), M1.rword(buf)), M1.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))) :
    {Laws.col_after(_, 0) == ca(buf, toks) : U32}
  %Equal.sym(U32, Laws.col_after(String.append(M1.rspell(rplaced(toks)), M1.rword(buf)), 0),
    Laws.col_after(M1.rword(buf), rcol(rplaced(toks))), col.app(M1.rspell(rplaced(toks)), M1.rword(buf), 0)) :
    {_ == ca(buf, toks) : U32}
  %Equal.sym(String, M1.rspell(rplaced(toks)), M1.rspell(toks), rplaced.spell(toks)) :
    {Laws.col_after(M1.rword(buf), Laws.col_after(_, 0)) == ca(buf, toks) : U32}
  {==}

# the token a flush onto moved tokens adds sits where the tokens under it end
law pos.flush.placed:
  for +k: Lex.TokKind
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {rplaced(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks)))
    == Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks)) : List<&2, Lex.Tok>}

def pos.flush.placed(k, buf, toks):
  match buf:
    case Nil{}:
      rplaced.idem(toks)
    case Con{h, t}:
      %Equal.sym(String, M1.rspell(rplaced(toks)), M1.rspell(toks), rplaced.spell(toks)) :
        {Lex.Tok{Lex.refine(k, Lex.word(h <> t)), Lex.word(h <> t), Laws.line_after(_, 0), Laws.col_after(_, 0)}
          <> rplaced(rplaced(toks))
          == Lex.Tok{Lex.refine(k, Lex.word(h <> t)), Lex.word(h <> t), rline(toks), rcol(toks)} <> rplaced(toks)
          : List<&2, Lex.Tok>}
      %rplaced.idem(toks) :
        {Lex.Tok{Lex.refine(k, Lex.word(h <> t)), Lex.word(h <> t), rline(toks), rcol(toks)} <> rplaced(rplaced(toks))
          == Lex.Tok{Lex.refine(k, Lex.word(h <> t)), Lex.word(h <> t), rline(toks), rcol(toks)} <> _
          : List<&2, Lex.Tok>}
      {==}

# whichever state the step picks, its positions are the recomputed ones
law pos.pick:
  for +b: Bool
  for -x: Lex.St
  for -y: Lex.St
  for +ex: {ghost(x) == x : Lex.St}
  for +ey: {ghost(y) == y : Lex.St}
  {ghost(Lazy.either(Lex.St, b, _u => x, _v => y)) == Lazy.either(Lex.St, b, _u => x, _v => y) : Lex.St}

def pos.pick(b, _x, _y, ex, ey):
  match b:
    case True{}:
      ex
    case False{}:
      ey

# a char that continues the token moves the position past it
law pos.cont:
  for +c: Char
  for +m: Lex.Mode
  for +k: Lex.TokKind
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {ghost(Lex.St{m, k,
      Bool.pick(U32, Lex.is_newline(c), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(c), 0, (ca(buf, toks) + 1 : U32)),
      rline(toks), rcol(toks), c <> buf, rplaced(toks)})
    == Lex.St{m, k,
      Bool.pick(U32, Lex.is_newline(c), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(c), 0, (ca(buf, toks) + 1 : U32)),
      rline(toks), rcol(toks), c <> buf, rplaced(toks)} : Lex.St}

def pos.cont(c, m, k, buf, toks):
  %Equal.sym(U32, Laws.line_after(String.append(M1.rword(buf), M1.one(c)), rline(rplaced(toks))),
    Laws.line_after(M1.one(c), Laws.line_after(M1.rword(buf), rline(rplaced(toks)))),
    line.app(M1.rword(buf), M1.one(c), rline(rplaced(toks)))) :
    {Lex.St{m, k, _, Laws.col_after(String.append(M1.rword(buf), M1.one(c)), rcol(rplaced(toks))),
      rline(rplaced(toks)), rcol(rplaced(toks)), c <> buf, rplaced(rplaced(toks))}
    == Lex.St{m, k,
      Bool.pick(U32, Lex.is_newline(c), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(c), 0, (ca(buf, toks) + 1 : U32)),
      rline(toks), rcol(toks), c <> buf, rplaced(toks)} : Lex.St}
  %Equal.sym(U32, Laws.col_after(String.append(M1.rword(buf), M1.one(c)), rcol(rplaced(toks))),
    Laws.col_after(M1.one(c), Laws.col_after(M1.rword(buf), rcol(rplaced(toks)))),
    col.app(M1.rword(buf), M1.one(c), rcol(rplaced(toks)))) :
    {Lex.St{m, k, Laws.line_after(M1.one(c), Laws.line_after(M1.rword(buf), rline(rplaced(toks)))), _,
      rline(rplaced(toks)), rcol(rplaced(toks)), c <> buf, rplaced(rplaced(toks))}
    == Lex.St{m, k,
      Bool.pick(U32, Lex.is_newline(c), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(c), 0, (ca(buf, toks) + 1 : U32)),
      rline(toks), rcol(toks), c <> buf, rplaced(toks)} : Lex.St}
  %Equal.sym(String, M1.rspell(rplaced(toks)), M1.rspell(toks), rplaced.spell(toks)) :
    {Lex.St{m, k, Laws.line_after(M1.one(c), Laws.line_after(M1.rword(buf), Laws.line_after(_, 0))),
      Laws.col_after(M1.one(c), Laws.col_after(M1.rword(buf), Laws.col_after(_, 0))),
      Laws.line_after(_, 0), Laws.col_after(_, 0), c <> buf, rplaced(rplaced(toks))}
    == Lex.St{m, k,
      Bool.pick(U32, Lex.is_newline(c), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(c), 0, (ca(buf, toks) + 1 : U32)),
      rline(toks), rcol(toks), c <> buf, rplaced(toks)} : Lex.St}
  %Equal.sym(List<&2, Lex.Tok>, rplaced(rplaced(toks)), rplaced(toks), rplaced.idem(toks)) :
    {Lex.St{m, k, Laws.line_after(M1.one(c), la(buf, toks)),
      Laws.col_after(M1.one(c), ca(buf, toks)),
      rline(toks), rcol(toks), c <> buf, _}
    == Lex.St{m, k,
      Bool.pick(U32, Lex.is_newline(c), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(c), 0, (ca(buf, toks) + 1 : U32)),
      rline(toks), rcol(toks), c <> buf, rplaced(toks)} : Lex.St}
  {==}

# a char that starts a token flushes the last one where it began, and moves
# the position past itself
law pos.begin:
  for +c: Char
  for +m: Lex.Mode
  for +k2: Lex.TokKind
  for +k: Lex.TokKind
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {ghost(Lex.St{m, k2,
      Bool.pick(U32, Lex.is_newline(c), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(c), 0, (ca(buf, toks) + 1 : U32)),
      la(buf, toks), ca(buf, toks), [c],
      Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))})
    == Lex.St{m, k2,
      Bool.pick(U32, Lex.is_newline(c), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(c), 0, (ca(buf, toks) + 1 : U32)),
      la(buf, toks), ca(buf, toks), [c],
      Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))} : Lex.St}

def pos.begin(c, m, k2, k, buf, toks):
  %Equal.sym(U32, rline(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))),
    la(buf, toks), pos.flush.line(k, buf, toks)) :
    {Lex.St{m, k2, Laws.line_after(M1.one(c), _),
      Laws.col_after(M1.one(c), rcol(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks)))),
      _, rcol(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))), [c],
      rplaced(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks)))}
    == Lex.St{m, k2,
      Bool.pick(U32, Lex.is_newline(c), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(c), 0, (ca(buf, toks) + 1 : U32)),
      la(buf, toks), ca(buf, toks), [c],
      Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))} : Lex.St}
  %Equal.sym(U32, rcol(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))),
    ca(buf, toks), pos.flush.col(k, buf, toks)) :
    {Lex.St{m, k2, Laws.line_after(M1.one(c), la(buf, toks)),
      Laws.col_after(M1.one(c), _),
      la(buf, toks), _, [c],
      rplaced(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks)))}
    == Lex.St{m, k2,
      Bool.pick(U32, Lex.is_newline(c), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(c), 0, (ca(buf, toks) + 1 : U32)),
      la(buf, toks), ca(buf, toks), [c],
      Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))} : Lex.St}
  %Equal.sym(List<&2, Lex.Tok>, rplaced(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))),
    Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks)), pos.flush.placed(k, buf, toks)) :
    {Lex.St{m, k2, Laws.line_after(M1.one(c), la(buf, toks)),
      Laws.col_after(M1.one(c), ca(buf, toks)),
      la(buf, toks), ca(buf, toks), [c], _}
    == Lex.St{m, k2,
      Bool.pick(U32, Lex.is_newline(c), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(c), 0, (ca(buf, toks) + 1 : U32)),
      la(buf, toks), ca(buf, toks), [c],
      Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))} : Lex.St}
  {==}

# one char read from a state whose positions are the recomputed ones keeps
# them so
law pos.step:
  for +c: Char
  for +m: Lex.Mode
  for +k: Lex.TokKind
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {ghost(Lex.step(c, ghost(Lex.St{m, k, 0, 0, 0, 0, buf, toks})))
    == Lex.step(c, ghost(Lex.St{m, k, 0, 0, 0, 0, buf, toks})) : Lex.St}

def pos.step(c, m, k, buf, toks):
  pos.pick(Lex.continues(m, Lex.classify(c)),
    Lex.St{Lex.after(m, Lex.classify(c)), k,
      Bool.pick(U32, Lex.is_newline(c), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(c), 0, (ca(buf, toks) + 1 : U32)),
      rline(toks), rcol(toks), c <> buf, rplaced(toks)},
    Lex.St{Lex.begin.mode(Lex.classify(c)), Lex.begin.kind(Lex.classify(c)),
      Bool.pick(U32, Lex.is_newline(c), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(c), 0, (ca(buf, toks) + 1 : U32)),
      la(buf, toks), ca(buf, toks), [c],
      Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))},
    pos.cont(c, Lex.after(m, Lex.classify(c)), k, buf, toks),
    pos.begin(c, Lex.begin.mode(Lex.classify(c)), Lex.begin.kind(Lex.classify(c)), k, buf, toks))

# pos.step, for any state recomputed
law pos.step.on:
  for +c: Char
  for +st: Lex.St
  {ghost(Lex.step(c, ghost(st))) == Lex.step(c, ghost(st)) : Lex.St}

def pos.step.on(c, st):
  match st:
    case Lex.St{m, k, _l, _c, _sl, _sc, buf, toks}:
      pos.step(c, m, k, buf, toks)

# a step keeps the positions the recomputed ones
law pos.kept:
  for +c: Char
  for +st: Lex.St
  for +e: {ghost(st) == st : Lex.St}
  {ghost(Lex.step(c, st)) == Lex.step(c, st) : Lex.St}

def pos.kept(c, st, e):
  %e : {ghost(Lex.step(c, _)) == Lex.step(c, _) : Lex.St}
  pos.step.on(c, st)

# running over chars keeps the positions the recomputed ones
law pos.run:
  for +cs: List<&2, Char>
  for +st: Lex.St
  for +e: {ghost(st) == st : Lex.St}
  {ghost(Lex.run(cs, st)) == Lex.run(cs, st) : Lex.St}

def pos.run(cs, st, e):
  match cs:
    case Nil{}:
      e
    case Con{h, t}:
      pos.run(t, Lex.step(h, st), pos.kept(h, st, e))

# placing a list reversed onto another: the moved first list, reversed, onto
# the other placed from where the first's texts end
law pos.rev:
  for +xs: List<&2, Lex.Tok>
  for +acc: List<&2, Lex.Tok>
  {Laws.placed(List.reverse.go(&2, Lex.Tok, xs, acc), 0, 0)
    == List.reverse.go(&2, Lex.Tok, rplaced(xs), Laws.placed(acc, rline(xs), rcol(xs))) : List<&2, Lex.Tok>}

def pos.rev(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, t, l, c}, rest}:
      %Equal.sym(List<&2, Lex.Tok>,
        Laws.placed(List.reverse.go(&2, Lex.Tok, rest, Lex.Tok{k, t, l, c} <> acc), 0, 0),
        List.reverse.go(&2, Lex.Tok, rplaced(rest),
          Lex.Tok{k, t, rline(rest), rcol(rest)}
            <> Laws.placed(acc, Laws.line_after(t, rline(rest)), Laws.col_after(t, rcol(rest)))),
        pos.rev(rest, Lex.Tok{k, t, l, c} <> acc)) :
        {_ == List.reverse.go(&2, Lex.Tok, rplaced(Lex.Tok{k, t, l, c} <> rest),
          Laws.placed(acc, rline(Lex.Tok{k, t, l, c} <> rest), rcol(Lex.Tok{k, t, l, c} <> rest))) : List<&2, Lex.Tok>}
      %Equal.sym(U32, Laws.line_after(String.append(M1.rspell(rest), t), 0),
        Laws.line_after(t, rline(rest)), line.app(M1.rspell(rest), t, 0)) :
        {List.reverse.go(&2, Lex.Tok, rplaced(rest),
          Lex.Tok{k, t, rline(rest), rcol(rest)}
            <> Laws.placed(acc, Laws.line_after(t, rline(rest)), Laws.col_after(t, rcol(rest))))
          == List.reverse.go(&2, Lex.Tok, rplaced(rest),
          Lex.Tok{k, t, rline(rest), rcol(rest)}
            <> Laws.placed(acc, _, Laws.col_after(String.append(M1.rspell(rest), t), 0)))
          : List<&2, Lex.Tok>}
      %Equal.sym(U32, Laws.col_after(String.append(M1.rspell(rest), t), 0),
        Laws.col_after(t, rcol(rest)), col.app(M1.rspell(rest), t, 0)) :
        {List.reverse.go(&2, Lex.Tok, rplaced(rest),
          Lex.Tok{k, t, rline(rest), rcol(rest)}
            <> Laws.placed(acc, Laws.line_after(t, rline(rest)), Laws.col_after(t, rcol(rest))))
          == List.reverse.go(&2, Lex.Tok, rplaced(rest),
          Lex.Tok{k, t, rline(rest), rcol(rest)} <> Laws.placed(acc, Laws.line_after(t, rline(rest)), _))
          : List<&2, Lex.Tok>}
      {==}

# the finished tokens of a recomputed state sit where placed puts them
law pos.finish.on:
  for +st: Lex.St
  {Laws.placed(Lex.finish(ghost(st)), 0, 0) == Lex.finish(ghost(st)) : List<&2, Lex.Tok>}

def pos.finish.on(st):
  match st:
    case Lex.St{m, k, _l, _c, _sl, _sc, buf, toks}:
      Equal.trans(List<&2, Lex.Tok>,
        Laws.placed(List.reverse.go(&2, Lex.Tok, Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks)), []), 0, 0),
        List.reverse.go(&2, Lex.Tok, rplaced(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))), []),
        List.reverse.go(&2, Lex.Tok, Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks)), []),
        pos.rev(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks)), []),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, x => List.reverse.go(&2, Lex.Tok, x, []),
          rplaced(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))),
          Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks)),
          pos.flush.placed(k, buf, toks)))

# the finished tokens of a state whose positions are the recomputed ones sit
# where placed puts them
law pos.finish:
  for +st: Lex.St
  for +e: {ghost(st) == st : Lex.St}
  {Laws.placed(Lex.finish(st), 0, 0) == Lex.finish(st) : List<&2, Lex.Tok>}

def pos.finish(st, e):
  %e : {Laws.placed(Lex.finish(_), 0, 0) == Lex.finish(_) : List<&2, Lex.Tok>}
  pos.finish.on(st)

def Laws.positions(s):
  pos.finish(Lex.run(String.to_list(s), Lex.St{Lex.Fresh{}, Lex.TSpace{}, 0, 0, 0, 0, [], []}),
    pos.run(String.to_list(s), Lex.St{Lex.Fresh{}, Lex.TSpace{}, 0, 0, 0, 0, [], []}, {==}))
