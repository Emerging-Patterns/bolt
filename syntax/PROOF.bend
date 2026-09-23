# syntax: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./lex.bend as Lex
import ./LAWS.bend as Laws

# a string onto nothing is itself
law app.nil:
  for +a: String
  {String.append(a, SNil{}) == a : String}

def app.nil(a):
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, x => SCon{h, x}, String.append(t, SNil{}), t, app.nil(t))

# appending strings is associative
law app.assoc:
  for +a: String
  for +b: String
  for +c: String
  {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}

def app.assoc(a, b, c):
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, x => SCon{h, x},
        String.append(String.append(t, b), c), String.append(t, String.append(b, c)), app.assoc(t, b, c))

# a string's chars make the string again
law chars:
  for +s: String
  {String.from_list(String.to_list(s)) == s : String}

def chars(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, x => SCon{h, x}, String.from_list(String.to_list(t)), t, chars(t))

# one char as a string
def one(cc: Char) -> String:
  SCon{cc, SNil{}}

# a reversed buffer's chars, in order
def rword(buf: List<&2, Char>) -> String:
  match buf:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      String.append(rword(t), one(h))

# reversing onto an accumulator spells the reversed list, then the accumulator
law rword.go:
  for +xs: List<&2, Char>
  for +acc: List<&2, Char>
  {String.from_list(List.reverse.go(&2, Char, xs, acc)) == String.append(rword(xs), String.from_list(acc)) : String}

def rword.go(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.trans(String,
        String.from_list(List.reverse.go(&2, Char, t, h <> acc)),
        String.append(rword(t), SCon{h, String.from_list(acc)}),
        String.append(String.append(rword(t), one(h)), String.from_list(acc)),
        rword.go(t, h <> acc),
        Equal.sym(String, String.append(String.append(rword(t), one(h)), String.from_list(acc)),
          String.append(rword(t), SCon{h, String.from_list(acc)}),
          app.assoc(rword(t), one(h), String.from_list(acc))))

# a buffer's word is its reversed chars
law rword.word:
  for +buf: List<&2, Char>
  {Lex.word(buf) == rword(buf) : String}

def rword.word(buf):
  Equal.trans(String, Lex.word(buf), String.append(rword(buf), SNil{}), rword(buf),
    rword.go(buf, []), app.nil(rword(buf)))

# a reversed token list's texts, in order
def rspell(toks: List<&2, Lex.Tok>) -> String:
  match toks:
    case Nil{}:
      SNil{}
    case Con{Lex.Tok{k, t, l, c}, rest}:
      String.append(rspell(rest), t)

# a token list's texts, in order
def spell(toks: List<&2, Lex.Tok>) -> String:
  match toks:
    case Nil{}:
      SNil{}
    case Con{Lex.Tok{k, t, l, c}, rest}:
      String.append(t, spell(rest))

# what the machine has read so far: its tokens, then its buffer
def seen(st: Lex.St) -> String:
  match st:
    case Lex.St{m, k, l, c, sl, sc, buf, toks}:
      String.append(rspell(toks), rword(buf))

# flushing the buffer keeps what was read
law flush:
  for +kind: Lex.TokKind
  for +sl: U32
  for +sc: U32
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {rspell(Lex.flush(kind, sl, sc, buf, toks)) == String.append(rspell(toks), rword(buf)) : String}

def flush(_kind, _sl, _sc, buf, toks):
  match buf:
    case Nil{}:
      Equal.sym(String, String.append(rspell(toks), SNil{}), rspell(toks), app.nil(rspell(toks)))
    case Con{h, t}:
      Equal.cong(String, String, x => String.append(rspell(toks), x),
        Lex.word(h <> t), rword(h <> t), rword.word(h <> t))

# whichever state the step picks, it has read one char more
law pick:
  for +b: Bool
  for -x: Lex.St
  for -y: Lex.St
  for -z: String
  for +ex: {seen(x) == z : String}
  for +ey: {seen(y) == z : String}
  {seen(Bool.pick(Lex.St, b, x, y)) == z : String}

def pick(b, _x, _y, _z, ex, ey):
  match b:
    case True{}:
      ex
    case False{}:
      ey

# one char read onto what was read
law step:
  for +cc: Char
  for +mode: Lex.Mode
  for +kind: Lex.TokKind
  for +line: U32
  for +col: U32
  for +sl: U32
  for +sc: U32
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {seen(Lex.step(cc, Lex.St{mode, kind, line, col, sl, sc, buf, toks}))
    == String.append(String.append(rspell(toks), rword(buf)), one(cc)) : String}

def step(cc, mode, kind, line, col, sl, sc, buf, toks):
  pick(Lex.continues(mode, Lex.classify(cc)),
    Lex.St{Lex.after(mode, Lex.classify(cc)), kind,
      Bool.pick(U32, Lex.is_newline(cc), (line + 1 : U32), line),
      Bool.pick(U32, Lex.is_newline(cc), 0, (col + 1 : U32)), sl, sc, cc <> buf, toks},
    Lex.St{Lex.begin.mode(Lex.classify(cc)), Lex.begin.kind(Lex.classify(cc)),
      Bool.pick(U32, Lex.is_newline(cc), (line + 1 : U32), line),
      Bool.pick(U32, Lex.is_newline(cc), 0, (col + 1 : U32)), line, col, [cc],
      Lex.flush(kind, sl, sc, buf, toks)},
    String.append(String.append(rspell(toks), rword(buf)), one(cc)),
    Equal.sym(String, String.append(String.append(rspell(toks), rword(buf)), one(cc)),
      String.append(rspell(toks), String.append(rword(buf), one(cc))),
      app.assoc(rspell(toks), rword(buf), one(cc))),
    Equal.cong(String, String, x => String.append(x, one(cc)),
      rspell(Lex.flush(kind, sl, sc, buf, toks)), String.append(rspell(toks), rword(buf)),
      flush(kind, sl, sc, buf, toks)))

# the step's char, then the rest
law run.on:
  for +h: Char
  for +t: List<&2, Char>
  for +st: Lex.St
  for +ih: {seen(Lex.run(t, Lex.step(h, st))) == String.append(seen(Lex.step(h, st)), String.from_list(t)) : String}
  {seen(Lex.run(t, Lex.step(h, st))) == String.append(seen(st), SCon{h, String.from_list(t)}) : String}

def run.on(h, t, st, ih):
  match st:
    case Lex.St{m, k, l, c, sl, sc, buf, toks}:
      Equal.trans(String,
        seen(Lex.run(t, Lex.step(h, Lex.St{m, k, l, c, sl, sc, buf, toks}))),
        String.append(String.append(String.append(rspell(toks), rword(buf)), one(h)), String.from_list(t)),
        String.append(String.append(rspell(toks), rword(buf)), SCon{h, String.from_list(t)}),
        Equal.trans(String,
          seen(Lex.run(t, Lex.step(h, Lex.St{m, k, l, c, sl, sc, buf, toks}))),
          String.append(seen(Lex.step(h, Lex.St{m, k, l, c, sl, sc, buf, toks})), String.from_list(t)),
          String.append(String.append(String.append(rspell(toks), rword(buf)), one(h)), String.from_list(t)),
          ih,
          Equal.cong(String, String, x => String.append(x, String.from_list(t)),
            seen(Lex.step(h, Lex.St{m, k, l, c, sl, sc, buf, toks})),
            String.append(String.append(rspell(toks), rword(buf)), one(h)),
            step(h, m, k, l, c, sl, sc, buf, toks))),
        app.assoc(String.append(rspell(toks), rword(buf)), one(h), String.from_list(t)))

# running over chars reads them all onto what was read
law run:
  for +cs: List<&2, Char>
  for +st: Lex.St
  {seen(Lex.run(cs, st)) == String.append(seen(st), String.from_list(cs)) : String}

def run(cs, st):
  match cs:
    case Nil{}:
      Equal.sym(String, String.append(seen(st), SNil{}), seen(st), app.nil(seen(st)))
    case Con{h, t}:
      run.on(h, t, st, run(t, Lex.step(h, st)))

# the texts of a list reversed onto another: the first's, reversed, then the other's
law spell.rev:
  for +xs: List<&2, Lex.Tok>
  for +acc: List<&2, Lex.Tok>
  {spell(List.reverse.go(&2, Lex.Tok, xs, acc)) == String.append(rspell(xs), spell(acc)) : String}

def spell.rev(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, t, l, c}, rest}:
      Equal.trans(String,
        spell(List.reverse.go(&2, Lex.Tok, rest, Lex.Tok{k, t, l, c} <> acc)),
        String.append(rspell(rest), String.append(t, spell(acc))),
        String.append(String.append(rspell(rest), t), spell(acc)),
        spell.rev(rest, Lex.Tok{k, t, l, c} <> acc),
        Equal.sym(String, String.append(String.append(rspell(rest), t), spell(acc)),
          String.append(rspell(rest), String.append(t, spell(acc))),
          app.assoc(rspell(rest), t, spell(acc))))

# texts pushed onto a stack, in the stack's reversed order
def rcat(ss: List<&2, String>) -> String:
  match ss:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      String.append(rcat(t), h)

# concat of a list reversed onto another: the first's, reversed, then the other's
law rcat.rev:
  for +xs: List<&2, String>
  for +acc: List<&2, String>
  {String.concat(List.reverse.go(&2, String, xs, acc)) == String.append(rcat(xs), String.concat(acc)) : String}

def rcat.rev(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.trans(String,
        String.concat(List.reverse.go(&2, String, t, h <> acc)),
        String.append(rcat(t), String.append(h, String.concat(acc))),
        String.append(String.append(rcat(t), h), String.concat(acc)),
        rcat.rev(t, h <> acc),
        Equal.sym(String, String.append(String.append(rcat(t), h), String.concat(acc)),
          String.append(rcat(t), String.append(h, String.concat(acc))),
          app.assoc(rcat(t), h, String.concat(acc))))

# text.go's stack spells what was on it, then the tokens
law text.go:
  for +xs: List<&2, Lex.Tok>
  for +acc: List<&2, String>
  {rcat(Lex.text.go(xs, acc)) == String.append(rcat(acc), spell(xs)) : String}

def text.go(xs, acc):
  match xs:
    case Nil{}:
      Equal.sym(String, String.append(rcat(acc), SNil{}), rcat(acc), app.nil(rcat(acc)))
    case Con{Lex.Tok{k, t, l, c}, rest}:
      Equal.trans(String,
        rcat(Lex.text.go(rest, t <> acc)),
        String.append(String.append(rcat(acc), t), spell(rest)),
        String.append(rcat(acc), String.append(t, spell(rest))),
        text.go(rest, t <> acc),
        app.assoc(rcat(acc), t, spell(rest)))

# the tokens' text is their texts in order
law text:
  for +xs: List<&2, Lex.Tok>
  {Lex.text(xs) == spell(xs) : String}

def text(xs):
  Equal.trans(String, Lex.text(xs), String.append(rcat(Lex.text.go(xs, [])), SNil{}), spell(xs),
    rcat.rev(Lex.text.go(xs, []), []),
    Equal.trans(String, String.append(rcat(Lex.text.go(xs, [])), SNil{}), rcat(Lex.text.go(xs, [])), spell(xs),
      app.nil(rcat(Lex.text.go(xs, []))), text.go(xs, [])))

# the finished tokens spell what the machine read
law finish:
  for +st: Lex.St
  {Lex.text(Lex.finish(st)) == seen(st) : String}

def finish(st):
  match st:
    case Lex.St{m, k, l, c, sl, sc, buf, toks}:
      Equal.trans(String,
        Lex.text(Lex.finish(Lex.St{m, k, l, c, sl, sc, buf, toks})),
        String.append(rspell(Lex.flush(k, sl, sc, buf, toks)), SNil{}),
        String.append(rspell(toks), rword(buf)),
        Equal.trans(String,
          Lex.text(Lex.finish(Lex.St{m, k, l, c, sl, sc, buf, toks})),
          spell(Lex.finish(Lex.St{m, k, l, c, sl, sc, buf, toks})),
          String.append(rspell(Lex.flush(k, sl, sc, buf, toks)), SNil{}),
          text(Lex.finish(Lex.St{m, k, l, c, sl, sc, buf, toks})),
          spell.rev(Lex.flush(k, sl, sc, buf, toks), [])),
        Equal.trans(String,
          String.append(rspell(Lex.flush(k, sl, sc, buf, toks)), SNil{}),
          rspell(Lex.flush(k, sl, sc, buf, toks)),
          String.append(rspell(toks), rword(buf)),
          app.nil(rspell(Lex.flush(k, sl, sc, buf, toks))),
          flush(k, sl, sc, buf, toks)))

def Laws.lossless(s):
  Equal.trans(String,
    Lex.text(Lex.tokens(s)),
    String.from_list(String.to_list(s)),
    s,
    Equal.trans(String,
      Lex.text(Lex.tokens(s)),
      seen(Lex.run(String.to_list(s), Lex.St{Lex.Fresh{}, Lex.TSpace{}, 0, 0, 0, 0, [], []})),
      String.from_list(String.to_list(s)),
      finish(Lex.run(String.to_list(s), Lex.St{Lex.Fresh{}, Lex.TSpace{}, 0, 0, 0, 0, [], []})),
      run(String.to_list(s), Lex.St{Lex.Fresh{}, Lex.TSpace{}, 0, 0, 0, 0, [], []})),
    chars(s))

# the line reading a reversed token list's texts ends on, from line 0
def rline(toks: List<&2, Lex.Tok>) -> U32:
  Laws.line_after(rspell(toks), 0)

# the column reading a reversed token list's texts ends on, from column 0
def rcol(toks: List<&2, Lex.Tok>) -> U32:
  Laws.col_after(rspell(toks), 0)

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
      Lex.St{m, k, Laws.line_after(rword(buf), rline(toks)), Laws.col_after(rword(buf), rcol(toks)),
        rline(toks), rcol(toks), buf, rplaced(toks)}

# the line the buffer ends on, over moved tokens
def la(buf: List<&2, Char>, toks: List<&2, Lex.Tok>) -> U32:
  Laws.line_after(rword(buf), rline(toks))

# the column the buffer ends on, over moved tokens
def ca(buf: List<&2, Char>, toks: List<&2, Lex.Tok>) -> U32:
  Laws.col_after(rword(buf), rcol(toks))

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
      line.app(t, b, Bool.pick(U32, Laws.breaks(h), (l + 1 : U32), l))

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
      col.app(t, b, Bool.pick(U32, Laws.breaks(h), 0, (c + 1 : U32)))

# moving tokens keeps their texts
law rplaced.spell:
  for +xs: List<&2, Lex.Tok>
  {rspell(rplaced(xs)) == rspell(xs) : String}

def rplaced.spell(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, t, l, c}, rest}:
      Equal.cong(String, String, x => String.append(x, t), rspell(rplaced(rest)), rspell(rest),
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
      %Equal.sym(String, rspell(rplaced(rest)), rspell(rest), rplaced.spell(rest)) :
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
  %Equal.sym(String, rspell(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))),
    String.append(rspell(rplaced(toks)), rword(buf)), flush(k, rline(toks), rcol(toks), buf, rplaced(toks))) :
    {Laws.line_after(_, 0) == la(buf, toks) : U32}
  %Equal.sym(U32, Laws.line_after(String.append(rspell(rplaced(toks)), rword(buf)), 0),
    Laws.line_after(rword(buf), rline(rplaced(toks))), line.app(rspell(rplaced(toks)), rword(buf), 0)) :
    {_ == la(buf, toks) : U32}
  %Equal.sym(String, rspell(rplaced(toks)), rspell(toks), rplaced.spell(toks)) :
    {Laws.line_after(rword(buf), Laws.line_after(_, 0)) == la(buf, toks) : U32}
  {==}

# flushing onto moved tokens starts the new token on the column the buffer ends on
law pos.flush.col:
  for +k: Lex.TokKind
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {rcol(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))) == ca(buf, toks) : U32}

def pos.flush.col(k, buf, toks):
  %Equal.sym(String, rspell(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))),
    String.append(rspell(rplaced(toks)), rword(buf)), flush(k, rline(toks), rcol(toks), buf, rplaced(toks))) :
    {Laws.col_after(_, 0) == ca(buf, toks) : U32}
  %Equal.sym(U32, Laws.col_after(String.append(rspell(rplaced(toks)), rword(buf)), 0),
    Laws.col_after(rword(buf), rcol(rplaced(toks))), col.app(rspell(rplaced(toks)), rword(buf), 0)) :
    {_ == ca(buf, toks) : U32}
  %Equal.sym(String, rspell(rplaced(toks)), rspell(toks), rplaced.spell(toks)) :
    {Laws.col_after(rword(buf), Laws.col_after(_, 0)) == ca(buf, toks) : U32}
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
      %Equal.sym(String, rspell(rplaced(toks)), rspell(toks), rplaced.spell(toks)) :
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
  {ghost(Bool.pick(Lex.St, b, x, y)) == Bool.pick(Lex.St, b, x, y) : Lex.St}

def pos.pick(b, _x, _y, ex, ey):
  match b:
    case True{}:
      ex
    case False{}:
      ey

# a char that continues the token moves the position past it
law pos.cont:
  for +cc: Char
  for +m: Lex.Mode
  for +k: Lex.TokKind
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {ghost(Lex.St{m, k,
      Bool.pick(U32, Lex.is_newline(cc), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(cc), 0, (ca(buf, toks) + 1 : U32)),
      rline(toks), rcol(toks), cc <> buf, rplaced(toks)})
    == Lex.St{m, k,
      Bool.pick(U32, Lex.is_newline(cc), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(cc), 0, (ca(buf, toks) + 1 : U32)),
      rline(toks), rcol(toks), cc <> buf, rplaced(toks)} : Lex.St}

def pos.cont(cc, m, k, buf, toks):
  %Equal.sym(U32, Laws.line_after(String.append(rword(buf), one(cc)), rline(rplaced(toks))),
    Laws.line_after(one(cc), Laws.line_after(rword(buf), rline(rplaced(toks)))),
    line.app(rword(buf), one(cc), rline(rplaced(toks)))) :
    {Lex.St{m, k, _, Laws.col_after(String.append(rword(buf), one(cc)), rcol(rplaced(toks))),
      rline(rplaced(toks)), rcol(rplaced(toks)), cc <> buf, rplaced(rplaced(toks))}
    == Lex.St{m, k,
      Bool.pick(U32, Lex.is_newline(cc), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(cc), 0, (ca(buf, toks) + 1 : U32)),
      rline(toks), rcol(toks), cc <> buf, rplaced(toks)} : Lex.St}
  %Equal.sym(U32, Laws.col_after(String.append(rword(buf), one(cc)), rcol(rplaced(toks))),
    Laws.col_after(one(cc), Laws.col_after(rword(buf), rcol(rplaced(toks)))),
    col.app(rword(buf), one(cc), rcol(rplaced(toks)))) :
    {Lex.St{m, k, Laws.line_after(one(cc), Laws.line_after(rword(buf), rline(rplaced(toks)))), _,
      rline(rplaced(toks)), rcol(rplaced(toks)), cc <> buf, rplaced(rplaced(toks))}
    == Lex.St{m, k,
      Bool.pick(U32, Lex.is_newline(cc), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(cc), 0, (ca(buf, toks) + 1 : U32)),
      rline(toks), rcol(toks), cc <> buf, rplaced(toks)} : Lex.St}
  %Equal.sym(String, rspell(rplaced(toks)), rspell(toks), rplaced.spell(toks)) :
    {Lex.St{m, k, Laws.line_after(one(cc), Laws.line_after(rword(buf), Laws.line_after(_, 0))),
      Laws.col_after(one(cc), Laws.col_after(rword(buf), Laws.col_after(_, 0))),
      Laws.line_after(_, 0), Laws.col_after(_, 0), cc <> buf, rplaced(rplaced(toks))}
    == Lex.St{m, k,
      Bool.pick(U32, Lex.is_newline(cc), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(cc), 0, (ca(buf, toks) + 1 : U32)),
      rline(toks), rcol(toks), cc <> buf, rplaced(toks)} : Lex.St}
  %Equal.sym(List<&2, Lex.Tok>, rplaced(rplaced(toks)), rplaced(toks), rplaced.idem(toks)) :
    {Lex.St{m, k, Laws.line_after(one(cc), la(buf, toks)),
      Laws.col_after(one(cc), ca(buf, toks)),
      rline(toks), rcol(toks), cc <> buf, _}
    == Lex.St{m, k,
      Bool.pick(U32, Lex.is_newline(cc), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(cc), 0, (ca(buf, toks) + 1 : U32)),
      rline(toks), rcol(toks), cc <> buf, rplaced(toks)} : Lex.St}
  {==}

# a char that starts a token flushes the last one where it began, and moves
# the position past itself
law pos.begin:
  for +cc: Char
  for +m: Lex.Mode
  for +k2: Lex.TokKind
  for +k: Lex.TokKind
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {ghost(Lex.St{m, k2,
      Bool.pick(U32, Lex.is_newline(cc), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(cc), 0, (ca(buf, toks) + 1 : U32)),
      la(buf, toks), ca(buf, toks), [cc],
      Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))})
    == Lex.St{m, k2,
      Bool.pick(U32, Lex.is_newline(cc), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(cc), 0, (ca(buf, toks) + 1 : U32)),
      la(buf, toks), ca(buf, toks), [cc],
      Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))} : Lex.St}

def pos.begin(cc, m, k2, k, buf, toks):
  %Equal.sym(U32, rline(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))),
    la(buf, toks), pos.flush.line(k, buf, toks)) :
    {Lex.St{m, k2, Laws.line_after(one(cc), _),
      Laws.col_after(one(cc), rcol(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks)))),
      _, rcol(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))), [cc],
      rplaced(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks)))}
    == Lex.St{m, k2,
      Bool.pick(U32, Lex.is_newline(cc), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(cc), 0, (ca(buf, toks) + 1 : U32)),
      la(buf, toks), ca(buf, toks), [cc],
      Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))} : Lex.St}
  %Equal.sym(U32, rcol(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))),
    ca(buf, toks), pos.flush.col(k, buf, toks)) :
    {Lex.St{m, k2, Laws.line_after(one(cc), la(buf, toks)),
      Laws.col_after(one(cc), _),
      la(buf, toks), _, [cc],
      rplaced(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks)))}
    == Lex.St{m, k2,
      Bool.pick(U32, Lex.is_newline(cc), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(cc), 0, (ca(buf, toks) + 1 : U32)),
      la(buf, toks), ca(buf, toks), [cc],
      Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))} : Lex.St}
  %Equal.sym(List<&2, Lex.Tok>, rplaced(Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))),
    Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks)), pos.flush.placed(k, buf, toks)) :
    {Lex.St{m, k2, Laws.line_after(one(cc), la(buf, toks)),
      Laws.col_after(one(cc), ca(buf, toks)),
      la(buf, toks), ca(buf, toks), [cc], _}
    == Lex.St{m, k2,
      Bool.pick(U32, Lex.is_newline(cc), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(cc), 0, (ca(buf, toks) + 1 : U32)),
      la(buf, toks), ca(buf, toks), [cc],
      Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))} : Lex.St}
  {==}

# one char read from a state whose positions are the recomputed ones keeps
# them so
law pos.step:
  for +cc: Char
  for +m: Lex.Mode
  for +k: Lex.TokKind
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {ghost(Lex.step(cc, ghost(Lex.St{m, k, 0, 0, 0, 0, buf, toks})))
    == Lex.step(cc, ghost(Lex.St{m, k, 0, 0, 0, 0, buf, toks})) : Lex.St}

def pos.step(cc, m, k, buf, toks):
  pos.pick(Lex.continues(m, Lex.classify(cc)),
    Lex.St{Lex.after(m, Lex.classify(cc)), k,
      Bool.pick(U32, Lex.is_newline(cc), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(cc), 0, (ca(buf, toks) + 1 : U32)),
      rline(toks), rcol(toks), cc <> buf, rplaced(toks)},
    Lex.St{Lex.begin.mode(Lex.classify(cc)), Lex.begin.kind(Lex.classify(cc)),
      Bool.pick(U32, Lex.is_newline(cc), (la(buf, toks) + 1 : U32), la(buf, toks)),
      Bool.pick(U32, Lex.is_newline(cc), 0, (ca(buf, toks) + 1 : U32)),
      la(buf, toks), ca(buf, toks), [cc],
      Lex.flush(k, rline(toks), rcol(toks), buf, rplaced(toks))},
    pos.cont(cc, Lex.after(m, Lex.classify(cc)), k, buf, toks),
    pos.begin(cc, Lex.begin.mode(Lex.classify(cc)), Lex.begin.kind(Lex.classify(cc)), k, buf, toks))

# pos.step, for any state recomputed
law pos.step.on:
  for +cc: Char
  for +st: Lex.St
  {ghost(Lex.step(cc, ghost(st))) == Lex.step(cc, ghost(st)) : Lex.St}

def pos.step.on(cc, st):
  match st:
    case Lex.St{m, k, _l, _c, _sl, _sc, buf, toks}:
      pos.step(cc, m, k, buf, toks)

# a step keeps the positions the recomputed ones
law pos.kept:
  for +cc: Char
  for +st: Lex.St
  for +e: {ghost(st) == st : Lex.St}
  {ghost(Lex.step(cc, st)) == Lex.step(cc, st) : Lex.St}

def pos.kept(cc, st, e):
  %e : {ghost(Lex.step(cc, _)) == Lex.step(cc, _) : Lex.St}
  pos.step.on(cc, st)

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
      %Equal.sym(U32, Laws.line_after(String.append(rspell(rest), t), 0),
        Laws.line_after(t, rline(rest)), line.app(rspell(rest), t, 0)) :
        {List.reverse.go(&2, Lex.Tok, rplaced(rest),
          Lex.Tok{k, t, rline(rest), rcol(rest)}
            <> Laws.placed(acc, Laws.line_after(t, rline(rest)), Laws.col_after(t, rcol(rest))))
          == List.reverse.go(&2, Lex.Tok, rplaced(rest),
          Lex.Tok{k, t, rline(rest), rcol(rest)}
            <> Laws.placed(acc, _, Laws.col_after(String.append(rspell(rest), t), 0)))
          : List<&2, Lex.Tok>}
      %Equal.sym(U32, Laws.col_after(String.append(rspell(rest), t), 0),
        Laws.col_after(t, rcol(rest)), col.app(rspell(rest), t, 0)) :
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
