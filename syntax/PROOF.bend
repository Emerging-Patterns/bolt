# syntax: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./lex.bend as Lex
import ./tree.bend as Tree
import ../lazy/lazy.bend as Lazy
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

# the tree (BOLT-SYN-3)
# ---------------------
# The machine's stack is read as the leaves it holds so far, newest first:
# vg is that list while the stack is well formed, None when it is not. Every
# step keeps it the reversed leaves of the tokens read, so the finished tree
# reads them back in order.

# Unit for None, Empty for Some: a motive that tells them apart
def none_ty(mm: Maybe<&2, List<&2, Lex.Tok>>) -> Type:
  match mm:
    case None{}:
      Unit
    case Some{_a}:
      Empty

# None is never Some
law none_some:
  for -a: List<&2, Lex.Tok>
  for e: {None{} == Some{a} : Maybe<&2, List<&2, Lex.Tok>>}
  Empty

def none_some(_a, e):
  %e : none_ty(_)
  Unit{}

# Unit for 0, Empty for a successor
def zero_ty(nn: Nat) -> Type:
  match nn:
    case Zero{}:
      Unit
    case Succ{_p}:
      Empty

# 0 is never a successor
law zero_succ:
  for -p: Nat
  for e: {0n == 1n+p : Nat}
  Empty

def zero_succ(_p, e):
  %e : zero_ty(_)
  Unit{}

# Unit for False, Empty for True
def false_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Unit
    case True{}:
      Empty

# False is never True
law false_true:
  for e: {False{} == True{} : Bool}
  Empty

def false_true(e):
  %e : false_ty(_)
  Unit{}

# a chain stored reversed, its leaves pushed onto acc oldest first: what the
# chain gives once reversed back
def rgo(cells: Tree.Node, acc: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match cells:
    case Tree.NCons{h, t}:
      Tree.leaves.go(h, rgo(t, acc))
    case _other:
      acc

# a node's leaves onto a known list
def m_leaf(mm: Maybe<&2, List<&2, Lex.Tok>>, nn: Tree.Node) -> Maybe<&2, List<&2, Lex.Tok>>:
  match mm:
    case None{}:
      None{}
    case Some{a}:
      Some{Tree.leaves.go(nn, a)}

# a group's close, if any, onto a known list
def m_close(mm: Maybe<&2, List<&2, Lex.Tok>>, close: Maybe<&2, Lex.Tok>) -> Maybe<&2, List<&2, Lex.Tok>>:
  match mm:
    case None{}:
      None{}
    case Some{a}:
      Some{Tree.leaf_close(close, a)}

# an open group's bracket and kids onto a known list
def m_group(mm: Maybe<&2, List<&2, Lex.Tok>>, open: Lex.Tok, kids: Tree.Node) -> Maybe<&2, List<&2, Lex.Tok>>:
  match mm:
    case None{}:
      None{}
    case Some{a}:
      Some{rgo(kids, open <> a)}

# an open statement's kids, then its body, onto a known list
def m_stmt(mm: Maybe<&2, List<&2, Lex.Tok>>, kids: Tree.Node, body: Tree.Node) -> Maybe<&2, List<&2, Lex.Tok>>:
  match mm:
    case None{}:
      None{}
    case Some{a}:
      Some{rgo(body, rgo(kids, a))}

# tokens, in order, onto a known list
def m_toks(mm: Maybe<&2, List<&2, Lex.Tok>>, xs: List<&2, Lex.Tok>) -> Maybe<&2, List<&2, Lex.Tok>>:
  match mm:
    case None{}:
      None{}
    case Some{a}:
      Some{List.reverse.go(&2, Lex.Tok, xs, a)}

# the leaves of a stack of statements over the root, newest first
def vs(stack: List<&2, Tree.Frame>) -> Maybe<&2, List<&2, Lex.Tok>>:
  match stack:
    case Con{Tree.FStmt{_i, kids, body}, rest}:
      m_stmt(vs(rest), kids, body)
    case Con{Tree.FRoot{body}, _rest}:
      Some{rgo(body, [])}
    case _other:
      None{}

# the leaves of a well-formed stack, newest first: groups over statements
# over the root, the innermost statement with no body yet
def vg(stack: List<&2, Tree.Frame>) -> Maybe<&2, List<&2, Lex.Tok>>:
  match stack:
    case Con{Tree.FGroup{open, kids}, rest}:
      m_group(vg(rest), open, kids)
    case Con{Tree.FStmt{_i, kids, Tree.NNil{}}, rest}:
      m_stmt(vs(rest), kids, Tree.NNil{})
    case Con{Tree.FRoot{body}, _rest}:
      Some{rgo(body, [])}
    case _other:
      None{}

# a chain reversed onto another, read: the first's leaves, then the other's
law rev:
  for +x: Tree.Node
  for +m: Tree.Node
  for +acc: List<&2, Lex.Tok>
  {Tree.leaves.go(Tree.reverse(x, m), acc) == Tree.leaves.go(m, rgo(x, acc)) : List<&2, Lex.Tok>}

def rev(x, m, acc):
  match x:
    case Tree.NCons{h, t}:
      rev(t, Tree.NCons{h, m}, acc)
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_o, _k, _c}:
      {==}
    case Tree.Stmt{_kd, _k, _b}:
      {==}
    case Tree.NNil{}:
      {==}

# a node put into a group's kids lands on the group's leaves
law put.group:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  for +o: Lex.Tok
  for +k: Tree.Node
  for +nn: Tree.Node
  {m_group(mm, o, Tree.NCons{nn, k}) == m_leaf(m_group(mm, o, k), nn) : Maybe<&2, List<&2, Lex.Tok>>}

def put.group(mm, _o, _k, _nn):
  match mm:
    case None{}:
      {==}
    case Some{_a}:
      {==}

# a node put into a statement's kids lands on its leaves, while it has no body
law put.stmt:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  for +k: Tree.Node
  for +nn: Tree.Node
  {m_stmt(mm, Tree.NCons{nn, k}, Tree.NNil{}) == m_leaf(m_stmt(mm, k, Tree.NNil{}), nn) : Maybe<&2, List<&2, Lex.Tok>>}

def put.stmt(mm, _k, _nn):
  match mm:
    case None{}:
      {==}
    case Some{_a}:
      {==}

# a finished node lands on the leaves of the stack
law put:
  for +s: List<&2, Tree.Frame>
  for +nn: Tree.Node
  {vg(Tree.put(s, nn)) == m_leaf(vg(s), nn) : Maybe<&2, List<&2, Lex.Tok>>}

def put(s, nn):
  match s:
    case Nil{}:
      {==}
    case Con{Tree.FGroup{o, k}, rest}:
      put.group(vg(rest), o, k, nn)
    case Con{Tree.FStmt{_i, k, Tree.NNil{}}, rest}:
      put.stmt(vs(rest), k, nn)
    case Con{Tree.FStmt{_i, _k, Tree.NCons{_h, _t}}, _rest}:
      {==}
    case Con{Tree.FStmt{_i, _k, Tree.Leaf{_x}}, _rest}:
      {==}
    case Con{Tree.FStmt{_i, _k, Tree.Group{_x, _y, _z}}, _rest}:
      {==}
    case Con{Tree.FStmt{_i, _k, Tree.Stmt{_x, _y, _z}}, _rest}:
      {==}
    case Con{Tree.FRoot{_b}, _rest}:
      {==}

# a closed group's leaves: its bracket, its kids, then its close, if any
law close.m:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  for +o: Lex.Tok
  for +k: Tree.Node
  for +cl: Maybe<&2, Lex.Tok>
  {m_leaf(mm, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), cl}) == m_close(m_group(mm, o, k), cl)
    : Maybe<&2, List<&2, Lex.Tok>>}

def close.m(mm, o, k, cl):
  match mm:
    case None{}:
      {==}
    case Some{a}:
      Equal.cong(List<&2, Lex.Tok>, Maybe<&2, List<&2, Lex.Tok>>, x => Some{Tree.leaf_close(cl, x)},
        Tree.leaves.go(Tree.reverse(k, Tree.NNil{}), o <> a), rgo(k, o <> a), rev(k, Tree.NNil{}, o <> a))

# closing the group on top adds its close to the leaves
law close.group:
  for +o: Lex.Tok
  for +k: Tree.Node
  for +rest: List<&2, Tree.Frame>
  for +cl: Maybe<&2, Lex.Tok>
  {vg(Tree.close_one(Tree.FGroup{o, k} <> rest, cl)) == m_close(vg(Tree.FGroup{o, k} <> rest), cl)
    : Maybe<&2, List<&2, Lex.Tok>>}

def close.group(o, k, rest, cl):
  Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
    vg(Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), cl})),
    m_leaf(vg(rest), Tree.Group{o, Tree.reverse(k, Tree.NNil{}), cl}),
    m_close(m_group(vg(rest), o, k), cl),
    put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), cl}),
    close.m(vg(rest), o, k, cl))

# no close adds nothing
law m_close.none:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  {m_close(mm, None{}) == mm : Maybe<&2, List<&2, Lex.Tok>>}

def m_close.none(mm):
  match mm:
    case None{}:
      {==}
    case Some{_a}:
      {==}

# a group closed by nothing keeps the leaves
law close.none:
  for +s: List<&2, Tree.Frame>
  {vg(Tree.close_one(s, None{})) == vg(s) : Maybe<&2, List<&2, Lex.Tok>>}

def close.none(s):
  match s:
    case Con{Tree.FGroup{o, k}, rest}:
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
        vg(Tree.close_one(Tree.FGroup{o, k} <> rest, None{})),
        m_close(vg(Tree.FGroup{o, k} <> rest), None{}),
        vg(Tree.FGroup{o, k} <> rest),
        close.group(o, k, rest, None{}),
        m_close.none(vg(Tree.FGroup{o, k} <> rest)))
    case Con{Tree.FStmt{_i, _k, _b}, _rest}:
      {==}
    case Con{Tree.FRoot{_b}, _rest}:
      {==}
    case Nil{}:
      {==}

# groups closed by nothing keep the leaves
law close_n.none:
  for +n: Nat
  for +s: List<&2, Tree.Frame>
  {vg(Tree.close_n(n, s, None{})) == vg(s) : Maybe<&2, List<&2, Lex.Tok>>}

def close_n.none(n, s):
  match n:
    case Zero{}:
      {==}
    case Succ{Zero{}}:
      close.none(s)
    case Succ{Succ{q}}:
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
        vg(Tree.close_n(1n+q, Tree.close_one(s, None{}), None{})),
        vg(Tree.close_one(s, None{})),
        vg(s),
        close_n.none(1n+q, Tree.close_one(s, None{})),
        close.none(s))

# closing every group keeps the leaves
law close_all:
  for +s: List<&2, Tree.Frame>
  {vg(Tree.close_all(s)) == vg(s) : Maybe<&2, List<&2, Lex.Tok>>}

def close_all(s):
  close_n.none(Tree.groups(s), s)

# are the top n frames of the stack all open groups?
def at_least(nn: Nat, stack: List<&2, Tree.Frame>) -> Bool:
  match nn stack:
    case Zero{} _s:
      True{}
    case Succ{p} Con{Tree.FGroup{_o, _k}, rest}:
      at_least(p, rest)
    case Succ{_p} _other:
      False{}

# a put leaves the frames' kinds as they were
law at_least.put:
  for +n: Nat
  for +s: List<&2, Tree.Frame>
  for +x: Tree.Node
  {at_least(n, Tree.put(s, x)) == at_least(n, s) : Bool}

def at_least.put(n, s, _x):
  match n s:
    case Zero{} _s:
      {==}
    case Succ{_p} Nil{}:
      {==}
    case Succ{_p} Con{Tree.FGroup{_o, _k}, _rest}:
      {==}
    case Succ{_p} Con{Tree.FStmt{_i, _k, _b}, _rest}:
      {==}
    case Succ{_p} Con{Tree.FRoot{_b}, _rest}:
      {==}

# whichever count the search stops on, the groups are there
law al.stop:
  for +b: Bool
  for -x: Nat
  for -f: Unit -> Nat
  for -s: List<&2, Tree.Frame>
  for ex: {at_least(x, s) == True{} : Bool}
  for ef: {at_least(f(Unit{}), s) == True{} : Bool}
  {at_least(Lazy.stop(Nat, b, x, f), s) == True{} : Bool}

def al.stop(b, _x, _f, _s, ex, ef):
  match b:
    case True{}:
      ex
    case False{}:
      ef

# one more group above the ones found below
law al.up:
  for +d: Nat
  for -o: Lex.Tok
  for -k: Tree.Node
  for -rest: List<&2, Tree.Frame>
  for e: {at_least(d, rest) == True{} : Bool}
  {at_least(Tree.depth_to.up(d), Tree.FGroup{o, k} <> rest) == True{} : Bool}

def al.up(d, _o, _k, _rest, e):
  match d:
    case Zero{}:
      {==}
    case Succ{_p}:
      e

# the groups a close bracket reaches down to are all open groups
law at_least.depth:
  for +s: List<&2, Tree.Frame>
  for +cc: String
  {at_least(Tree.depth_to(s, cc), s) == True{} : Bool}

def at_least.depth(s, cc):
  match s:
    case Con{Tree.FGroup{Lex.Tok{k, t, l, c2}, kids}, rest}:
      al.stop(String.eq(Tree.closer(t), cc), 1n,
        _u => Lazy.stop(Nat, String.eq(cc, ">"), 0n, _v => Tree.depth_to.up(Tree.depth_to(rest, cc))),
        Tree.FGroup{Lex.Tok{k, t, l, c2}, kids} <> rest, {==},
        al.stop(String.eq(cc, ">"), 0n, _v => Tree.depth_to.up(Tree.depth_to(rest, cc)),
          Tree.FGroup{Lex.Tok{k, t, l, c2}, kids} <> rest, {==},
          al.up(Tree.depth_to(rest, cc), Lex.Tok{k, t, l, c2}, kids, rest, at_least.depth(rest, cc))))
    case Con{Tree.FStmt{_i, _k, _b}, _rest}:
      {==}
    case Con{Tree.FRoot{_b}, _rest}:
      {==}
    case Nil{}:
      {==}

# closing groups that are all there adds the close, if any, to the leaves
law close_n.some:
  for +p: Nat
  for +s: List<&2, Tree.Frame>
  for +cl: Maybe<&2, Lex.Tok>
  for e: {at_least(1n+p, s) == True{} : Bool}
  {vg(Tree.close_n(1n+p, s, cl)) == m_close(vg(s), cl) : Maybe<&2, List<&2, Lex.Tok>>}

def close_n.some(p, s, cl, e):
  match p s:
    case Zero{} Con{Tree.FGroup{o, k}, rest}:
      close.group(o, k, rest, cl)
    case Succ{q} Con{Tree.FGroup{o, k}, rest}:
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
        vg(Tree.close_n(1n+q, Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}}), cl)),
        m_close(vg(Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}})), cl),
        m_close(vg(Tree.FGroup{o, k} <> rest), cl),
        close_n.some(q, Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}}), cl,
          Equal.trans(Bool, at_least(1n+q, Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}})),
            at_least(1n+q, rest), True{},
            at_least.put(1n+q, rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}}), e)),
        Equal.cong(Maybe<&2, List<&2, Lex.Tok>>, Maybe<&2, List<&2, Lex.Tok>>, m => m_close(m, cl),
          vg(Tree.close_one(Tree.FGroup{o, k} <> rest, None{})), vg(Tree.FGroup{o, k} <> rest),
          close.none(Tree.FGroup{o, k} <> rest)))
    case _p Nil{}:
      Empty.absurd({vg(Tree.close_n(1n+_p, [], cl)) == m_close(vg([]), cl) : Maybe<&2, List<&2, Lex.Tok>>},
        false_true(e))
    case _p Con{Tree.FStmt{i, k, b}, rest}:
      Empty.absurd({vg(Tree.close_n(1n+_p, Tree.FStmt{i, k, b} <> rest, cl))
        == m_close(vg(Tree.FStmt{i, k, b} <> rest), cl) : Maybe<&2, List<&2, Lex.Tok>>},
        false_true(e))
    case _p Con{Tree.FRoot{b}, rest}:
      Empty.absurd({vg(Tree.close_n(1n+_p, Tree.FRoot{b} <> rest, cl))
        == m_close(vg(Tree.FRoot{b} <> rest), cl) : Maybe<&2, List<&2, Lex.Tok>>},
        false_true(e))

# a close that closes a group is that group's last leaf
law m_close.some:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  for +tok: Lex.Tok
  {m_close(mm, Some{tok}) == m_leaf(mm, Tree.Leaf{tok}) : Maybe<&2, List<&2, Lex.Tok>>}

def m_close.some(mm, _tok):
  match mm:
    case None{}:
      {==}
    case Some{_a}:
      {==}

# a close bracket is a leaf: a stray one when it reaches no group, else the
# close of the group it reaches
law close.to:
  for +n: Nat
  for +s: List<&2, Tree.Frame>
  for +tok: Lex.Tok
  for e: {at_least(n, s) == True{} : Bool}
  {vg(Lazy.stop(List<&2, Tree.Frame>, Nat.is_eq(n, 0n), Tree.put(s, Tree.Leaf{tok}),
    _u => Tree.close_n(n, s, Some{tok}))) == m_leaf(vg(s), Tree.Leaf{tok}) : Maybe<&2, List<&2, Lex.Tok>>}

def close.to(n, s, tok, e):
  match n:
    case Zero{}:
      put(s, Tree.Leaf{tok})
    case Succ{p}:
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
        vg(Tree.close_n(1n+p, s, Some{tok})),
        m_close(vg(s), Some{tok}),
        m_leaf(vg(s), Tree.Leaf{tok}),
        close_n.some(p, s, Some{tok}, e),
        m_close.some(vg(s), tok))

# a close bracket adds itself to the leaves
law close_tok:
  for +s: List<&2, Tree.Frame>
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  {vg(Tree.close_tok(s, Lex.Tok{k, t, l, c})) == m_leaf(vg(s), Tree.Leaf{Lex.Tok{k, t, l, c}})
    : Maybe<&2, List<&2, Lex.Tok>>}

def close_tok(s, k, t, l, c):
  close.to(Tree.depth_to(s, t), s, Lex.Tok{k, t, l, c}, at_least.depth(s, t))

# no tokens add nothing
law m_toks.nil:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  {m_toks(mm, []) == mm : Maybe<&2, List<&2, Lex.Tok>>}

def m_toks.nil(mm):
  match mm:
    case None{}:
      {==}
    case Some{_a}:
      {==}

# a leaf is its one token
law m_toks.one:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  for +tok: Lex.Tok
  {m_leaf(mm, Tree.Leaf{tok}) == m_toks(mm, [tok]) : Maybe<&2, List<&2, Lex.Tok>>}

def m_toks.one(mm, _tok):
  match mm:
    case None{}:
      {==}
    case Some{_a}:
      {==}

# a leaf, then tokens: the leaf's token first
law m_toks.con:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  for +tok: Lex.Tok
  for +ys: List<&2, Lex.Tok>
  {m_toks(m_leaf(mm, Tree.Leaf{tok}), ys) == m_toks(mm, tok <> ys) : Maybe<&2, List<&2, Lex.Tok>>}

def m_toks.con(mm, _tok, _ys):
  match mm:
    case None{}:
      {==}
    case Some{_a}:
      {==}

# a run of `>` adds one `>` per char
law close_gts:
  for +cs: List<&2, Char>
  for +s: List<&2, Tree.Frame>
  for +l: U32
  for +c: U32
  {vg(Tree.close_gts(cs, s, l, c)) == m_toks(vg(s), Laws.gts(cs, l, c)) : Maybe<&2, List<&2, Lex.Tok>>}

def close_gts(cs, s, l, c):
  match cs:
    case Nil{}:
      Equal.sym(Maybe<&2, List<&2, Lex.Tok>>, m_toks(vg(s), []), vg(s), m_toks.nil(vg(s)))
    case Con{_ch, t}:
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
        vg(Tree.close_gts(t, Tree.close_tok(s, Lex.Tok{Lex.TOp{}, ">", l, c}), l, (c + 1 : U32))),
        m_toks(vg(Tree.close_tok(s, Lex.Tok{Lex.TOp{}, ">", l, c})), Laws.gts(t, l, (c + 1 : U32))),
        m_toks(vg(s), Lex.Tok{Lex.TOp{}, ">", l, c} <> Laws.gts(t, l, (c + 1 : U32))),
        close_gts(t, Tree.close_tok(s, Lex.Tok{Lex.TOp{}, ">", l, c}), l, (c + 1 : U32)),
        Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
          m_toks(vg(Tree.close_tok(s, Lex.Tok{Lex.TOp{}, ">", l, c})), Laws.gts(t, l, (c + 1 : U32))),
          m_toks(m_leaf(vg(s), Tree.Leaf{Lex.Tok{Lex.TOp{}, ">", l, c}}), Laws.gts(t, l, (c + 1 : U32))),
          m_toks(vg(s), Lex.Tok{Lex.TOp{}, ">", l, c} <> Laws.gts(t, l, (c + 1 : U32))),
          Equal.cong(Maybe<&2, List<&2, Lex.Tok>>, Maybe<&2, List<&2, Lex.Tok>>,
            m => m_toks(m, Laws.gts(t, l, (c + 1 : U32))),
            vg(Tree.close_tok(s, Lex.Tok{Lex.TOp{}, ">", l, c})),
            m_leaf(vg(s), Tree.Leaf{Lex.Tok{Lex.TOp{}, ">", l, c}}),
            close_tok(s, Lex.TOp{}, ">", l, c)),
          m_toks.con(vg(s), Lex.Tok{Lex.TOp{}, ">", l, c}, Laws.gts(t, l, (c + 1 : U32)))))

# a close adds a run of `>` split, or itself
law close_any.at:
  for +gt: Bool
  for +s: List<&2, Tree.Frame>
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  {vg(Tree.close_any.at(gt, s, Lex.Tok{k, t, l, c}, t, l, c))
    == m_toks(vg(s), Bool.pick(List<&2, Lex.Tok>, gt, Laws.gts(String.to_list(t), l, c), [Lex.Tok{k, t, l, c}]))
    : Maybe<&2, List<&2, Lex.Tok>>}

def close_any.at(gt, s, k, t, l, c):
  match gt:
    case True{}:
      close_gts(String.to_list(t), s, l, c)
    case False{}:
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
        vg(Tree.close_tok(s, Lex.Tok{k, t, l, c})),
        m_leaf(vg(s), Tree.Leaf{Lex.Tok{k, t, l, c}}),
        m_toks(vg(s), [Lex.Tok{k, t, l, c}]),
        close_tok(s, k, t, l, c),
        m_toks.one(vg(s), Lex.Tok{k, t, l, c}))

# an open bracket's leaves so far: itself
law m_group.one:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  for +tok: Lex.Tok
  {m_group(mm, tok, Tree.NNil{}) == m_toks(mm, [tok]) : Maybe<&2, List<&2, Lex.Tok>>}

def m_group.one(mm, _tok):
  match mm:
    case None{}:
      {==}
    case Some{_a}:
      {==}

# an opener or a leaf adds itself
law push.leaf:
  for +o: Bool
  for +s: List<&2, Tree.Frame>
  for +tok: Lex.Tok
  {vg(Bool.pick(List<&2, Tree.Frame>, o, Tree.FGroup{tok, Tree.NNil{}} <> s, Tree.put(s, Tree.Leaf{tok})))
    == m_toks(vg(s), [tok]) : Maybe<&2, List<&2, Lex.Tok>>}

def push.leaf(o, s, tok):
  match o:
    case True{}:
      m_group.one(vg(s), tok)
    case False{}:
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
        vg(Tree.put(s, Tree.Leaf{tok})),
        m_leaf(vg(s), Tree.Leaf{tok}),
        m_toks(vg(s), [tok]),
        put(s, Tree.Leaf{tok}),
        m_toks.one(vg(s), tok))

# a token pushed adds itself, or, when it closes, what its close adds
law push.at:
  for +b: Bool
  for +o: Bool
  for +s: List<&2, Tree.Frame>
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  {vg(Lazy.stop(List<&2, Tree.Frame>, Bool.not(b),
      Bool.pick(List<&2, Tree.Frame>, o, Tree.FGroup{Lex.Tok{k, t, l, c}, Tree.NNil{}} <> s,
        Tree.put(s, Tree.Leaf{Lex.Tok{k, t, l, c}})),
      _u => Tree.close_any(s, Lex.Tok{k, t, l, c})))
    == m_toks(vg(s), Bool.pick(List<&2, Lex.Tok>, Bool.not(b), [Lex.Tok{k, t, l, c}],
      Bool.pick(List<&2, Lex.Tok>, String.starts_with(t, ">"), Laws.gts(String.to_list(t), l, c),
        [Lex.Tok{k, t, l, c}])))
    : Maybe<&2, List<&2, Lex.Tok>>}

def push.at(b, o, s, k, t, l, c):
  match b:
    case True{}:
      close_any.at(String.starts_with(t, ">"), s, k, t, l, c)
    case False{}:
      push.leaf(o, s, Lex.Tok{k, t, l, c})

# what the tree adds for a significant token: itself, or, when it closes,
# what its close adds
def code_adds(+k: Lex.TokKind, +t: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  Bool.pick(List<&2, Lex.Tok>, Bool.not(Tree.closes_with(k, t)), [Lex.Tok{k, t, l, c}],
    Bool.pick(List<&2, Lex.Tok>, String.starts_with(t, ">"), Laws.gts(String.to_list(t), l, c), [Lex.Tok{k, t, l, c}]))

# what the law adds for a significant token: a run of `>` split, else itself
def law_adds(+k: Lex.TokKind, +t: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  Bool.pick(List<&2, Lex.Tok>, Laws.gt_run(k, t), Laws.gts(String.to_list(t), l, c), [Lex.Tok{k, t, l, c}])

# a token pushed adds itself, or, when it closes, what its close adds
law push:
  for +s: List<&2, Tree.Frame>
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +g: Bool
  {vg(Tree.push(s, Lex.Tok{k, t, l, c}, g))
    == m_toks(vg(s), code_adds(k, t, l, c))
    : Maybe<&2, List<&2, Lex.Tok>>}

def push(s, k, t, l, c, g):
  push.at(Tree.closes_with(k, t), Bool.or(Lex.is_open(k), Tree.opens_angle(k, t, g)), s, k, t, l, c)

# the tree's test for a run of `>` is the law's
law only_gt:
  for +cs: List<&2, Char>
  {Laws.only_gt(cs) == Tree.all_gt(cs) : Bool}

def only_gt(cs):
  match cs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Bool, Bool, x => Lazy.and_then(Char.is_eq(h, '>'), _u => x),
        Laws.only_gt(t), Tree.all_gt(t), only_gt(t))

# every text starts with the empty one
law starts_nil:
  for +s: String
  {True{} == String.starts_with(s, SNil{}) : Bool}

def starts_nil(s):
  match s:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

# picking on a negation swaps the branches
law not_pick:
  for +x: Bool
  for +a: List<&2, Lex.Tok>
  for +b: List<&2, Lex.Tok>
  {Bool.pick(List<&2, Lex.Tok>, Bool.not(x), a, b) == Bool.pick(List<&2, Lex.Tok>, x, b, a) : List<&2, Lex.Tok>}

def not_pick(x, _a, _b):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# an operator past its first char, by whether that char is a `>`
law decide.op:
  for +b: Bool
  for +r: String
  for +gs: List<&2, Lex.Tok>
  for +one: List<&2, Lex.Tok>
  {Bool.pick(List<&2, Lex.Tok>, Bool.not(Lazy.and_then(b, _u => Tree.all_gt(String.to_list(r)))), one,
      Bool.pick(List<&2, Lex.Tok>, String.starts_with.if(r, SNil{}, b), gs, one))
    == Bool.pick(List<&2, Lex.Tok>, Lazy.and_then(b, _u => Laws.only_gt(String.to_list(r))), gs, one)
    : List<&2, Lex.Tok>}

def decide.op(b, r, gs, one):
  match b:
    case False{}:
      {==}
    case True{}:
      %starts_nil(r) :
        {Bool.pick(List<&2, Lex.Tok>, Bool.not(Tree.all_gt(String.to_list(r))), one,
          Bool.pick(List<&2, Lex.Tok>, _, gs, one))
          == Bool.pick(List<&2, Lex.Tok>, Laws.only_gt(String.to_list(r)), gs, one) : List<&2, Lex.Tok>}
      %only_gt(String.to_list(r)) :
        {Bool.pick(List<&2, Lex.Tok>, Bool.not(_), one, gs)
          == Bool.pick(List<&2, Lex.Tok>, Laws.only_gt(String.to_list(r)), gs, one) : List<&2, Lex.Tok>}
      not_pick(Laws.only_gt(String.to_list(r)), one, gs)

# the tree splits a token exactly when the law says it is a run of `>`
law decide:
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  {code_adds(k, t, l, c)
    == law_adds(k, t, l, c)
    : List<&2, Lex.Tok>}

def decide(k, t, l, c):
  match k t:
    case Lex.TOp{} SNil{}:
      {==}
    case Lex.TOp{} SCon{h, r}:
      decide.op(Char.is_eq(h, '>'), r, Laws.gts(String.to_list(SCon{h, r}), l, c),
        [Lex.Tok{Lex.TOp{}, SCon{h, r}, l, c}])
    case Lex.TClose{} _t:
      {==}
    case Lex.TName{} _t:
      {==}
    case Lex.TUpper{} _t:
      {==}
    case Lex.TDotted{} _t:
      {==}
    case Lex.TWild{} _t:
      {==}
    case Lex.TKey{} _t:
      {==}
    case Lex.TNum{} _t:
      {==}
    case Lex.TStr{} _t:
      {==}
    case Lex.TChar{} _t:
      {==}
    case Lex.TComment{} _t:
      {==}
    case Lex.TSpace{} _t:
      {==}
    case Lex.TNewline{} _t:
      {==}
    case Lex.TColon{} _t:
      {==}
    case Lex.TEq{} _t:
      {==}
    case Lex.TBind{} _t:
      {==}
    case Lex.TArrow{} _t:
      {==}
    case Lex.TLam{} _t:
      {==}
    case Lex.TAll{} _t:
      {==}
    case Lex.TAmp{} _t:
      {==}
    case Lex.TOpen{} _t:
      {==}
    case Lex.TComma{} _t:
      {==}

# a finished statement's leaves: its kids, then its body
law stmt_leaves:
  for +kd: Tree.StmtKind
  for +k: Tree.Node
  for +b: Tree.Node
  for +acc: List<&2, Lex.Tok>
  {Tree.leaves.go(Tree.Stmt{kd, Tree.reverse(k, Tree.NNil{}), Tree.reverse(b, Tree.NNil{})}, acc)
    == rgo(b, rgo(k, acc)) : List<&2, Lex.Tok>}

def stmt_leaves(_kd, k, b, acc):
  Equal.trans(List<&2, Lex.Tok>,
    Tree.leaves.go(Tree.reverse(b, Tree.NNil{}), Tree.leaves.go(Tree.reverse(k, Tree.NNil{}), acc)),
    Tree.leaves.go(Tree.reverse(b, Tree.NNil{}), rgo(k, acc)),
    rgo(b, rgo(k, acc)),
    Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, x => Tree.leaves.go(Tree.reverse(b, Tree.NNil{}), x),
      Tree.leaves.go(Tree.reverse(k, Tree.NNil{}), acc), rgo(k, acc), rev(k, Tree.NNil{}, acc)),
    rev(b, Tree.NNil{}, rgo(k, acc)))

# a finished statement put in its parent's body keeps the leaves
law end.m:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  for +k2: Tree.Node
  for +b2: Tree.Node
  for +kd: Tree.StmtKind
  for +k: Tree.Node
  for +b: Tree.Node
  {m_stmt(mm, k2, Tree.NCons{Tree.Stmt{kd, Tree.reverse(k, Tree.NNil{}), Tree.reverse(b, Tree.NNil{})}, b2})
    == m_stmt(m_stmt(mm, k2, b2), k, b) : Maybe<&2, List<&2, Lex.Tok>>}

def end.m(mm, k2, b2, kd, k, b):
  match mm:
    case None{}:
      {==}
    case Some{a}:
      Equal.cong(List<&2, Lex.Tok>, Maybe<&2, List<&2, Lex.Tok>>, x => Some{x},
        Tree.leaves.go(Tree.Stmt{kd, Tree.reverse(k, Tree.NNil{}), Tree.reverse(b, Tree.NNil{})}, rgo(b2, rgo(k2, a))),
        rgo(b, rgo(k, rgo(b2, rgo(k2, a)))),
        stmt_leaves(kd, k, b, rgo(b2, rgo(k2, a))))

# finishing the innermost statement keeps the leaves
law end_stmt:
  for +s: List<&2, Tree.Frame>
  {vs(Tree.end_stmt(s)) == vs(s) : Maybe<&2, List<&2, Lex.Tok>>}

def end_stmt(s):
  match s:
    case Con{Tree.FStmt{_i, k, b}, Con{Tree.FStmt{_i2, k2, b2}, r2}}:
      end.m(vs(r2), k2, b2, Tree.classify(Tree.reverse(k, Tree.NNil{})), k, b)
    case Con{Tree.FStmt{_i, k, b}, Con{Tree.FRoot{bd}, _r2}}:
      Equal.cong(List<&2, Lex.Tok>, Maybe<&2, List<&2, Lex.Tok>>, x => Some{x},
        Tree.leaves.go(Tree.Stmt{Tree.classify(Tree.reverse(k, Tree.NNil{})), Tree.reverse(k, Tree.NNil{}),
          Tree.reverse(b, Tree.NNil{})}, rgo(bd, [])),
        rgo(b, rgo(k, rgo(bd, []))),
        stmt_leaves(Tree.classify(Tree.reverse(k, Tree.NNil{})), k, b, rgo(bd, [])))
    case Con{Tree.FStmt{_i, _k, _b}, Con{Tree.FGroup{_o, _k2}, _r2}}:
      {==}
    case Con{Tree.FStmt{_i, _k, _b}, Nil{}}:
      {==}
    case Con{Tree.FGroup{_o, _k}, _rest}:
      {==}
    case Con{Tree.FRoot{_b}, _rest}:
      {==}
    case Nil{}:
      {==}

# finishing statements keeps the leaves
law end_n:
  for +n: Nat
  for +s: List<&2, Tree.Frame>
  {vs(Tree.end_n(n, s)) == vs(s) : Maybe<&2, List<&2, Lex.Tok>>}

def end_n(n, s):
  match n:
    case Zero{}:
      {==}
    case Succ{p}:
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
        vs(Tree.end_n(p, Tree.end_stmt(s))), vs(Tree.end_stmt(s)), vs(s),
        end_n(p, Tree.end_stmt(s)), end_stmt(s))

# an empty statement adds nothing
law m_stmt.nil:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  {m_stmt(mm, Tree.NNil{}, Tree.NNil{}) == mm : Maybe<&2, List<&2, Lex.Tok>>}

def m_stmt.nil(mm):
  match mm:
    case None{}:
      {==}
    case Some{_a}:
      {==}

# a new statement over the ones it leaves open keeps the leaves
law open.go:
  for +s: List<&2, Tree.Frame>
  for +cc: U32
  for -r: List<&2, Lex.Tok>
  for e: {vs(s) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {vg(Tree.FStmt{cc, Tree.NNil{}, Tree.NNil{}} <> Tree.end_n(Tree.deeper(s, cc), s)) == Some{r}
    : Maybe<&2, List<&2, Lex.Tok>>}

def open.go(s, cc, r, e):
  Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
    m_stmt(vs(Tree.end_n(Tree.deeper(s, cc), s)), Tree.NNil{}, Tree.NNil{}),
    vs(s), Some{r},
    Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
      m_stmt(vs(Tree.end_n(Tree.deeper(s, cc), s)), Tree.NNil{}, Tree.NNil{}),
      vs(Tree.end_n(Tree.deeper(s, cc), s)), vs(s),
      m_stmt.nil(vs(Tree.end_n(Tree.deeper(s, cc), s))),
      end_n(Tree.deeper(s, cc), s)),
    e)

# a line's start keeps the leaves
law open_stmt:
  for +s: List<&2, Tree.Frame>
  for +cc: U32
  for -r: List<&2, Lex.Tok>
  for e: {vg(s) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {vg(Tree.open_stmt(s, cc)) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}

def open_stmt(s, cc, r, e):
  match s:
    case Con{Tree.FGroup{_o, _k}, _rest}:
      e
    case Con{Tree.FStmt{i, k, Tree.NNil{}}, rest}:
      open.go(Tree.FStmt{i, k, Tree.NNil{}} <> rest, cc, r, e)
    case Con{Tree.FStmt{i, k, Tree.NCons{h, t}}, rest}:
      Empty.absurd({vg(Tree.open_stmt(Tree.FStmt{i, k, Tree.NCons{h, t}} <> rest, cc)) == Some{r}
        : Maybe<&2, List<&2, Lex.Tok>>}, none_some(r, e))
    case Con{Tree.FStmt{i, k, Tree.Leaf{x}}, rest}:
      Empty.absurd({vg(Tree.open_stmt(Tree.FStmt{i, k, Tree.Leaf{x}} <> rest, cc)) == Some{r}
        : Maybe<&2, List<&2, Lex.Tok>>}, none_some(r, e))
    case Con{Tree.FStmt{i, k, Tree.Group{x, y, z}}, rest}:
      Empty.absurd({vg(Tree.open_stmt(Tree.FStmt{i, k, Tree.Group{x, y, z}} <> rest, cc)) == Some{r}
        : Maybe<&2, List<&2, Lex.Tok>>}, none_some(r, e))
    case Con{Tree.FStmt{i, k, Tree.Stmt{x, y, z}}, rest}:
      Empty.absurd({vg(Tree.open_stmt(Tree.FStmt{i, k, Tree.Stmt{x, y, z}} <> rest, cc)) == Some{r}
        : Maybe<&2, List<&2, Lex.Tok>>}, none_some(r, e))
    case Con{Tree.FRoot{b}, rest}:
      open.go(Tree.FRoot{b} <> rest, cc, r, e)
    case Nil{}:
      e

# whichever stack the cut picks, the leaves are the same
law vg.stop:
  for +b: Bool
  for -x: List<&2, Tree.Frame>
  for -f: Unit -> List<&2, Tree.Frame>
  for -z: Maybe<&2, List<&2, Lex.Tok>>
  for ex: {vg(x) == z : Maybe<&2, List<&2, Lex.Tok>>}
  for ef: {vg(f(Unit{})) == z : Maybe<&2, List<&2, Lex.Tok>>}
  {vg(Lazy.stop(List<&2, Tree.Frame>, b, x, f)) == z : Maybe<&2, List<&2, Lex.Tok>>}

def vg.stop(b, _x, _f, _z, ex, ef):
  match b:
    case True{}:
      ex
    case False{}:
      ef

# a token that starts a line keeps the leaves
law fresh:
  for +s: List<&2, Tree.Frame>
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for -r: List<&2, Lex.Tok>
  for +e: {vg(s) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {vg(Tree.fresh(s, Lex.Tok{k, t, l, c})) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}

def fresh(s, _k, t, _l, c, r, e):
  open_stmt(
    Lazy.stop(List<&2, Tree.Frame>,
      Bool.not(Bool.and(Bool.and(Tree.in_group(s), U32.is_eq(c, 0)), Nat.is_eq(Tree.depth_to(s, t), 0n))),
      s, _u => Tree.close_all(s)),
    c, r,
    vg.stop(Bool.not(Bool.and(Bool.and(Tree.in_group(s), U32.is_eq(c, 0)), Nat.is_eq(Tree.depth_to(s, t), 0n))),
      s, _u => Tree.close_all(s), Some{r}, e,
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>, vg(Tree.close_all(s)), vg(s), Some{r}, close_all(s), e)))

# the machine's stack
def stk(st: Tree.B) -> List<&2, Tree.Frame>:
  match st:
    case Tree.B{_fr, stack}:
      stack

# the leaves one token adds: none when it is trivia, else what the law splits
# it into
def adds(+kk: Lex.TokKind, +tt: String, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  Bool.pick(List<&2, Lex.Tok>, Lex.significant(kk), law_adds(kk, tt, ll, cc), [])

# trivia keeps the leaves; a significant token adds what it adds
law sig.stop:
  for +s: Bool
  for -x: Tree.B
  for -f: Unit -> Tree.B
  for -a: List<&2, Lex.Tok>
  for -r: List<&2, Lex.Tok>
  for ex: {vg(stk(x)) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  for ef: {vg(stk(f(Unit{}))) == Some{List.reverse.go(&2, Lex.Tok, a, r)} : Maybe<&2, List<&2, Lex.Tok>>}
  {vg(stk(Lazy.stop(Tree.B, Bool.not(s), x, f)))
    == Some{List.reverse.go(&2, Lex.Tok, Bool.pick(List<&2, Lex.Tok>, s, a, []), r)} : Maybe<&2, List<&2, Lex.Tok>>}

def sig.stop(s, _x, _f, _a, _r, ex, ef):
  match s:
    case True{}:
      ef
    case False{}:
      ex

# the stack a significant token lands on: fresh's when it starts a line
def landing(fr: Bool, +s: List<&2, Tree.Frame>, k: Lex.TokKind, t: String, l: U32, c: U32) -> List<&2, Tree.Frame>:
  Lazy.stop(List<&2, Tree.Frame>, Bool.not(fr), s, _u2 => Tree.fresh(s, Lex.Tok{k, t, l, c}))

# a line's first token keeps the leaves
law landing.keeps:
  for +fr: Bool
  for +s: List<&2, Tree.Frame>
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for -r: List<&2, Lex.Tok>
  for +e: {vg(s) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {vg(landing(fr, s, k, t, l, c)) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}

def landing.keeps(fr, s, k, t, l, c, r, e):
  vg.stop(Bool.not(fr), s, _u2 => Tree.fresh(s, Lex.Tok{k, t, l, c}), Some{r}, e, fresh(s, k, t, l, c, r, e))

# one step adds the token's leaves
law tstep:
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +st: Tree.B
  for +g: Bool
  for -r: List<&2, Lex.Tok>
  for +e: {vg(stk(st)) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {vg(stk(Tree.step(Lex.Tok{k, t, l, c}, st, g))) == Some{List.reverse.go(&2, Lex.Tok, adds(k, t, l, c), r)}
    : Maybe<&2, List<&2, Lex.Tok>>}

def tstep(k, t, l, c, st, g, r, e):
  match st:
    case Tree.B{fr, s}:
      sig.stop(Lex.significant(k), Tree.B{Bool.or(fr, Lex.is_nl(k)), s},
        _u => Tree.B{False{}, Tree.push(landing(fr, s, k, t, l, c), Lex.Tok{k, t, l, c}, g)},
        law_adds(k, t, l, c), r, e,
        Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
          vg(Tree.push(landing(fr, s, k, t, l, c), Lex.Tok{k, t, l, c}, g)),
          m_toks(vg(landing(fr, s, k, t, l, c)), code_adds(k, t, l, c)),
          Some{List.reverse.go(&2, Lex.Tok, law_adds(k, t, l, c), r)},
          push(landing(fr, s, k, t, l, c), k, t, l, c, g),
          Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
            m_toks(vg(landing(fr, s, k, t, l, c)), code_adds(k, t, l, c)),
            Some{List.reverse.go(&2, Lex.Tok, code_adds(k, t, l, c), r)},
            Some{List.reverse.go(&2, Lex.Tok, law_adds(k, t, l, c), r)},
            Equal.cong(Maybe<&2, List<&2, Lex.Tok>>, Maybe<&2, List<&2, Lex.Tok>>,
              m => m_toks(m, code_adds(k, t, l, c)),
              vg(landing(fr, s, k, t, l, c)), Some{r},
              landing.keeps(fr, s, k, t, l, c, r, e)),
            Equal.cong(List<&2, Lex.Tok>, Maybe<&2, List<&2, Lex.Tok>>,
              x => Some{List.reverse.go(&2, Lex.Tok, x, r)},
              code_adds(k, t, l, c), law_adds(k, t, l, c), decide(k, t, l, c)))))

# one less
def pred(nn: Nat) -> Nat:
  match nn:
    case Zero{}:
      0n
    case Succ{p}:
      p

# a known list's value, [] for none
def got(mm: Maybe<&2, List<&2, Lex.Tok>>) -> List<&2, Lex.Tok>:
  match mm:
    case None{}:
      []
    case Some{a}:
      a

# a put keeps the groups on top
law groups.put:
  for +s: List<&2, Tree.Frame>
  for +x: Tree.Node
  {Tree.groups(Tree.put(s, x)) == Tree.groups(s) : Nat}

def groups.put(s, _x):
  match s:
    case Con{Tree.FGroup{_o, _k}, _rest}:
      {==}
    case Con{Tree.FStmt{_i, _k, _b}, _rest}:
      {==}
    case Con{Tree.FRoot{_b}, _rest}:
      {==}
    case Nil{}:
      {==}

# a statement put in a body keeps the statements on top
law stmts.put:
  for +s: List<&2, Tree.Frame>
  for +x: Tree.Node
  {Tree.stmts(Tree.put_stmt(s, x)) == Tree.stmts(s) : Nat}

def stmts.put(s, _x):
  match s:
    case Con{Tree.FGroup{_o, _k}, _rest}:
      {==}
    case Con{Tree.FStmt{_i, _k, _b}, _rest}:
      {==}
    case Con{Tree.FRoot{_b}, _rest}:
      {==}
    case Nil{}:
      {==}

# with no group on top, a well-formed stack's leaves are its statements'
law no_group:
  for +s: List<&2, Tree.Frame>
  for -r: List<&2, Lex.Tok>
  for eg: {Tree.groups(s) == 0n : Nat}
  for ev: {vg(s) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {vs(s) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}

def no_group(s, r, eg, ev):
  match s:
    case Con{Tree.FGroup{o, k}, rest}:
      Empty.absurd({vs(Tree.FGroup{o, k} <> rest) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>},
        zero_succ(Tree.groups(rest), Equal.sym(Nat, 1n+Tree.groups(rest), 0n, eg)))
    case Con{Tree.FStmt{_i, _k, Tree.NNil{}}, _rest}:
      ev
    case Con{Tree.FStmt{i, k, Tree.NCons{h, t}}, rest}:
      Empty.absurd({vs(Tree.FStmt{i, k, Tree.NCons{h, t}} <> rest) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>},
        none_some(r, ev))
    case Con{Tree.FStmt{i, k, Tree.Leaf{x}}, rest}:
      Empty.absurd({vs(Tree.FStmt{i, k, Tree.Leaf{x}} <> rest) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>},
        none_some(r, ev))
    case Con{Tree.FStmt{i, k, Tree.Group{x, y, z}}, rest}:
      Empty.absurd({vs(Tree.FStmt{i, k, Tree.Group{x, y, z}} <> rest) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>},
        none_some(r, ev))
    case Con{Tree.FStmt{i, k, Tree.Stmt{x, y, z}}, rest}:
      Empty.absurd({vs(Tree.FStmt{i, k, Tree.Stmt{x, y, z}} <> rest) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>},
        none_some(r, ev))
    case Con{Tree.FRoot{_b}, _rest}:
      ev
    case Nil{}:
      ev

# closing the n groups on top leaves a stack whose statements hold the leaves
law close_down:
  for +n: Nat
  for +s: List<&2, Tree.Frame>
  for -r: List<&2, Lex.Tok>
  for eg: {Tree.groups(s) == n : Nat}
  for ev: {vg(s) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {vs(Tree.close_n(n, s, None{})) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}

def close_down(n, s, r, eg, ev):
  match n s:
    case Zero{} _s:
      no_group(_s, r, eg, ev)
    case Succ{Zero{}} Con{Tree.FGroup{o, k}, rest}:
      no_group(Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}}), r,
        Equal.trans(Nat, Tree.groups(Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}})),
          Tree.groups(rest), 0n,
          groups.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}}),
          Equal.cong(Nat, Nat, pred, 1n+Tree.groups(rest), 1n, eg)),
        Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
          vg(Tree.close_one(Tree.FGroup{o, k} <> rest, None{})), vg(Tree.FGroup{o, k} <> rest), Some{r},
          close.none(Tree.FGroup{o, k} <> rest), ev))
    case Succ{Succ{q}} Con{Tree.FGroup{o, k}, rest}:
      close_down(1n+q, Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}}), r,
        Equal.trans(Nat, Tree.groups(Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}})),
          Tree.groups(rest), 1n+q,
          groups.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}}),
          Equal.cong(Nat, Nat, pred, 1n+Tree.groups(rest), 1n+1n+q, eg)),
        Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
          vg(Tree.close_one(Tree.FGroup{o, k} <> rest, None{})), vg(Tree.FGroup{o, k} <> rest), Some{r},
          close.none(Tree.FGroup{o, k} <> rest), ev))
    case Succ{p} Con{Tree.FStmt{i, k, b}, rest}:
      Empty.absurd({vs(Tree.close_n(1n+p, Tree.FStmt{i, k, b} <> rest, None{})) == Some{r}
        : Maybe<&2, List<&2, Lex.Tok>>},
        zero_succ(p, eg))
    case Succ{p} Con{Tree.FRoot{b}, rest}:
      Empty.absurd({vs(Tree.close_n(1n+p, Tree.FRoot{b} <> rest, None{})) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>},
        zero_succ(p, eg))
    case Succ{p} Nil{}:
      Empty.absurd({vs(Tree.close_n(1n+p, [], None{})) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>},
        zero_succ(p, eg))

# finishing the n statements on top leaves the root, whose items read back
# the leaves in order
law end_down:
  for +n: Nat
  for +s: List<&2, Tree.Frame>
  for -r: List<&2, Lex.Tok>
  for es: {Tree.stmts(s) == n : Nat}
  for ev: {vs(s) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {Tree.leaves(Tree.root(Tree.end_n(n, s))) == List.reverse(&2, Lex.Tok, r) : List<&2, Lex.Tok>}

def end_down(n, s, r, es, ev):
  match n s:
    case Zero{} Con{Tree.FRoot{b}, _rest}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, x => List.reverse(&2, Lex.Tok, x),
        Tree.leaves.go(Tree.reverse(b, Tree.NNil{}), []), r,
        Equal.trans(List<&2, Lex.Tok>, Tree.leaves.go(Tree.reverse(b, Tree.NNil{}), []), rgo(b, []), r,
          rev(b, Tree.NNil{}, []),
          Equal.cong(Maybe<&2, List<&2, Lex.Tok>>, List<&2, Lex.Tok>, got, Some{rgo(b, [])}, Some{r}, ev)))
    case Zero{} Con{Tree.FStmt{i, k, b}, rest}:
      Empty.absurd({Tree.leaves(Tree.root(Tree.end_n(0n, Tree.FStmt{i, k, b} <> rest))) == List.reverse(&2, Lex.Tok, r)
        : List<&2, Lex.Tok>},
        zero_succ(Tree.stmts(rest), Equal.sym(Nat, 1n+Tree.stmts(rest), 0n, es)))
    case Zero{} Con{Tree.FGroup{o, k}, rest}:
      Empty.absurd({Tree.leaves(Tree.root(Tree.end_n(0n, Tree.FGroup{o, k} <> rest))) == List.reverse(&2, Lex.Tok, r)
        : List<&2, Lex.Tok>},
        none_some(r, ev))
    case Zero{} Nil{}:
      Empty.absurd({Tree.leaves(Tree.root(Tree.end_n(0n, []))) == List.reverse(&2, Lex.Tok, r) : List<&2, Lex.Tok>},
        none_some(r, ev))
    case Succ{p} Con{Tree.FStmt{i, k, b}, rest}:
      end_down(p, Tree.end_stmt(Tree.FStmt{i, k, b} <> rest), r,
        Equal.trans(Nat, Tree.stmts(Tree.end_stmt(Tree.FStmt{i, k, b} <> rest)), Tree.stmts(rest), p,
          stmts.put(rest, Tree.Stmt{Tree.classify(Tree.reverse(k, Tree.NNil{})), Tree.reverse(k, Tree.NNil{}),
            Tree.reverse(b, Tree.NNil{})}),
          Equal.cong(Nat, Nat, pred, 1n+Tree.stmts(rest), 1n+p, es)),
        Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
          vs(Tree.end_stmt(Tree.FStmt{i, k, b} <> rest)), vs(Tree.FStmt{i, k, b} <> rest), Some{r},
          end_stmt(Tree.FStmt{i, k, b} <> rest), ev))
    case Succ{p} Con{Tree.FGroup{o, k}, rest}:
      Empty.absurd({Tree.leaves(Tree.root(Tree.end_n(1n+p, Tree.FGroup{o, k} <> rest))) == List.reverse(&2, Lex.Tok, r)
        : List<&2, Lex.Tok>},
        zero_succ(p, es))
    case Succ{p} Con{Tree.FRoot{b}, rest}:
      Empty.absurd({Tree.leaves(Tree.root(Tree.end_n(1n+p, Tree.FRoot{b} <> rest))) == List.reverse(&2, Lex.Tok, r)
        : List<&2, Lex.Tok>},
        zero_succ(p, es))
    case Succ{p} Nil{}:
      Empty.absurd({Tree.leaves(Tree.root(Tree.end_n(1n+p, []))) == List.reverse(&2, Lex.Tok, r) : List<&2, Lex.Tok>},
        zero_succ(p, es))

# the finished tree reads back the leaves in order
law tfinish:
  for +st: Tree.B
  for -r: List<&2, Lex.Tok>
  for e: {vg(stk(st)) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {Tree.leaves(Tree.finish(st)) == List.reverse(&2, Lex.Tok, r) : List<&2, Lex.Tok>}

def tfinish(st, r, e):
  match st:
    case Tree.B{_fr, s}:
      end_down(Tree.stmts(Tree.close_all(s)), Tree.close_all(s), r, {==},
        close_down(Tree.groups(s), s, r, {==}, e))

# a list reversed onto a list reversed onto another
law rev_rev:
  for +xs: List<&2, Lex.Tok>
  for +r: List<&2, Lex.Tok>
  for +ys: List<&2, Lex.Tok>
  {List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, xs, r), ys)
    == List.reverse.go(&2, Lex.Tok, r, List.append(&2, Lex.Tok, xs, ys)) : List<&2, Lex.Tok>}

def rev_rev(xs, r, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      rev_rev(t, h <> r, ys)

# one token's leaves, then the rest's: the law's leaves of both
law split_one:
  for +s: Bool
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +more: List<&2, Lex.Tok>
  {List.append(&2, Lex.Tok,
      Bool.pick(List<&2, Lex.Tok>, s,
        law_adds(k, t, l, c), []),
      Laws.split_gts(more))
    == Laws.split_gts(Bool.pick(List<&2, Lex.Tok>, s, Lex.Tok{k, t, l, c} <> more, more)) : List<&2, Lex.Tok>}

def split_one(s, _k, _t, _l, _c, _more):
  match s:
    case True{}:
      {==}
    case False{}:
      {==}

# running over tokens adds their leaves, and the finished tree reads all of
# them back in order
law trun:
  for +toks: List<&2, Lex.Tok>
  for +st: Tree.B
  for +g: Bool
  for +r: List<&2, Lex.Tok>
  for +e: {vg(stk(st)) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {Tree.leaves(Tree.finish(Tree.run(toks, st, g)))
    == List.reverse.go(&2, Lex.Tok, r, Laws.split_gts(Laws.significant(toks))) : List<&2, Lex.Tok>}

def trun(toks, st, g, r, e):
  match toks:
    case Nil{}:
      tfinish(st, r, e)
    case Con{Lex.Tok{k, t, l, c}, rest}:
      Equal.trans(List<&2, Lex.Tok>,
        Tree.leaves(Tree.finish(Tree.run(rest, Tree.step(Lex.Tok{k, t, l, c}, st, g),
          Tree.is_name_tok(Lex.Tok{k, t, l, c})))),
        List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, adds(k, t, l, c), r),
          Laws.split_gts(Laws.significant(rest))),
        List.reverse.go(&2, Lex.Tok, r, Laws.split_gts(Laws.significant(Lex.Tok{k, t, l, c} <> rest))),
        trun(rest, Tree.step(Lex.Tok{k, t, l, c}, st, g), Tree.is_name_tok(Lex.Tok{k, t, l, c}),
          List.reverse.go(&2, Lex.Tok, adds(k, t, l, c), r), tstep(k, t, l, c, st, g, r, e)),
        Equal.trans(List<&2, Lex.Tok>,
          List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, adds(k, t, l, c), r),
            Laws.split_gts(Laws.significant(rest))),
          List.reverse.go(&2, Lex.Tok, r, List.append(&2, Lex.Tok, adds(k, t, l, c),
            Laws.split_gts(Laws.significant(rest)))),
          List.reverse.go(&2, Lex.Tok, r, Laws.split_gts(Laws.significant(Lex.Tok{k, t, l, c} <> rest))),
          rev_rev(adds(k, t, l, c), r, Laws.split_gts(Laws.significant(rest))),
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, x => List.reverse.go(&2, Lex.Tok, r, x),
            List.append(&2, Lex.Tok, adds(k, t, l, c), Laws.split_gts(Laws.significant(rest))),
            Laws.split_gts(Laws.significant(Lex.Tok{k, t, l, c} <> rest)),
            split_one(Lex.significant(k), k, t, l, c, Laws.significant(rest)))))

def Laws.leaves(toks):
  trun(toks, Tree.B{True{}, [Tree.FRoot{Tree.NNil{}}]}, False{}, [], {==})
