# syntax: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./lex.bend as Lex
import ./tree.bend as Tree
import ./outline.bend as Outline
import ../lazy/lazy.bend as Lazy
import ./bind.bend as Bind
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

# the outline (BOLT-SYN-4)
# ------------------------
# The machine's state is read as the items it has settled, by kind, name and
# line, newest first (a pending header counts), and the line it is on. Each
# line adds the item the spec says it opens, or none, and moves one line on;
# the flags of the lines that start inside a string are the spec's.

# reversing a list with one item picked on or not: that item moves across
law ol.rev_pick:
  for -A: Data
  for +b: Bool
  for +i: A
  for +xs: List<&2, A>
  for +acc: List<&2, A>
  {List.reverse.go(&2, A, Bool.pick(List<&2, A>, b, i <> xs, xs), acc)
    == List.reverse.go(&2, A, xs, Bool.pick(List<&2, A>, b, i <> acc, acc)) : List<&2, A>}

def ol.rev_pick(_A, b, _i, _xs, _acc):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# reversing an append onto acc: the first list reversed onto acc, then the second
law ol.rev_app:
  for -A: Data
  for +xs: List<&2, A>
  for +ys: List<&2, A>
  for +acc: List<&2, A>
  {List.reverse.go(&2, A, List.append(&2, A, xs, ys), acc)
    == List.reverse.go(&2, A, ys, List.reverse.go(&2, A, xs, acc)) : List<&2, A>}

def ol.rev_app(A, xs, ys, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      ol.rev_app(A, t, ys, h <> acc)

# a list onto nothing is itself
law ol.app_nil:
  for -A: Data
  for +xs: List<&2, A>
  {List.append(&2, A, xs, []) == xs : List<&2, A>}

def ol.app_nil(A, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, A>, List<&2, A>, r => h <> r, List.append(&2, A, t, []), t, ol.app_nil(A, t))

# reversing twice: what was under the first reversal, then the list, then ys
law ol.rev_rev:
  for -A: Data
  for +xs: List<&2, A>
  for +acc: List<&2, A>
  for +ys: List<&2, A>
  {List.reverse.go(&2, A, List.reverse.go(&2, A, xs, acc), ys)
    == List.reverse.go(&2, A, acc, List.append(&2, A, xs, ys)) : List<&2, A>}

def ol.rev_rev(A, xs, acc, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      ol.rev_rev(A, t, h <> acc, ys)

# the outline's flags of a text's line breaks, pushed onto acc, are the
# spec's, reversed onto acc
law ol.breaks:
  for +tt: String
  for +s: Bool
  for +acc: List<&2, Bool>
  {Outline.breaks(tt, s, acc) == List.reverse.go(&2, Bool, Laws.top.breaks(tt, s), acc) : List<&2, Bool>}

def ol.breaks(tt, s, acc):
  match tt:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.trans(List<&2, Bool>,
        Outline.breaks(t, s, Bool.pick(List<&2, Bool>, Laws.breaks(h), s <> acc, acc)),
        List.reverse.go(&2, Bool, Laws.top.breaks(t, s), Bool.pick(List<&2, Bool>, Laws.breaks(h), s <> acc, acc)),
        List.reverse.go(&2, Bool, Laws.top.breaks(SCon{h, t}, s), acc),
        ol.breaks(t, s, Bool.pick(List<&2, Bool>, Laws.breaks(h), s <> acc, acc)),
        Equal.sym(List<&2, Bool>,
          List.reverse.go(&2, Bool, Laws.top.breaks(SCon{h, t}, s), acc),
          List.reverse.go(&2, Bool, Laws.top.breaks(t, s), Bool.pick(List<&2, Bool>, Laws.breaks(h), s <> acc, acc)),
          ol.rev_pick(Bool, Laws.breaks(h), s, Laws.top.breaks(t, s), acc)))

# the outline's flags of the tokens' line breaks, pushed onto acc, are the
# spec's, reversed onto acc
law ol.inside:
  for +toks: List<&2, Lex.Tok>
  for +acc: List<&2, Bool>
  {Outline.inside.go(toks, acc) == List.reverse.go(&2, Bool, Laws.top.strung(toks), acc) : List<&2, Bool>}

def ol.inside(toks, acc):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      Equal.trans(List<&2, Bool>,
        Outline.inside.go(rest, Outline.breaks(t, Lex.is_str(k), acc)),
        List.reverse.go(&2, Bool, Laws.top.strung(rest), Outline.breaks(t, Lex.is_str(k), acc)),
        List.reverse.go(&2, Bool, Laws.top.strung(Lex.Tok{k, t, l, c} <> rest), acc),
        ol.inside(rest, Outline.breaks(t, Lex.is_str(k), acc)),
        Equal.trans(List<&2, Bool>,
          List.reverse.go(&2, Bool, Laws.top.strung(rest), Outline.breaks(t, Lex.is_str(k), acc)),
          List.reverse.go(&2, Bool, Laws.top.strung(rest),
            List.reverse.go(&2, Bool, Laws.top.breaks(t, Lex.is_str(k)), acc)),
          List.reverse.go(&2, Bool, Laws.top.strung(Lex.Tok{k, t, l, c} <> rest), acc),
          Equal.cong(List<&2, Bool>, List<&2, Bool>, x => List.reverse.go(&2, Bool, Laws.top.strung(rest), x),
            Outline.breaks(t, Lex.is_str(k), acc),
            List.reverse.go(&2, Bool, Laws.top.breaks(t, Lex.is_str(k)), acc),
            ol.breaks(t, Lex.is_str(k), acc)),
          Equal.sym(List<&2, Bool>,
            List.reverse.go(&2, Bool, Laws.top.strung(Lex.Tok{k, t, l, c} <> rest), acc),
            List.reverse.go(&2, Bool, Laws.top.strung(rest),
              List.reverse.go(&2, Bool, Laws.top.breaks(t, Lex.is_str(k)), acc)),
            ol.rev_app(Bool, Laws.top.breaks(t, Lex.is_str(k)), Laws.top.strung(rest), acc))))

# the outline's line flags are the spec's: line 0 outside, then one per break
law ol.flags:
  for +toks: List<&2, Lex.Tok>
  {Outline.inside(toks) == False{} <> Laws.top.strung(toks) : List<&2, Bool>}

def ol.flags(toks):
  Equal.cong(List<&2, Bool>, List<&2, Bool>, x => False{} <> x,
    List.reverse(&2, Bool, Outline.inside.go(toks, [])), Laws.top.strung(toks),
    Equal.trans(List<&2, Bool>,
      List.reverse(&2, Bool, Outline.inside.go(toks, [])),
      List.reverse(&2, Bool, List.reverse.go(&2, Bool, Laws.top.strung(toks), [])),
      Laws.top.strung(toks),
      Equal.cong(List<&2, Bool>, List<&2, Bool>, x => List.reverse(&2, Bool, x),
        Outline.inside.go(toks, []), List.reverse.go(&2, Bool, Laws.top.strung(toks), []),
        ol.inside(toks, [])),
      Equal.trans(List<&2, Bool>,
        List.reverse(&2, Bool, List.reverse.go(&2, Bool, Laws.top.strung(toks), [])),
        List.append(&2, Bool, Laws.top.strung(toks), []),
        Laws.top.strung(toks),
        ol.rev_rev(Bool, Laws.top.strung(toks), [], []),
        ol.app_nil(Bool, Laws.top.strung(toks)))))

# reversing onto a text: the reversal, then the text
law ol.srev:
  for +acc: String
  for +x: String
  {String.reverse.go(acc, x) == String.append(String.reverse.go(acc, SNil{}), x) : String}

def ol.srev(acc, x):
  match acc:
    case SNil{}:
      {==}
    case SCon{+a, +rest}:
      Equal.trans(String,
        String.reverse.go(rest, SCon{a, x}),
        String.append(String.reverse.go(rest, SNil{}), SCon{a, x}),
        String.append(String.reverse.go(SCon{a, rest}, SNil{}), x),
        ol.srev(rest, SCon{a, x}),
        Equal.sym(String,
          String.append(String.reverse.go(SCon{a, rest}, SNil{}), x),
          String.append(String.reverse.go(rest, SNil{}), SCon{a, x}),
          Equal.trans(String,
            String.append(String.reverse.go(rest, SCon{a, SNil{}}), x),
            String.append(String.append(String.reverse.go(rest, SNil{}), SCon{a, SNil{}}), x),
            String.append(String.reverse.go(rest, SNil{}), SCon{a, x}),
            Equal.cong(String, String, y => String.append(y, x),
              String.reverse.go(rest, SCon{a, SNil{}}),
              String.append(String.reverse.go(rest, SNil{}), SCon{a, SNil{}}),
              ol.srev(rest, SCon{a, SNil{}})),
            app.assoc(String.reverse.go(rest, SNil{}), SCon{a, SNil{}}, x))))

# the name's next char, whether or not it stops the name
law ol.name.arm:
  for +b: Bool
  for +t: String
  for +h: Char
  for +acc: String
  for +ih: {Outline.name.go(t, SCon{h, acc}, False{})
    == String.append(String.reverse(SCon{h, acc}), Laws.top.name(t)) : String}
  {Outline.name.go(t, Outline.name.push(b, h, acc), b)
    == String.append(String.reverse(acc), Bool.pick(String, b, SNil{}, SCon{h, Laws.top.name(t)})) : String}

def ol.name.arm(b, t, h, acc, ih):
  match b:
    case True{}:
      match t:
        case SNil{}:
          Equal.sym(String, String.append(String.reverse(acc), SNil{}), String.reverse(acc),
            app.nil(String.reverse(acc)))
        case SCon{_h2, _t2}:
          Equal.sym(String, String.append(String.reverse(acc), SNil{}), String.reverse(acc),
            app.nil(String.reverse(acc)))
    case False{}:
      Equal.trans(String,
        Outline.name.go(t, SCon{h, acc}, False{}),
        String.append(String.reverse(SCon{h, acc}), Laws.top.name(t)),
        String.append(String.reverse(acc), SCon{h, Laws.top.name(t)}),
        ih,
        Equal.trans(String,
          String.append(String.reverse.go(acc, SCon{h, SNil{}}), Laws.top.name(t)),
          String.append(String.append(String.reverse(acc), SCon{h, SNil{}}), Laws.top.name(t)),
          String.append(String.reverse(acc), SCon{h, Laws.top.name(t)}),
          Equal.cong(String, String, y => String.append(y, Laws.top.name(t)),
            String.reverse.go(acc, SCon{h, SNil{}}),
            String.append(String.reverse(acc), SCon{h, SNil{}}),
            ol.srev(acc, SCon{h, SNil{}})),
          app.assoc(String.reverse(acc), SCon{h, SNil{}}, Laws.top.name(t))))

# the name read with acc (reversed) before it: acc, then the spec's name
law ol.name.go:
  for +ss: String
  for +acc: String
  {Outline.name.go(ss, acc, False{}) == String.append(String.reverse(acc), Laws.top.name(ss)) : String}

def ol.name.go(ss, acc):
  match ss:
    case SNil{}:
      Equal.sym(String, String.append(String.reverse(acc), SNil{}), String.reverse(acc),
        app.nil(String.reverse(acc)))
    case SCon{+h, +t}:
      ol.name.arm(Laws.top.stop(h), t, h, acc, ol.name.go(t, SCon{h, acc}))

# the outline's name is the spec's
law ol.name:
  for +ss: String
  {Outline.name(ss) == Laws.top.name(ss) : String}

def ol.name(ss):
  ol.name.go(ss, SNil{})

# Unit for False, Empty for True: tells them apart the other way round
def true_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Empty
    case True{}:
      Unit

# True is never False
law true_false:
  for e: {True{} == False{} : Bool}
  Empty

def true_false(e):
  %e : true_ty(_)
  Unit{}

# words that compare equal, bit by bit past the first: the rest equal, the
# first bits the same
law ol.weq.arm:
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

def ol.weq.arm(p, at, bt, c, ec, ih, ab, bb, e):
  match c:
    case LT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, false_true(e))
    case GT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, false_true(e))
    case EQ{}:
      match ab bb:
        case False{} False{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{False{}, w}, at, bt,
            ih(Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, at, bt), EQ{}, ec)))
        case True{} True{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{True{}, w}, at, bt,
            ih(Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, at, bt), EQ{}, ec)))
        case False{} True{}:
          Empty.absurd({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, false_true(e))
        case True{} False{}:
          Empty.absurd({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, false_true(e))

# words that compare equal are equal
law ol.weq:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for e: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}
  {a == b : Word(n)}

def ol.weq(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          ol.weq.arm(p, at, bt, Word.cmp(p, at, bt), {==}, x => ol.weq(p, at, bt, x), ab, bb, e)

# U32s that compare equal are equal
law ol.ueq:
  for a: U32
  for b: U32
  for e: {U32.is_eq(a, b) == True{} : Bool}
  {a == b : U32}

def ol.ueq(a, b, e):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, ol.weq(32n, x, y, e))

# what a state has settled: its items by kind, name and line, newest first
# (a pending header counts), and the line it is on
type Seen is Data:
  Seen{keys: List<&2, Outline.Item>, line: U32}

# a state as what it has settled
def shown(st: Outline.St) -> Seen:
  match st:
    case Outline.St{mode, n, _doc, out}:
      Seen{Laws.top.keys(Outline.flush(mode, out)), n}

# what a line that opens no item leaves: the same items, one line on
def ol.same(mode: Outline.Mode, out: List<&2, Outline.Item>, nn: U32) -> Seen:
  Seen{Laws.top.keys(Outline.flush(mode, out)), (nn + 1 : U32)}

# a def header's continuation settles the pending def or keeps it pending
law ol.closed:
  for +colon: Bool
  for +nm: String
  for +ll: U32
  for +dd: String
  for +sig: List<&2, String>
  for +text: String
  for +nn: U32
  for +out: List<&2, Outline.Item>
  {shown(Outline.pend_more.closed(colon, nm, ll, dd, sig, text, nn, out))
    == ol.same(Outline.Pending{Outline.IDef{}, nm, ll, dd, sig}, out, nn) : Seen}

def ol.closed(colon, _nm, _ll, _dd, _sig, _text, _nn, _out):
  match colon:
    case True{}:
      {==}
    case False{}:
      {==}

# more of a pending header opens nothing
law ol.pend:
  for +k: Outline.ItemKind
  for +nm: String
  for +ll: U32
  for +dd: String
  for +sig: List<&2, String>
  for +text: String
  for +nn: U32
  for +out: List<&2, Outline.Item>
  {shown(Outline.pend_more(k, nm, ll, dd, sig, text, nn, out))
    == ol.same(Outline.Pending{k, nm, ll, dd, sig}, out, nn) : Seen}

def ol.pend(k, nm, ll, dd, sig, text, nn, out):
  match k:
    case Outline.IDef{}:
      ol.closed(Outline.ends_colon(text), nm, ll, dd, sig, text, nn, out)
    case Outline.IImport{}:
      {==}
    case Outline.ILaw{}:
      {==}
    case Outline.IType{}:
      {==}
    case Outline.ICtor{}:
      {==}
    case Outline.ILocal{}:
      {==}

# a constructor, or none, adds no key
law ol.ctor.stop:
  for +b: Bool
  for +nm: String
  for +nn: U32
  for +s: String
  for +out: List<&2, Outline.Item>
  {Laws.top.keys(Outline.add(Lazy.stop(Maybe<&2, Outline.Item>, b, None{},
      _u => Some{Outline.Item{Outline.ICtor{}, nm, nn, s, "", ""}}), out))
    == Laws.top.keys(out) : List<&2, Outline.Item>}

def ol.ctor.stop(b, _nm, _nn, _s, _out):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a line of a type block adds no key
law ol.ctor:
  for +text: String
  for +nn: U32
  for +out: List<&2, Outline.Item>
  {Laws.top.keys(Outline.add(Outline.ctor(text, nn), out)) == Laws.top.keys(out) : List<&2, Outline.Item>}

def ol.ctor(text, nn, out):
  ol.ctor.stop(
    Bool.not(Bool.and(Outline.starts_upper(Outline.lstrip(text)), String.contains(Outline.lstrip(text), "{"))),
    Outline.name(Outline.lstrip(text)), nn, Outline.lstrip(text), out)

# an indented line opens nothing
law ol.indent:
  for +mode: Outline.Mode
  for +text: String
  for +nn: U32
  for +out: List<&2, Outline.Item>
  {shown(Outline.indent(mode, text, nn, out)) == ol.same(mode, out, nn) : Seen}

def ol.indent(mode, text, nn, out):
  match mode:
    case Outline.Top{}:
      {==}
    case Outline.InType{}:
      Equal.cong(List<&2, Outline.Item>, Seen, ks => Seen{ks, (nn + 1 : U32)},
        Laws.top.keys(Outline.add(Outline.ctor(text, nn), out)), Laws.top.keys(out), ol.ctor(text, nn, out))
    case Outline.Pending{k, nm, ll, dd, sig}:
      ol.pend(k, nm, ll, dd, sig, text, nn, out)

# a column-0 line that starts nothing opens nothing
law ol.stray:
  for +mode: Outline.Mode
  for +text: String
  for +nn: U32
  for +out: List<&2, Outline.Item>
  {shown(Outline.stray(mode, text, nn, out)) == ol.same(mode, out, nn) : Seen}

def ol.stray(mode, text, nn, out):
  match mode:
    case Outline.Top{}:
      {==}
    case Outline.InType{}:
      {==}
    case Outline.Pending{k, nm, ll, dd, sig}:
      match k:
        case Outline.IDef{}:
          ol.pend(Outline.IDef{}, nm, ll, dd, sig, text, nn, out)
        case Outline.IImport{}:
          {==}
        case Outline.ILaw{}:
          {==}
        case Outline.IType{}:
          {==}
        case Outline.ICtor{}:
          {==}
        case Outline.ILocal{}:
          {==}

# does a class open an item?
def ol.loud(cls: Outline.Cls) -> Bool:
  match cls:
    case Outline.LImport{}:
      True{}
    case Outline.LDef{}:
      True{}
    case Outline.LLaw{}:
      True{}
    case Outline.LType{}:
      True{}
    case other:
      False{}

# what a class the outline steps on leaves
def ol.after(
  cls: Outline.Cls,
  mode: Outline.Mode,
  ss: String,
  nn: U32,
  doc: List<&2, String>,
  out: List<&2, Outline.Item>
) -> Seen:
  shown(Outline.step.go(cls, mode, ss, nn, doc, out))

# a class that opens no item leaves the same items, one line on
law ol.quiet:
  for +cls: Outline.Cls
  for +mode: Outline.Mode
  for +ss: String
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for e: {ol.loud(cls) == False{} : Bool}
  {ol.after(cls, mode, ss, nn, doc, out) == ol.same(mode, out, nn) : Seen}

def ol.quiet(cls, mode, ss, nn, doc, out, e):
  match cls:
    case Outline.LBlank{}:
      {==}
    case Outline.LComment{_t}:
      {==}
    case Outline.LIndent{t}:
      ol.indent(mode, t, nn, out)
    case Outline.LOther{}:
      ol.stray(mode, ss, nn, out)
    case Outline.LImport{}:
      Empty.absurd({ol.after(Outline.LImport{}, mode, ss, nn, doc, out) == ol.same(mode, out, nn) : Seen},
        true_false(e))
    case Outline.LDef{}:
      Empty.absurd({ol.after(Outline.LDef{}, mode, ss, nn, doc, out) == ol.same(mode, out, nn) : Seen},
        true_false(e))
    case Outline.LLaw{}:
      Empty.absurd({ol.after(Outline.LLaw{}, mode, ss, nn, doc, out) == ol.same(mode, out, nn) : Seen},
        true_false(e))
    case Outline.LType{}:
      Empty.absurd({ol.after(Outline.LType{}, mode, ss, nn, doc, out) == ol.same(mode, out, nn) : Seen},
        true_false(e))

# the end of a line of whitespace is blank, indented or other
law ol.hit:
  for +indent: Bool
  for +acc: List<&2, Char>
  for +hh: Char
  for +rest: String
  {ol.loud(Outline.classify.white.hit(indent, acc, hh, rest)) == False{} : Bool}

def ol.hit(indent, _acc, _hh, _rest):
  match indent:
    case True{}:
      {==}
    case False{}:
      {==}

# a line that opens with whitespace opens no item
law ol.white:
  for +tt: String
  for +space: Bool
  for +hh: Char
  for +indent: Bool
  for +acc: List<&2, Char>
  {ol.loud(Outline.classify.white(tt, space, hh, indent, acc)) == False{} : Bool}

def ol.white(tt, space, hh, indent, acc):
  match tt space:
    case SNil{} True{}:
      {==}
    case SNil{} False{}:
      ol.hit(indent, acc, hh, SNil{})
    case SCon{+h2, +r} True{}:
      ol.white(r, Char.is_space(h2), h2, indent, hh <> acc)
    case SCon{+h2, +r} False{}:
      ol.hit(indent, acc, hh, SCon{h2, r})

# not `t`: not `type `
law ol.l_ty:
  for +t: String
  for +b: Bool
  for e: {b == False{} : Bool}
  {ol.loud(Outline.classify.ktype(b, t)) == False{} : Bool}

def ol.l_ty(t, b, e):
  match b:
    case True{}:
      Empty.absurd({ol.loud(Outline.classify.ktype(True{}, t)) == False{} : Bool}, true_false(e))
    case False{}:
      {==}

# not `l`: not `law `
law ol.l_law:
  for +x: U32
  for +t: String
  for +b: Bool
  for e: {b == False{} : Bool}
  for e116: {U32.is_eq(x, 116) == False{} : Bool}
  {ol.loud(Outline.classify.klaw(b, x, t)) == False{} : Bool}

def ol.l_law(x, t, b, e, e116):
  match b:
    case True{}:
      Empty.absurd({ol.loud(Outline.classify.klaw(True{}, x, t)) == False{} : Bool}, true_false(e))
    case False{}:
      ol.l_ty(t, U32.is_eq(x, 116), e116)

# not `@`: not `@unsafe def `
law ol.l_at:
  for +x: U32
  for +t: String
  for +b: Bool
  for e: {b == False{} : Bool}
  for e108: {U32.is_eq(x, 108) == False{} : Bool}
  for e116: {U32.is_eq(x, 116) == False{} : Bool}
  {ol.loud(Outline.classify.kat(b, x, t)) == False{} : Bool}

def ol.l_at(x, t, b, e, e108, e116):
  match b:
    case True{}:
      Empty.absurd({ol.loud(Outline.classify.kat(True{}, x, t)) == False{} : Bool}, true_false(e))
    case False{}:
      ol.l_law(x, t, U32.is_eq(x, 108), e108, e116)

# not `d`: not `def `
law ol.l_def:
  for +x: U32
  for +t: String
  for +b: Bool
  for e: {b == False{} : Bool}
  for e64: {U32.is_eq(x, 64) == False{} : Bool}
  for e108: {U32.is_eq(x, 108) == False{} : Bool}
  for e116: {U32.is_eq(x, 116) == False{} : Bool}
  {ol.loud(Outline.classify.kdef(b, x, t)) == False{} : Bool}

def ol.l_def(x, t, b, e, e64, e108, e116):
  match b:
    case True{}:
      Empty.absurd({ol.loud(Outline.classify.kdef(True{}, x, t)) == False{} : Bool}, true_false(e))
    case False{}:
      ol.l_at(x, t, U32.is_eq(x, 64), e64, e108, e116)

# not `i`: not `import `
law ol.l_imp:
  for +x: U32
  for +t: String
  for +b: Bool
  for e: {b == False{} : Bool}
  for e100: {U32.is_eq(x, 100) == False{} : Bool}
  for e64: {U32.is_eq(x, 64) == False{} : Bool}
  for e108: {U32.is_eq(x, 108) == False{} : Bool}
  for e116: {U32.is_eq(x, 116) == False{} : Bool}
  {ol.loud(Outline.classify.kimp(b, x, t)) == False{} : Bool}

def ol.l_imp(x, t, b, e, e100, e64, e108, e116):
  match b:
    case True{}:
      Empty.absurd({ol.loud(Outline.classify.kimp(True{}, x, t)) == False{} : Bool}, true_false(e))
    case False{}:
      ol.l_def(x, t, U32.is_eq(x, 100), e100, e64, e108, e116)

# what the outline makes of a line's pair of class and text
def ol.use(
  pp: Outline.Cls & String,
  mode: Outline.Mode,
  nn: U32,
  doc: List<&2, String>,
  out: List<&2, Outline.Item>
) -> Seen:
  shown(Outline.step.use(pp, mode, nn, doc, out))

# a line that opens with a space opens no item
law ol.gap:
  for +g: Bool
  for +x: U32
  for +t: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  {ol.use(Outline.classify.hold.gap(g, x, Chr{x}, t), mode, nn, doc, out) == ol.same(mode, out, nn) : Seen}

def ol.gap(g, x, t, mode, nn, doc, out):
  match g:
    case True{}:
      ol.quiet(Outline.classify.white.enter(t, x), mode, SNil{}, nn, doc, out,
        ol.white(t, True{}, Char.from_u32(x), U32.is_eq(x, 32), []))
    case False{}:
      ol.quiet(Outline.classify.white.enter(t, x), mode, SCon{Chr{x}, t}, nn, doc, out,
        ol.white(t, True{}, Char.from_u32(x), U32.is_eq(x, 32), []))

# a line whose first char is none of `i`, `d`, `@`, `l` and `t` opens no item
law ol.hash:
  for +h: Bool
  for +sp: Bool
  for +x: U32
  for +t: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for e105: {U32.is_eq(x, 105) == False{} : Bool}
  for e100: {U32.is_eq(x, 100) == False{} : Bool}
  for e64: {U32.is_eq(x, 64) == False{} : Bool}
  for e108: {U32.is_eq(x, 108) == False{} : Bool}
  for e116: {U32.is_eq(x, 116) == False{} : Bool}
  {ol.use(Outline.classify.hold.hash(h, sp, x, Chr{x}, t), mode, nn, doc, out) == ol.same(mode, out, nn) : Seen}

def ol.hash(h, sp, x, t, mode, nn, doc, out, e105, e100, e64, e108, e116):
  match h:
    case True{}:
      {==}
    case False{}:
      match sp:
        case True{}:
          ol.gap(U32.is_eq(x, 32), x, t, mode, nn, doc, out)
        case False{}:
          ol.quiet(Outline.classify.keys(x, t), mode, SCon{Chr{x}, t}, nn, doc, out,
            ol.l_imp(x, t, U32.is_eq(x, 105), e105, e100, e64, e108, e116))

# the outline's words are the spec's
law ol.words:
  for +xs: List<&2, String>
  {List.filter(~String, ~Outline.nonempty, xs) == List.filter(~String, ~Laws.top.word, xs) : List<&2, String>}

def ol.words(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, String>, List<&2, String>, r => List.filter.put(String, h, r, Laws.top.word(h)),
        List.filter(~String, ~Outline.nonempty, t), List.filter(~String, ~Laws.top.word, t), ol.words(t))

# what a line that opens mm leaves: that item onto the items settled, one
# line on
def ol.adds(mm: Maybe<&2, Outline.Item>, mode: Outline.Mode, out: List<&2, Outline.Item>, nn: U32) -> Seen:
  Seen{Laws.top.put(mm, Laws.top.keys(Outline.flush(mode, out))), (nn + 1 : U32)}

# a keyword line opens its item when the rest of the keyword follows, and
# nothing when it does not
law ol.kw:
  for +b: Bool
  for +cls: Outline.Cls
  for +mode: Outline.Mode
  for +ss: String
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +mm: Maybe<&2, Outline.Item>
  for on: {ol.after(cls, mode, ss, nn, doc, out) == ol.adds(mm, mode, out, nn) : Seen}
  {ol.after(Outline.classify.kw(b, cls), mode, ss, nn, doc, out)
    == ol.adds(Bool.pick(Maybe<&2, Outline.Item>, b, mm, None{}), mode, out, nn) : Seen}

def ol.kw(b, _cls, mode, ss, nn, _doc, out, _mm, on):
  match b:
    case True{}:
      on
    case False{}:
      ol.stray(mode, ss, nn, out)

# an import line's item, by its words, is the spec's
law ol.import.of:
  for +ws: List<&2, String>
  for +ss: String
  for +nn: U32
  for +dd: String
  for +xs: List<&2, Outline.Item>
  {Laws.top.keys(Outline.add(Outline.import_item.of(ws, ss, nn, dd), xs))
    == Laws.top.put(Laws.top.import(ws, nn), Laws.top.keys(xs)) : List<&2, Outline.Item>}

def ol.import.of(ws, _ss, _nn, _dd, _xs):
  match ws:
    case Nil{}:
      {==}
    case Con{_i, r1}:
      match r1:
        case Nil{}:
          {==}
        case Con{_p, r2}:
          match r2:
            case Nil{}:
              {==}
            case Con{_a, r3}:
              match r3:
                case Nil{}:
                  {==}
                case Con{_al, _r}:
                  {==}

# an import line opens the spec's import
law ol.imp_on:
  for +mode: Outline.Mode
  for +ss: String
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  {ol.after(Outline.LImport{}, mode, ss, nn, doc, out)
    == ol.adds(Laws.top.import(List.filter(~String, ~Laws.top.word, String.split(ss, ' ')), nn), mode, out, nn) : Seen}

def ol.imp_on(mode, ss, nn, doc, out):
  Equal.trans(Seen,
    Seen{Laws.top.keys(Outline.add(Outline.import_item.of(Outline.words(ss), ss, nn, Outline.doc_text(doc)),
      Outline.flush(mode, out))), (nn + 1 : U32)},
    ol.adds(Laws.top.import(Outline.words(ss), nn), mode, out, nn),
    ol.adds(Laws.top.import(List.filter(~String, ~Laws.top.word, String.split(ss, ' ')), nn), mode, out, nn),
    Equal.cong(List<&2, Outline.Item>, Seen, ks => Seen{ks, (nn + 1 : U32)},
      Laws.top.keys(Outline.add(Outline.import_item.of(Outline.words(ss), ss, nn, Outline.doc_text(doc)),
        Outline.flush(mode, out))),
      Laws.top.put(Laws.top.import(Outline.words(ss), nn), Laws.top.keys(Outline.flush(mode, out))),
      ol.import.of(Outline.words(ss), ss, nn, Outline.doc_text(doc), Outline.flush(mode, out))),
    Equal.cong(List<&2, String>, Seen, ws => ol.adds(Laws.top.import(ws, nn), mode, out, nn),
      Outline.words(ss), List.filter(~String, ~Laws.top.word, String.split(ss, ' ')),
      ol.words(String.split(ss, ' '))))

# a def line settles its def at once, or leaves it pending: either way it is
# listed, by the name the outline reads
law ol.start:
  for +colon: Bool
  for +ss: String
  for +nn: U32
  for +dd: String
  for +xs: List<&2, Outline.Item>
  {shown(Outline.start_def.on(colon, ss, nn, dd, xs))
    == Seen{Outline.Item{Outline.IDef{}, Outline.def_name(ss), nn, "", "", ""} <> Laws.top.keys(xs),
      (nn + 1 : U32)} : Seen}

def ol.start(colon, _ss, _nn, _dd, _xs):
  match colon:
    case True{}:
      {==}
    case False{}:
      {==}

# a def line whose name is read from nm opens the spec's def
law ol.def_on:
  for +mode: Outline.Mode
  for +ss: String
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +nm: String
  for en: {Outline.def_name(ss) == Outline.name(nm) : String}
  {ol.after(Outline.LDef{}, mode, ss, nn, doc, out)
    == ol.adds(Some{Outline.Item{Outline.IDef{}, Laws.top.name(nm), nn, "", "", ""}}, mode, out, nn) : Seen}

def ol.def_on(mode, ss, nn, doc, out, nm, en):
  Equal.trans(Seen,
    shown(Outline.start_def.on(Outline.ends_colon(ss), ss, nn, Outline.doc_text(doc), Outline.flush(mode, out))),
    Seen{Outline.Item{Outline.IDef{}, Outline.def_name(ss), nn, "", "", ""} <> Laws.top.keys(Outline.flush(mode, out)),
      (nn + 1 : U32)},
    ol.adds(Some{Outline.Item{Outline.IDef{}, Laws.top.name(nm), nn, "", "", ""}}, mode, out, nn),
    ol.start(Outline.ends_colon(ss), ss, nn, Outline.doc_text(doc), Outline.flush(mode, out)),
    Equal.cong(String, Seen,
      v => Seen{Outline.Item{Outline.IDef{}, v, nn, "", "", ""} <> Laws.top.keys(Outline.flush(mode, out)),
        (nn + 1 : U32)},
      Outline.def_name(ss), Laws.top.name(nm),
      Equal.trans(String, Outline.def_name(ss), Outline.name(nm), Laws.top.name(nm), en, ol.name(nm))))

# a law line opens the spec's law
law ol.law_on:
  for +mode: Outline.Mode
  for +ss: String
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  {ol.after(Outline.LLaw{}, mode, ss, nn, doc, out)
    == ol.adds(Some{Outline.Item{Outline.ILaw{}, Laws.top.name(String.drop(ss, 4n)), nn, "", "", ""}},
      mode, out, nn) : Seen}

def ol.law_on(mode, ss, nn, _doc, out):
  Equal.cong(String, Seen,
    v => Seen{Outline.Item{Outline.ILaw{}, v, nn, "", "", ""} <> Laws.top.keys(Outline.flush(mode, out)),
      (nn + 1 : U32)},
    Outline.name(String.drop(ss, 4n)), Laws.top.name(String.drop(ss, 4n)), ol.name(String.drop(ss, 4n)))

# a type line opens the spec's type
law ol.type_on:
  for +mode: Outline.Mode
  for +ss: String
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  {ol.after(Outline.LType{}, mode, ss, nn, doc, out)
    == ol.adds(Some{Outline.Item{Outline.IType{}, Laws.top.name(String.drop(ss, 5n)), nn, "", "", ""}},
      mode, out, nn) : Seen}

def ol.type_on(mode, ss, nn, _doc, out):
  Equal.cong(String, Seen,
    v => Seen{Outline.Item{Outline.IType{}, v, nn, "", "", ""} <> Laws.top.keys(Outline.flush(mode, out)),
      (nn + 1 : U32)},
    Outline.name(String.drop(ss, 5n)), Laws.top.name(String.drop(ss, 5n)), ol.name(String.drop(ss, 5n)))

# five keyword tests that all fail pick nothing
law ol.none5:
  for +b1: Bool
  for +b2: Bool
  for +b3: Bool
  for +b4: Bool
  for +b5: Bool
  for +a1: Maybe<&2, Outline.Item>
  for +a2: Maybe<&2, Outline.Item>
  for +a3: Maybe<&2, Outline.Item>
  for +a4: Maybe<&2, Outline.Item>
  for +a5: Maybe<&2, Outline.Item>
  for +e1: {b1 == False{} : Bool}
  for +e2: {b2 == False{} : Bool}
  for +e3: {b3 == False{} : Bool}
  for +e4: {b4 == False{} : Bool}
  for +e5: {b5 == False{} : Bool}
  {Bool.pick(Maybe<&2, Outline.Item>, b1, a1, Bool.pick(Maybe<&2, Outline.Item>, b2, a2,
    Bool.pick(Maybe<&2, Outline.Item>, b3, a3, Bool.pick(Maybe<&2, Outline.Item>, b4, a4,
      Bool.pick(Maybe<&2, Outline.Item>, b5, a5, None{}))))) == None{} : Maybe<&2, Outline.Item>}

def ol.none5(b1, b2, b3, b4, b5, a1, a2, a3, a4, a5, e1, e2, e3, e4, e5):
  match b1:
    case True{}:
      Empty.absurd({Bool.pick(Maybe<&2, Outline.Item>, True{}, a1, Bool.pick(Maybe<&2, Outline.Item>, b2, a2,
        Bool.pick(Maybe<&2, Outline.Item>, b3, a3, Bool.pick(Maybe<&2, Outline.Item>, b4, a4,
          Bool.pick(Maybe<&2, Outline.Item>, b5, a5, None{}))))) == None{} : Maybe<&2, Outline.Item>},
        true_false(e1))
    case False{}:
      match b2:
        case True{}:
          Empty.absurd({Bool.pick(Maybe<&2, Outline.Item>, True{}, a2,
            Bool.pick(Maybe<&2, Outline.Item>, b3, a3, Bool.pick(Maybe<&2, Outline.Item>, b4, a4,
              Bool.pick(Maybe<&2, Outline.Item>, b5, a5, None{})))) == None{} : Maybe<&2, Outline.Item>},
            true_false(e2))
        case False{}:
          match b3:
            case True{}:
              Empty.absurd({Bool.pick(Maybe<&2, Outline.Item>, True{}, a3, Bool.pick(Maybe<&2, Outline.Item>, b4, a4,
                Bool.pick(Maybe<&2, Outline.Item>, b5, a5, None{}))) == None{} : Maybe<&2, Outline.Item>},
                true_false(e3))
            case False{}:
              match b4:
                case True{}:
                  Empty.absurd({Bool.pick(Maybe<&2, Outline.Item>, True{}, a4,
                    Bool.pick(Maybe<&2, Outline.Item>, b5, a5, None{})) == None{} : Maybe<&2, Outline.Item>},
                    true_false(e4))
                case False{}:
                  match b5:
                    case True{}:
                      Empty.absurd({Bool.pick(Maybe<&2, Outline.Item>, True{}, a5, None{})
                        == None{} : Maybe<&2, Outline.Item>}, true_false(e5))
                    case False{}:
                      {==}

# a line whose first char is none of `i`, `d`, `@`, `l` and `t` opens no
# item in the spec
law ol.head_none:
  for +x: U32
  for +t: String
  for +nn: U32
  for +e105: {U32.is_eq(x, 105) == False{} : Bool}
  for +e100: {U32.is_eq(x, 100) == False{} : Bool}
  for +e64: {U32.is_eq(x, 64) == False{} : Bool}
  for +e108: {U32.is_eq(x, 108) == False{} : Bool}
  for +e116: {U32.is_eq(x, 116) == False{} : Bool}
  {Laws.top.head(SCon{Chr{x}, t}, nn) == None{} : Maybe<&2, Outline.Item>}

def ol.head_none(x, t, nn, e105, e100, e64, e108, e116):
  ol.none5(String.starts_with(SCon{Chr{x}, t}, "import "), String.starts_with(SCon{Chr{x}, t}, "def "),
    String.starts_with(SCon{Chr{x}, t}, "@unsafe def "), String.starts_with(SCon{Chr{x}, t}, "law "),
    String.starts_with(SCon{Chr{x}, t}, "type "),
    Laws.top.import(List.filter(~String, ~Laws.top.word, String.split(SCon{Chr{x}, t}, ' ')), nn),
    Some{Outline.Item{Outline.IDef{}, Laws.top.name(String.drop(SCon{Chr{x}, t}, 4n)), nn, "", "", ""}},
    Some{Outline.Item{Outline.IDef{}, Laws.top.name(String.drop(SCon{Chr{x}, t}, 12n)), nn, "", "", ""}},
    Some{Outline.Item{Outline.ILaw{}, Laws.top.name(String.drop(SCon{Chr{x}, t}, 4n)), nn, "", "", ""}},
    Some{Outline.Item{Outline.IType{}, Laws.top.name(String.drop(SCon{Chr{x}, t}, 5n)), nn, "", "", ""}},
    Equal.cong(Bool, Bool, b => String.starts_with.if(t, "mport ", b), U32.is_eq(x, 105), False{}, e105),
    Equal.cong(Bool, Bool, b => String.starts_with.if(t, "ef ", b), U32.is_eq(x, 100), False{}, e100),
    Equal.cong(Bool, Bool, b => String.starts_with.if(t, "unsafe def ", b), U32.is_eq(x, 64), False{}, e64),
    Equal.cong(Bool, Bool, b => String.starts_with.if(t, "aw ", b), U32.is_eq(x, 108), False{}, e108),
    Equal.cong(Bool, Bool, b => String.starts_with.if(t, "ype ", b), U32.is_eq(x, 116), False{}, e116))

# what a line of code with first char x leaves: what the spec says it opens,
# onto the items settled, one line on
def ol.goal(x: U32, t: String, mode: Outline.Mode, nn: U32, doc: List<&2, String>, out: List<&2, Outline.Item>) -> Type:
  {shown(Outline.step(False{}, SCon{Chr{x}, t}, Outline.St{mode, nn, doc, out}))
    == ol.adds(Bool.pick(Maybe<&2, Outline.Item>, False{}, None{}, Laws.top.head(SCon{Chr{x}, t}, nn)),
      mode, out, nn) : Seen}

# a line that opens with none of the keywords' first chars opens nothing, in
# the outline and in the spec
law ol.plain:
  for +x: U32
  for +t: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +e105: {U32.is_eq(x, 105) == False{} : Bool}
  for +e100: {U32.is_eq(x, 100) == False{} : Bool}
  for +e64: {U32.is_eq(x, 64) == False{} : Bool}
  for +e108: {U32.is_eq(x, 108) == False{} : Bool}
  for +e116: {U32.is_eq(x, 116) == False{} : Bool}
  ol.goal(x, t, mode, nn, doc, out)

def ol.plain(x, t, mode, nn, doc, out, e105, e100, e64, e108, e116):
  Equal.trans(Seen,
    shown(Outline.step(False{}, SCon{Chr{x}, t}, Outline.St{mode, nn, doc, out})),
    ol.same(mode, out, nn),
    ol.adds(Bool.pick(Maybe<&2, Outline.Item>, False{}, None{}, Laws.top.head(SCon{Chr{x}, t}, nn)), mode, out, nn),
    ol.hash(U32.is_eq(x, 35), Char.is_space(Chr{x}), x, t, mode, nn, doc, out, e105, e100, e64, e108, e116),
    Equal.cong(Maybe<&2, Outline.Item>, Seen, m => ol.adds(m, mode, out, nn),
      None{}, Laws.top.head(SCon{Chr{x}, t}, nn),
      Equal.sym(Maybe<&2, Outline.Item>, Laws.top.head(SCon{Chr{x}, t}, nn), None{},
        ol.head_none(x, t, nn, e105, e100, e64, e108, e116))))

# first char `t`, or none of the keywords'
law ol.c_ty:
  for +x: U32
  for +t: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +e105: {U32.is_eq(x, 105) == False{} : Bool}
  for +e100: {U32.is_eq(x, 100) == False{} : Bool}
  for +e64: {U32.is_eq(x, 64) == False{} : Bool}
  for +e108: {U32.is_eq(x, 108) == False{} : Bool}
  for +b: Bool
  for +e: {U32.is_eq(x, 116) == b : Bool}
  ol.goal(x, t, mode, nn, doc, out)

def ol.c_ty(x, t, mode, nn, doc, out, e105, e100, e64, e108, b, e):
  match b:
    case True{}:
      %Equal.sym(U32, x, 116, ol.ueq(x, 116, e)) : ol.goal(_, t, mode, nn, doc, out)
      ol.kw(String.starts_with(t, "ype "), Outline.LType{}, mode, SCon{Chr{116}, t}, nn, doc, out,
        Some{Outline.Item{Outline.IType{}, Laws.top.name(String.drop(SCon{Chr{116}, t}, 5n)), nn, "", "", ""}},
        ol.type_on(mode, SCon{Chr{116}, t}, nn, doc, out))
    case False{}:
      ol.plain(x, t, mode, nn, doc, out, e105, e100, e64, e108, e)

# first char `l`, else on
law ol.c_law:
  for +x: U32
  for +t: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +e105: {U32.is_eq(x, 105) == False{} : Bool}
  for +e100: {U32.is_eq(x, 100) == False{} : Bool}
  for +e64: {U32.is_eq(x, 64) == False{} : Bool}
  for +b: Bool
  for +e: {U32.is_eq(x, 108) == b : Bool}
  ol.goal(x, t, mode, nn, doc, out)

def ol.c_law(x, t, mode, nn, doc, out, e105, e100, e64, b, e):
  match b:
    case True{}:
      %Equal.sym(U32, x, 108, ol.ueq(x, 108, e)) : ol.goal(_, t, mode, nn, doc, out)
      ol.kw(String.starts_with(t, "aw "), Outline.LLaw{}, mode, SCon{Chr{108}, t}, nn, doc, out,
        Some{Outline.Item{Outline.ILaw{}, Laws.top.name(String.drop(SCon{Chr{108}, t}, 4n)), nn, "", "", ""}},
        ol.law_on(mode, SCon{Chr{108}, t}, nn, doc, out))
    case False{}:
      ol.c_ty(x, t, mode, nn, doc, out, e105, e100, e64, e, U32.is_eq(x, 116), {==})

# first char `@`, else on
law ol.c_at:
  for +x: U32
  for +t: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +e105: {U32.is_eq(x, 105) == False{} : Bool}
  for +e100: {U32.is_eq(x, 100) == False{} : Bool}
  for +b: Bool
  for +e: {U32.is_eq(x, 64) == b : Bool}
  ol.goal(x, t, mode, nn, doc, out)

def ol.c_at(x, t, mode, nn, doc, out, e105, e100, b, e):
  match b:
    case True{}:
      %Equal.sym(U32, x, 64, ol.ueq(x, 64, e)) : ol.goal(_, t, mode, nn, doc, out)
      ol.kw(String.starts_with(t, "unsafe def "), Outline.LDef{}, mode, SCon{Chr{64}, t}, nn, doc, out,
        Some{Outline.Item{Outline.IDef{}, Laws.top.name(String.drop(SCon{Chr{64}, t}, 12n)), nn, "", "", ""}},
        ol.def_on(mode, SCon{Chr{64}, t}, nn, doc, out, String.drop(SCon{Chr{64}, t}, 12n),
          Equal.cong(Bool, String, b => Outline.name(Bool.pick(String, b, String.drop(t, 11n), String.drop(t, 3n))),
            String.starts_with(t, SNil{}), True{},
            Equal.sym(Bool, True{}, String.starts_with(t, SNil{}), starts_nil(t)))))
    case False{}:
      ol.c_law(x, t, mode, nn, doc, out, e105, e100, e, U32.is_eq(x, 108), {==})

# first char `d`, else on
law ol.c_def:
  for +x: U32
  for +t: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +e105: {U32.is_eq(x, 105) == False{} : Bool}
  for +b: Bool
  for +e: {U32.is_eq(x, 100) == b : Bool}
  ol.goal(x, t, mode, nn, doc, out)

def ol.c_def(x, t, mode, nn, doc, out, e105, b, e):
  match b:
    case True{}:
      %Equal.sym(U32, x, 100, ol.ueq(x, 100, e)) : ol.goal(_, t, mode, nn, doc, out)
      ol.kw(String.starts_with(t, "ef "), Outline.LDef{}, mode, SCon{Chr{100}, t}, nn, doc, out,
        Some{Outline.Item{Outline.IDef{}, Laws.top.name(String.drop(SCon{Chr{100}, t}, 4n)), nn, "", "", ""}},
        ol.def_on(mode, SCon{Chr{100}, t}, nn, doc, out, String.drop(SCon{Chr{100}, t}, 4n), {==}))
    case False{}:
      ol.c_at(x, t, mode, nn, doc, out, e105, e, U32.is_eq(x, 64), {==})

# first char `i`, else on
law ol.c_imp:
  for +x: U32
  for +t: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +b: Bool
  for +e: {U32.is_eq(x, 105) == b : Bool}
  ol.goal(x, t, mode, nn, doc, out)

def ol.c_imp(x, t, mode, nn, doc, out, b, e):
  match b:
    case True{}:
      %Equal.sym(U32, x, 105, ol.ueq(x, 105, e)) : ol.goal(_, t, mode, nn, doc, out)
      ol.kw(String.starts_with(t, "mport "), Outline.LImport{}, mode, SCon{Chr{105}, t}, nn, doc, out,
        Laws.top.import(List.filter(~String, ~Laws.top.word, String.split(SCon{Chr{105}, t}, ' ')), nn),
        ol.imp_on(mode, SCon{Chr{105}, t}, nn, doc, out))
    case False{}:
      ol.c_def(x, t, mode, nn, doc, out, e, U32.is_eq(x, 100), {==})

# one line: text inside a string opens nothing; a line of code opens what
# the spec says; either way the machine moves one line on
law ol.step:
  for +w: Bool
  for +ll: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  {shown(Outline.step(w, ll, Outline.St{mode, nn, doc, out}))
    == ol.adds(Bool.pick(Maybe<&2, Outline.Item>, w, None{}, Laws.top.head(ll, nn)), mode, out, nn) : Seen}

def ol.step(w, ll, mode, nn, doc, out):
  match w:
    case True{}:
      match mode:
        case Outline.Top{}:
          {==}
        case Outline.InType{}:
          {==}
        case Outline.Pending{_k, _nm, _l, _d, _sig}:
          {==}
    case False{}:
      match ll:
        case SNil{}:
          {==}
        case SCon{c, t}:
          match c:
            case Chr{+x}:
              ol.c_imp(x, t, mode, nn, doc, out, U32.is_eq(x, 105), {==})

# a list with an item picked on or not, by kind, name and line, reversed onto r
law ol.key_rev:
  for +h: Outline.Item
  for +ks: List<&2, Outline.Item>
  for +r: List<&2, Outline.Item>
  {List.reverse.go(&2, Outline.Item, Laws.top.key(h, ks), r)
    == List.reverse.go(&2, Outline.Item, ks, Laws.top.key(h, r)) : List<&2, Outline.Item>}

def ol.key_rev(h, ks, r):
  match h:
    case Outline.Item{+k, +nm, +ln, _s, _d, _p}:
      ol.rev_pick(Outline.Item, Laws.top.kept(k), Outline.Item{k, nm, ln, "", "", ""}, ks, r)

# the keys of a list reversed onto acc: its keys reversed onto acc's
law ol.keys_rev:
  for +xs: List<&2, Outline.Item>
  for +acc: List<&2, Outline.Item>
  {Laws.top.keys(List.reverse.go(&2, Outline.Item, xs, acc))
    == List.reverse.go(&2, Outline.Item, Laws.top.keys(xs), Laws.top.keys(acc)) : List<&2, Outline.Item>}

def ol.keys_rev(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(List<&2, Outline.Item>,
        Laws.top.keys(List.reverse.go(&2, Outline.Item, t, h <> acc)),
        List.reverse.go(&2, Outline.Item, Laws.top.keys(t), Laws.top.key(h, Laws.top.keys(acc))),
        List.reverse.go(&2, Outline.Item, Laws.top.key(h, Laws.top.keys(t)), Laws.top.keys(acc)),
        ol.keys_rev(t, h <> acc),
        Equal.sym(List<&2, Outline.Item>,
          List.reverse.go(&2, Outline.Item, Laws.top.key(h, Laws.top.keys(t)), Laws.top.keys(acc)),
          List.reverse.go(&2, Outline.Item, Laws.top.keys(t), Laws.top.key(h, Laws.top.keys(acc))),
          ol.key_rev(h, Laws.top.keys(t), Laws.top.keys(acc))))

# an item, or none, put on a list reversed onto r: put on r instead
law ol.put_rev:
  for +mm: Maybe<&2, Outline.Item>
  for +ks: List<&2, Outline.Item>
  for +r: List<&2, Outline.Item>
  {List.reverse.go(&2, Outline.Item, Laws.top.put(mm, ks), r)
    == List.reverse.go(&2, Outline.Item, ks, Laws.top.put(mm, r)) : List<&2, Outline.Item>}

def ol.put_rev(mm, _ks, _r):
  match mm:
    case None{}:
      {==}
    case Some{_i}:
      {==}

# the keys a view holds
def ol.ks(vv: Seen) -> List<&2, Outline.Item>:
  match vv:
    case Seen{ks, _l}:
      ks

# the line a view is on
def ol.ln(vv: Seen) -> U32:
  match vv:
    case Seen{_ks, l}:
      l

# one line more: the keys the rest of the run lists follow the ones this
# line settles
law ol.run.arm:
  for +w: Bool
  for +ll: String
  for +t: List<&2, String>
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +r: List<&2, Bool>
  for ih: {Laws.top.keys(Outline.finish(Outline.run(t, Outline.step(w, ll, Outline.St{mode, nn, doc, out}), r)))
    == List.reverse.go(&2, Outline.Item, ol.ks(shown(Outline.step(w, ll, Outline.St{mode, nn, doc, out}))),
      Laws.top.spec(t, r, ol.ln(shown(Outline.step(w, ll, Outline.St{mode, nn, doc, out}))))) : List<&2, Outline.Item>}
  {Laws.top.keys(Outline.finish(Outline.run(t, Outline.step(w, ll, Outline.St{mode, nn, doc, out}), r)))
    == List.reverse.go(&2, Outline.Item, Laws.top.keys(Outline.flush(mode, out)),
      Laws.top.put(Bool.pick(Maybe<&2, Outline.Item>, w, None{}, Laws.top.head(ll, nn)),
        Laws.top.spec(t, r, (nn + 1 : U32)))) : List<&2, Outline.Item>}

def ol.run.arm(w, ll, t, mode, nn, doc, out, r, ih):
  Equal.trans(List<&2, Outline.Item>,
    Laws.top.keys(Outline.finish(Outline.run(t, Outline.step(w, ll, Outline.St{mode, nn, doc, out}), r))),
    List.reverse.go(&2, Outline.Item, ol.ks(shown(Outline.step(w, ll, Outline.St{mode, nn, doc, out}))),
      Laws.top.spec(t, r, ol.ln(shown(Outline.step(w, ll, Outline.St{mode, nn, doc, out}))))),
    List.reverse.go(&2, Outline.Item, Laws.top.keys(Outline.flush(mode, out)),
      Laws.top.put(Bool.pick(Maybe<&2, Outline.Item>, w, None{}, Laws.top.head(ll, nn)),
        Laws.top.spec(t, r, (nn + 1 : U32)))),
    ih,
    Equal.trans(List<&2, Outline.Item>,
      List.reverse.go(&2, Outline.Item, ol.ks(shown(Outline.step(w, ll, Outline.St{mode, nn, doc, out}))),
        Laws.top.spec(t, r, ol.ln(shown(Outline.step(w, ll, Outline.St{mode, nn, doc, out}))))),
      List.reverse.go(&2, Outline.Item,
        Laws.top.put(Bool.pick(Maybe<&2, Outline.Item>, w, None{}, Laws.top.head(ll, nn)),
          Laws.top.keys(Outline.flush(mode, out))),
        Laws.top.spec(t, r, (nn + 1 : U32))),
      List.reverse.go(&2, Outline.Item, Laws.top.keys(Outline.flush(mode, out)),
        Laws.top.put(Bool.pick(Maybe<&2, Outline.Item>, w, None{}, Laws.top.head(ll, nn)),
          Laws.top.spec(t, r, (nn + 1 : U32)))),
      Equal.cong(Seen, List<&2, Outline.Item>,
        vv => List.reverse.go(&2, Outline.Item, ol.ks(vv), Laws.top.spec(t, r, ol.ln(vv))),
        shown(Outline.step(w, ll, Outline.St{mode, nn, doc, out})),
        ol.adds(Bool.pick(Maybe<&2, Outline.Item>, w, None{}, Laws.top.head(ll, nn)), mode, out, nn),
        ol.step(w, ll, mode, nn, doc, out)),
      ol.put_rev(Bool.pick(Maybe<&2, Outline.Item>, w, None{}, Laws.top.head(ll, nn)),
        Laws.top.keys(Outline.flush(mode, out)), Laws.top.spec(t, r, (nn + 1 : U32)))))

# running the outline over the lines lists what the state has settled, then
# what the spec says the lines open
law ol.run:
  for +lines: List<&2, String>
  for +st: Outline.St
  for +ins: List<&2, Bool>
  {Laws.top.keys(Outline.finish(Outline.run(lines, st, ins)))
    == List.reverse.go(&2, Outline.Item, ol.ks(shown(st)), Laws.top.spec(lines, ins, ol.ln(shown(st))))
    : List<&2, Outline.Item>}

def ol.run(lines, st, ins):
  match lines:
    case Nil{}:
      match st:
        case Outline.St{mode, _nn, _doc, out}:
          ol.keys_rev(Outline.flush(mode, out), [])
    case Con{+ll, +t}:
      match st:
        case Outline.St{+mode, +nn, +doc, +out}:
          match ins:
            case Nil{}:
              ol.run.arm(False{}, ll, t, mode, nn, doc, out, [],
                ol.run(t, Outline.step(False{}, ll, Outline.St{mode, nn, doc, out}), []))
            case Con{+h, +r}:
              ol.run.arm(h, ll, t, mode, nn, doc, out, r,
                ol.run(t, Outline.step(h, ll, Outline.St{mode, nn, doc, out}), r))

def Laws.outline(text, toks):
  Equal.trans(List<&2, Outline.Item>,
    Laws.top.keys(Outline.of_tokens(text, toks)),
    Laws.top.spec(String.lines(text), Outline.inside(toks), 0),
    Laws.top.spec(String.lines(text), False{} <> Laws.top.strung(toks), 0),
    ol.run(String.lines(text), Outline.St{Outline.Top{}, 0, [], []}, Outline.inside(toks)),
    Equal.cong(List<&2, Bool>, List<&2, Outline.Item>, x => Laws.top.spec(String.lines(text), x, 0),
      Outline.inside(toks), False{} <> Laws.top.strung(toks), ol.flags(toks)))

# the binder's resolution (BOLT-SYN-5)
# ------------------------------------

# the innermost binder, one binder further out: the one here when it has the
# name, else the one the rest has
law rs.find.arm:
  for +b: Bool
  for +bb: Bind.Bind
  for -found: Maybe<&2, Bind.Bind>
  for -all: List<&2, Bind.Bind>
  for ih: {found == List.head(&2, Bind.Bind, all) : Maybe<&2, Bind.Bind>}
  {Bool.pick(Maybe<&2, Bind.Bind>, b, Some{bb}, found)
    == List.head(&2, Bind.Bind, Bool.pick(List<&2, Bind.Bind>, b, bb <> all, all)) : Maybe<&2, Bind.Bind>}

def rs.find.arm(b, _bb, _found, _all, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# the binder's search finds the first binder of the name
law rs.find:
  for +env: List<&2, Bind.Bind>
  for +name: String
  {Bind.find(env, name) == List.head(&2, Bind.Bind, Laws.res.all(env, name)) : Maybe<&2, Bind.Bind>}

def rs.find(env, name):
  match env:
    case Nil{}:
      {==}
    case Con{Bind.Bind{+n, +l, +c, +k, +note}, +t}:
      rs.find.arm(String.eq(n, name), Bind.Bind{n, l, c, k, note}, Bind.find(t, name), Laws.res.all(t, name),
        rs.find(t, name))

# is there a part after a dot?
def rs.ok(mm: Maybe<&2, String>) -> Bool:
  match mm:
    case None{}:
      False{}
    case Some{_r}:
      True{}

# the part after a dot, "" when there is none
def rs.dflt(mm: Maybe<&2, String>) -> String:
  match mm:
    case None{}:
      ""
    case Some{r}:
      r

# any text starts with the empty text
law rs.starts:
  for +t: String
  {String.starts_with(t, SNil{}) == True{} : Bool}

def rs.starts(t):
  match t:
    case SNil{}:
      {==}
    case SCon{_h, _r}:
      {==}

# a dot, one char further in: here, or wherever the rest has one
law rs.dot.arm:
  for +b: Bool
  for +t: String
  for ih: {String.contains(t, ".") == rs.ok(Laws.res.after(t)) : Bool}
  {String.contains.if(t, ".", String.starts_with.if(t, SNil{}, b))
    == rs.ok(Bool.pick(Maybe<&2, String>, b, Some{t}, Laws.res.after(t))) : Bool}

def rs.dot.arm(b, t, ih):
  match b:
    case True{}:
      %Equal.sym(Bool, String.starts_with(t, SNil{}), True{}, rs.starts(t))
        : {String.contains.if(t, ".", _) == True{} : Bool}
      {==}
    case False{}:
      ih

# a name holds a dot exactly when it has a part after one
law rs.dot:
  for +s: String
  {String.contains(s, ".") == rs.ok(Laws.res.after(s)) : Bool}

def rs.dot(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      rs.dot.arm(Char.is_eq(h, '.'), t, rs.dot(t))

# the part before a dot, one char further in
law rs.head.arm:
  for +b: Bool
  for +h: Char
  for +t: String
  for ih: {Bind.head_of(String.to_list(t)) == Laws.res.before(t) : String}
  {String.from_list(Lazy.stop(List<&2, Char>, b, Nil{}, _u => h <> Bind.head_of.go(String.to_list(t))))
    == Bool.pick(String, b, SNil{}, SCon{h, Laws.res.before(t)}) : String}

def rs.head.arm(b, h, t, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.cong(String, String, x => SCon{h, x}, Bind.head_of(String.to_list(t)), Laws.res.before(t), ih)

# the binder's qualifier is the part before the first dot
law rs.head:
  for +s: String
  {Bind.head_of(String.to_list(s)) == Laws.res.before(s) : String}

def rs.head(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      rs.head.arm(Char.is_eq(h, '.'), h, t, rs.head(t))

# the part after a dot, one char further in
law rs.rest.arm:
  for +b: Bool
  for +t: String
  for ih: {Bind.rest_of(String.to_list(t)) == rs.dflt(Laws.res.after(t)) : String}
  {Lazy.stop(String, b, String.from_list(String.to_list(t)), _u => Bind.rest_of(String.to_list(t)))
    == rs.dflt(Bool.pick(Maybe<&2, String>, b, Some{t}, Laws.res.after(t))) : String}

def rs.rest.arm(b, t, ih):
  match b:
    case True{}:
      chars(t)
    case False{}:
      ih

# the binder's qualified name is the part after the first dot
law rs.rest:
  for +s: String
  {Bind.rest_of(String.to_list(s)) == rs.dflt(Laws.res.after(s)) : String}

def rs.rest(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      rs.rest.arm(Char.is_eq(h, '.'), t, rs.rest(t))

# an alias qualifier, once the name is known to have a dot
law rs.alias:
  for +c: Bool
  for +q: String
  for +r: String
  {Lazy.stop(Bind.Target, Bool.not(c), Bind.TFree{}, _u => Bind.TQual{q, r})
    == Bool.pick(Bind.Target, c, Bind.TQual{q, r}, Bind.TFree{}) : Bind.Target}

def rs.alias(c, _q, _r):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# the binder's alias test, by whether the name has a part after a dot
law rs.qual:
  for +mm: Maybe<&2, String>
  for +q: String
  for +als: List<&2, String>
  {Lazy.stop(Bind.Target, Bool.not(Bool.and(rs.ok(mm), Bind.has(als, q))), Bind.TFree{},
      _u => Bind.TQual{q, rs.dflt(mm)})
    == Laws.res.qual(mm, q, als) : Bind.Target}

def rs.qual(mm, q, als):
  match mm:
    case None{}:
      {==}
    case Some{+r}:
      rs.alias(Bind.has(als, q), q, r)

# the binder's alias test, from what it computes of a name: whether it has a
# dot (c) and its part after one (r)
law rs.qual.at:
  for +c: Bool
  for +q: String
  for +r: String
  for +mm: Maybe<&2, String>
  for +als: List<&2, String>
  for e1: {c == rs.ok(mm) : Bool}
  for e2: {r == rs.dflt(mm) : String}
  {Lazy.stop(Bind.Target, Bool.not(Bool.and(c, Bind.has(als, q))), Bind.TFree{}, _u => Bind.TQual{q, r})
    == Laws.res.qual(mm, q, als) : Bind.Target}

def rs.qual.at(c, q, r, mm, als, e1, e2):
  %Equal.sym(Bool, c, rs.ok(mm), e1) : {Lazy.stop(Bind.Target, Bool.not(Bool.and(_, Bind.has(als, q))), Bind.TFree{},
      _u => Bind.TQual{q, r}) == Laws.res.qual(mm, q, als) : Bind.Target}
  %Equal.sym(String, r, rs.dflt(mm), e2) : {Lazy.stop(Bind.Target, Bool.not(Bool.and(rs.ok(mm), Bind.has(als, q))),
      Bind.TFree{}, _u => Bind.TQual{q, _}) == Laws.res.qual(mm, q, als) : Bind.Target}
  rs.qual(mm, q, als)

# what the binder makes of a name no binder holds and no item has
def rs.code(+name: String, als: List<&2, String>) -> Bind.Target:
  +cs = String.to_list(name)
  +head = Bind.head_of(cs)
  Lazy.stop(Bind.Target, Bool.not(Bool.and(String.contains(name, "."), Bind.has(als, head))), Bind.TFree{},
    _u => Bind.TQual{head, Bind.rest_of(cs)})

# a name no binder holds: an item, else what its dot and alias make of it
law rs.none:
  for +name: String
  for +its: List<&2, String>
  for +als: List<&2, String>
  {Bind.resolve.local(None{}, name, Bind.Names{its, als}) == Laws.res.found(None{}, name, its, als) : Bind.Target}

def rs.none(name, its, als):
  Equal.cong(Bind.Target, Bind.Target, x => Bool.pick(Bind.Target, Bind.has(its, name), Bind.TItem{name}, x),
    rs.code(name, als),
    Laws.res.qual(Laws.res.after(name), Laws.res.before(name), als),
    Equal.trans(Bind.Target,
      rs.code(name, als),
      Laws.res.qual(Laws.res.after(name), Bind.head_of(String.to_list(name)), als),
      Laws.res.qual(Laws.res.after(name), Laws.res.before(name), als),
      rs.qual.at(String.contains(name, "."), Bind.head_of(String.to_list(name)), Bind.rest_of(String.to_list(name)),
        Laws.res.after(name), als, rs.dot(name), rs.rest(name)),
      Equal.cong(String, Bind.Target, y => Laws.res.qual(Laws.res.after(name), y, als),
        Bind.head_of(String.to_list(name)), Laws.res.before(name), rs.head(name))))

# whatever the search found, the binder and the spec make the same of it
law rs.local:
  for +mm: Maybe<&2, Bind.Bind>
  for +name: String
  for +its: List<&2, String>
  for +als: List<&2, String>
  {Bind.resolve.local(mm, name, Bind.Names{its, als}) == Laws.res.found(mm, name, its, als) : Bind.Target}

def rs.local(mm, name, its, als):
  match mm:
    case Some{Bind.Bind{_n, _l, _c, _k, _note}}:
      {==}
    case None{}:
      rs.none(name, its, als)

def Laws.resolves(env, name, its, als):
  %Equal.sym(Maybe<&2, Bind.Bind>, Bind.find(env, name), List.head(&2, Bind.Bind, Laws.res.all(env, name)),
      rs.find(env, name))
    : {Bind.resolve.local(_, name, Bind.Names{its, als}) == Laws.res.spec(env, name, its, als) : Bind.Target}
  rs.local(List.head(&2, Bind.Bind, Laws.res.all(env, name)), name, its, als)

def Laws.uses(name, line, col, env, its, als, binds, us, scopes):
  Equal.cong(Bind.Target, Bind.W,
    x => Bind.W{env, Bind.Out{binds, Bind.Use{name, line, col, x} <> us, scopes}},
    Bind.resolve(env, name, Bind.Names{its, als}), Laws.res.spec(env, name, its, als),
    Laws.resolves(env, name, its, als))

# the environment the walk threads (BOLT-SYN-5)
# ---------------------------------------------

def Laws.fronts(_name, _line, _col, _kind, _env, out):
  match out:
    case Bind.Out{_b, _u, _s}:
      {==}

def Laws.fronts_decl(name, _line, _col, _kind, quantity, rest, _env, out):
  match out:
    case Bind.Out{_b, _u, _s}:
      (quantity ++ name ++ Bind.render(rest), {==})

def Laws.restores(kk, kids, body, rest, env, ns, out, e):
  match kk:
    case Tree.SDef{}:
      +h = Bind.walk(kids, Bind.MHead{}, env, ns, out)
      (Bind.out_of(Bind.walk(body, Bind.MBlock{}, Bind.env_of(h), ns,
        Bind.mark(Tree.line(kids), Bind.env_of(h), Bind.out_of(h)))), {==})
    case Tree.SType{}:
      +h = Bind.walk(kids, Bind.MHead{}, env, ns, out)
      (Bind.out_of(Bind.walk(body, Bind.MCtors{}, Bind.env_of(h), ns, Bind.out_of(h))), {==})
    case Tree.SLaw{}:
      +h = Bind.walk(kids, Bind.MHead{}, env, ns, out)
      (Bind.out_of(Bind.walk(body, Bind.MBlock{}, Bind.env_of(h), ns, Bind.out_of(h))), {==})
    case Tree.SImport{}:
      (out, {==})
    case Tree.SCase{}:
      +p = Bind.walk(kids, Bind.MLhs{env, Bind.KPat{}}, env, ns, Bind.mark(Tree.line(kids), env, out))
      (Bind.out_of(Bind.walk(body, Bind.MBlock{}, Bind.env_of(p), ns, Bind.out_of(p))), {==})
    case Tree.SFor{}:
      Empty.absurd(&o: Bind.Out
        -> {Bind.walk(Tree.NCons{Tree.Stmt{Tree.SFor{}, kids, body}, rest}, Bind.MBlock{}, env, ns, out)
          == Bind.walk(rest, Bind.MBlock{}, env, ns, o) : Bind.W}, false_true(e))
    case Tree.SLet{}:
      Empty.absurd(&o: Bind.Out
        -> {Bind.walk(Tree.NCons{Tree.Stmt{Tree.SLet{}, kids, body}, rest}, Bind.MBlock{}, env, ns, out)
          == Bind.walk(rest, Bind.MBlock{}, env, ns, o) : Bind.W}, false_true(e))
    case Tree.STerm{}:
      +t = Bind.walk(kids, Bind.MTerm{}, env, ns, Bind.mark(Tree.line(kids), env, out))
      (Bind.out_of(Bind.walk(body, Bind.MBlock{}, Bind.env_of(t), ns, Bind.out_of(t))), {==})

def Laws.groups(open, gkids, _close, _rest, env, ns, out):
  match open:
    case Lex.Tok{_k, _t, _l, _c}:
      (Bind.out_of(Bind.walk(gkids, Bind.MTerm{}, env, ns, out)), {==})
