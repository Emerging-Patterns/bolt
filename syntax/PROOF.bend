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
      Bool.pick(U32, Lex.is_newline(Lex.classify(cc)), (line + 1 : U32), line),
      Bool.pick(U32, Lex.is_newline(Lex.classify(cc)), 0, (col + 1 : U32)), sl, sc, cc <> buf, toks},
    Lex.St{Lex.begin.mode(Lex.classify(cc)), Lex.begin.kind(Lex.classify(cc)),
      Bool.pick(U32, Lex.is_newline(Lex.classify(cc)), (line + 1 : U32), line),
      Bool.pick(U32, Lex.is_newline(Lex.classify(cc)), 0, (col + 1 : U32)), line, col, [cc],
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
