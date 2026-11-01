# string, char and leaf-adding facts behind lexing, tree and outline proofs
import Base
import ../../src/syntax/lex.bend as Lex
import ../../src/rchars.bend as Rchars
import ../../src/syntax/tree.bend as Tree
import ../../src/lazy/lazy.bend as Lazy
import ../../laws/TreeKeepsEveryToken.bend as L1

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

# folding a buffer onto a string spells the reversed buffer, then the string
law rword.go:
  for +xs: List<&2, Char>
  for +acc: String
  {Rchars.onto(xs, acc) == String.append(rword(xs), acc) : String}

def rword.go(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.trans(String,
        Rchars.onto(t, SCon{h, acc}),
        String.append(rword(t), SCon{h, acc}),
        String.append(String.append(rword(t), one(h)), acc),
        rword.go(t, SCon{h, acc}),
        Equal.sym(String, String.append(String.append(rword(t), one(h)), acc),
          String.append(rword(t), SCon{h, acc}),
          app.assoc(rword(t), one(h), acc)))

# a buffer's word is its reversed chars
law rword.word:
  for +buf: List<&2, Char>
  {Lex.word(buf) == rword(buf) : String}

def rword.word(buf):
  Equal.trans(String, Lex.word(buf), String.append(rword(buf), SNil{}), rword(buf),
    rword.go(buf, SNil{}), app.nil(rword(buf)))

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

# whichever state the step takes, it has read one char more
law pick:
  for +b: Bool
  for -x: Lex.St
  for -y: Lex.St
  for -z: String
  for +ex: {seen(x) == z : String}
  for +ey: {seen(y) == z : String}
  {seen(Lazy.either(Lex.St, b, _u => x, _v => y)) == z : String}

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

# what the law adds for a significant token: a run of `>` split, else itself
def law_adds(+k: Lex.TokKind, +t: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  Bool.pick(List<&2, Lex.Tok>, L1.gt_run(k, t), L1.gts(String.to_list(t), l, c), [Lex.Tok{k, t, l, c}])

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

# the leaves one token adds: none when it is trivia, else what the law splits
# it into
def adds(+kk: Lex.TokKind, +tt: String, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  Bool.pick(List<&2, Lex.Tok>, Lex.significant(kk), law_adds(kk, tt, ll, cc), [])

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
