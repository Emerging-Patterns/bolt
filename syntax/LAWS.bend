# syntax: the laws. Each quantifies over every source, never one fixture.
import Base
import ./lex.bend as Lex
import ./tree.bend as Tree
import ./outline.bend as Outline
import ../lazy/lazy.bend as Lazy
import ./bind.bend as Bind

# LAW: the tokens' texts spell the source back, whatever the source is
# BOLT-SYN-1
law lossless:
  for +s: String
  {Lex.text(Lex.tokens(s)) == s : String}

# is the char a line break? '\n', code point 10
def breaks(cc: Char) -> Bool:
  U32.is_eq(Char.to_u32(cc), 10)

# the line reading a text ends on, from line ln: one more per line break
def line_after(src: String, +ln: U32) -> U32:
  match src:
    case SNil{}:
      ln
    case SCon{h, t}:
      line_after(t, Bool.pick(U32, breaks(h), (ln + 1 : U32), ln))

# the column reading a text ends on, from column cn: one more per code point,
# back to 0 after a line break
def col_after(src: String, +cn: U32) -> U32:
  match src:
    case SNil{}:
      cn
    case SCon{h, t}:
      col_after(t, Bool.pick(U32, breaks(h), 0, (cn + 1 : U32)))

# the tokens, each moved to where reading the texts before it from (ln, cn)
# ends: the position of its first char
def placed(toks: List<&2, Lex.Tok>, +ln: U32, +cn: U32) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      []
    case Con{Lex.Tok{k, +t, _l, _c}, rest}:
      Lex.Tok{k, t, ln, cn} <> placed(rest, line_after(t, ln), col_after(t, cn))

# LAW: every token already sits where placed puts it. By lossless, the texts
# before a token are the source up to its first char, so its line and column
# are that char's, 0-based, counting code points
# BOLT-SYN-2
law positions:
  for +s: String
  {placed(Lex.tokens(s), 0, 0) == Lex.tokens(s) : List<&2, Lex.Tok>}

# the significant tokens, in order: no space, newline or comment
def significant(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      []
    case Con{Lex.Tok{+k, t, l, c}, rest}:
      +more = significant(rest)
      Bool.pick(List<&2, Lex.Tok>, Lex.significant(k), Lex.Tok{k, t, l, c} <> more, more)

# is every char a `>`?
def only_gt(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+ch, t}:
      Lazy.and_then(Char.is_eq(ch, '>'), _u => only_gt(t))

# a token the tree reads as a run of closing `>`: an operator of one or more
# `>` and nothing else (`>`, `>>`), whatever is open when it comes; also a
# close bracket whose text starts with `>`, which the lexer never makes (its
# close brackets are `)`, `]` and `}`)
def gt_run(kk: Lex.TokKind, +tt: String) -> Bool:
  match kk:
    case Lex.TOp{}:
      Bool.and(Bool.not(String.is_empty(tt)), only_gt(String.to_list(tt)))
    case Lex.TClose{}:
      String.starts_with(tt, ">")
    case other:
      False{}

# one `>` operator per char, on line ln at consecutive columns from cn
def gts(cs: List<&2, Char>, +ln: U32, +cn: U32) -> List<&2, Lex.Tok>:
  match cs:
    case Nil{}:
      []
    case Con{_ch, t}:
      Lex.Tok{Lex.TOp{}, ">", ln, cn} <> gts(t, ln, (cn + 1 : U32))

# the tokens in order, each run of `>` split into one `>` per char
def split_gts(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      []
    case Con{Lex.Tok{+k, +t, +l, +c}, rest}:
      List.append(&2, Lex.Tok,
        Bool.pick(List<&2, Lex.Tok>, gt_run(k, t), gts(String.to_list(t), l, c), [Lex.Tok{k, t, l, c}]),
        split_gts(rest))

# LAW: the tree drops no token and adds none: read back in order, its leaves
# are the significant tokens, except that a run of `>` becomes one `>` leaf
# per char, at consecutive columns (each closes the angle group on top, or is
# a stray leaf when there is none: an operator `>>` is split too)
# BOLT-SYN-3
law leaves:
  for +toks: List<&2, Lex.Tok>
  {Tree.leaves(Tree.of_tokens(toks)) == split_gts(significant(toks)) : List<&2, Lex.Tok>}

# the outline (BOLT-SYN-4), written apart from outline.bend. A line starts
# inside a string when the line break before it sits in a string token: such
# a line is text, never an item. Any other line opens an item when it starts,
# at column 0, with `import `, `def `, `@unsafe def `, `law ` or `type `. An
# item is compared by its kind, name and line; its header, doc and path are
# left out, and so are the constructors of a type block, which are not
# column-0 items.

# one flag per line break in a text, in order, each str: whether the text is
# a string's
def top.breaks(tt: String, +str: Bool) -> List<&2, Bool>:
  match tt:
    case SNil{}:
      []
    case SCon{h, t}:
      +rest = top.breaks(t, str)
      Bool.pick(List<&2, Bool>, breaks(h), str <> rest, rest)

# one flag per line break in the tokens' texts, in order: does it sit inside
# a string?
def top.strung(toks: List<&2, Lex.Tok>) -> List<&2, Bool>:
  match toks:
    case Nil{}:
      []
    case Con{Lex.Tok{k, t, _l, _c}, rest}:
      List.append(&2, Bool, top.breaks(t, Lex.is_str(k)), top.strung(rest))

# what ends a name: `(`, `<`, `:`, `{` or a space
def top.stop(+hh: Char) -> Bool:
  Bool.or(Char.is_eq(hh, '('),
    Bool.or(Char.is_eq(hh, '<'),
      Bool.or(Char.is_eq(hh, ':'),
        Bool.or(Char.is_eq(hh, '{'), Char.is_eq(hh, ' ')))))

# the name a header gives: its text up to the first char that ends a name
def top.name(ss: String) -> String:
  match ss:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      Bool.pick(String, top.stop(h), SNil{}, SCon{h, top.name(t)})

# a word is not empty
def top.word(ss: String) -> Bool:
  Bool.not(String.is_empty(ss))

# an import line, by its words: named by its fourth, the alias of `import P
# as A`, when it has four or more; by its path when it has two; else no item
# (bend reads no other shape)
def top.import(ws: List<&2, String>, nn: U32) -> Maybe<&2, Outline.Item>:
  match ws:
    case Con{_i, Con{_p, Con{_a, Con{alias, _r}}}}:
      Some{Outline.Item{Outline.IImport{}, alias, nn, "", "", ""}}
    case Con{_i, Con{path, Nil{}}}:
      Some{Outline.Item{Outline.IImport{}, path, nn, "", "", ""}}
    case _other:
      None{}

# the item a line of code opens at column 0, by its kind, name and line nn
def top.head(+ss: String, +nn: U32) -> Maybe<&2, Outline.Item>:
  Bool.pick(Maybe<&2, Outline.Item>, String.starts_with(ss, "import "),
    top.import(List.filter(~String, ~top.word, String.split(ss, ' ')), nn),
  Bool.pick(Maybe<&2, Outline.Item>, String.starts_with(ss, "def "),
    Some{Outline.Item{Outline.IDef{}, top.name(String.drop(ss, 4n)), nn, "", "", ""}},
  Bool.pick(Maybe<&2, Outline.Item>, String.starts_with(ss, "@unsafe def "),
    Some{Outline.Item{Outline.IDef{}, top.name(String.drop(ss, 12n)), nn, "", "", ""}},
  Bool.pick(Maybe<&2, Outline.Item>, String.starts_with(ss, "law "),
    Some{Outline.Item{Outline.ILaw{}, top.name(String.drop(ss, 4n)), nn, "", "", ""}},
  Bool.pick(Maybe<&2, Outline.Item>, String.starts_with(ss, "type "),
    Some{Outline.Item{Outline.IType{}, top.name(String.drop(ss, 5n)), nn, "", "", ""}},
    None{})))))

# an item onto the items, when there is one
def top.put(mm: Maybe<&2, Outline.Item>, rest: List<&2, Outline.Item>) -> List<&2, Outline.Item>:
  match mm:
    case None{}:
      rest
    case Some{item}:
      item <> rest

# the first line's flag; no flag left is no
def top.first(ins: List<&2, Bool>) -> Bool:
  match ins:
    case Nil{}:
      False{}
    case Con{h, _t}:
      h

# the flags of the lines after the first
def top.later(ins: List<&2, Bool>) -> List<&2, Bool>:
  match ins:
    case Nil{}:
      []
    case Con{_h, t}:
      t

# the items the lines open, the first numbered nn; ins flags the lines that
# start inside a string, which open none
def top.spec(lines: List<&2, String>, +ins: List<&2, Bool>, +nn: U32) -> List<&2, Outline.Item>:
  match lines:
    case Nil{}:
      []
    case Con{ll, rest}:
      top.put(Bool.pick(Maybe<&2, Outline.Item>, top.first(ins), None{}, top.head(ll, nn)),
        top.spec(rest, top.later(ins), (nn + 1 : U32)))

# every kind but a constructor
def top.kept(kk: Outline.ItemKind) -> Bool:
  match kk:
    case Outline.ICtor{}:
      False{}
    case other:
      True{}

# an item by its kind, name and line, onto the rest; a constructor is left out
def top.key(item: Outline.Item, +rest: List<&2, Outline.Item>) -> List<&2, Outline.Item>:
  match item:
    case Outline.Item{+k, nm, ln, _s, _d, _p}:
      Bool.pick(List<&2, Outline.Item>, top.kept(k), Outline.Item{k, nm, ln, "", "", ""} <> rest, rest)

# the items by kind, name and line, constructors left out
def top.keys(items: List<&2, Outline.Item>) -> List<&2, Outline.Item>:
  match items:
    case Nil{}:
      []
    case Con{h, t}:
      top.key(h, top.keys(t))

# LAW: the outline lists exactly the column-0 imports, defs, `@unsafe def`s,
# laws and types, in order, each with its name and line: whatever the text
# and its tokens, line 0 starts outside any string, and the line after each
# line break starts inside one exactly when that break sits in a string token
# BOLT-SYN-4
law outline:
  for +text: String
  for +toks: List<&2, Lex.Tok>
  {top.keys(Outline.of_tokens(text, toks))
    == top.spec(String.lines(text), False{} <> top.strung(toks), 0) : List<&2, Outline.Item>}

# the binder's resolution (BOLT-SYN-5), written apart from bind.bend. The
# environment lists the binders in scope innermost first. A use of a name
# refers to the first binder of that name there; with none, to an item of
# the file of that name; with none, when the name has a dot and its part
# before the first dot is an import alias, to the rest after that dot behind
# the alias; else to nothing the file knows.

# the binders of a name, in the environment's order
def res.all(env: List<&2, Bind.Bind>, +name: String) -> List<&2, Bind.Bind>:
  match env:
    case Nil{}:
      []
    case Con{Bind.Bind{+n, l, c, k, note}, t}:
      +more = res.all(t, name)
      Bool.pick(List<&2, Bind.Bind>, String.eq(n, name), Bind.Bind{n, l, c, k, note} <> more, more)

# a name's part before its first dot: all of it when it has none
def res.before(ss: String) -> String:
  match ss:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      +more = res.before(t)
      Bool.pick(String, Char.is_eq(h, '.'), SNil{}, SCon{h, more})

# a name's part after its first dot, when it has one
def res.after(ss: String) -> Maybe<&2, String>:
  match ss:
    case SNil{}:
      None{}
    case SCon{+h, +t}:
      +more = res.after(t)
      Bool.pick(Maybe<&2, String>, Char.is_eq(h, '.'), Some{t}, more)

# a name no binder holds and no item has: behind an alias when it has a dot
# and the part before is one of the aliases, else free
def res.qual(after: Maybe<&2, String>, +before: String, als: List<&2, String>) -> Bind.Target:
  match after:
    case None{}:
      Bind.TFree{}
    case Some{rest}:
      Bool.pick(Bind.Target, List.contains(~String, ~String.eq, als, before), Bind.TQual{before, rest}, Bind.TFree{})

# what a name refers to once the innermost binder of it, if any, is found
def res.found(mm: Maybe<&2, Bind.Bind>, +name: String, its: List<&2, String>, als: List<&2, String>) -> Bind.Target:
  match mm:
    case Some{Bind.Bind{_n, l, c, _k, _note}}:
      Bind.TLocal{l, c}
    case None{}:
      Bool.pick(Bind.Target, List.contains(~String, ~String.eq, its, name), Bind.TItem{name},
        res.qual(res.after(name), res.before(name), als))

# what a name refers to, against the binders in scope and the file's items
# and aliases
def res.spec(env: List<&2, Bind.Bind>, +name: String, its: List<&2, String>, als: List<&2, String>) -> Bind.Target:
  res.found(List.head(&2, Bind.Bind, res.all(env, name)), name, its, als)

# LAW: the binder resolves a name to the innermost binder of it, else an
# item of the file, else an alias qualifier, else free: whatever the
# environment, the name, the items and the aliases
# BOLT-SYN-5
law resolves:
  for +env: List<&2, Bind.Bind>
  for +name: String
  for +its: List<&2, String>
  for +als: List<&2, String>
  {Bind.resolve(env, name, Bind.Names{its, als}) == res.spec(env, name, its, als) : Bind.Target}

# LAW: the walk records each use it reads with that target, and changes
# neither the environment nor anything else it has gathered
# BOLT-SYN-5
law uses:
  for +name: String
  for +line: U32
  for +col: U32
  for +env: List<&2, Bind.Bind>
  for +its: List<&2, String>
  for +als: List<&2, String>
  for +binds: List<&2, Bind.Bind>
  for +us: List<&2, Bind.Use>
  for +scopes: List<&2, Bind.Scope>
  {Bind.use(name, line, col, env, Bind.Names{its, als}, Bind.Out{binds, us, scopes})
    == Bind.W{env, Bind.Out{binds, Bind.Use{name, line, col, res.spec(env, name, its, als)} <> us, scopes}} : Bind.W}

# the environment the walk threads (BOLT-SYN-5): what makes the first binder
# of a name in it the innermost one in scope. A binder goes on the front, and
# a scope, once left, gives back the environment it was entered with: a
# statement other than a let or a `for` is such a scope for the statements
# after it, and a group for the terms after it. Still to prove: that the walk
# only ever puts binders in front of the environment it was given.

# LAW: a binder the walk introduces goes on the front of the environment
# BOLT-SYN-5
law fronts:
  for +name: String
  for +line: U32
  for +col: U32
  for +kind: Bind.BindKind
  for +env: List<&2, Bind.Bind>
  for +out: Bind.Out
  {Bind.env_of(Bind.bind(name, line, col, kind, env, out)) == Bind.Bind{name, line, col, kind, ""} <> env
    : List<&2, Bind.Bind>}

# LAW: so does a binder of a telescope, whatever its note says
# BOLT-SYN-5
law fronts_decl:
  for +name: String
  for +line: U32
  for +col: U32
  for +kind: Bind.BindKind
  for +quantity: String
  for +rest: Tree.Node
  for +env: List<&2, Bind.Bind>
  for +out: Bind.Out
  exs note: String
  {Bind.env_of(Bind.bind_decl(name, line, col, kind, quantity, rest, env, out))
    == Bind.Bind{name, line, col, kind, note} <> env : List<&2, Bind.Bind>}

# does a statement of this kind close its scope for the statements after it?
# All but a let and a `for` do
def scoped(kk: Tree.StmtKind) -> Bool:
  match kk:
    case Tree.SLet{}:
      False{}
    case Tree.SFor{}:
      False{}
    case _other:
      True{}

# LAW: the statements after a def, law, type, import, case or term statement
# are read with the environment it was entered with
# BOLT-SYN-5
law restores:
  for +kk: Tree.StmtKind
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +env: List<&2, Bind.Bind>
  for +ns: Bind.Names
  for +out: Bind.Out
  for e: {scoped(kk) == True{} : Bool}
  exs o: Bind.Out
  {Bind.walk(Tree.NCons{Tree.Stmt{kk, kids, body}, rest}, Bind.MBlock{}, env, ns, out)
    == Bind.walk(rest, Bind.MBlock{}, env, ns, o) : Bind.W}

# LAW: the terms after a group are read with the environment it was entered
# with: a lambda inside it binds only inside it
# BOLT-SYN-5
law groups:
  for +open: Lex.Tok
  for +gkids: Tree.Node
  for +close: Maybe<&2, Lex.Tok>
  for +rest: Tree.Node
  for +env: List<&2, Bind.Bind>
  for +ns: Bind.Names
  for +out: Bind.Out
  exs o: Bind.Out
  {Bind.walk(Tree.NCons{Tree.Group{open, gkids, close}, rest}, Bind.MTerm{}, env, ns, out)
    == Bind.walk(rest, Bind.MTerm{}, env, ns, o) : Bind.W}
