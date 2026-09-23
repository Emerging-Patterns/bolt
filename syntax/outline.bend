# syntax/outline: a source's top-level items, read line by line. A top-level
# item starts at column 0, so a line the outline does not understand costs
# nothing: it is skipped, and the items around it still stand. That tolerance
# is the point: an editor asks about files that are half-written.
import Base
import ../lazy/lazy.bend as Lazy
import ./lex.bend as Lex

# what an item is; ILocal is not read from a source, it is how the server
# offers a binder as a candidate
type ItemKind is Data:
  IImport{}
  IDef{}
  ILaw{}
  IType{}
  ICtor{}
  ILocal{}

# line is 0-based; sig is the header text (a def's through its `:`, a law's
# whole block, a constructor's line); doc is the comment block right above;
# path is an import's target
type Item is Data:
  Item{kind: ItemKind, name: String, line: U32, sig: String, doc: String, path: String}

# what a line is, by its first chars
type Cls is Data:
  LBlank{}
  LComment{text: String}
  LIndent{text: String}
  LImport{}
  LDef{}
  LLaw{}
  LType{}
  LOther{}

# Pending: a def's header that has not reached its `:`, or a law's block
type Mode is Data:
  Top{}
  InType{}
  Pending{kind: ItemKind, name: String, line: U32, doc: String, sig: List<&2, String>}

# doc and out are reversed
type St is Data:
  St{mode: Mode, n: U32, doc: List<&2, String>, out: List<&2, Item>}

# only whitespace?
def is_blank(ss: String) -> Bool:
  List.all(~&2, ~Char, ~Char.is_space, String.to_list(ss))

# the class when the prefix matches, else other
def classify.kw(hit: Bool, yes: Cls) -> Cls:
  match hit:
    case True{}:
      yes
    case False{}:
      LOther{}

# leading spaces (reversed) in front of the rest of the line
def classify.rebuild(acc: List<&2, Char>, rest: String) -> String:
  match acc:
    case Nil{}:
      rest
    case Con{h, t}:
      classify.rebuild(t, SCon{h, rest})

# an indented line when the first char is a space, else other
def classify.white.hit(indent: Bool, acc: List<&2, Char>, hh: Char, rest: String) -> Cls:
  match indent:
    case True{}:
      LIndent{classify.rebuild(acc, SCon{hh, rest})}
    case False{}:
      LOther{}

# whitespace after a leading space-class char. `space` says `h` is whitespace;
# `acc` is the whitespace before `h`, reversed; `indent` when that line opened
# with a space
def classify.white(tt: String, space: Bool, hh: Char, indent: Bool, acc: List<&2, Char>) -> Cls:
  match tt space:
    case SNil{} True{}:
      LBlank{}
    case SNil{} False{}:
      classify.white.hit(indent, acc, hh, SNil{})
    case SCon{+h2, r} True{}:
      classify.white(r, Char.is_space(h2), h2, indent, hh <> acc)
    case SCon{h2, r} False{}:
      classify.white.hit(indent, acc, hh, SCon{h2, r})

# a line whose first char is whitespace
def classify.white.enter(tt: String, +xx: U32) -> Cls:
  classify.white(tt, True{}, Char.from_u32(xx), U32.is_eq(xx, 32), []) # ' '

# `type `, once the `t` is known
def classify.ktype(hit: Bool, tt: String) -> Cls:
  match hit:
    case True{}:
      classify.kw(String.starts_with(tt, "ype "), LType{})
    case False{}:
      LOther{}

# `law `, else `type `
def classify.klaw(hit: Bool, +xx: U32, tt: String) -> Cls:
  match hit:
    case True{}:
      classify.kw(String.starts_with(tt, "aw "), LLaw{})
    case False{}:
      classify.ktype(U32.is_eq(xx, 116), tt) # 't'

# `@unsafe def `, else `law `
def classify.kat(hit: Bool, +xx: U32, tt: String) -> Cls:
  match hit:
    case True{}:
      classify.kw(String.starts_with(tt, "unsafe def "), LDef{})
    case False{}:
      classify.klaw(U32.is_eq(xx, 108), xx, tt) # 'l'

# `def `, else `@unsafe def `
def classify.kdef(hit: Bool, +xx: U32, tt: String) -> Cls:
  match hit:
    case True{}:
      classify.kw(String.starts_with(tt, "ef "), LDef{})
    case False{}:
      classify.kat(U32.is_eq(xx, 64), xx, tt) # '@'

# `import `, else `def `
def classify.kimp(hit: Bool, +xx: U32, tt: String) -> Cls:
  match hit:
    case True{}:
      classify.kw(String.starts_with(tt, "mport "), LImport{})
    case False{}:
      classify.kdef(U32.is_eq(xx, 100), xx, tt) # 'd'

# a column-0 keyword, from the first character's code
def classify.keys(+xx: U32, tt: String) -> Cls:
  classify.kimp(U32.is_eq(xx, 105), xx, tt) # 'i'

def classify.space.go(space: Bool, xx: U32, tt: String) -> Cls:
  match space:
    case True{}:
      classify.white.enter(tt, xx)
    case False{}:
      classify.keys(xx, tt)

# whitespace, else a keyword
def classify.space(+xx: U32, tt: String) -> Cls:
  classify.space.go(Char.is_space(Char.from_u32(xx)), xx, tt)

# a column-0 keyword keeps the line; the class comes from its first character
def classify.hold.keys(+xx: U32, cc: Char, +tt: String) -> Cls & String:
  (classify.keys(xx, tt), SCon{cc, tt})

# whitespace that is not a leading space keeps the line: the class may not
def classify.hold.gap.keep(+xx: U32, cc: Char, +tt: String) -> Cls & String:
  (classify.white.enter(tt, xx), SCon{cc, tt})

# a leading space is blank or indented, and that class already carries the line
def classify.hold.gap(indent: Bool, xx: U32, cc: Char, tt: String) -> Cls & String:
  match indent:
    case True{}:
      (classify.white.enter(tt, xx), SNil{})
    case False{}:
      classify.hold.gap.keep(xx, cc, tt)

# whitespace, else a keyword
def classify.hold.space(space: Bool, +xx: U32, cc: Char, tt: String) -> Cls & String:
  match space:
    case True{}:
      classify.hold.gap(U32.is_eq(xx, 32), xx, cc, tt) # ' '
    case False{}:
      classify.hold.keys(xx, cc, tt)

# a comment keeps its text; anything else is whitespace or a keyword
def classify.hold.hash(is_hash: Bool, space: Bool, xx: U32, cc: Char, tt: String) -> Cls & String:
  match is_hash:
    case True{}:
      (LComment{SCon{cc, tt}}, SNil{})
    case False{}:
      classify.hold.space(space, xx, cc, tt)

# the first character, then the rest of the line
def classify.hold.open(+xx: U32, +cc: Char, tt: String) -> Cls & String:
  classify.hold.hash(U32.is_eq(xx, 35), Char.is_space(cc), xx, cc, tt) # '#'

# the class, and the line when the class does not already carry it
def classify.hold(ss: String) -> Cls & String:
  match ss:
    case SNil{}:
      (LBlank{}, SNil{})
    case SCon{+c, t}:
      classify.hold.open(Char.to_u32(c), c, t)

# the class, dropping a line the caller does not keep
def classify.cls(pp: Cls & String) -> Cls:
  (cls, _s) = pp
  cls

# a line's class, from its first character
def classify(ss: String) -> Cls:
  classify.cls(classify.hold(ss))

# `(`, `<`, `:`, `{` or a space ends a name
def name.stop(+hh: Char) -> Bool:
  Bool.or(Char.is_eq(hh, '('),
    Bool.or(Char.is_eq(hh, '<'),
      Bool.or(Char.is_eq(hh, ':'),
        Bool.or(Char.is_eq(hh, '{'), Char.is_eq(hh, ' ')))))

# a delimiter is not part of the name
def name.push(stop: Bool, hh: Char, acc: String) -> String:
  match stop:
    case True{}:
      acc
    case False{}:
      SCon{hh, acc}

# the name, reversed into acc, up to a delimiter
def name.go(ss: String, acc: String, stop: Bool) -> String:
  match ss stop:
    case SNil{} _:
      String.reverse(acc)
    case SCon{h, t} True{}:
      String.reverse(acc)
    case SCon{+h, t} False{}:
      name.go(t, name.push(name.stop(h), h, acc), name.stop(h))

# the name that starts a header: up to `(`, `<`, `:`, `{` or a space
def name(ss: String) -> String:
  name.go(ss, SNil{}, False{})

def lstrip.go(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Con{' ', t}:
      lstrip.go(t)
    case other:
      other

# leading spaces dropped
def lstrip(ss: String) -> String:
  String.from_list(lstrip.go(String.to_list(ss)))

# not ""?
def nonempty(ss: String) -> Bool:
  Bool.not(String.is_empty(ss))

# the words of a line
def words(ss: String) -> List<&2, String>:
  List.filter(~String, ~nonempty, String.split(ss, ' '))

# a comment line without its `# `
def undoc(+ss: String) -> String:
  Bool.pick(String, String.starts_with(ss, "# "), String.drop(ss, 2n),
    Bool.pick(String, String.starts_with(ss, "#"), String.drop(ss, 1n), ss))

def undoc.all(doc: List<&2, String>, acc: List<&2, String>) -> List<&2, String>:
  match doc:
    case Nil{}:
      acc
    case Con{h, t}:
      undoc.all(t, undoc(h) <> acc)

# the comment block (reversed) as text
def doc_text(doc: List<&2, String>) -> String:
  String.join(undoc.all(doc, []), "\n")

# the pending header lines (reversed) as one text
def sig_text(sig: List<&2, String>) -> String:
  String.join(List.reverse(&2, String, sig), "\n")

# an item, when there is one, onto the items
def add(mm: Maybe<&2, Item>, out: List<&2, Item>) -> List<&2, Item>:
  match mm:
    case None{}:
      out
    case Some{item}:
      item <> out

# `import <path> as <Alias>` is named by its alias; `import Base` by its path
def import_item.of(ws: List<&2, String>, ss: String, nn: U32, doc: String) -> Maybe<&2, Item>:
  match ws:
    case Con{i, Con{path, Con{as, Con{alias, r}}}}:
      Some{Item{IImport{}, alias, nn, ss, doc, path}}
    case Con{i, Con{+path, Nil{}}}:
      Some{Item{IImport{}, path, nn, ss, doc, path}}
    case other:
      None{}

# an `import` line as an item: `import Base`, or `import <path> as <Alias>`
def import_item(+ss: String, nn: U32, doc: String) -> Maybe<&2, Item>:
  import_item.of(words(ss), ss, nn, doc)

# the name of a `def` or `@unsafe def` line
def def_name(+ss: String) -> String:
  name(Bool.pick(String, String.starts_with(ss, "@"), String.drop(ss, 12n), String.drop(ss, 4n)))

def starts_upper.of(cs: List<&2, Char>) -> Bool:
  match cs:
    case Con{c, t}:
      Char.is_upper(c)
    case Nil{}:
      False{}

# does the text start with a capital?
def starts_upper(ss: String) -> Bool:
  starts_upper.of(String.to_list(ss))

# an indented line of a type block: `Ctor{..}`
def ctor.of(+tt: String, nn: U32) -> Maybe<&2, Item>:
  Lazy.stop(Maybe<&2, Item>, Bool.not(Bool.and(starts_upper(tt), String.contains(tt, "{"))), None{},
    _u => Some{Item{ICtor{}, name(tt), nn, tt, "", ""}})

# an indented line of a type block as a constructor item, when it is one
def ctor(text: String, nn: U32) -> Maybe<&2, Item>:
  ctor.of(lstrip(text), nn)

# a def?
def is_def(kk: ItemKind) -> Bool:
  match kk:
    case IDef{}:
      True{}
    case other:
      False{}

# what was pending becomes an item
def flush(mode: Mode, out: List<&2, Item>) -> List<&2, Item>:
  match mode:
    case Pending{k, nm, l, d, sig}:
      Item{k, nm, l, sig_text(sig), d, ""} <> out
    case other:
      out

# a `:` token?
def ends_colon.is(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TColon{}:
      True{}
    case other:
      False{}

# the tokens walked so far ended in `:`; a space or a comment keeps that
def ends_colon.go(toks: List<&2, Lex.Tok>, prev: Bool) -> Bool:
  match toks:
    case Nil{}:
      prev
    case Con{Lex.Tok{+kk, tx, ln, cl}, t}:
      ends_colon.go(t, Bool.pick(Bool, Lex.significant(kk), ends_colon.is(kk), prev))

# the line's last token that is not a space or a comment is `:`, so a header
# ends at its `:` though a comment follows it (`def f() -> U32: # note`)
def ends_colon(ss: String) -> Bool:
  ends_colon.go(Lex.tokens(ss), False{})

# a def continuation that does or does not end in `:`
def pend_more.closed(
  colon: Bool,
  nm: String,
  ll: U32,
  dd: String,
  sig: List<&2, String>,
  text: String,
  nn: U32,
  out: List<&2, Item>
) -> St:
  match colon:
    case True{}:
      St{Top{}, (nn + 1 : U32), [], Item{IDef{}, nm, ll, sig_text(text <> sig), dd, ""} <> out}
    case False{}:
      St{Pending{IDef{}, nm, ll, dd, text <> sig}, (nn + 1 : U32), [], out}

# one more line of a def header
def pend_more.def(
  nm: String,
  ll: U32,
  dd: String,
  sig: List<&2, String>,
  +text: String,
  nn: U32,
  out: List<&2, Item>
) -> St:
  pend_more.closed(ends_colon(text), nm, ll, dd, sig, text, nn, out)

# one more line of a pending header; a def's ends at the line that ends in `:`
def pend_more(
  kk: ItemKind,
  nm: String,
  ll: U32,
  dd: String,
  sig: List<&2, String>,
  text: String,
  nn: U32,
  out: List<&2, Item>
) -> St:
  match kk:
    case IDef{}:
      pend_more.def(nm, ll, dd, sig, text, nn, out)
    case other:
      St{Pending{kk, nm, ll, dd, text <> sig}, (nn + 1 : U32), [], out}

# an indented line: more of a pending header, a constructor of an open
# type, or nothing
def indent(mode: Mode, text: String, +nn: U32, out: List<&2, Item>) -> St:
  match mode:
    case Pending{k, nm, l, d, sig}:
      pend_more(k, nm, l, d, sig, text, nn, out)
    case InType{}:
      St{InType{}, (nn + 1 : U32), [], add(ctor(text, nn), out)}
    case Top{}:
      St{Top{}, (nn + 1 : U32), [], out}

# a column-0 line that starts nothing: `) -> T:` closing a def's header that
# broke across lines; anywhere else it is junk, and ends what was pending
def stray(+mode: Mode, text: String, +nn: U32, +out: List<&2, Item>) -> St:
  match mode:
    case Pending{IDef{}, nm, l, d, sig}:
      pend_more(IDef{}, nm, l, d, sig, text, nn, out)
    case m:
      St{Top{}, (nn + 1 : U32), [], flush(m, out)}

# a finished def, or a header that is still open
def start_def.on(colon: Bool, +ss: String, +nn: U32, doc: String, out: List<&2, Item>) -> St:
  match colon:
    case True{}:
      St{Top{}, (nn + 1 : U32), [], Item{IDef{}, def_name(ss), nn, ss, doc, ""} <> out}
    case False{}:
      St{Pending{IDef{}, def_name(ss), nn, doc, [ss]}, (nn + 1 : U32), [], out}

# a `def` line: an item at once when it ends in `:`, else a pending header
def start_def(+ss: String, +nn: U32, doc: String, out: List<&2, Item>) -> St:
  start_def.on(ends_colon(ss), ss, nn, doc, out)

# a comment continues the block above it only at the top level
def doc_above(mode: Mode, doc: List<&2, String>) -> List<&2, String>:
  match mode:
    case Top{}:
      doc
    case other:
      []

# a law header, pending the block under it
def step.law(+ss: String, +nn: U32, doc: String, mode: Mode, out: List<&2, Item>) -> St:
  St{Pending{ILaw{}, name(String.drop(ss, 4n)), nn, doc, [ss]}, (nn + 1 : U32), [], flush(mode, out)}

# a type header, and the block that follows it
def step.ty(+ss: String, +nn: U32, doc: String, mode: Mode, out: List<&2, Item>) -> St:
  St{InType{}, (nn + 1 : U32), [],
    Item{IType{}, name(String.drop(ss, 5n)), nn, ss, doc, ""} <> flush(mode, out)}

def step.go(cls: Cls, +mode: Mode, ss: String, +nn: U32, doc: List<&2, String>, out: List<&2, Item>) -> St:
  match cls:
    case LBlank{}:
      St{Top{}, (nn + 1 : U32), [], flush(mode, out)}
    case LComment{t}:
      St{Top{}, (nn + 1 : U32), t <> doc_above(mode, doc), flush(mode, out)}
    case LIndent{t}:
      indent(mode, t, nn, out)
    case LImport{}:
      St{Top{}, (nn + 1 : U32), [], add(import_item(ss, nn, doc_text(doc)), flush(mode, out))}
    case LDef{}:
      start_def(ss, nn, doc_text(doc), flush(mode, out))
    case LLaw{}:
      step.law(ss, nn, doc_text(doc), mode, out)
    case LType{}:
      step.ty(ss, nn, doc_text(doc), mode, out)
    case LOther{}:
      stray(mode, ss, nn, out)

# the class and the line, applied to the outline
def step.use(pp: Cls & String, mode: Mode, +nn: U32, doc: List<&2, String>, out: List<&2, Item>) -> St:
  (cls, s) = pp
  step.go(cls, mode, s, nn, doc, out)

# one line, by its class
def step(ss: String, st: St) -> St:
  St{mode, n, doc, out} = st
  step.use(classify.hold(ss), mode, n, doc, out)

# every line, in order
def run(lines: List<&2, String>, st: St) -> St:
  match lines:
    case Nil{}:
      st
    case Con{l, t}:
      run(t, step(l, st))

# the items once the lines are over, a pending header flushed
def finish(st: St) -> List<&2, Item>:
  St{mode, n, doc, out} = st
  List.reverse(&2, Item, flush(mode, out))

# the top-level items of a source, in order
def items(text: String) -> List<&2, Item>:
  finish(run(String.lines(text), St{Top{}, 0, [], []}))

# lookups
# -------

# an import?
def is_import(kk: ItemKind) -> Bool:
  match kk:
    case IImport{}:
      True{}
    case other:
      False{}

# the item of that name; imports are not names of the module
def find(items: List<&2, Item>, +name: String) -> Maybe<&2, Item>:
  match items:
    case Nil{}:
      None{}
    case Con{Item{+k, +nm, l, s, d, p}, t}:
      Lazy.stop(Maybe<&2, Item>, Bool.and(Bool.not(is_import(k)), String.eq(nm, name)),
        Some{Item{k, nm, l, s, d, p}}, _u => find(t, name))

# the path behind an import alias
def import_path(items: List<&2, Item>, +alias: String) -> Maybe<&2, String>:
  match items:
    case Nil{}:
      None{}
    case Con{Item{k, nm, l, s, d, p}, t}:
      Lazy.stop(Maybe<&2, String>, Bool.and(is_import(k), String.eq(nm, alias)),
        Some{p}, _u => import_path(t, alias))

# is the name among these?
def has(names: List<&2, String>, +name: String) -> Bool:
  match names:
    case Nil{}:
      False{}
    case Con{h, t}:
      Lazy.or_else(String.eq(h, name), _u => has(t, name))

def starting.go(items: List<&2, Item>, +prefix: String, +qual: String, +seen: List<&2, String>) -> List<&2, Item>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Item{+k, +nm, l, s, d, p}, t}:
      +take = Bool.and(Bool.and(Bool.not(is_import(k)), String.starts_with(nm, prefix)), Bool.not(has(seen, nm)))
      # one recursive call: Bool.pick evaluates both of its branches
      +rest = starting.go(t, prefix, qual, Bool.pick(List<&2, String>, take, nm <> seen, seen))
      Bool.pick(List<&2, Item>, take, Item{k, qual ++ nm, l, s, d, p} <> rest, rest)

# the named items whose name starts with prefix, each renamed qual ++ name (the
# text to insert). A law and the def that fills it share a name: the first
# stands for both.
def starting(items: List<&2, Item>, prefix: String, qual: String) -> List<&2, Item>:
  starting.go(items, prefix, qual, [])

# the import aliases that start with prefix (`import Base` has none)
def aliases(items: List<&2, Item>, +prefix: String) -> List<&2, Item>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Item{+k, +nm, l, s, d, +p}, t}:
      +rest = aliases(t, prefix)
      Bool.pick(List<&2, Item>,
        Bool.and(Bool.and(is_import(k), String.starts_with(nm, prefix)), Bool.not(String.eq(nm, p))),
        Item{k, nm, l, s, d, p} <> rest, rest)
