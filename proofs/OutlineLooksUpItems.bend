# proofs of laws/OutlineLooksUpItems.bend
import Base
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/lex.bend as Lex
import ../src/syntax/outline.bend as Outline
import ../laws/OutlineLooksUpItems.bend as Laws
import ./lemmas/BoolEmptiness.bend as M1

# a search that stops at the first hit is the pick of it
law ol.stop:
  for -A: Type
  for c: Bool
  for -x: A
  for -y: A
  {Lazy.stop(A, c, x, _u => y) == Bool.pick(A, c, x, y) : A}

def ol.stop(_A, c, _x, _y):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# a stop at the first True is the plain or
law ol.or_else:
  for c: Bool
  for -x: Bool
  {Lazy.or_else(c, _u => x) == Bool.or(c, x) : Bool}

def ol.or_else(c, _x):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# a name is the one given or it is not: or with False is the test itself
law ol.or_false:
  for c: Bool
  {Bool.or(c, False{}) == c : Bool}

def ol.or_false(c):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# taking an item remembers its name and passing over it does not: the walk's
# pick of what to remember and its pick of what to give are one pick of the
# two outcomes
law ol.take:
  for b: Bool
  for -x: Outline.Item
  for -f: List<&2, String> -> List<&2, Outline.Item>
  for -a: List<&2, String>
  for -c: List<&2, String>
  {Bool.pick(List<&2, Outline.Item>, b, x <> f(Bool.pick(List<&2, String>, b, a, c)),
    f(Bool.pick(List<&2, String>, b, a, c))) == Bool.pick(List<&2, Outline.Item>, b, x <> f(a), f(c))
    : List<&2, Outline.Item>}

def ol.take(b, _x, _f, _a, _c):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.is_import_only_imports(k):
  match k:
    case Outline.IImport{}:
      {==}
    case Outline.IDef{}:
      {==}
    case Outline.ILaw{}:
      {==}
    case Outline.IType{}:
      {==}
    case Outline.ICtor{}:
      {==}
    case Outline.ILocal{}:
      {==}

def Laws.find_first_named(k, nm, l, s, d, p, t, name):
  ol.stop(Maybe<&2, Outline.Item>, Bool.and(Bool.not(Outline.is_import(k)), String.eq(nm, name)),
    Some{Outline.Item{k, nm, l, s, d, p}}, Outline.find(t, name))

def Laws.import_path_first_alias(k, nm, _l, _s, _d, p, t, alias):
  ol.stop(Maybe<&2, String>, Bool.and(Outline.is_import(k), String.eq(nm, alias)), Some{p},
    Outline.import_path(t, alias))

def Laws.has_first_or_rest(h, t, name):
  ol.or_else(String.eq(h, name), Outline.has(t, name))

def Laws.has_one_name(h, name):
  Equal.trans(Bool, Outline.has(h <> Nil{}, name), Bool.or(String.eq(h, name), False{}), String.eq(h, name),
    Laws.has_first_or_rest(h, Nil{}, name), ol.or_false(String.eq(h, name)))

def Laws.starting_takes_first_of_each_name(k, nm, l, s, d, p, t, prefix, qual, seen):
  ol.take(Bool.and(Bool.and(Bool.not(Outline.is_import(k)), String.starts_with(nm, prefix)),
    Bool.not(Outline.has(seen, nm))), Outline.Item{k, qual ++ nm, l, s, d, p},
    z => Outline.starting.go(t, prefix, qual, z), nm <> seen, seen)

def Laws.aliases_take_named_imports(_k, _nm, _l, _s, _d, _p, _t, _prefix):
  {==}

def Laws.starts_upper_first_char(_c, _t):
  {==}

def Laws.starts_upper_needs_a_char(cs, e):
  match cs:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Outline.starts_upper.of(cs) == False{} : Bool}, M1.false_true(e))

def Laws.ends_colon_last_significant(_kk, _tx, _ln, _cl, _t, _prev):
  {==}

def Laws.ends_colon_stands(_prev):
  {==}

def Laws.ends_colon_of_line(_ss):
  {==}
