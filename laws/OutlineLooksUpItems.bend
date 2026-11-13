# Looking items up in a file's outline. The language server completes names,
# jumps to items and follows import aliases through these, and `closed` and
# `coverage` read the same outline. An import is never a name of its module:
# a lookup by name passes over imports, a lookup by alias reads only them.
# The first item that matches is the one found. Completion offers each name
# once, where it first appears (a law and the def that fills it share one),
# and offers an alias only when it differs from its path (`import Base` has
# none).
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/outline.bend as Outline

# is the item an import? Law vocabulary: bolt never calls it
def outline.is_import(kk: Outline.ItemKind) -> Bool:
  match kk:
    case Outline.IImport{}:
      True{}
    case Outline.IDef{}:
      False{}
    case Outline.ILaw{}:
      False{}
    case Outline.IType{}:
      False{}
    case Outline.ICtor{}:
      False{}
    case Outline.ILocal{}:
      False{}

# LAW: only an import is an import
law is_import_only_imports:
  for kk: Outline.ItemKind
  {Outline.is_import(kk) == outline.is_import(kk) : Bool}

# LAW: the item of a name is the first item that is not an import and has
# that name
law find_first_named:
  for +k: Outline.ItemKind
  for +nm: String
  for l: U32
  for s: String
  for d: String
  for p: String
  for t: List<&2, Outline.Item>
  for +name: String
  {Outline.find(Outline.Item{k, nm, l, s, d, p} <> t, name)
    == Bool.pick(Maybe<&2, Outline.Item>, Bool.and(Bool.not(Outline.is_import(k)), String.eq(nm, name)),
      Some{Outline.Item{k, nm, l, s, d, p}}, Outline.find(t, name)) : Maybe<&2, Outline.Item>}

# LAW: the path behind an alias is that of the first import with that name
law import_path_first_alias:
  for k: Outline.ItemKind
  for nm: String
  for l: U32
  for s: String
  for d: String
  for p: String
  for t: List<&2, Outline.Item>
  for +alias: String
  {Outline.import_path(Outline.Item{k, nm, l, s, d, p} <> t, alias)
    == Bool.pick(Maybe<&2, String>, Bool.and(Outline.is_import(k), String.eq(nm, alias)), Some{p},
      Outline.import_path(t, alias)) : Maybe<&2, String>}

# LAW: a name is among some names when it is the first of them or among the
# rest
law has_first_or_rest:
  for h: String
  for t: List<&2, String>
  for +name: String
  {Outline.has(h <> t, name) == Bool.or(String.eq(h, name), Outline.has(t, name)) : Bool}

# LAW: a name is among a lone name exactly when it is that name, so it is
# among none of no names
law has_one_name:
  for +h: String
  for +name: String
  {Outline.has(h <> Nil{}, name) == String.eq(h, name) : Bool}

# LAW: completing a prefix takes an item when it is not an import, its name
# starts with the prefix, and no item before it had that name; the item is
# offered under the qualifier, and its name is remembered
law starting_takes_first_of_each_name:
  for +k: Outline.ItemKind
  for +nm: String
  for l: U32
  for s: String
  for d: String
  for p: String
  for t: List<&2, Outline.Item>
  for +prefix: String
  for +qual: String
  for +seen: List<&2, String>
  {Outline.starting.go(Outline.Item{k, nm, l, s, d, p} <> t, prefix, qual, seen)
    == Bool.pick(List<&2, Outline.Item>,
      Bool.and(Bool.and(Bool.not(Outline.is_import(k)), String.starts_with(nm, prefix)),
        Bool.not(Outline.has(seen, nm))),
      Outline.Item{k, qual ++ nm, l, s, d, p} <> Outline.starting.go(t, prefix, qual, nm <> seen),
      Outline.starting.go(t, prefix, qual, seen)) : List<&2, Outline.Item>}

# LAW: completing an alias takes an import whose name starts with the prefix
# and differs from its path
law aliases_take_named_imports:
  for +k: Outline.ItemKind
  for +nm: String
  for l: U32
  for s: String
  for d: String
  for +p: String
  for t: List<&2, Outline.Item>
  for +prefix: String
  {Outline.aliases(Outline.Item{k, nm, l, s, d, p} <> t, prefix)
    == Bool.pick(List<&2, Outline.Item>,
      Bool.and(Bool.and(Outline.is_import(k), String.starts_with(nm, prefix)), Bool.not(String.eq(nm, p))),
      Outline.Item{k, nm, l, s, d, p} <> Outline.aliases(t, prefix), Outline.aliases(t, prefix))
    : List<&2, Outline.Item>}

# LAW: a text starts with a capital when its first char is one
law starts_upper_first_char:
  for c: Char
  for t: List<&2, Char>
  {Outline.starts_upper.of(c <> t) == Char.is_upper(c) : Bool}

# LAW: no chars start with no capital
law starts_upper_needs_a_char:
  for cs: List<&2, Char>
  for e: {List.is_empty(&2, Char, cs) == True{} : Bool}
  {Outline.starts_upper.of(cs) == False{} : Bool}

# LAW: a header line ends in `:` when its last token that is not a space or a
# comment is one: each such token decides afresh, and a space or a comment
# keeps what was decided
law ends_colon_last_significant:
  for +kk: Lex.TokKind
  for tx: String
  for ln: U32
  for cl: U32
  for t: List<&2, Lex.Tok>
  for prev: Bool
  {Outline.ends_colon.go(Lex.Tok{kk, tx, ln, cl} <> t, prev)
    == Outline.ends_colon.go(t, Bool.pick(Bool, Lex.significant(kk), Outline.ends_colon.is(kk), prev)) : Bool}

# LAW: with no token left, what was decided stands
law ends_colon_stands:
  for prev: Bool
  {Outline.ends_colon.go(Nil{}, prev) == prev : Bool}

# LAW: a line that holds no such token does not end in `:`
law ends_colon_of_line:
  for ss: String
  {Outline.ends_colon(ss) == Outline.ends_colon.go(Lex.tokens(ss), False{}) : Bool}
