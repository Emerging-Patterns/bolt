# checker/names: pure. The names bend gives the items of the file it
# checks, so a report's Location can be told apart as this file's or an
# import's (report.bend's mine). bend keys a def by its name, and a def
# whose name opens with an import alias (`def Laws.x` filling a law of
# `./LAWS.bend`) by that import's namespace: its path, `./` and `.bend`
# dropped (`LAWS.x`). A def of an import beside the file is keyed the same
# way (`m.g`), which is why the file's own keys are needed at all.
import Base
import ../../syntax/outline.bend as Outline
import ../../lazy/lazy.bend as Lazy

# a path without its leading `./`s
def ns.lead(s: String) -> String:
  match s:
    case SCon{'.', SCon{'/', t}}:
      ns.lead(t)
    case other:
      other

# an import's namespace: its path, without a leading `./` or its `.bend`
def ns(path: String) -> String:
  +p = ns.lead(path)
  Bool.pick(String, String.ends_with(p, ".bend"), String.take(p, Nat.sub(String.length(p), 5n)), p)

# the key of a name that opens with `head.`: through the import aliased head
# when there is one, else the name as written
def key.of(alias: Maybe<&2, String>, +name: String, +rest: String) -> String:
  match alias:
    case None{}:
      name
    case Some{path}:
      ns(path) ++ "." ++ rest

# an item's key, among the file's items
def key.parts(items: List<&2, Outline.Item>, +name: String, parts: List<&2, String>) -> String:
  match parts:
    case Con{+head, Con{r, more}}:
      key.of(Outline.import_path(items, head), name, String.join(r <> more, "."))
    case other:
      name

# an item's key: bend's name for it
def key(items: List<&2, Outline.Item>, +name: String) -> String:
  key.parts(items, name, String.split(name, '.'))

# the keys of the items, imports aside, onto acc (in no particular order)
def keys(its: List<&2, Outline.Item>, +items: List<&2, Outline.Item>, +acc: List<&2, String>) -> List<&2, String>:
  match its:
    case Nil{}:
      acc
    case Con{Outline.Item{+k, +n, _line, _sig, _doc, _path}, rest}:
      keys(rest, items, Lazy.stop(List<&2, String>, Outline.is_import(k), acc, _u => key(items, n) <> acc))

# the names bend gives a file's items, when its text could be read
def of(m: Maybe<&2, String>) -> Maybe<&2, List<&2, String>>:
  match m:
    case None{}:
      None{}
    case Some{text}:
      +items = Outline.items(text)
      Some{keys(items, items, [])}
