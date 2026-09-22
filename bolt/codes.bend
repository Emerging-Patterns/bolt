# bolt/codes: the stable id of every rule. A bolt.bend still names the slug
# (`wrap`); a diagnostic shows the code (`S003`) and, in an editor, the
# source `bolt(group:slug)`. Numbers are assigned once, in the group order
# of bolt/README.md: do not renumber a rule.
import Base
import ../lazy/lazy.bend as Lazy

# one rule: the slug bolt.bend names, its code, its group
type Entry is Data:
  Entry{slug: String, id: String, grp: String}

# every rule, in group order
def table() -> List<&2, Entry>:
  [
    Entry{"shadow", "C001", "correctness"},
    Entry{"hole", "C002", "correctness"},
    Entry{"pick", "C003", "correctness"},
    Entry{"put", "C004", "correctness"},
    Entry{"arms", "C005", "correctness"},
    Entry{"escape", "C006", "correctness"},
    Entry{"twice", "C007", "correctness"},
    Entry{"strings", "C008", "correctness"},
    Entry{"chars", "C009", "correctness"},
    Entry{"foreign", "C010", "correctness"},
    Entry{"unused", "U001", "suspicious"},
    Entry{"strict", "U002", "suspicious"},
    Entry{"eager", "U003", "suspicious"},
    Entry{"concat", "U004", "suspicious"},
    Entry{"nat", "U005", "suspicious"},
    Entry{"fuel", "U006", "suspicious"},
    Entry{"index", "U007", "suspicious"},
    Entry{"doc", "S001", "style"},
    Entry{"space", "S002", "style"},
    Entry{"wrap", "S003", "style"},
    Entry{"param", "S004", "style"},
    Entry{"law", "L001", "laws"},
    Entry{"closed", "L002", "laws"},
    Entry{"unsafe", "L003", "laws"},
    Entry{"tail", "P001", "pedantic"}]

# this row is the slug
def find.same(+row: Entry, +slug: String) -> Bool:
  Entry{+s, _id, _grp} = row
  String.eq(s, slug)

# the row for a slug
def find(rows: List<&2, Entry>, +slug: String) -> Maybe<&2, Entry>:
  match rows:
    case Nil{}:
      None{}
    case Con{+row, rest}:
      Lazy.stop(Maybe<&2, Entry>, find.same(row, slug), Some{row}, _u => find(rest, slug))

# the stable code; the slug itself when it is not a rule
def code.at(mm: Maybe<&2, Entry>, +slug: String) -> String:
  match mm:
    case None{}:
      slug
    case Some{Entry{_s, +id, _grp}}:
      id

# the stable code; the slug itself when it is not a rule
def code(+slug: String) -> String:
  code.at(find(table(), slug), slug)

# the group; empty when the slug is not a rule
def group.at(mm: Maybe<&2, Entry>) -> String:
  match mm:
    case None{}:
      ""
    case Some{Entry{_s, _id, +grp}}:
      grp

# the group; empty when the slug is not a rule
def group(+slug: String) -> String:
  group.at(find(table(), slug))

# `bolt(group:slug)`; `bolt` when the slug is not a rule
def source.at(mm: Maybe<&2, Entry>) -> String:
  match mm:
    case None{}:
      "bolt"
    case Some{Entry{+s, _id, +grp}}:
      "bolt(" ++ grp ++ ":" ++ s ++ ")"

# `bolt(group:slug)`; `bolt` when the slug is not a rule
def source(+slug: String) -> String:
  source.at(find(table(), slug))

# one rule as `slug code group`
def listed.row(+ee: Entry) -> String:
  Entry{+slug, +id, +grp} = ee
  slug ++ " " ++ id ++ " " ++ grp

# every rule as `slug code group`, one a line
def listed.go(rows: List<&2, Entry>) -> String:
  match rows:
    case Nil{}:
      ""
    case Con{+ee, Nil{}}:
      listed.row(ee)
    case Con{+ee, rest}:
      listed.row(ee) ++ "\n" ++ listed.go(rest)

# every rule as `slug code group`, one a line
def listed() -> String:
  listed.go(table())
