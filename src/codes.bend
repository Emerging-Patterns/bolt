# src/codes: the stable id of every rule. A bolt.bend still names the slug
# (`wrap`); a diagnostic shows the code (`S003`) and, in an editor, the
# source `bolt(group:slug)`. Numbers are assigned once, in the group order
# of src/README.md: do not renumber a rule, and do not reuse a retired code
# (L004 was `quantify`, now `closed` itself; C001 was `shadow` and U005 was
# `nat`, whose failures bend 2.0.25 no longer has; C007 was `twice`, a list
# pattern opening with one literal twice, on which the checker hung through
# bend 2.0.28 and does not from 2.0.38, the oldest bend bolt runs on; U014
# was `argv`, retired before its first release, since every reader already
# drops the program; S004 was `param`, a two-character minimum on parameter
# names, which writers met by doubling the letter: `reach` (S008) took its
# place;
# U008 `table`, U009 `hoist`, U010 `ring`, U012 `unit` and U013 `scan` were
# retired for want of real hits, and L003 `unsafe` since bend 2.0.32 reports
# an unsafe def a proof reaches itself). A code names the rule, not its
# group: a rule that moves keeps its code (`strings` is `perf`; `chars`,
# `foreign` and the cost rules `fuel`, `index`, `strict` and `rewalk` are
# `pedantic`).
#
# No law can say this, since it is about versions: a released code is never
# renumbered or reused, which review of this table keeps.
import Base
import ./lazy/lazy.bend as Lazy

# one rule: the slug bolt.bend names, its code, its group
type Entry is Data:
  Entry{slug: String, id: String, grp: String}

# every rule, in group order
def table() -> List<&2, Entry>:
  [
    Entry{"hole", "C002", "correctness"},
    Entry{"pick", "C003", "correctness"},
    Entry{"put", "C004", "correctness"},
    Entry{"arms", "C005", "correctness"},
    Entry{"escape", "C006", "correctness"},
    Entry{"setting", "C011", "correctness"},
    Entry{"unused", "U001", "suspicious"},
    Entry{"eager", "U003", "suspicious"},
    Entry{"concat", "U004", "suspicious"},
    Entry{"thunk", "U015", "suspicious"},
    Entry{"fromrev", "U016", "suspicious"},
    Entry{"prefix", "U017", "suspicious"},
    Entry{"empty", "U018", "suspicious"},
    Entry{"idle", "U019", "suspicious"},
    Entry{"strings", "C008", "perf"},
    Entry{"doc", "S001", "style"},
    Entry{"space", "S002", "style"},
    Entry{"wrap", "S003", "style"},
    Entry{"noqa", "S005", "style"},
    Entry{"transcong", "S006", "style"},
    Entry{"blank", "S007", "style"},
    Entry{"reach", "S008", "style"},
    Entry{"arity", "S009", "style"},
    Entry{"length", "S010", "style"},
    Entry{"depth", "S011", "style"},
    Entry{"coverage", "L001", "laws"},
    Entry{"closed", "L002", "laws"},
    Entry{"chars", "C009", "pedantic"},
    Entry{"foreign", "C010", "pedantic"},
    Entry{"strict", "U002", "pedantic"},
    Entry{"fuel", "U006", "pedantic"},
    Entry{"index", "U007", "pedantic"},
    Entry{"rewalk", "U011", "pedantic"},
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
def code.at(m: Maybe<&2, Entry>, +slug: String) -> String:
  match m:
    case None{}:
      slug
    case Some{Entry{_s, +id, _grp}}:
      id

# the stable code; the slug itself when it is not a rule
def code(+slug: String) -> String:
  code.at(find(table(), slug), slug)

# the group; empty when the slug is not a rule
def group.at(m: Maybe<&2, Entry>) -> String:
  match m:
    case None{}:
      ""
    case Some{Entry{_s, _id, +grp}}:
      grp

# the group; empty when the slug is not a rule
def group(+slug: String) -> String:
  group.at(find(table(), slug))

# `bolt(group:slug)`; `bolt` when the slug is not a rule
def source.at(m: Maybe<&2, Entry>) -> String:
  match m:
    case None{}:
      "bolt"
    case Some{Entry{+s, _id, +grp}}:
      "bolt(" ++ grp ++ ":" ++ s ++ ")"

# `bolt(group:slug)`; `bolt` when the slug is not a rule
def source(+slug: String) -> String:
  source.at(find(table(), slug))
