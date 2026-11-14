# The code table maps each rule slug to exactly one code and each code to
# exactly one slug.
import Base
import ../src/codes.bend as Codes
import ../src/lazy/lazy.bend as Lazy

# The code table and the printed line. The table is finite, so
# its laws quantify over every index into it: the row there, looked up again
# by its slug and by its code, is the same row.

# the row at an index, looked up again by its slug; none stays none
def by_slug(m: Maybe<&2, Codes.Entry>) -> Maybe<&2, Codes.Entry>:
  match m:
    case None{}:
      None{}
    case Some{Codes.Entry{+s, _id, _grp}}:
      Codes.find(Codes.table(), s)

# this row carries the code
def by_code.same(+row: Codes.Entry, +id: String) -> Bool:
  Codes.Entry{_s, +rid, _grp} = row
  String.eq(rid, id)

# the first row with the code
def by_code(rows: List<&2, Codes.Entry>, +id: String) -> Maybe<&2, Codes.Entry>:
  match rows:
    case Nil{}:
      None{}
    case Con{+row, rest}:
      Lazy.stop(Maybe<&2, Codes.Entry>, by_code.same(row, id), Some{row}, _u => by_code(rest, id))

# the row at an index, looked up again by its code; none stays none
def code_back(m: Maybe<&2, Codes.Entry>) -> Maybe<&2, Codes.Entry>:
  match m:
    case None{}:
      None{}
    case Some{Codes.Entry{_s, +id, _grp}}:
      by_code(Codes.table(), id)

# LAW: every row of the code table is the row its own slug finds, so no slug
# is listed twice and `code`, `group` and `source` read each rule's own row
law slug_finds_row:
  for +n: Nat
  {by_slug(List.get(&2, Codes.Entry, Codes.table(), n)) == List.get(&2, Codes.Entry, Codes.table(), n)
    : Maybe<&2, Codes.Entry>}

# LAW: every row of the code table is the row its own code finds, so no code
# is listed twice: with slug_finds_row, slugs and codes are one-to-one
law code_finds_row:
  for +n: Nat
  {code_back(List.get(&2, Codes.Entry, Codes.table(), n)) == List.get(&2, Codes.Entry, Codes.table(), n)
    : Maybe<&2, Codes.Entry>}
