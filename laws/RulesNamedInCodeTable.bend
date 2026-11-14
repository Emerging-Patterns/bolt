# bolt keeps two tables of its rules. The code table (src/codes.bend) gives
# each rule's slug its code and group: it is what a printed finding, a
# `# noqa` and a bolt.bend setting read. The run table (`on.table` in
# src/rules.bend) says which check runs on each file, and names the
# findings it returns by a slug. A finding whose slug the code table does
# not hold prints with no code, cannot be silenced by its code and is set
# by no group. The two tables name the same rules:
#
# - every check the run table runs is named by a slug of the code table;
# - every slug of the code table is run on each file, except the four
#   rules that read the whole project: `setting` (bolt.bend's own
#   settings), `coverage` (which defs a law reaches), `spare` (which
#   imports a file never names, and what each imported file loads) and
#   `noqa` (stale `# noqa` comments, which needs every other rule's
#   findings first).
import Base
import ../src/codes.bend as Codes
import ../src/rules.bend as Rules

# the rules that read the whole project, and so are not in the run table
def project_rules() -> List<&2, String>:
  ["setting", "coverage", "spare", "noqa"]

# is the slug one of these?
def among(+slug: String, s: List<&2, String>) -> Bool:
  List.contains(~String, ~String.eq, s, slug)

# the slugs of the run table, in order
def run_slugs(rs: List<&2, Rules.Run>) -> List<&2, String>:
  match rs:
    case Nil{}:
      []
    case Con{Rules.Run{slug, _w}, rest}:
      slug <> run_slugs(rest)

# is there a row?
def found(m: Maybe<&2, Codes.Entry>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{_e}:
      True{}

# does the code table hold this slug?
def coded(+slug: String) -> Bool:
  found(Codes.find(Codes.table(), slug))

# a run table entry's slug is in the code table; past the end holds
def run.coded(m: Maybe<&2, Rules.Run>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Rules.Run{+slug, _w}}:
      coded(slug)

# a code table row's slug is run per file or is a project rule; past the
# end holds
def code.run(m: Maybe<&2, Codes.Entry>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Codes.Entry{+slug, _id, _grp}}:
      Bool.or(among(slug, run_slugs(Rules.on.table())), among(slug, project_rules()))

# LAW: every check the run table runs is named by a slug of the code table
law run_slug_coded:
  for +n: Nat
  {run.coded(List.get(&2, Rules.Run, Rules.on.table(), n)) == True{} : Bool}

# LAW: every slug of the code table is run on each file, or is one of the
# four project rules
law code_slug_run:
  for +n: Nat
  {code.run(List.get(&2, Codes.Entry, Codes.table(), n)) == True{} : Bool}

# a project rule is in the run table; past the end does not
def project.run(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+slug}:
      among(slug, run_slugs(Rules.on.table()))

# LAW: no project rule is in the run table, so none runs twice
law project_rule_not_run:
  for +n: Nat
  {project.run(List.get(&2, String, project_rules(), n)) == False{} : Bool}
