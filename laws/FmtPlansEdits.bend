# `bolt fmt` writes exactly the files formatting changes, each with its
# formatted text, in the order the run reads them: a file whose formatted
# text is its text gets no edit, one whose text changes gets one edit
# holding the formatted text, and a path the run could not read gets none.
# `bolt fmt --check` writes nothing, whatever it finds, and exits 1 when a
# file would change. A path that could not be read is exit 1 either way, a
# write run with every path read exits 0, and a run with nothing to say
# prints `clean` and exits 0.
#
# What the files are (the ones `bolt` would lint) is
# laws/PlannerAsksEachPathOnce.bend's and its neighbours'; that the
# interpreter writes each edit as planned is trusted in src/fmt/run.bend.
import Base
import ../src/fmt.bend as Fmt
import ../src/fmt/plan.bend as Fp
import ../src/lint/plan.bend as Lint
import ../src/lint/world.bend as W

# the edits of a plan
def edits_of(pl: Fp.Plan) -> List<&2, Fp.Edit>:
  match pl:
    case Fp.Plan{es, _ls, _x}:
      es

# the lines of a plan
def lines_of(pl: Fp.Plan) -> List<&2, String>:
  match pl:
    case Fp.Plan{_es, ls, _x}:
      ls

# the exit status of a plan
def exit_of(pl: Fp.Plan) -> U32:
  match pl:
    case Fp.Plan{_es, _ls, x}:
      x

# LAW: the files a run formats are the ones the World answered for among
# those `bolt` would lint there
law fmt_reads_lint_inputs:
  for check: Bool
  for +world: W.World
  {Fp.plan(check, world) == Fp.plan.at(check, Lint.gots(Lint.inputs(world), world)) : Fp.Plan}

# LAW: `bolt fmt --check` plans no write, whatever the files hold
law fmt_check_writes_nothing:
  for +gs: List<&2, Lint.Got>
  {edits_of(Fp.plan.at(True{}, gs)) == Nil{} : List<&2, Fp.Edit>}

# LAW: `bolt fmt` plans every edit, and only those
law fmt_writes_every_edit:
  for +gs: List<&2, Lint.Got>
  {edits_of(Fp.plan.at(False{}, gs)) == Fp.edits(gs) : List<&2, Fp.Edit>}

# LAW: a file whose formatted text is its text gets no edit
law fmt_same_text_no_edit:
  for path: String
  for +text: String
  for rest: List<&2, Lint.Got>
  for e: {String.eq(Fmt.text(text), text) == True{} : Bool}
  {Fp.edits(Lint.Got{path, Some{text}} <> rest) == Fp.edits(rest) : List<&2, Fp.Edit>}

# LAW: a file formatting changes gets one edit, its path with the formatted
# text, before the edits of the files after it
law fmt_changed_text_one_edit:
  for path: String
  for +text: String
  for rest: List<&2, Lint.Got>
  for e: {String.eq(Fmt.text(text), text) == False{} : Bool}
  {Fp.edits(Lint.Got{path, Some{text}} <> rest) == Fp.Edit{path, Fmt.text(text)} <> Fp.edits(rest)
    : List<&2, Fp.Edit>}

# LAW: a path the run could not read gets no edit
law fmt_unread_no_edit:
  for path: String
  for rest: List<&2, Lint.Got>
  {Fp.edits(Lint.Got{path, None{}} <> rest) == Fp.edits(rest) : List<&2, Fp.Edit>}

# LAW: checking, a file that would change is exit 1, whatever else there is
law fmt_check_fails_on_change:
  for path: String
  for text: String
  for es: List<&2, Fp.Edit>
  for bad: List<&2, String>
  {Fp.exit(True{}, Fp.Edit{path, text} <> es, bad) == 1 : U32}

# LAW: a path that could not be read is exit 1, checking or not
law fmt_unread_fails:
  for check: Bool
  for es: List<&2, Fp.Edit>
  for path: String
  for bad: List<&2, String>
  {Fp.exit(check, es, path <> bad) == 1 : U32}

# LAW: writing, with every path read, is exit 0 however many files changed
law fmt_write_succeeds:
  for es: List<&2, Fp.Edit>
  {Fp.exit(False{}, es, Nil{}) == 0 : U32}

# LAW: a run with no file to change and no path unread prints `clean` and
# exits 0, checking or not
law fmt_clean:
  for +check: Bool
  for +gs: List<&2, Lint.Got>
  for e1: {Fp.edits(gs) == Nil{} : List<&2, Fp.Edit>}
  for e2: {Fp.unread(gs) == Nil{} : List<&2, String>}
  {Fp.plan.at(check, gs) == Fp.Plan{Nil{}, ["clean"], 0} : Fp.Plan}
