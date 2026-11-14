# src/fmt/plan: what `bolt fmt` does, decided from a World of answers
# (src/lint/world.bend). Pure: it reads no file and writes none. The files
# are the ones `bolt` would lint, the files named or every `.bend` file
# under the working directory (src/lint/plan.bend's `inputs`; a bolt.bend is
# not among them), and the World is filled by the same questions the lint
# asks. For each file the World read, formatting (src/fmt.bend) either
# leaves its text as it is or gives another; a file that changes is an edit,
# its path and its new text. `bolt fmt` plans every edit and prints
# `formatted <path>` for each; `bolt fmt --check` plans none, prints
# `would format <path>` for each, and exits 1 when there is one. A path the
# World could not read is `cannot read <path>` and exit 1 either way. With
# nothing to say the one line is `clean`.
import Base
import ../fmt.bend as Fmt
import ../lint/world.bend as W
import ../lint/plan.bend as Lint

# a file to write: its path and its new text
type Edit is Data:
  Edit{path: String, text: String}

# what the run does: the files to write, the lines to print, the exit status
type Plan is Data:
  Plan{edits: List<&2, Edit>, lines: List<&2, String>, exit: U32}

# a file's edit when formatting changes its text, before the rest
def edit(same: Bool, path: String, text: String, more: List<&2, Edit>) -> List<&2, Edit>:
  match same:
    case True{}:
      more
    case False{}:
      Edit{path, text} <> more

# one file's edit, if formatting changes it; a path with no text has none
def edits.one(path: String, m: Maybe<&2, String>, more: List<&2, Edit>) -> List<&2, Edit>:
  match m:
    case None{}:
      more
    case Some{+text}:
      +new = Fmt.text(text)
      edit(String.eq(new, text), path, new, more)

# every file formatting changes, in order, each with its new text
def edits(gs: List<&2, Lint.Got>) -> List<&2, Edit>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{Lint.Got{path, m}, rest}:
      edits.one(path, m, edits(rest))

# the paths the World could not read, in order
def unread(gs: List<&2, Lint.Got>) -> List<&2, String>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{Lint.Got{path, None{}}, rest}:
      path <> unread(rest)
    case Con{Lint.Got{_path, Some{_text}}, rest}:
      unread(rest)

# a line for each path, the word before it
def said(+word: String, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, rest}:
      (word ++ " " ++ p) <> said(word, rest)

# the paths of the edits, in order
def paths(es: List<&2, Edit>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Edit{path, _text}, rest}:
      path <> paths(rest)

# what is said of the files that change
def word(check: Bool) -> String:
  match check:
    case True{}:
      "would format"
    case False{}:
      "formatted"

# the lines, or `clean` when there are none
def lines.or(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      ["clean"]
    case Con{h, t}:
      h <> t

# 1 when the list holds anything
def some(-A: Data, xs: List<&2, A>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{_h, _t}:
      1

# the exit status: 1 when a path could not be read, and, when only
# checking, when a file would change
def exit(check: Bool, +es: List<&2, Edit>, bad: List<&2, String>) -> U32:
  match check:
    case True{}:
      U32.max(some(Edit, es), some(String, bad))
    case False{}:
      some(String, bad)

# the edits a run writes: none when it only checks
def written(check: Bool, es: List<&2, Edit>) -> List<&2, Edit>:
  match check:
    case True{}:
      Nil{}
    case False{}:
      es

# the plan over the files the World answered for
def plan.at(+check: Bool, +gs: List<&2, Lint.Got>) -> Plan:
  +es = edits(gs)
  +bad = unread(gs)
  Plan{written(check, es),
    lines.or(List.append(&2, String, said("cannot read", bad), said(word(check), paths(es)))),
    exit(check, es, bad)}

# what `bolt fmt` does in a World: check says whether it only checks
def plan(check: Bool, +world: W.World) -> Plan:
  plan.at(check, Lint.gots(Lint.inputs(world), world))
