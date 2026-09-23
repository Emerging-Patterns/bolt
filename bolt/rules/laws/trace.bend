# rule trace (project-wide, opt-in): SPEC.md and the laws agree. SPEC.md,
# read from the directory bolt runs in, lists requirements in tables whose
# header is exactly `| ID | Requirement | Level | Status | Law |`, and trust
# rows in tables headed `| ID | Assumption | Why it is trusted |`. An ID is
# uppercase letters and digits in two or more segments joined by `-`
# (`BOLT-CFG-1`); a law proves one when a line of its comment block is exactly
# that ID (`# BOLT-CFG-1`). The findings: a row that is not a well-formed
# requirement; an ID listed twice; a Proved row with status proved whose Law
# cell names no law, or a law that is missing, has no `for`/`exs` binder, or
# lacks the tag; a Trusted row with no trust row; and a tag naming an ID
# SPEC.md does not list as Proved and proved. A Law entry is
# `<path> <law>`, the path relative to SPEC.md, entries joined by `; `. Only
# a bolt.bend that names the rule turns it on (bolt/config.bend). It runs
# only when bolt lints the whole tree, never over files named on the line.
import Base
import ../../finding.bend as F
import ../digest.bend as Digest
import ../imports.bend as Imports
import ../../../lazy/lazy.bend as Lazy

# reading SPEC.md
# ---------------

# one requirement row: its ID, level and status, the Law cell's entries, and
# its line (0-based)
type Row is Data:
  Row{id: String, level: String, status: String, laws: List<&2, String>, line: U32}

# an ID, or a reason, at a line
type Mark is Data:
  Mark{id: String, line: U32}

# which table the lines are in; Head is the header row, whose `| :-- |` line
# comes next
type Mode is Data:
  Out{}
  ReqHead{}
  Reqs{}
  TrustHead{}
  Trusts{}

# what SPEC.md says: the requirement rows, the trust rows, the rows that are
# not well formed (why, where), each list in reverse file order while read
type Spec is Data:
  Spec{mode: Mode, reqs: List<&2, Row>, trust: List<&2, Mark>, bad: List<&2, Mark>}

# the requirement table's header
def req_head() -> String:
  "| ID | Requirement | Level | Status | Law |"

# the trust table's header
def trust_head() -> String:
  "| ID | Assumption | Why it is trusted |"

# a cell's text, spaces trimmed
def trim(+ss: String) -> String:
  String.trim(ss)

# the cells of a table line, split at every `|` not escaped as `\|`
def cells.go(cs: List<&2, Char>, cur: List<&2, Char>, acc: List<&2, String>) -> List<&2, String>:
  match cs:
    case Nil{}:
      List.reverse(&2, String, String.from_list(List.reverse(&2, Char, cur)) <> acc)
    case Con{'\\', Con{'|', t}}:
      cells.go(t, '|' <> ('\\' <> cur), acc)
    case Con{'|', t}:
      cells.go(t, [], trim(String.from_list(List.reverse(&2, Char, cur))) <> acc)
    case Con{c, t}:
      cells.go(t, c <> cur, acc)

# the cells between a line's outer bars
def cells(+line: String) -> List<&2, String>:
  +all = cells.go(String.to_list(String.trim(line)), [], [])
  List.take(&2, String, List.drop(&2, String, all, 1n), Nat.sub(List.length(&2, String, all), 2n))

# the i-th cell, or empty
def cell(+cs: List<&2, String>, ii: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, cs, ii), "")

def entries.go(ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{+s, rest}:
      +more = entries.go(rest)
      Bool.pick(List<&2, String>, String.is_empty(trim(s)), more, trim(s) <> more)

# a Law cell's entries
def entries(ss: String) -> List<&2, String>:
  entries.go(String.split(ss, ';'))

# a requirement row onto the spec, or a malformed one
def add_req(+line: String, +nn: U32, st: Spec) -> Spec:
  Spec{+mode, +reqs, +trust, +bad} = st
  +cs = cells(line)
  Lazy.stop(Spec, Bool.not(Nat.is_eq(List.length(&2, String, cs), 5n)),
    Spec{mode, reqs, trust, Mark{"a requirement row has five cells", nn} <> bad},
    _u => Spec{mode, Row{cell(cs, 0n), cell(cs, 2n), cell(cs, 3n), entries(cell(cs, 4n)), nn} <> reqs, trust, bad})

# a trust row onto the spec, or a malformed one
def add_trust(+line: String, +nn: U32, st: Spec) -> Spec:
  Spec{+mode, +reqs, +trust, +bad} = st
  +cs = cells(line)
  Bool.pick(Spec, Nat.is_eq(List.length(&2, String, cs), 3n),
    Spec{mode, reqs, Mark{cell(cs, 0n), nn} <> trust, bad},
    Spec{mode, reqs, trust, Mark{"a trust row has three cells", nn} <> bad})

# the spec in another mode
def moved(st: Spec, mm: Mode) -> Spec:
  Spec{mode, reqs, trust, bad} = st
  Spec{mm, reqs, trust, bad}

# a line inside a table: the header's `| :-- |` line, a row, or the end
def in_table(mode: Mode, +line: String, +nn: U32, st: Spec) -> Spec:
  match mode:
    case Out{}:
      st
    case ReqHead{}:
      moved(st, Reqs{})
    case Reqs{}:
      add_req(line, nn, st)
    case TrustHead{}:
      moved(st, Trusts{})
    case Trusts{}:
      add_trust(line, nn, st)

# the mode a spec is in
def mode_of(st: Spec) -> Mode:
  Spec{mode, reqs, trust, bad} = st
  mode

# one line of SPEC.md onto what it says
def step(+line: String, +nn: U32, +st: Spec) -> Spec:
  +tt = String.trim(line)
  Bool.pick(Spec, String.eq(tt, req_head()), moved(st, ReqHead{}),
    Bool.pick(Spec, String.eq(tt, trust_head()), moved(st, TrustHead{}),
      Lazy.stop(Spec, Bool.not(String.starts_with(tt, "|")), moved(st, Out{}),
        _u => in_table(mode_of(st), tt, nn, st))))

def parse.go(ls: List<&2, String>, +nn: U32, st: Spec) -> Spec:
  match ls:
    case Nil{}:
      st
    case Con{l, rest}:
      parse.go(rest, (nn + 1 : U32), step(l, nn, st))

# what SPEC.md's text says
def parse(text: String) -> Spec:
  parse.go(String.lines(text), 0, Spec{Out{}, [], [], []})

# IDs
# ---

# is the char an uppercase letter or a digit?
def id_char(cc: Char) -> Bool:
  +u = Char.to_u32(cc)
  Bool.or(Bool.and(U32.is_ge(u, 65), U32.is_le(u, 90)), Bool.and(U32.is_ge(u, 48), U32.is_le(u, 57)))

# is every char an uppercase letter or a digit?
def id_chars(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, rest}:
      Lazy.and_then(id_char(c), _u => id_chars(rest))

# is every char of the segment an uppercase letter or a digit, and is there one?
def segment(+ss: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(ss)), id_chars(String.to_list(ss)))

# is every segment well formed?
def segments(ss: List<&2, String>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{s, rest}:
      Lazy.and_then(segment(s), _u => segments(rest))

# does the ID start with a letter?
def lettered(+ss: String) -> Bool:
  +c = Maybe.default(&2, Char, List.head(&2, Char, String.to_list(ss)), '0')
  +u = Char.to_u32(c)
  Bool.and(U32.is_ge(u, 65), U32.is_le(u, 90))

# is the text an ID: `[A-Z][A-Z0-9]*(-[A-Z0-9]+)+`?
def is_id(+ss: String) -> Bool:
  +parts = String.split(ss, '-')
  Bool.and(Bool.and(Nat.is_ge(List.length(&2, String, parts), 2n), segments(parts)), lettered(ss))

# checking
# --------

# a finding in SPEC.md
def at(+nn: U32, msg: String) -> F.Finding:
  F.Finding{"SPEC.md", nn, 0, 0, "trace", msg}

# how many rows have this ID
def rows_with(rs: List<&2, Row>, +id: String) -> U32:
  match rs:
    case Nil{}:
      0
    case Con{Row{+i, lv, s, ls, n}, rest}:
      (Bool.pick(U32, String.eq(i, id), 1, 0) + rows_with(rest, id) : U32)

# how many trust rows have this ID
def marks_with(ms: List<&2, Mark>, +id: String) -> U32:
  match ms:
    case Nil{}:
      0
    case Con{Mark{+i, n}, rest}:
      (Bool.pick(U32, String.eq(i, id), 1, 0) + marks_with(rest, id) : U32)

# the digest of a LAWS.bend at a path, when it was read
def laws_file(ds: List<&2, Digest.Digest>, +pp: String) -> Maybe<&2, List<&2, Digest.Law>>:
  match ds:
    case Nil{}:
      None{}
    case Con{Digest.Digest{path, +norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      Lazy.stop(Maybe<&2, List<&2, Digest.Law>>, Bool.and(is_laws, String.eq(norm, pp)), Some{laws},
        _u => laws_file(rest, pp))

# the law of that name
def law_named(ls: List<&2, Digest.Law>, +name: String) -> Maybe<&2, Digest.Law>:
  match ls:
    case Nil{}:
      None{}
    case Con{Digest.Law{+n, l, b, d}, rest}:
      Lazy.stop(Maybe<&2, Digest.Law>, String.eq(n, name), Some{Digest.Law{n, l, b, d}}, _u => law_named(rest, name))

# is the ID one of the doc lines?
def tagged(doc: List<&2, String>, +id: String) -> Bool:
  match doc:
    case Nil{}:
      False{}
    case Con{d, rest}:
      Lazy.or_else(String.eq(trim(d), id), _u => tagged(rest, id))

# what is wrong with the law a proved row names, found or not
def judge_law(mm: Maybe<&2, Digest.Law>, +id: String, +entry: String, +nn: U32) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      [at(nn, id ++ " names " ++ entry ++ ", which is not a law of a LAWS.bend bolt read.")]
    case Some{Digest.Law{n, l, +b, +d}}:
      List.append(&2, F.Finding,
        Bool.pick(List<&2, F.Finding>, b, [], [at(nn, id ++ " names " ++ entry ++ ", which has no for or exs.")]),
        Bool.pick(List<&2, F.Finding>, tagged(d, id), [],
          [at(nn, id ++ " names " ++ entry ++ ", which is not tagged # " ++ id ++ ".")]))

# the law file of an entry, then the law in it
def judge_file(
  mm: Maybe<&2, List<&2, Digest.Law>>,
  +name: String,
  +id: String,
  +entry: String,
  +nn: U32
) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      [at(nn, id ++ " names " ++ entry ++ ", whose file is not a LAWS.bend bolt read.")]
    case Some{ls}:
      judge_law(law_named(ls, name), id, entry, nn)

# one Law entry of a proved row: `<path> <law>`
def judge_entry(+ds: List<&2, Digest.Digest>, +id: String, +entry: String, +nn: U32) -> List<&2, F.Finding>:
  +words = String.split(entry, ' ')
  +path = Imports.norm(cell(words, 0n))
  Lazy.stop(List<&2, F.Finding>, Bool.not(Nat.is_eq(List.length(&2, String, words), 2n)),
    [at(nn, id ++ ": a Law entry is <path> <law>, not " ++ entry ++ ".")],
    _u => judge_file(laws_file(ds, path), cell(words, 1n), id, entry, nn))

# every Law entry of a proved row
def judge_entries(es: List<&2, String>, +ds: List<&2, Digest.Digest>, +id: String, +nn: U32) -> List<&2, F.Finding>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, rest}:
      List.append(&2, F.Finding, judge_entry(ds, id, e, nn), judge_entries(rest, ds, id, nn))

# what is wrong with a row's level, status and Law cell
def shape(+lv: String, +st: String, +ls: List<&2, String>) -> String:
  +proved = Bool.and(String.eq(lv, "Proved"), String.eq(st, "proved"))
  +pending = Bool.and(String.eq(lv, "Proved"), String.eq(st, "pending"))
  +trusted = Bool.and(String.eq(lv, "Trusted"), String.is_empty(st))
  +none = List.is_empty(&2, String, ls)
  Bool.pick(String, Bool.not(Bool.or(Bool.or(proved, pending), trusted)),
    "the level is Proved or Trusted, the status proved or pending for Proved and empty for Trusted",
    Bool.pick(String, Bool.and(proved, none), "a proved row names its law",
      Bool.pick(String, Bool.and(Bool.not(proved), Bool.not(none)), "only a proved row names a law", "")))

# every finding of one requirement row
def judge_row(rr: Row, +sp: Spec, +ds: List<&2, Digest.Digest>) -> List<&2, F.Finding>:
  Row{+id, +lv, +st, +ls, +nn} = rr
  Spec{mode, reqs, trust, bad} = sp
  +why = shape(lv, st, ls)
  List.concat(&2, F.Finding, [
    Bool.pick(List<&2, F.Finding>, is_id(id), [], [at(nn, id ++ " is not an ID: [A-Z][A-Z0-9]*(-[A-Z0-9]+)+.")]),
    Bool.pick(List<&2, F.Finding>, U32.is_gt(rows_with(reqs, id), 1), [at(nn, id ++ " is listed twice.")], []),
    Bool.pick(List<&2, F.Finding>, String.is_empty(why), [], [at(nn, id ++ ": " ++ why ++ ".")]),
    Bool.pick(List<&2, F.Finding>, Bool.and(String.eq(lv, "Trusted"), U32.is_eq(marks_with(trust, id), 0)),
      [at(nn, id ++ " is Trusted and has no row in the trust boundary table.")], []),
    Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(String.eq(lv, "Proved"), String.eq(st, "proved"))), [],
      _u => judge_entries(ls, ds, id, nn))])

# every finding of every requirement row
def judge_rows(rs: List<&2, Row>, +sp: Spec, +ds: List<&2, Digest.Digest>) -> List<&2, F.Finding>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, rest}:
      List.append(&2, F.Finding, judge_row(r, sp, ds), judge_rows(rest, sp, ds))

# is the ID a Proved, proved row?
def proved(rs: List<&2, Row>, +id: String) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{Row{+i, +lv, +st, ls, n}, rest}:
      Lazy.or_else(Bool.and(String.eq(i, id), Bool.and(String.eq(lv, "Proved"), String.eq(st, "proved"))),
        _u => proved(rest, id))

# the tags of a law SPEC.md does not list as proved
def stray(
  doc: List<&2, String>,
  +rs: List<&2, Row>,
  +path: String,
  +name: String,
  +ll: U32
) -> List<&2, F.Finding>:
  match doc:
    case Nil{}:
      Nil{}
    case Con{d, rest}:
      +tt = trim(d)
      +more = stray(rest, rs, path, name, ll)
      Lazy.stop(List<&2, F.Finding>, Lazy.or_else(Bool.not(is_id(tt)), _u => proved(rs, tt)), more,
        _u => F.Finding{path, ll, 0, 0, "trace",
          "Law " ++ name ++ " is tagged " ++ tt ++ ", which SPEC.md does not list as Proved and proved."} <> more)

def strays.laws(ls: List<&2, Digest.Law>, +rs: List<&2, Row>, +path: String) -> List<&2, F.Finding>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Digest.Law{+n, +l, b, d}, rest}:
      List.append(&2, F.Finding, stray(d, rs, path, n, l), strays.laws(rest, rs, path))

# every stray tag of every law file
def strays(ds: List<&2, Digest.Digest>, +rs: List<&2, Row>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{+path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      List.append(&2, F.Finding, strays.laws(laws, rs, path), strays(rest, rs))

# the rows that are not rows
def malformed(ms: List<&2, Mark>) -> List<&2, F.Finding>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{Mark{why, nn}, rest}:
      at(nn, "Not a well-formed row: " ++ why ++ ".") <> malformed(rest)

# every trust row listed twice
def twins(ms: List<&2, Mark>, +all: List<&2, Mark>) -> List<&2, F.Finding>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{Mark{+id, +nn}, rest}:
      +more = twins(rest, all)
      Bool.pick(List<&2, F.Finding>, U32.is_gt(marks_with(all, id), 1), at(nn, id ++ " is listed twice.") <> more, more)

# the rule over a SPEC.md that was read
def check.spec(+sp: Spec, +ds: List<&2, Digest.Digest>) -> List<&2, F.Finding>:
  Spec{mode, +reqs, +trust, bad} = sp
  List.concat(&2, F.Finding, [malformed(List.reverse(&2, Mark, bad)),
    judge_rows(List.reverse(&2, Row, reqs), sp, ds), twins(List.reverse(&2, Mark, trust), trust), strays(ds, reqs)])

# the rule over SPEC.md's text (None when there is none) and every file read
def check.at(mm: Maybe<&2, String>, +ds: List<&2, Digest.Digest>) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      [at(0, "Cannot read SPEC.md.")]
    case Some{text}:
      check.spec(parse(text), ds)

# the rule, when bolt lints the whole tree; a run over the files named on the
# line holds only some of the laws, so it has nothing sound to check
def check(whole: Bool, mm: Maybe<&2, String>, +ds: List<&2, Digest.Digest>) -> List<&2, F.Finding>:
  match whole:
    case True{}:
      check.at(mm, ds)
    case False{}:
      Nil{}
