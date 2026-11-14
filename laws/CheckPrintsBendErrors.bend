# `bolt check` prints one `path:line:1: error:` line per error bend reports,
# on the line bend marks, then a count; it exits 1 when there is any, and
# treats a failure to run bend as an error.
import Base
import ../src/check.bend as Check
import ../src/lsp/checker/answer.bend as Checker
import ../src/lsp/report.bend as Rep

# The checker. `bolt check` runs bend on each file (trusted in src/lsp/report.bend
# for what bend prints, src/lsp/report.bend for how it is read), and
# Check.out decides, from the diagnostics each file got, every line the
# command prints and its exit code; Check.run only does it (trusted in src/lint.bend).
# The laws below quantify over every list of files and every diagnostics
# each could get, and over a file bend could not be run on: exec tags its
# text (checker/bend.bend's bendcheck.exec; that the tag is honest is
# trusted in src/lint.bend), Checker.answer reads the tag, and a file with no check
# is an error line of its own. "On the line bend marks" is the section after
# these (check_marked): that bend prints the shape it reads is trusted in src/lsp/report.bend.

# the line for an error bend reported at a 0-based line of a file: the
# path, the line counted from 1, column 1, and the message
def chk_line(path: String, d: Rep.Diag) -> String:
  Rep.Diag{line, msg} = d
  path ++ ":" ++ U32.show((line + 1 : U32)) ++ ":1: error: " ++ Check.message(msg)

# one file's error lines, in the order bend reported them, onto more
def chk_file(ds: List<&2, Rep.Diag>, +path: String, more: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      more
    case Con{d, rest}:
      chk_line(path, d) <> chk_file(rest, path, more)

# every file's error lines, file by file in the order given
def chk_lines(runs: List<&2, Check.Run>) -> List<&2, String>:
  match runs:
    case Nil{}:
      []
    case Con{Check.Run{path, ds}, rest}:
      chk_file(ds, path, chk_lines(rest))
    case Con{Check.Failed{path}, rest}:
      (path ++ ":1:1: error: could not run bend") <> chk_lines(rest)

# how many errors bend reported, over every file, and one for each file
# bend could not be run on
def chk_count(runs: List<&2, Check.Run>) -> Nat:
  match runs:
    case Nil{}:
      0n
    case Con{Check.Run{_path, ds}, rest}:
      Nat.add(List.length(&2, Rep.Diag, ds), chk_count(rest))
    case Con{Check.Failed{_path}, rest}:
      1n+chk_count(rest)

# LAW: `bolt check` prints, for each file in turn, one line per error bend
# reported, in bend's order, on the line bend marked, and for a file bend
# could not be run on, `path:1:1: error: could not run bend`
law check_lines:
  for runs: List<&2, Check.Run>
  {Check.lines_of(runs) == chk_lines(runs) : List<&2, String>}

# LAW: there are exactly as many error lines as errors, a file bend could
# not be run on counting as one
law check_one_each:
  for runs: List<&2, Check.Run>
  {List.length(&2, String, Check.lines_of(runs)) == chk_count(runs) : Nat}

# LAW: with no error in any file, `bolt check` prints `clean` alone and
# exits 0
law check_clean:
  for +runs: List<&2, Check.Run>
  for h: {chk_count(runs) == 0n : Nat}
  {Check.out(runs) == Check.Out{["clean"], 0} : Check.Out}

# LAW: with one error, `bolt check` prints its line, then `1 error`, and
# exits 1
law check_one:
  for +runs: List<&2, Check.Run>
  for h: {chk_count(runs) == 1n : Nat}
  {Check.out(runs) == Check.Out{List.append(&2, String, chk_lines(runs), ["1 error, 0 warnings"]), 1} : Check.Out}

# LAW: with more errors, `bolt check` prints their lines, then the count,
# and exits 1
law check_many:
  for +runs: List<&2, Check.Run>
  for +more: Nat
  for h: {chk_count(runs) == 2n+more : Nat}
  {Check.out(runs)
    == Check.Out{List.append(&2, String, chk_lines(runs),
      [U32.show(U32.from_nat(2n+more)) ++ " errors, 0 warnings"]), 1} : Check.Out}

# an Out's exit code
def chk_code(o: Check.Out) -> U32:
  Check.Out{_lines, code} = o
  code

# LAW: a file bend could not be run on is an error: whatever the other files
# got, `bolt check` exits 1
law check_unrun_error:
  for +path: String
  for +runs: List<&2, Check.Run>
  {chk_code(Check.out(Check.Failed{path} <> runs)) == 1 : U32}

# LAW: a file's run is the checker's diagnostics for it
law check_run_of:
  for +path: String
  for ds: List<&2, Rep.Diag>
  {Check.run_of(path, Checker.Checked{ds}) == Check.Run{path, ds} : Check.Run}

# LAW: a checker that could not run bend gives a failed run, never a clean one
law check_run_unrun:
  for +path: String
  {Check.run_of(path, Checker.Unrun{}) == Check.Failed{path} : Check.Run}

# LAW: when bend ran and exited, however it exited, the checker's answer is
# what it printed read as diagnostics, as it was before exec tagged its text,
# placed by the checked file's names
law check_exec_ran:
  for +names: Maybe<&2, List<&2, String>>
  for text: String
  {Checker.answer(names, "r" ++ text) == Checker.Checked{Rep.parse_in(names, text)} : Checker.Answer}

# LAW: when bend could not be run (no pipe, no fork, or exit 127), the answer
# is Unrun, whatever was printed
law check_exec_unrun:
  for -names: Maybe<&2, List<&2, String>>
  for text: String
  {Checker.answer(names, "x" ++ text) == Checker.Unrun{} : Checker.Answer}

# LAW: when a signal killed bend before it reported an error, the answer is
# Unrun, not clean
law check_exec_died:
  for +names: Maybe<&2, List<&2, String>>
  for +text: String
  for h: {Rep.parse_in(names, text) == [] : List<&2, Rep.Diag>}
  {Checker.answer(names, "s" ++ text) == Checker.Unrun{} : Checker.Answer}

# LAW: when a signal killed bend after it reported errors, the answer is
# those errors
law check_exec_died_reported:
  for +names: Maybe<&2, List<&2, String>>
  for +text: String
  for d: Rep.Diag
  for ds: List<&2, Rep.Diag>
  for h: {Rep.parse_in(names, text) == d <> ds : List<&2, Rep.Diag>}
  {Checker.answer(names, "s" ++ text) == Checker.Checked{d <> ds} : Checker.Answer}

# LAW: any other text from exec, the empty text included, is Unrun: text
# with no tag is never read as a clean check
law check_exec_untagged:
  for -names: Maybe<&2, List<&2, String>>
  for +c: Char
  for text: String
  for h: {Bool.or(Char.is_eq(c, 'r'), Char.is_eq(c, 's')) == False{} : Bool}
  {Checker.answer(names, SCon{c, text}) == Checker.Unrun{} : Checker.Answer}

# LAW: a LAWS.bend whose PROOF.bend bend could not be run on is not settled
# clean: its answer is Unrun
law check_proof_unrun:
  for ds: List<&2, Rep.Diag>
  {Checker.proved(Checker.Unrun{}, ds) == Checker.Unrun{} : Checker.Answer}

# The line bend marks (laws/CheckPrintsBendErrors.bend). bend prints an error in one shape
# (trusted in src/lsp/report.bend; err_show in bend 2.0.25): `Error:`, the message lines
# (`- expected : ..` and `- observed : ..`, or `- message  : ..`, then
# `Context:` and its `- name : type` lines), then, when bend knows where the
# error is, `Location:` with the def's name after a space, the excerpt (the
# marked line `n>| code` between a line of context on each side, `n | code`,
# the numbers padded to one width), and, for a bare operator, a two-line
# note. chk.report prints that shape for any list of errors, written apart
# from report.bend, and the laws below read it back through Rep.parse_in. A
# marked line's number is its numeral as Base's U32.read reads it (0 when
# the numeral overflows a U32).
#
# The Location names the def by bend's key for it: its name in the checked
# file (`f`, `m.g` for a def `m.g`), the import's namespace and the name in
# another file (`sub/m.g`, `../m.g`, and `m.g` for `g` in `./m.bend`). So
# whether an error is the checked file's is read against the checked file's
# own keys (checker/names.bend; that they are bend's keys is trusted in src/lsp/report.bend):
# an error the file owns lands on the line bend marks, and one in another
# file, where bend marks no line of this one, falls back to line 1 of the
# checked file, its message headed by the def and file it is in. Without the
# names (the file could not be read), a place holding a path is another
# file's. The laws below hold for every list of names.

# a decimal digit
type chk.Dig is Data:
  ChkD0{}
  ChkD1{}
  ChkD2{}
  ChkD3{}
  ChkD4{}
  ChkD5{}
  ChkD6{}
  ChkD7{}
  ChkD8{}
  ChkD9{}

# a digit as bend prints it
def chk.digit(d: chk.Dig) -> Char:
  match d:
    case ChkD0{}:
      '0'
    case ChkD1{}:
      '1'
    case ChkD2{}:
      '2'
    case ChkD3{}:
      '3'
    case ChkD4{}:
      '4'
    case ChkD5{}:
      '5'
    case ChkD6{}:
      '6'
    case ChkD7{}:
      '7'
    case ChkD8{}:
      '8'
    case ChkD9{}:
      '9'

# a numeral as bend prints it
def chk.num(ds: List<&2, chk.Dig>) -> String:
  match ds:
    case Nil{}:
      SNil{}
    case Con{d, rest}:
      SCon{chk.digit(d), chk.num(rest)}

# spaces, the padding before a line number shorter than the widest
def chk.pad(nn: Nat) -> String:
  match nn:
    case 0n:
      SNil{}
    case 1n+p:
      SCon{' ', chk.pad(p)}

# a source line of an excerpt: its padding, its number's digits, and its code
type chk.Src is Data:
  ChkSrc{pad: Nat, first: chk.Dig, rest: List<&2, chk.Dig>, code: String}

# a source line as bend prints it, sep after the number: `>| ` on the marked
# line, ` | ` on a line of context
def chk.src(s: chk.Src, sep: String) -> String:
  ChkSrc{pad, first, rest, code} = s
  String.append(chk.pad(pad), String.append(chk.num(first <> rest), String.append(sep, code)))

# an excerpt: the marked line, with the line before it and the line after it
# when the file has them
type chk.Span is Data:
  ChkSpan{before: Maybe<&2, chk.Src>, mark: chk.Src, after: Maybe<&2, chk.Src>}

# where bend places an error: the def's name when it has one, and the
# excerpt when it has one
type chk.Where is Data:
  ChkWhere{name: Maybe<&2, String>, span: Maybe<&2, chk.Span>}

# a message line: `- text`, or the `Context:` header
type chk.Part is Data:
  ChkItem{text: String}
  ChkCtx{}

# an error as bend prints it: its message lines, where it is when bend says,
# and whether bend's note on a bare operator follows
type chk.Err is Data:
  ChkErr{parts: List<&2, chk.Part>, at: Maybe<&2, chk.Where>, note: Bool}

# the message lines as bend prints them
def chk.parts(ps: List<&2, chk.Part>) -> List<&2, String>:
  match ps:
    case Nil{}:
      []
    case Con{ChkItem{text}, rest}:
      ("- " ++ text) <> chk.parts(rest)
    case Con{ChkCtx{}, rest}:
      "Context:" <> chk.parts(rest)

# a line of context, when the file has one
def chk.context(m: Maybe<&2, chk.Src>) -> List<&2, String>:
  match m:
    case None{}:
      []
    case Some{s}:
      [chk.src(s, " | ")]

# an excerpt's lines, when there is one
def chk.span(m: Maybe<&2, chk.Span>) -> List<&2, String>:
  match m:
    case None{}:
      []
    case Some{ChkSpan{before, mark, after}}:
      List.append(&2, String, chk.context(before), chk.src(mark, ">| ") <> chk.context(after))

# what follows `Location:`: a space and the def's name, when it has one
def chk.name(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      ""
    case Some{n}:
      " " ++ n

# the Location line and the excerpt, when bend knows where the error is
def chk.where(m: Maybe<&2, chk.Where>) -> List<&2, String>:
  match m:
    case None{}:
      []
    case Some{ChkWhere{name, span}}:
      ("Location:" ++ chk.name(name)) <> chk.span(span)

# bend's note on a bare operator, when it follows
def chk.note(b: Bool) -> List<&2, String>:
  match b:
    case False{}:
      []
    case True{}:
      ["Note: we broke this after launch, sorry. Until 2.0.16 a bare operator meant Nat.",
        "That was a bug: operators demand annotation. Wrap the expression and it'll work again."]

# an error's lines
def chk.lines(e: chk.Err) -> List<&2, String>:
  ChkErr{parts, at, note} = e
  "Error:" <> List.append(&2, String, chk.parts(parts), List.append(&2, String, chk.where(at), chk.note(note)))

# every error's lines, in order
def chk.all(es: List<&2, chk.Err>) -> List<&2, String>:
  match es:
    case Nil{}:
      []
    case Con{e, rest}:
      List.append(&2, String, chk.lines(e), chk.all(rest))

# lines as text, each ended by a newline
def chk.text(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      SNil{}
    case Con{l, rest}:
      String.append(l, SCon{'\n', chk.text(rest)})

# the report bend prints for the errors
def chk.report(es: List<&2, chk.Err>) -> String:
  chk.text(chk.all(es))

# the message lines' texts
def chk.texts(ps: List<&2, chk.Part>) -> List<&2, String>:
  match ps:
    case Nil{}:
      []
    case Con{ChkItem{text}, rest}:
      text <> chk.texts(rest)
    case Con{ChkCtx{}, rest}:
      "Context:" <> chk.texts(rest)

# an error's message lines: its parts, then bend's note when no Location
# came before it
def chk.said(at: Maybe<&2, chk.Where>, ts: List<&2, String>, ns: List<&2, String>) -> List<&2, String>:
  match at:
    case None{}:
      List.append(&2, String, ts, ns)
    case Some{_ww}:
      ts

# the place an error names: its def's name, or nothing
def chk.place(at: Maybe<&2, chk.Where>) -> String:
  match at:
    case None{}:
      ""
    case Some{ChkWhere{name, _span}}:
      Maybe.default(&2, String, name, "")

# the number an excerpt marks, as U32.read reads its numeral: 0 when there
# is no excerpt or the numeral overflows
def chk.marks(m: Maybe<&2, chk.Span>) -> U32:
  match m:
    case None{}:
      0
    case Some{ChkSpan{_before, ChkSrc{_pad, first, rest, _code}, _after}}:
      Maybe.default(&2, U32, U32.read(chk.num(first <> rest)), 0)

# the number an error's excerpt marks, 0 when it has none
def chk.marked(at: Maybe<&2, chk.Where>) -> U32:
  match at:
    case None{}:
      0
    case Some{ChkWhere{_name, span}}:
      chk.marks(span)

# an error's place
def chk.err_at(e: chk.Err) -> Maybe<&2, chk.Where>:
  ChkErr{_parts, at, _note} = e
  at

# an error's message lines
def chk.err_parts(e: chk.Err) -> List<&2, chk.Part>:
  ChkErr{parts, _at, _note} = e
  parts

# a place up to its first `~`: bend names an instance of a template `f` as
# `f~1`
def chk.stem(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      Bool.pick(String, Char.is_eq(h, '~'), SNil{}, SCon{h, chk.stem(t)})

# is the name one of these?
def chk.among(ks: List<&2, String>, +name: String) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{k, rest}:
      Bool.or(String.eq(k, name), chk.among(rest, name))

# is an error at this place the checked file's? With the file's names: when
# the place names nothing or names one of them. Without: when it holds no
# path
def chk.own(names: Maybe<&2, List<&2, String>>, +place: String) -> Bool:
  match names:
    case None{}:
      Bool.not(String.contains(place, "/"))
    case Some{ks}:
      Bool.or(String.is_empty(place), chk.among(ks, chk.stem(place)))

# an error's message lines, as one text
def chk.body(e: chk.Err) -> String:
  ChkErr{parts, +at, note} = e
  String.join(chk.said(at, chk.texts(parts), chk.note(note)), "\n")

# an error's message: its lines, headed by where it is when that is another
# file
def chk.msg(names: Maybe<&2, List<&2, String>>, +e: chk.Err) -> String:
  +place = chk.place(chk.err_at(e))
  +body = chk.body(e)
  Bool.pick(String, chk.own(names, place), body, "in " ++ place ++ ":\n" ++ body)

# the 0-based line an error lands on: the line its excerpt marks, counted
# from 0, in the checked file; line 0 when it marks none, or when it is in
# another file
def chk.row(own: Bool, +v: U32) -> U32:
  Bool.pick(U32, Bool.or(Bool.not(own), U32.is_eq(v, 0)), 0, (v - 1 : U32))

# the diagnostic an error is, by the checked file's names
def chk.diag(+names: Maybe<&2, List<&2, String>>, +e: chk.Err) -> Rep.Diag:
  +at = chk.err_at(e)
  Rep.Diag{chk.row(chk.own(names, chk.place(at)), chk.marked(at)), chk.msg(names, e)}

# the diagnostics the errors are, in order
def chk.diags(es: List<&2, chk.Err>, +names: Maybe<&2, List<&2, String>>) -> List<&2, Rep.Diag>:
  match es:
    case Nil{}:
      []
    case Con{e, rest}:
      chk.diag(names, e) <> chk.diags(rest, names)

# every line of a report is one line: no newline inside it
def chk.flat(ls: List<&2, String>) -> Type:
  match ls:
    case Nil{}:
      Unit
    case Con{l, rest}:
      {String.contains(l, "\n") == False{} : Bool} & chk.flat(rest)

# every message line bend prints says something, and none is bend's update
# nag, which the parser drops wherever it stands
def chk.parts_ok(ps: List<&2, chk.Part>) -> Type:
  match ps:
    case Nil{}:
      Unit
    case Con{ChkItem{+text}, rest}:
      ({String.is_empty(text) == False{} : Bool}
        & {String.contains(text, "is available: run bend update") == False{} : Bool}) & chk.parts_ok(rest)
    case Con{ChkCtx{}, rest}:
      chk.parts_ok(rest)

# a def's name as bend prints one: no leading whitespace
def chk.name_ok(at: Maybe<&2, chk.Where>) -> Type:
  match at:
    case None{}:
      Unit
    case Some{ChkWhere{None{}, _span}}:
      Unit
    case Some{ChkWhere{Some{+n}, _span}}:
      {String.trim_start(n) == n : String}

# errors as bend prints them: message lines kept, names plain, and no
# message that is "no main to run", which bend says of a library, not of an
# error
def chk.fits(es: List<&2, chk.Err>) -> Type:
  match es:
    case Nil{}:
      Unit
    case Con{+e, rest}:
      ((chk.parts_ok(chk.err_parts(e)) & chk.name_ok(chk.err_at(e)))
        & {String.eq(chk.body(e), "no main to run") == False{} : Bool}) & chk.fits(rest)

# LAW: for every list of errors bend could print and every list of the
# checked file's names, the parser reads back one diagnostic per error, in
# order, with its message, on the line its excerpt marks counted from 0 when
# the error is the file's, or on line 0 when bend marked no line or the
# error is in another file
law check_marked:
  for +names: Maybe<&2, List<&2, String>>
  for +es: List<&2, chk.Err>
  for flat: chk.flat(chk.all(es))
  for fits: chk.fits(es)
  {Rep.parse_in(names, chk.report(es)) == chk.diags(es, names) : List<&2, Rep.Diag>}

# the number `bolt check` prints for an error: the number bend marked, or 1
# when bend marked no line or the error is in another file
def chk.shown(own: Bool, +v: U32) -> U32:
  Bool.pick(U32, Bool.or(Bool.not(own), U32.is_eq(v, 0)), 1, v)

# the lines `bolt check` prints for the errors bend reported for a file
def chk.printed(es: List<&2, chk.Err>, +path: String, +names: Maybe<&2, List<&2, String>>) -> List<&2, String>:
  match es:
    case Nil{}:
      []
    case Con{+e, rest}:
      +at = chk.err_at(e)
      (path ++ ":" ++ U32.show(chk.shown(chk.own(names, chk.place(at)), chk.marked(at))) ++ ":1: error: "
        ++ Check.message(chk.msg(names, e))) <> chk.printed(rest, path, names)

# LAW: `bolt check` prints each error bend reported for a file on the line
# bend marked, numbered from 1 as bend numbers it, when the error is the
# file's, and on line 1 when bend marked no line or the error is in another
# file
law check_marked_line:
  for +names: Maybe<&2, List<&2, String>>
  for +path: String
  for +es: List<&2, chk.Err>
  for flat: chk.flat(chk.all(es))
  for fits: chk.fits(es)
  {Check.lines_of([Check.Run{path, Rep.parse_in(names, chk.report(es))}]) == chk.printed(es, path, names)
    : List<&2, String>}

# LAW: an error bend reports in another file, its Location naming no item
# of the checked file (`sub/m.g`, or `m.g` for `g` in `./m.bend`), is
# printed on line 1 of the checked file, the message headed by where it is:
# bend marks no line of the checked file
law check_import_first:
  for +names: Maybe<&2, List<&2, String>>
  for +path: String
  for +parts: List<&2, chk.Part>
  for +name: String
  for +span: Maybe<&2, chk.Span>
  for +note: Bool
  for other: {chk.own(names, name) == False{} : Bool}
  for flat: chk.flat(chk.all([ChkErr{parts, Some{ChkWhere{Some{name}, span}}, note}]))
  for fits: chk.fits([ChkErr{parts, Some{ChkWhere{Some{name}, span}}, note}])
  {Check.lines_of([Check.Run{path,
      Rep.parse_in(names, chk.report([ChkErr{parts, Some{ChkWhere{Some{name}, span}}, note}]))}])
    == [path ++ ":1:1: error: " ++ Check.message("in " ++ name ++ ":\n" ++ String.join(chk.texts(parts), "\n"))]
    : List<&2, String>}

# LAW: an error the checked file owns, its Location naming one of the file's
# items (a def `m.g` of the file included), is printed on the line bend
# marked, numbered as bend numbers it
law check_own_marked:
  for +names: Maybe<&2, List<&2, String>>
  for +path: String
  for +parts: List<&2, chk.Part>
  for +name: String
  for +span: chk.Span
  for +note: Bool
  for own: {chk.own(names, name) == True{} : Bool}
  for some: {U32.is_eq(chk.marks(Some{span}), 0) == False{} : Bool}
  for flat: chk.flat(chk.all([ChkErr{parts, Some{ChkWhere{Some{name}, Some{span}}}, note}]))
  for fits: chk.fits([ChkErr{parts, Some{ChkWhere{Some{name}, Some{span}}}, note}])
  {Check.lines_of([Check.Run{path,
      Rep.parse_in(names, chk.report([ChkErr{parts, Some{ChkWhere{Some{name}, Some{span}}}, note}]))}])
    == [path ++ ":" ++ U32.show(chk.marks(Some{span})) ++ ":1: error: "
      ++ Check.message(String.join(chk.texts(parts), "\n"))]
    : List<&2, String>}

# LAW: a LAWS.bend whose PROOF.bend checks clean has no errors of its own to
# show, whatever bend said of it alone
law proved_clean_shows_none:
  for +pds: List<&2, Rep.Diag>
  for ds: List<&2, Rep.Diag>
  for e: {List.is_empty(&2, Rep.Diag, pds) == True{} : Bool}
  {Checker.proved(Checker.Checked{pds}, ds) == Checker.Checked{[]} : Checker.Answer}

# LAW: one whose PROOF.bend has errors shows the LAWS.bend's own
law proved_failing_shows_its_own:
  for +pds: List<&2, Rep.Diag>
  for +ds: List<&2, Rep.Diag>
  for e: {List.is_empty(&2, Rep.Diag, pds) == False{} : Bool}
  {Checker.proved(Checker.Checked{pds}, ds) == Checker.Checked{ds} : Checker.Answer}

# LAW: each line of a message after its first is printed on a line of its
# own, two spaces in
law rest_lines_indent_each_line:
  for l: String
  for t: List<&2, String>
  {Check.rest_lines(l <> t) == "\n  " ++ l ++ Check.rest_lines(t) : String}
