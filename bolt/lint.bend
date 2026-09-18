# bolt/lint: `bolt` itself: every rule over the files named in BOLT_FILES
# (one a line; the bolt script fills it from its arguments, as a native Bend
# binary takes no arguments of its own). The per-file rules run on each
# file, the project rules on the set; each finding is graded by the
# bolt.bend nearest its file (bolt/config.bend), and a bolt.bend is read,
# never linted. Prints the findings, then the counts; the script exits 1
# when there were errors.
import Base
import ./finding.bend as F
import ./file.bend as File
import ./rules.bend as Rules
import ./config.bend as Config
import ./lsp/files/service.bend as Files
import ./lsp/files/disk.bend as Disk
import ./args.bend as Args

# a path and what was read at it
type Read is Data:
  Read{path: String, text: Maybe<&2, String>}

# every path read
def read_all(~fs: Files.Files, paths: List<&2, String>) -> IO(List<&2, Read>):
  match paths:
    case Nil{}:
      IO.pure(List<&2, Read>, [])
    case Con{+path, rest}:
      do IO<List<&2, Read>>:
        r : Maybe<&2, String> <- Files.read(fs, path)
        more : List<&2, Read> <- read_all(~fs, rest)
        return Read{path, r} <> more

# a file's findings from the per-file rules; unreadable, one finding
def lint.text(+path: String, r: Maybe<&2, String>) -> List<&2, F.Finding>:
  match r:
    case None{}:
      [F.Finding{path, 0, 0, 0, "read", "cannot read this file"}]
    case Some{text}:
      Rules.all(path, text)

# every file's findings from the per-file rules
def per_file(rs: List<&2, Read>) -> List<&2, F.Finding>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{Read{path, r}, rest}:
      List.concat(&2, F.Finding, [lint.text(path, r), per_file(rest)])

# the files that were read, for the project rules
def files_of(rs: List<&2, Read>) -> List<&2, File.File>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{Read{path, None{}}, rest}:
      files_of(rest)
    case Con{Read{path, Some{text}}, rest}:
      File.File{path, text} <> files_of(rest)

# a finding graded by the config nearest its file
def grade(~fs: Files.Files, f: F.Finding) -> IO(List<&2, F.Graded>):
  F.Finding{+path, line, col, len, rule, msg} = f
  do IO<List<&2, F.Graded>>:
    rs : List<&2, Maybe<&2, String>> <- Files.read_all(~fs, Config.candidates(64n, Config.dir_of(path)))
    return Rules.graded(Config.nearest(rs), [F.Finding{path, line, col, len, rule, msg}])

# every finding graded
def grade_all(~fs: Files.Files, fs1: List<&2, F.Finding>) -> IO(List<&2, F.Graded>):
  match fs1:
    case Nil{}:
      IO.pure(List<&2, F.Graded>, [])
    case Con{f, rest}:
      do IO<List<&2, F.Graded>>:
        g : List<&2, F.Graded> <- grade(~fs, f)
        more : List<&2, F.Graded> <- grade_all(~fs, rest)
        return List.append(&2, F.Graded, g, more)

# each line printed
def print_all(lines: List<&2, String>) -> IO(Unit):
  match lines:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{l, t}:
      do IO<Unit>:
        IO.print(l)
        print_all(t)

# a bolt.bend is configuration, not source
def is_config(+p: String) -> Bool:
  Bool.or(String.eq(p, "bolt.bend"), String.ends_with(p, "/bolt.bend"))

# the paths that are source
def sources(ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, rest}:
      +more = sources(rest)
      Bool.pick(List<&2, String>, is_config(p), more, p <> more)

# every finding of every rule on the files read
def findings(+rs: List<&2, Read>) -> List<&2, F.Finding>:
  List.concat(&2, F.Finding, [per_file(rs), Rules.project(files_of(rs))])

# how many are errors
def errors(gs: List<&2, F.Graded>) -> U32:
  match gs:
    case Nil{}:
      0
    case Con{F.Graded{l, f}, rest}:
      (Bool.pick(U32, Config.is_error(l), 1, 0) + errors(rest) : U32)

# `1 error`, `2 errors`
def count(+n: U32, +what: String) -> String:
  U32.show(n) ++ " " ++ what ++ Bool.pick(String, U32.is_eq(n, 1), "", "s")

# `clean`, or the counts
def summary(+n: U32, +e: U32) -> String:
  Bool.pick(String, U32.is_eq(n, 0), "clean", count(e, "error") ++ ", " ++ count((n - e : U32), "warning"))

# every graded finding as a line
def show_all(gs: List<&2, F.Graded>) -> List<&2, String>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{g, rest}:
      F.show_graded(g) <> show_all(rest)

# the linter, over the files in BOLT_FILES
def run() -> IO(Unit):
  do IO<Unit>:
    paths : List<&2, String> <- Args.files()
    rs : List<&2, Read> <- read_all(~Disk.new(), sources(paths))
    +gs : List<&2, F.Graded> <- grade_all(~Disk.new(), findings(rs))
    print_all(show_all(gs))
    IO.print(summary(U32.from_nat(List.length(&2, F.Graded, gs)), errors(gs)))
