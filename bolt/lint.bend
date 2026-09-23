# bolt/lint: `bolt` itself: every rule over the files it was given, or every
# `.bend` file under the current directory when it was given none
# (bolt/glob.bend). The per-file rules run on each file, the project rules on
# the set; each finding is graded by the bolt.bend nearest its file
# (bolt/config.bend), and a bolt.bend is read, never linted. Prints the
# findings, then the counts, and exits 1 when there were errors.
import Base
import ./finding.bend as F
import ./src.bend as Src
import ./rules.bend as Rules
import ./config.bend as Config
import ./lsp/files/service.bend as Files
import ./lsp/files/disk.bend as Disk
import ./glob.bend as Glob
import ./walk/service.bend as Walk
import ./walk/disk.bend as WalkDisk
import ./status.bend as Status

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

# one finding for each file that could not be read
def unread(rs: List<&2, Read>) -> List<&2, F.Finding>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{Read{+path, None{}}, rest}:
      F.Finding{path, 0, 0, 0, "read", "Cannot read this file."} <> unread(rest)
    case Con{Read{path, Some{text}}, rest}:
      unread(rest)

# every file that was read, parsed once for every rule
def srcs_of(rs: List<&2, Read>) -> List<&2, Src.Src>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{Read{path, None{}}, rest}:
      srcs_of(rest)
    case Con{Read{path, Some{text}}, rest}:
      Src.of(path, text) <> srcs_of(rest)

# every file's findings from the per-file rules
def per_file(ss: List<&2, Src.Src>) -> List<&2, F.Finding>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, rest}:
      List.concat(&2, F.Finding, [Rules.on(s), per_file(rest)])

# a finding graded by the config nearest its file
def grade(~fs: Files.Files, ff: F.Finding) -> IO(List<&2, F.Graded>):
  F.Finding{+path, line, col, len, rule, msg} = ff
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
def is_config(+pp: String) -> Bool:
  Bool.or(String.eq(pp, "bolt.bend"), String.ends_with(pp, "/bolt.bend"))

# the paths that are source
def sources(ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, rest}:
      +more = sources(rest)
      Bool.pick(List<&2, String>, is_config(p), more, p <> more)

# every finding of every rule on the files read, and SPEC.md's text
def findings(+rs: List<&2, Read>, spec: Maybe<&2, String>) -> List<&2, F.Finding>:
  +ss = srcs_of(rs)
  List.concat(&2, F.Finding, [unread(rs), per_file(ss), Rules.project(ss, spec)])

# how many are errors
def errors(gs: List<&2, F.Graded>) -> U32:
  match gs:
    case Nil{}:
      0
    case Con{F.Graded{l, f}, rest}:
      +more = errors(rest)
      (Bool.pick(U32, Config.is_error(l), 1, 0) + more : U32)

# `1 error`, `2 errors`
def count(+nn: U32, +what: String) -> String:
  U32.show(nn) ++ " " ++ what ++ Bool.pick(String, U32.is_eq(nn, 1), "", "s")

# `clean`, or the counts
def summary(+nn: U32, +ee: U32) -> String:
  Bool.pick(String, U32.is_eq(nn, 0), "clean", count(ee, "error") ++ ", " ++ count((nn - ee : U32), "warning"))

# every graded finding as a line
def show_all(gs: List<&2, F.Graded>) -> List<&2, String>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{g, rest}:
      F.show_graded(g) <> show_all(rest)

# the files to lint: those given, or the whole tree when none were
def chosen(~ww: Walk.Walk, paths: List<&2, String>) -> IO(List<&2, String>):
  match paths:
    case Nil{}:
      Glob.find(~ww, ".")
    case Con{p, rest}:
      IO.pure(List<&2, String>, p <> rest)

# the linter, over the files given, or the tree below
def run(paths: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    files : List<&2, String> <- chosen(~WalkDisk.new(), paths)
    rs : List<&2, Read> <- read_all(~Disk.new(), sources(files))
    spec : Maybe<&2, String> <- Files.read(Disk.new(), "SPEC.md")
    +gs : List<&2, F.Graded> <- grade_all(~Disk.new(), findings(rs, spec))
    print_all(show_all(gs))
    +e : U32 = errors(gs)
    IO.print(summary(U32.from_nat(List.length(&2, F.Graded, gs)), e))
    Status.stop(U32.is_gt(e, 0))
