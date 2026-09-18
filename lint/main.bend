# bend-lint: runs every rule over the files named in BEND_LINT_FILES (one a
# line; the bend-lint script fills it from its arguments, as a native Bend
# binary takes no arguments of its own), except the rules named in
# BEND_LINT_SKIP (comma-separated). The per-file rules run on each file, the
# project rules on the set. Prints the findings, then a count.
import Base
import ./finding.bend as F
import ./file.bend as File
import ./rules.bend as Rules
import ../lsp/files/service.bend as Files
import ../lsp/files/disk.bend as Disk

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

# the findings whose rule is not skipped
def kept(fs: List<&2, F.Finding>, +skip: List<&2, String>) -> List<&2, F.Finding>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{F.Finding{path, line, col, len, +rule, msg}, rest}:
      +more = kept(rest, skip)
      Bool.pick(List<&2, F.Finding>, List.contains(~String, ~String.eq, skip, rule), more,
        F.Finding{path, line, col, len, rule, msg} <> more)

# each line printed
def print_all(lines: List<&2, String>) -> IO(Unit):
  match lines:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{l, t}:
      do IO<Unit>:
        IO.print(l)
        print_all(t)

# the non-empty strings
def nonempty(ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +more = nonempty(t)
      Bool.pick(List<&2, String>, String.is_empty(h), more, h <> more)

# the paths in BEND_LINT_FILES, one a line
def paths_of(r: Result<&1, &1, U32 & String, String>) -> List<&2, String>:
  match r:
    case Fail{e}:
      []
    case Done{s}:
      nonempty(String.lines(s))

# the rules in BEND_LINT_SKIP, comma-separated
def skip_of(r: Result<&1, &1, U32 & String, String>) -> List<&2, String>:
  match r:
    case Fail{e}:
      []
    case Done{s}:
      nonempty(String.split(s, ','))

# every finding of every rule on the files read, except the skipped rules
def findings(+rs: List<&2, Read>, skip: List<&2, String>) -> List<&2, F.Finding>:
  kept(List.concat(&2, F.Finding, [per_file(rs), Rules.project(files_of(rs))]), skip)

def main() -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("BEND_LINT_FILES")
    sk : Result<&1, &1, U32 & String, String> <- IO.get_env("BEND_LINT_SKIP")
    rs : List<&2, Read> <- read_all(~Disk.new(), paths_of(r))
    +shown : List<&2, String> = F.show_all(findings(rs, skip_of(sk)))
    +n : U32 = U32.from_nat(List.length(&2, String, shown))
    print_all(shown)
    IO.print(Bool.pick(String, U32.is_eq(n, 0), "clean", U32.show(n) ++ " findings"))
