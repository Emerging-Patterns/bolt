# bend-lint: runs every rule over the files named in BEND_LINT_FILES (one a
# line; the bend-lint script fills it from its arguments, as a native Bend
# binary takes no arguments of its own), except the rules named in
# BEND_LINT_SKIP (comma-separated). Prints the findings, then a count.
import Base
import ./finding.bend as F
import ./rules.bend as Rules
import ../lsp/files/service.bend as Files
import ../lsp/files/disk.bend as Disk

def lint.text(+path: String, r: Maybe<&2, String>) -> List<&2, F.Finding>:
  match r:
    case None{}:
      [F.Finding{path, 0, 0, 0, "read", "cannot read this file"}]
    case Some{text}:
      Rules.all(path, text)

# the findings whose rule is not skipped
def kept(fs: List<&2, F.Finding>, +skip: List<&2, String>) -> List<&2, F.Finding>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{F.Finding{path, line, col, len, +rule, msg}, rest}:
      +more = kept(rest, skip)
      Bool.pick(List<&2, F.Finding>, List.contains(~String, ~String.eq, skip, rule), more,
        F.Finding{path, line, col, len, rule, msg} <> more)

# a file's findings
def lint(~fs: Files.Files, +path: String, skip: List<&2, String>) -> IO(List<&2, F.Finding>):
  do IO<List<&2, F.Finding>>:
    r : Maybe<&2, String> <- Files.read(fs, path)
    return kept(lint.text(path, r), skip)

# each line printed
def print_all(lines: List<&2, String>) -> IO(Unit):
  match lines:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{l, t}:
      do IO<Unit>:
        IO.print(l)
        print_all(t)

# every file linted and printed; how many findings there were
def lint_all(~fs: Files.Files, paths: List<&2, String>, +skip: List<&2, String>) -> IO(U32):
  match paths:
    case Nil{}:
      IO.pure(U32, 0)
    case Con{path, rest}:
      do IO<U32>:
        fs1 : List<&2, F.Finding> <- lint(~fs, path, skip)
        +shown : List<&2, String> = F.show_all(fs1)
        n : U32 = U32.from_nat(List.length(&2, String, shown))
        print_all(shown)
        m : U32 <- lint_all(~fs, rest, skip)
        return (n + m : U32)

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

def main() -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("BEND_LINT_FILES")
    sk : Result<&1, &1, U32 & String, String> <- IO.get_env("BEND_LINT_SKIP")
    +n : U32 <- lint_all(~Disk.new(), paths_of(r), skip_of(sk))
    IO.print(Bool.pick(String, U32.is_eq(n, 0), "clean", U32.show(n) ++ " findings"))
