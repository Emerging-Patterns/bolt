# bolt/check: `bolt check file..`: the checker (`bend`) on each file, its
# errors in bolt's shape, `path:line:1: error: message` (bend reports no
# column; a message's further lines are indented under it), then the count.
import Base
import ./status.bend as Status
import ./lsp/report.bend as Rep
import ./lsp/checker/service.bend as Checker
import ./lsp/checker/bend.bend as BendChecker

# a message's lines after the first, indented
def rest_lines(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case Con{l, t}:
      "\n  " ++ l ++ rest_lines(t)

# a message's lines: the first, then the rest indented
def message.of(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case Con{h, t}:
      h ++ rest_lines(t)

# a message: its first line, the rest indented
def message(msg: String) -> String:
  message.of(String.lines(msg))

# each diagnostic as a line
def show_all(ds: List<&2, Rep.Diag>, +path: String) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Rep.Diag{line, msg}, rest}:
      (path ++ ":" ++ U32.show((line + 1 : U32)) ++ ":1: error: " ++ message(msg)) <> show_all(rest, path)

# each line printed
def print_all(lines: List<&2, String>) -> IO(Unit):
  match lines:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{l, t}:
      do IO<Unit>:
        IO.print(l)
        print_all(t)

# every file checked and its errors printed; how many there were
def check_all(~ck: Checker.Checker, paths: List<&2, String>) -> IO(U32):
  match paths:
    case Nil{}:
      IO.pure(U32, 0)
    case Con{+path, rest}:
      do IO<U32>:
        ds : List<&2, Rep.Diag> <- Checker.check(ck, path)
        +shown : List<&2, String> = show_all(ds, path)
        print_all(shown)
        more : U32 <- check_all(~ck, rest)
        return (U32.from_nat(List.length(&2, String, shown)) + more : U32)

# `clean`, or the count
def summary(+n: U32) -> String:
  Bool.pick(String, U32.is_eq(n, 0), "clean",
    U32.show(n) ++ Bool.pick(String, U32.is_eq(n, 1), " error", " errors") ++ ", 0 warnings")

# the checker over the files given, exiting 1 when any of them had an error
def run(paths: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    +n : U32 <- check_all(~BendChecker.new(), paths)
    IO.print(summary(n))
    Status.stop(U32.is_gt(n, 0))
