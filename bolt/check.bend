# bolt/check: `bolt check file..`: the checker (`bend`) on each file, its
# errors in bolt's shape, `path:line:1: error: message` (bend reports no
# column; a message's further lines are indented under it), then the count.
# A file bend could not be run on is one error, `path:1:1: error: could not
# run bend`, and never `clean`.
# What a check prints and how it exits is `out`'s decision over what bend
# reported (bolt/LAWS.bend proves it); `run` only does it.
import Base
import ./status.bend as Status
import ./lsp/report.bend as Rep
import ./lsp/checker/answer.bend as Checker
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

# a file checked: its path and the diagnostics bend reported for it, or a
# file bend could not be run on
type Run is Data:
  Run{path: String, ds: List<&2, Rep.Diag>}
  Failed{path: String}

# what a check prints, line by line, and the code it exits with
type Out is Data:
  Out{lines: List<&2, String>, code: U32}

# every run's error lines, in order
def lines_of(runs: List<&2, Run>) -> List<&2, String>:
  match runs:
    case Nil{}:
      Nil{}
    case Con{Run{path, ds}, rest}:
      List.append(&2, String, show_all(ds, path), lines_of(rest))
    case Con{Failed{path}, rest}:
      (path ++ ":1:1: error: could not run bend") <> lines_of(rest)

# the error lines, then `clean` or the count, and the exit code: 1 when
# there is any error
def out.at(ls: List<&2, String>, count: Nat) -> Out:
  match count:
    case 0n:
      Out{List.append(&2, String, ls, ["clean"]), 0}
    case 1n:
      Out{List.append(&2, String, ls, ["1 error, 0 warnings"]), 1}
    case 2n+more:
      Out{List.append(&2, String, ls, [U32.show(U32.from_nat(2n+more)) ++ " errors, 0 warnings"]), 1}

# what a check prints and how it exits, from what bend reported for each file
def out(runs: List<&2, Run>) -> Out:
  +ls = lines_of(runs)
  out.at(ls, List.length(&2, String, ls))

# each line printed
def print_all(lines: List<&2, String>) -> IO(Unit):
  match lines:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{l, t}:
      do IO<Unit>:
        IO.print(l)
        print_all(t)

# a file's run, from the checker's answer for it
def run_of(path: String, aa: Checker.Answer) -> Run:
  match aa:
    case Checker.Checked{ds}:
      Run{path, ds}
    case Checker.Unrun{}:
      Failed{path}

# every file checked, in order: what bend reported for each
def check_all(paths: List<&2, String>) -> IO(List<&2, Run>):
  match paths:
    case Nil{}:
      IO.pure(List<&2, Run>, [])
    case Con{+path, rest}:
      do IO<List<&2, Run>>:
        aa : Checker.Answer <- BendChecker.check(path)
        more : List<&2, Run> <- check_all(rest)
        return run_of(path, aa) <> more

# what out decided, done (BOLT-TRUST-9): its lines printed, then its code
def perform(oo: Out) -> IO(Unit):
  Out{lines, code} = oo
  do IO<Unit>:
    print_all(lines)
    Status.stop(U32.is_gt(code, 0))

# the checker over the files given, exiting 1 when any of them had an error
def run(paths: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    runs : List<&2, Run> <- check_all(paths)
    perform(out(runs))
