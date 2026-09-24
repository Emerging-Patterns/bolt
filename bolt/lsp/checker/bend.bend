# checker/bend: the real checker: runs `bend` on the file and reads its report.
# Which runs it makes is argv.bend's, pure; this file only performs them.
import Base
import ./service.bend as S
import ./argv.bend as Argv
import ../report.bend as Rep
import ./names.bend as Names
import ../files/disk.bend as Disk

# how `bend <path> <flag>` went, one tag char, then everything it printed.
# The flag is argv.bend's, `--check-only`: it checks, and never runs main.
# The tag is `r` when bend ran and exited, `s` when a signal killed it, and
# `x` when it could not be run: no pipe, no fork, or an exit with 127, the
# code a failed exec exits with (as a shell does for a command it cannot
# find)
def bendcheck.exec(path: String, flag: String) -> IO(String):
  import "./exec.c"
  import "./exec.js"

# what a run of bend answered, tag first; every run is argv.bend's, so it
# checks and never runs main
def launch(rr: Argv.Run) -> IO(String):
  Argv.Run{path, flag} = rr
  bendcheck.exec(path, flag)

# a run a signal cut short: what bend reported before it died, or, when that
# is nothing, no check at all
def died(ds: List<&2, Rep.Diag>) -> S.Answer:
  match ds:
    case Nil{}:
      S.Unrun{}
    case Con{dd, rest}:
      S.Checked{dd <> rest}

# the answer a tag gives: bend ran (`r`), a signal killed it (`s`), or
# neither, and it could not be run; each error placed by the checked file's
# names, when they are known
def answer.tag(ran: Bool, killed: Bool, names: Maybe<&2, List<&2, String>>, text: String) -> S.Answer:
  match ran killed:
    case True{} _k:
      S.Checked{Rep.parse_in(names, text)}
    case False{} True{}:
      died(Rep.parse_in(names, text))
    case False{} False{}:
      S.Unrun{}

# exec's text read: its tag, then what bend printed, as diagnostics placed by
# the checked file's names
def answer(names: Maybe<&2, List<&2, String>>, ss: String) -> S.Answer:
  match ss:
    case SNil{}:
      S.Unrun{}
    case SCon{+cc, text}:
      answer.tag(Char.is_eq(cc, 'r'), Char.is_eq(cc, 's'), names, text)

# a LAWS.bend's errors, settled by its PROOF.bend's answer: none when that
# checks clean, and no check at all when bend could not be run on it
def proved(aa: S.Answer, ds: List<&2, Rep.Diag>) -> S.Answer:
  match aa:
    case S.Checked{pds}:
      S.Checked{Bool.pick(List<&2, Rep.Diag>, List.is_empty(&2, Rep.Diag, pds), [], ds)}
    case S.Unrun{}:
      S.Unrun{}

# the first report, settled by the run that follows it (a LAWS.bend's
# PROOF.bend), when argv.bend gives one
def settle(mr: Maybe<&2, Argv.Run>, +ds: List<&2, Rep.Diag>) -> IO(S.Answer):
  match mr:
    case None{}:
      IO.pure(S.Answer, S.Checked{ds})
    case Some{rr}:
      do IO<S.Answer>:
        text : String <- launch(rr)
        return proved(answer(None{}, text), ds)

# the diagnostics of a run, settled by the run that follows it
def checked(+ds: List<&2, Rep.Diag>, +path: String) -> IO(S.Answer):
  settle(Argv.followup(ds, path), ds)

# a run's answer: its diagnostics settled when bend ran, else no check
def settled(aa: S.Answer, +path: String) -> IO(S.Answer):
  match aa:
    case S.Checked{ds}:
      checked(ds, path)
    case S.Unrun{}:
      IO.pure(S.Answer, S.Unrun{})

# bend's report on the file, its errors placed by the names of the file's
# items (read from the file bend read; unknown when it cannot be read)
def check.at(+path: String) -> IO(S.Answer):
  do IO<S.Answer>:
    text : String <- launch(Argv.run_of(path))
    src : Maybe<&2, String> <- Disk.read(path)
    settled(answer(Names.of(src), text), path)

# the service's field takes a plain path; quantities are part of its type
def check(path: String) -> IO(S.Answer):
  check.at(path)

# the real checker
def new() -> S.Checker:
  S.Checker{check}
