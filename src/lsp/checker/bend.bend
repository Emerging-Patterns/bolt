# checker/bend: an effect (CPU event loop only): the diagnostics of the file
# at a path. It runs `bend` on the file and reads its report. Which runs it
# makes is argv.bend's, and what its output answers is answer.bend's, both
# pure; this file only performs them. `service` hands it to the server and
# to `bolt check`, which take the checker as a service and never import this
# file, so their proofs reach no foreign code.
import Base
import ./answer.bend as S
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
def launch(rr: Argv.Run) -> IO(String):  # noqa: L001 checker effect
  Argv.Run{path, flag} = rr
  bendcheck.exec(path, flag)

# the first report, settled by the run that follows it (a LAWS.bend's
# PROOF.bend), when argv.bend gives one
def settle(mr: Maybe<&2, Argv.Run>, +ds: List<&2, Rep.Diag>) -> IO(S.Answer):  # noqa: L001 checker effect
  match mr:
    case None{}:
      IO.pure(S.Answer, S.Checked{ds})
    case Some{rr}:
      do IO<S.Answer>:
        text : String <- launch(rr)
        return S.proved(S.answer(None{}, text), ds)

# the diagnostics of a run, settled by the run that follows it
def checked(+ds: List<&2, Rep.Diag>, +path: String) -> IO(S.Answer):  # noqa: L001 checker effect
  settle(Argv.followup(ds, path), ds)

# a run's answer: its diagnostics settled when bend ran, else no check
def settled(aa: S.Answer, +path: String) -> IO(S.Answer):  # noqa: L001 checker effect
  match aa:
    case S.Checked{ds}:
      checked(ds, path)
    case S.Unrun{}:
      IO.pure(S.Answer, S.Unrun{})

# bend's report on the file, its errors placed by the names of the file's
# items (read from the file bend read; unknown when it cannot be read)
def check(+path: String) -> IO(S.Answer):  # noqa: L001 checker effect
  do IO<S.Answer>:
    text : String <- launch(Argv.run_of(path))
    src : Maybe<&2, String> <- Disk.read(path)
    settled(S.answer(Names.of(src), text), path)

# the checker as a service (answer.bend's Checker)
def service() -> S.Checker:  # noqa: L001 checker effect
  S.Checker{p => check(p)}
