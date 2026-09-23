# checker/bend: the real checker: runs `bend` on the file and reads its report.
# Which runs it makes is argv.bend's, pure; this file only performs them.
import Base
import ./service.bend as S
import ./argv.bend as Argv
import ../report.bend as Rep

# everything `bend <path> <flag>` printed
def bendcheck.exec(path: String, flag: String) -> IO(String):
  import "./exec.c"
  import "./exec.js"

# everything a run of bend printed; every run is argv.bend's, so it checks
# and never runs main
def launch(rr: Argv.Run) -> IO(String):
  Argv.Run{path, flag} = rr
  bendcheck.exec(path, flag)

# the first report, or nothing when the run that follows it (a PROOF.bend)
# checks clean
def settle(mr: Maybe<&2, Argv.Run>, +ds: List<&2, Rep.Diag>) -> IO(List<&2, Rep.Diag>):
  match mr:
    case None{}:
      IO.pure(List<&2, Rep.Diag>, ds)
    case Some{rr}:
      do IO<List<&2, Rep.Diag>>:
        text : String <- launch(rr)
        return Bool.pick(List<&2, Rep.Diag>, List.is_empty(&2, Rep.Diag, Rep.parse(text)), [], ds)

# the diagnostics of a run, settled by the run that follows it
def checked(+ds: List<&2, Rep.Diag>, +path: String) -> IO(List<&2, Rep.Diag>):
  settle(Argv.followup(ds, path), ds)

def check.at(+path: String) -> IO(List<&2, Rep.Diag>):
  do IO<List<&2, Rep.Diag>>:
    text : String <- launch(Argv.run_of(path))
    checked(Rep.parse(text), path)

# the service's field takes a plain path; quantities are part of its type
def check(path: String) -> IO(List<&2, Rep.Diag>):
  check.at(path)

# the real checker
def new() -> S.Checker:
  S.Checker{check}
