# checker/bend: the real checker: runs `bend` on the file and reads its report
import Base
import ./service.bend as S
import ../report.bend as Rep

# everything `bend <path> -o <tmp>.js` printed; it checks, and never runs main
def bendcheck.exec(path: String) -> IO(String):
  import "./exec.c"
  import "./exec.js"

# only the open-laws report ("N TODOs found"), and nothing else
def only_todos(ds: List<&2, Rep.Diag>) -> Bool:
  match ds:
    case Con{Rep.Diag{line, msg}, Nil{}}:
      String.contains(msg, "TODO found")
    case other:
      False{}

# the PROOF.bend beside a LAWS.bend
def proof_path(+path: String) -> String:
  String.take(path, Nat.sub(String.length(path), 9n)) ++ "PROOF.bend"

# By convention LAWS.bend states its laws as open claims and PROOF.bend, beside
# it, fills them: alone, LAWS.bend always has TODOs. They are an error only
# while PROOF.bend does not check clean.
def settle(open: Bool, +ds: List<&2, Rep.Diag>, path: String) -> IO(List<&2, Rep.Diag>):
  match open:
    case False{}:
      IO.pure(List<&2, Rep.Diag>, ds)
    case True{}:
      do IO<List<&2, Rep.Diag>>:
        text : String <- bendcheck.exec(proof_path(path))
        return Bool.pick(List<&2, Rep.Diag>, List.is_empty(&2, Rep.Diag, Rep.parse(text)), [], ds)

# the diagnostics of a run, settled when they are only the open laws of a
# LAWS.bend
def checked(+ds: List<&2, Rep.Diag>, +path: String) -> IO(List<&2, Rep.Diag>):
  settle(Bool.and(only_todos(ds), String.ends_with(path, "/LAWS.bend")), ds, path)

def check.at(+path: String) -> IO(List<&2, Rep.Diag>):
  do IO<List<&2, Rep.Diag>>:
    text : String <- bendcheck.exec(path)
    checked(Rep.parse(text), path)

# the service's field takes a plain path; quantities are part of its type
def check(path: String) -> IO(List<&2, Rep.Diag>):
  check.at(path)

# the real checker
def new() -> S.Checker:
  S.Checker{check}
