# checker/bend: the real checker: runs `bend` on the file and reads its report
import Base
import ./service.bend as S
import ../report.bend as Rep

# everything `bend <path> -o <tmp>.js` printed; it checks, and never runs main
def bendcheck.exec(path: String) -> IO(String):
  import "./exec.c"
  import "./exec.js"

def check(path: String) -> IO(List<&2, Rep.Diag>):
  do IO<List<&2, Rep.Diag>>:
    text : String <- bendcheck.exec(path)
    return Rep.parse(text)

def new() -> S.Checker:
  S.Checker{check}
