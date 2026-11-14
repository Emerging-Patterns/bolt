# src/fmt/run: the interpreter for `bolt fmt`. It fills a World as the lint
# does (src/lint.bend's loop: the same questions, answered by the same IO),
# then carries out the plan src/fmt/plan.bend makes of it: each edit written
# over its file, the lines printed, and the exit status. It decides nothing:
# which files change and what they become are the planner's. That it writes
# and prints faithfully is trusted, not proved, as with every interpreter
# here; a file that cannot be opened or written ends the run at once, exit 1.
# Effect: CPU event loop only.
import Base
import ../lint.bend as Lint
import ../status.bend as Status
import ../lint/world.bend as W
import ./plan.bend as Fp

# a write that failed ends the run
def write.closed(rr: Result<&1, &1, U32 & String, Unit>, path: String) -> IO(Unit):
  match rr:
    case Fail{_e}:
      IO.die(Unit, 1, "bolt: cannot write " ++ path)
    case Done{_u}:
      IO.pure(Unit, Unit{})

# the file closed, then the write's result read
def write.wrote(got: File & Result<&1, &1, U32 & String, Unit>, path: String) -> IO(Unit):
  (file, r) = got
  do IO<Unit>:
    File.close(file)
    write.closed(r, path)

# the text written to an opened file; one that did not open ends the run
def write.opened(rr: Result<&1, &1, U32 & String, File>, path: String, text: String) -> IO(Unit):
  match rr:
    case Fail{_e}:
      IO.die(Unit, 1, "bolt: cannot write " ++ path)
    case Done{file}:
      do IO<Unit>:
        got : File & Result<&1, &1, U32 & String, Unit> <- File.write(file, text)
        write.wrote(got, path)

# a file's text replaced
def write(+path: String, text: String) -> IO(Unit):  # noqa: L001 IO driver
  do IO<Unit>:
    rr : Result<&1, &1, U32 & String, File> <- File.open(path, "w")
    write.opened(rr, path, text)

# each edit written, in order
def write.all(es: List<&2, Fp.Edit>) -> IO(Unit):
  match es:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{Fp.Edit{path, text}, rest}:
      do IO<Unit>:
        write(path, text)
        write.all(rest)

# a plan, carried out: its edits written, its lines printed, then its exit
# status
def exec(pl: Fp.Plan) -> IO(Unit):  # noqa: L001 IO driver
  Fp.Plan{edits, lines, exit} = pl
  do IO<Unit>:
    write.all(edits)
    Lint.print_all(lines)
    Status.stop(U32.is_gt(exit, 0))

# `bolt fmt` over the files given, or the tree below; check: list the files
# that would change and write none
def run(check: Bool, paths: List<&2, String>) -> IO(Unit):  # noqa: L001 IO driver
  do IO<Unit>:
    world : W.World <- Lint.fill(paths)
    exec(Fp.plan(check, world))
