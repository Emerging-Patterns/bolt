# bolt/lint: the interpreter for `bolt` itself. It starts from a World
# holding the paths it was given and the working directory
# (bolt/lint/world.bend), then loops: it asks
# the planner (bolt/lint/plan.bend) what is still open, answers each question
# by IO, a directory listed through bolt/walk/ and a file read through
# bolt/lsp/files/ (a path bolt/walk/ calls a directory is answered as one,
# not read), and adds the answers to the World, until nothing is left to
# ask. Then it prints the planner's lines and exits with its status. It
# decides nothing: which files are linted, which bolt.bend grades each
# finding, and what is printed are the planner's. That it answers and prints
# faithfully is BOLT-TRUST-9.
import Base
import ./lint/world.bend as W
import ./lint/plan.bend as Plan
import ./lsp/files/disk.bend as Disk
import ./walk/disk.bend as WalkDisk
import ./status.bend as Status
import ../lazy/lazy.bend as Lazy

# a file's text as an answer
def read.answer(mm: Maybe<&2, String>) -> W.Answer:
  match mm:
    case None{}:
      W.Unread{}
    case Some{text}:
      W.Read{text}

# a path's text as an answer: a directory has none, and a file is read
def text.answer(dir: Bool, path: String) -> IO(W.Answer):
  match dir:
    case True{}:
      IO.pure(W.Answer, W.Directory{})
    case False{}:
      do IO<W.Answer>:
        mm : Maybe<&2, String> <- Disk.read(path)
        return read.answer(mm)

# one question, answered
def answer(ask: W.Ask) -> IO(W.Answer):  # noqa: L001 IO driver
  match ask:
    case W.Entries{dir}:
      do IO<W.Answer>:
        es : List<&2, String> <- WalkDisk.entries(dir)
        return W.Listed{es}
    case W.Text{+path}:
      do IO<W.Answer>:
        dir : Bool <- WalkDisk.is_dir(path)
        text.answer(dir, path)

# every question, answered, in order
def answer.all(asks: List<&2, W.Ask>) -> IO(List<&2, W.Reply>):
  match asks:
    case Nil{}:
      IO.pure(List<&2, W.Reply>, [])
    case Con{+ask, rest}:
      do IO<List<&2, W.Reply>>:
        a : W.Answer <- answer(ask)
        more : List<&2, W.Reply> <- answer.all(rest)
        return W.Reply{ask, a} <> more

# the World with more answers in it
def more(world: W.World, rs: List<&2, W.Reply>) -> W.World:
  W.World{paths, cwd, replies} = world
  W.World{paths, cwd, List.append(&2, W.Reply, replies, rs)}

# each line printed
def print_all(lines: List<&2, String>) -> IO(Unit):  # noqa: L001 IO driver
  match lines:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{l, t}:
      do IO<Unit>:
        IO.print(l)
        print_all(t)

# a plan, carried out: its lines printed, then its exit status
def exec(pl: Plan.Plan) -> IO(Unit):  # noqa: L001 IO driver
  Plan.Plan{lines, exit} = pl
  do IO<Unit>:
    print_all(lines)
    Status.stop(U32.is_gt(exit, 0))

# the planner's questions answered and the loop gone round again, or, when
# there are none, its plan carried out
def loop.step(asks: List<&2, W.Ask>, +world: W.World, go: W.World -> IO(Unit)) -> IO(Unit):
  match asks:
    case Nil{}:
      exec(Plan.plan(world))
    case Con{a, rest}:
      do IO<Unit>:
        rs : List<&2, W.Reply> <- answer.all(a <> rest)
        go(more(world, rs))

# the loop, under fuel: the walk's bound, plus a round for the texts and one
# to plan. Every round adds at least one answer, since the planner never asks
# what the World answers already.
def loop(fuel: Nat, +world: W.World) -> IO(Unit):  # noqa: L001 IO driver
  match fuel:
    case 0n:
      IO.die(Unit, 1, "bolt: the lint kept asking")
    case 1n+f:
      loop.step(Plan.wants(world), world, ww => loop(f, ww))

# the lint from a working directory; none that can be named is fatal, as no
# relative path could be resolved against it
def run.from(paths: List<&2, String>, +cwd: String) -> IO(Unit):
  Lazy.stop(IO(Unit), String.is_empty(cwd), IO.die(Unit, 1, "bolt: cannot name the working directory"),
    _u => loop(Nat.add(Plan.limit(), 2n), W.World{paths, cwd, []}))

# the linter, over the files given, or the tree below
def run(paths: List<&2, String>) -> IO(Unit):  # noqa: L001 IO driver
  do IO<Unit>:
    cwd : String <- WalkDisk.cwd()
    run.from(paths, cwd)
