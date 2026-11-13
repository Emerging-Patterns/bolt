# bench: per-stage timing of a whole-tree run's planner (not part of bolt).
#   cd <repo>; plan.bin +RTS --gpu off -RTS 2>&1 | while read -r l; do echo "$(date +%s.%N) $l"; done
# Each stage's strict let sits in its own def and prints a number read off
# its result.
import Base
import ../../src/lint.bend as Lint
import ../../src/lint/world.bend as W
import ../../src/lint/plan.bend as Plan
import ../../src/walk/disk.bend as WalkDisk
import ../../src/src.bend as Src
import ../../src/finding.bend as F
import ../../src/role.bend as Role
import ../../src/noqa.bend as Noqa
import ../../src/rules.bend as Rules

def say(+name: String, +n: Nat) -> IO(Unit):
  IO.print_err(name ++ " " ++ U32.show(U32.from_nat(n)))

def replies(world: W.World) -> Nat:
  W.World{_paths, _cwd, rs} = world
  List.length(&2, W.Reply, rs)

# one round: nothing left, or the questions answered and the loop gone round
def gather.step(asks: List<&2, W.Ask>, +world: W.World, go: W.World -> IO(W.World)) -> IO(W.World):
  match asks:
    case Nil{}:
      do IO<W.World>:
        say("wants: nothing left; replies", replies(world))
        return world
    case Con{+a, +rest}:
      do IO<W.World>:
        say("wants round: asks", List.length(&2, W.Ask, a <> rest))
        +rs : List<&2, W.Reply> <- Lint.answer.all(a <> rest)
        say("  answered", List.length(&2, W.Reply, rs))
        go(Lint.more(world, rs))

# the lint's loop, a line a round
def gather(fuel: Nat, +world: W.World) -> IO(W.World):
  match fuel:
    case 0n:
      IO.pure(W.World, world)
    case 1n+f:
      gather.step(Plan.wants(world), world, ww => gather(f, ww))

def st.inputs(+world: W.World) -> IO(List<&2, String>):
  +ps = Plan.inputs(world)
  do IO<List<&2, String>>:
    say("inputs", List.length(&2, String, ps))
    return ps

def st.gots(+ps: List<&2, String>, +world: W.World) -> IO(List<&2, Plan.Got>):
  +gs = Plan.gots(ps, world)
  do IO<List<&2, Plan.Got>>:
    say("gots", List.length(&2, Plan.Got, gs))
    return gs

def st.srcs(+gs: List<&2, Plan.Got>) -> IO(List<&2, Src.Src>):
  +ss = Plan.srcs_of(gs)
  do IO<List<&2, Src.Src>>:
    say("srcs_of (parse)", List.length(&2, Src.Src, ss))
    return ss

def st.confs(+world: W.World) -> IO(List<&2, Plan.Conf>):
  +cs = Plan.confs(world)
  do IO<List<&2, Plan.Conf>>:
    say("confs", List.length(&2, Plan.Conf, cs))
    return cs

def st.marks(+world: W.World, +ss: List<&2, Src.Src>) -> IO(List<&2, Role.Mark>):
  +ms = Plan.marks.run(W.paths.of(world), world, ss)
  do IO<List<&2, Role.Mark>>:
    say("marks.run", List.length(&2, Role.Mark, ms))
    return ms

def st.per(+cs: List<&2, Plan.Conf>, +world: W.World, +ms: List<&2, Role.Mark>, +ss: List<&2, Src.Src>) -> IO(List<&2, F.Finding>):
  +fs = Plan.per_file.live(cs, world, ms, ss)
  do IO<List<&2, F.Finding>>:
    say("per_file.live", List.length(&2, F.Finding, fs))
    return fs

def st.settings(+world: W.World) -> IO(List<&2, F.Finding>):
  +fs = Plan.settings(world)
  do IO<List<&2, F.Finding>>:
    say("settings", List.length(&2, F.Finding, fs))
    return fs

def st.roots(+world: W.World) -> IO(List<&2, String>):
  +rs = Plan.packages(Plan.roots(world))
  do IO<List<&2, String>>:
    say("roots", List.length(&2, String, rs))
    return rs

def st.project(+ss: List<&2, Src.Src>, +rs: List<&2, String>) -> IO(List<&2, F.Finding>):
  +fs = Rules.project(ss, rs)
  do IO<List<&2, F.Finding>>:
    say("project", List.length(&2, F.Finding, fs))
    return fs

def st.grade(+cs: List<&2, Plan.Conf>, +world: W.World, +fs: List<&2, F.Finding>) -> IO(List<&2, F.Graded>):
  +gs = Plan.grade(cs, world, fs)
  do IO<List<&2, F.Graded>>:
    say("grade", List.length(&2, F.Graded, gs))
    return gs

def st.nmarks(+ss: List<&2, Src.Src>) -> IO(List<&2, Noqa.Marks>):
  +ms = Noqa.of_srcs(ss)
  do IO<List<&2, Noqa.Marks>>:
    say("noqa marks", List.length(&2, Noqa.Marks, ms))
    return ms

def st.keep(+ms: List<&2, Noqa.Marks>, +gs: List<&2, F.Graded>) -> IO(Unit):
  +ks = Noqa.keep(ms, gs)
  say("noqa keep", List.length(&2, F.Graded, ks))

def st.noqa(+ms: List<&2, Noqa.Marks>, +gs: List<&2, F.Graded>) -> IO(Unit):
  +fs = Plan.noqa(ms, True{}, gs)
  say("noqa rule", List.length(&2, F.Finding, fs))

def st.plan(+world: W.World) -> IO(Unit):
  +pl = Plan.plan(world)
  say("plan (the whole of it again)", List.length(&2, String, Plan.lines.of(pl)))

def go(+world: W.World) -> IO(Unit):
  do IO<Unit>:
    +ps : List<&2, String> <- st.inputs(world)
    +gs : List<&2, Plan.Got> <- st.gots(ps, world)
    +ss : List<&2, Src.Src> <- st.srcs(gs)
    +cs : List<&2, Plan.Conf> <- st.confs(world)
    +ms : List<&2, Role.Mark> <- st.marks(world, ss)
    +f1 : List<&2, F.Finding> <- st.per(cs, world, ms, ss)
    +f2 : List<&2, F.Finding> <- st.settings(world)
    +rs : List<&2, String> <- st.roots(world)
    +f3 : List<&2, F.Finding> <- st.project(ss, rs)
    +gr : List<&2, F.Graded> <- st.grade(cs, world, List.concat(&2, F.Finding, [f1, f2, f3]))
    +nm : List<&2, Noqa.Marks> <- st.nmarks(ss)
    st.keep(nm, gr)
    st.noqa(nm, gr)
    st.plan(world)
    say("done", 0n)

def main() -> IO(Unit):
  do IO<Unit>:
    +cwd : String <- WalkDisk.cwd()
    say("start", 0n)
    +world : W.World <- gather(Nat.add(Plan.limit(), 2n), W.World{[], cwd, []})
    go(world)
