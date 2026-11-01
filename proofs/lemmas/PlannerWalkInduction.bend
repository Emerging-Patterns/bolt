# list-append facts and the planner's directory walk matching the search
import Base
import ../../src/lint/world.bend as W
import ../../src/lint/plan.bend as Plan
import ../../laws/WalkBfs.bend as L1
import ../../laws/defs/ScopeWalkFiles.bend as D1

# The lint planner. Every proof below is by induction over a list the
# planner folds (the questions, the source paths, the findings, the graded
# findings), with a step lemma that takes the one computed value the step
# branches on as a variable and cases on it.

# appending nothing leaves a list as it was
law lint.app_nil:
  for -A: Kind(&2)
  for xs: List<&2, A>
  {List.append(&2, A, xs, []) == xs : List<&2, A>}

def lint.app_nil(A, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{hd, +tl}:
      Equal.cong(List<&2, A>, List<&2, A>, rr => hd <> rr, List.append(&2, A, tl, []), tl, lint.app_nil(A, tl))

# The walk (laws/ScopeWalksWholeTree.bend). The planner's walk threads the files it has found
# so far through its loop; the search reads its directories first. A lemma
# over every fuel, queue and accumulator ties the two: whatever the walk
# carries in comes out after the search's files, and each step's listing is
# read the same way.

# appending regroups
law scope1.assoc:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  for +zs: List<&2, String>
  {List.append(&2, String, List.append(&2, String, xs, ys), zs)
    == List.append(&2, String, xs, List.append(&2, String, ys, zs)) : List<&2, String>}

def scope1.assoc(xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case Con{hd, +tl}:
      Equal.cong(List<&2, String>, List<&2, String>, rr => hd <> rr,
        List.append(&2, String, List.append(&2, String, tl, ys), zs),
        List.append(&2, String, tl, List.append(&2, String, ys, zs)), scope1.assoc(tl, ys, zs))

# the walk descends into the directories the search does
law scope1.dirs:
  for es: List<&2, String>
  for +dir: String
  {Plan.walk.dirs(es, dir) == D1.subdirs(es, dir) : List<&2, String>}

def scope1.dirs(es, dir):
  match es:
    case Nil{}:
      {==}
    case Con{+ee, +tl}:
      Equal.cong(List<&2, String>, List<&2, String>,
        mm => Bool.pick(List<&2, String>, D1.descends(ee), (dir ++ "/" ++ D1.entry_name(ee)) <> mm, mm),
        Plan.walk.dirs(tl, dir), D1.subdirs(tl, dir), scope1.dirs(tl, dir))

# the walk finds the `.bend` files the search does
law scope1.bends:
  for es: List<&2, String>
  for +dir: String
  {Plan.walk.bends(es, dir) == D1.bends_in(es, dir) : List<&2, String>}

def scope1.bends(es, dir):
  match es:
    case Nil{}:
      {==}
    case Con{+ee, +tl}:
      Equal.cong(List<&2, String>, List<&2, String>,
        mm => Bool.pick(List<&2, String>, String.ends_with(ee, ".bend"), (dir ++ "/" ++ ee) <> mm, mm),
        Plan.walk.bends(tl, dir), D1.bends_in(tl, dir), scope1.bends(tl, dir))

# one directory read: what the rest of the walk finds, onto its files and
# what came before, regrouped as the search's files then what came before
law scope1.walk.step:
  for +xs: List<&2, String>
  for +bs: List<&2, String>
  for +acc: List<&2, String>
  for -found: List<&2, String>
  for ih: {found == List.append(&2, String, xs, List.append(&2, String, bs, acc)) : List<&2, String>}
  {found == List.append(&2, String, List.append(&2, String, xs, bs), acc) : List<&2, String>}

def scope1.walk.step(xs, bs, acc, found, ih):
  Equal.trans(List<&2, String>, found, List.append(&2, String, xs, List.append(&2, String, bs, acc)),
    List.append(&2, String, List.append(&2, String, xs, bs), acc), ih,
    Equal.sym(List<&2, String>, List.append(&2, String, List.append(&2, String, xs, bs), acc),
      List.append(&2, String, xs, List.append(&2, String, bs, acc)), scope1.assoc(xs, bs, acc)))

# the walk from any queue, with any fuel, finds the search's files, then
# what it carried in
law scope1.walk:
  for +fuel: Nat
  for +world: W.World
  for +queue: List<&2, String>
  for +acc: List<&2, String>
  for seen: List<&2, String>
  {Plan.walk.found(Plan.walk(fuel, world, queue, acc, seen))
    == List.append(&2, String, D1.found_in(D1.bfs(fuel, world, queue), world), acc) : List<&2, String>}

def scope1.walk(fuel, world, queue, acc, seen):
  match fuel:
    case 0n:
      {==}
    case 1n+ff:
      match queue:
        case Nil{}:
          {==}
        case Con{+dd, +rest}:
          d = scope1.dirs(W.listing(world, dd), dd)
          %d : {Plan.walk.found(Plan.walk(ff, world,
              List.append(&2, String, rest, Plan.walk.dirs(W.listing(world, dd), dd)),
              List.append(&2, String, Plan.walk.bends(W.listing(world, dd), dd), acc), dd <> seen))
            == List.append(&2, String, List.append(&2, String,
              D1.found_in(D1.bfs(ff, world, List.append(&2, String, rest, _)), world),
              D1.bends_in(W.listing(world, dd), dd)), acc) : List<&2, String>}
          b = scope1.bends(W.listing(world, dd), dd)
          %b : {Plan.walk.found(Plan.walk(ff, world,
              List.append(&2, String, rest, Plan.walk.dirs(W.listing(world, dd), dd)),
              List.append(&2, String, Plan.walk.bends(W.listing(world, dd), dd), acc), dd <> seen))
            == List.append(&2, String, List.append(&2, String,
              D1.found_in(D1.bfs(ff, world,
                List.append(&2, String, rest, Plan.walk.dirs(W.listing(world, dd), dd))), world),
              _), acc) : List<&2, String>}
          scope1.walk.step(
            D1.found_in(D1.bfs(ff, world,
              List.append(&2, String, rest, Plan.walk.dirs(W.listing(world, dd), dd))), world),
            Plan.walk.bends(W.listing(world, dd), dd), acc,
            Plan.walk.found(Plan.walk(ff, world,
              List.append(&2, String, rest, Plan.walk.dirs(W.listing(world, dd), dd)),
              List.append(&2, String, Plan.walk.bends(W.listing(world, dd), dd), acc), dd <> seen)),
            scope1.walk(ff, world, List.append(&2, String, rest, Plan.walk.dirs(W.listing(world, dd), dd)),
              List.append(&2, String, Plan.walk.bends(W.listing(world, dd), dd), acc), dd <> seen))

def L1.walk_bfs(reads, world):
  Equal.trans(List<&2, String>, Plan.walk.found(Plan.walk(reads, world, ["."], [], [])),
    List.append(&2, String, D1.found_in(D1.bfs(reads, world, ["."]), world), []),
    D1.found_in(D1.bfs(reads, world, ["."]), world),
    scope1.walk(reads, world, ["."], [], []),
    lint.app_nil(String, D1.found_in(D1.bfs(reads, world, ["."]), world)))
