# proofs of laws/ScopePackageRootsFound.bend
import Base
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ../laws/ScopePackageRootsFound.bend as Laws
import ./lemmas/PackageRootLookup.bend as M1

# the planner's search of a listing for main.bend is the spec's
law pk.has:
  for es: List<&2, String>
  {Plan.seen.has(es, "main.bend") == Laws.names_main(es) : Bool}

def pk.has(es):
  match es:
    case Nil{}:
      {==}
    case Con{+e, +tl}:
      M1.pk.or(String.eq(e, "main.bend"), Plan.seen.has(tl, "main.bend"), Laws.names_main(tl), pk.has(tl))

# the planner's roots of the directories read are the spec's
law pk.of:
  for ds: List<&2, String>
  for +world: W.World
  {Plan.roots.of(ds, world) == Laws.main_dirs(world, ds) : List<&2, String>}

def pk.of(ds, world):
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +tl}:
      a = pk.has(W.listing(world, d))
      %a : {Bool.pick(List<&2, String>,
          Bool.and(Bool.not(String.eq(d, ".")), Plan.seen.has(W.listing(world, d), "main.bend")),
          d <> Plan.roots.of(tl, world), Plan.roots.of(tl, world))
        == Bool.pick(List<&2, String>, Bool.and(Bool.not(String.eq(d, ".")), _),
          d <> Laws.main_dirs(world, tl), Laws.main_dirs(world, tl))
        : List<&2, String>}
      e = pk.of(tl, world)
      %e : {Bool.pick(List<&2, String>,
          Bool.and(Bool.not(String.eq(d, ".")), Plan.seen.has(W.listing(world, d), "main.bend")),
          d <> Plan.roots.of(tl, world), Plan.roots.of(tl, world))
        == Bool.pick(List<&2, String>,
          Bool.and(Bool.not(String.eq(d, ".")), Plan.seen.has(W.listing(world, d), "main.bend")), d <> _, _)
        : List<&2, String>}
      {==}

def Laws.roots_named(world, p, rest, h):
  e = Equal.sym(List<&2, String>, W.paths.of(world), p <> rest, h)
  %e : {Plan.roots.named(_, world) == [] : List<&2, String>}
  {==}

def Laws.roots_whole(world, h):
  e = Equal.sym(List<&2, String>, W.paths.of(world), [], h)
  %e : {Plan.roots.named(_, world) == Laws.main_dirs(world, Plan.walk.read(Plan.tree(world))) : List<&2, String>}
  pk.of(Plan.walk.read(Plan.tree(world)), world)

def Laws.ups_nearest_first(_s, _rest):
  {==}
