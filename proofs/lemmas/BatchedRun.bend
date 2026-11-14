# a run parsed a batch at a time keeps and grades what one parsed whole does
import Base
import ../../src/finding.bend as F
import ../../src/src.bend as Src
import ../../src/role.bend as Role
import ../../src/noqa.bend as Noqa
import ../../src/rules.bend as Rules
import ../../src/lazy/lazy.bend as Lazy
import ../../src/rules/digest.bend as Digest
import ../../src/lint/world.bend as W
import ../../src/lint/plan.bend as Plan
import ../../laws/LargeRunParsesInBatches.bend as Laws

# a source put on the batches is that source, then theirs
law lb.put:
  for +g: Plan.Got
  for bs: List<&2, List<&2, Plan.Got>>
  {List.concat(&2, Plan.Got, Plan.batches.put(g, bs)) == g <> List.concat(&2, Plan.Got, bs) : List<&2, Plan.Got>}

def lb.put(_g, bs):
  match bs:
    case Nil{}:
      {==}
    case Con{b, rest}:
      {==}

# so is one cut from the batch before it, full or not
law lb.cut:
  for full: Bool
  for +g: Plan.Got
  for +more: List<&2, List<&2, Plan.Got>>
  {List.concat(&2, Plan.Got, Plan.batches.cut(full, g, more)) == g <> List.concat(&2, Plan.Got, more)
    : List<&2, Plan.Got>}

def lb.cut(full, g, more):
  match full:
    case True{}:
      lb.put(g, more)
    case False{}:
      lb.put(g, more)

def Laws.batches_keep_sources(gs, used, max):
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +tl}:
      +full = Bool.and(U32.is_gt(U32.add(used, Plan.got.size(g)), max), U32.is_gt(used, 0))
      +next = Bool.pick(U32, full, Plan.got.size(g), U32.add(used, Plan.got.size(g)))
      Equal.trans(List<&2, Plan.Got>,
        List.concat(&2, Plan.Got, Plan.batches.cut(full, g, Plan.batches(tl, next, max))),
        g <> List.concat(&2, Plan.Got, Plan.batches(tl, next, max)),
        g <> tl,
        lb.cut(full, g, Plan.batches(tl, next, max)),
        Equal.cong(List<&2, Plan.Got>, List<&2, Plan.Got>, r => g <> r,
          List.concat(&2, Plan.Got, Plan.batches(tl, next, max)), tl, Laws.batches_keep_sources(tl, next, max)))

def Laws.batch_holds_the_budget(_p, _q):
  {==}

def Laws.batch_closes_past_the_budget(_p, _q):
  {==}

def Laws.batch_of_one_large_source(_p, _q):
  {==}

def Laws.batch_unread_takes_no_room(_p, _q, _r):
  {==}

def Laws.size_counts_texts(_ps, _cwd, _p, _q, _d, _ns):
  {==}

def Laws.budget_is_sixteen_million(_world):
  {==}

# parsing the sources of two lists is parsing each list
law lk.srcs.app:
  for xs: List<&2, Plan.Got>
  for +ys: List<&2, Plan.Got>
  {Plan.srcs_of(List.append(&2, Plan.Got, xs, ys))
    == List.append(&2, Src.Src, Plan.srcs_of(xs), Plan.srcs_of(ys)) : List<&2, Src.Src>}

def lk.srcs.app(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{Plan.Got{_path, None{}}, +tl}:
      lk.srcs.app(tl, ys)
    case Con{Plan.Got{+path, Some{+text}}, +tl}:
      Equal.cong(List<&2, Src.Src>, List<&2, Src.Src>, r => Src.of(path, text) <> r,
        Plan.srcs_of(List.append(&2, Plan.Got, tl, ys)),
        List.append(&2, Src.Src, Plan.srcs_of(tl), Plan.srcs_of(ys)), lk.srcs.app(tl, ys))

# what is kept of the sources of two lists is what is kept of each list
law lk.keeps.app:
  for +cs: List<&2, Plan.Conf>
  for +world: W.World
  for +rs: Plan.Roles
  for xs: List<&2, Src.Src>
  for +ys: List<&2, Src.Src>
  {Plan.keeps.srcs(cs, world, rs, List.append(&2, Src.Src, xs, ys))
    == List.append(&2, Plan.Kept, Plan.keeps.srcs(cs, world, rs, xs), Plan.keeps.srcs(cs, world, rs, ys))
    : List<&2, Plan.Kept>}

def lk.keeps.app(cs, world, rs, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +tl}:
      Equal.cong(List<&2, Plan.Kept>, List<&2, Plan.Kept>, r => Plan.kept.of(cs, world, rs, s) <> r,
        Plan.keeps.srcs(cs, world, rs, List.append(&2, Src.Src, tl, ys)),
        List.append(&2, Plan.Kept, Plan.keeps.srcs(cs, world, rs, tl), Plan.keeps.srcs(cs, world, rs, ys)),
        lk.keeps.app(cs, world, rs, tl, ys))

# batch by batch, what is kept is what is kept of every source parsed at once
law lk.batches:
  for +cs: List<&2, Plan.Conf>
  for +world: W.World
  for +rs: Plan.Roles
  for bs: List<&2, List<&2, Plan.Got>>
  {Plan.keeps.batches(cs, world, rs, bs)
    == Plan.keeps.srcs(cs, world, rs, Plan.srcs_of(List.concat(&2, Plan.Got, bs))) : List<&2, Plan.Kept>}

def lk.batches(cs, world, rs, bs):
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +tl}:
      +kb = Plan.keeps.srcs(cs, world, rs, Plan.srcs_of(b))
      +rest = List.concat(&2, Plan.Got, tl)
      Equal.trans(List<&2, Plan.Kept>,
        List.append(&2, Plan.Kept, kb, Plan.keeps.batches(cs, world, rs, tl)),
        List.append(&2, Plan.Kept, kb, Plan.keeps.srcs(cs, world, rs, Plan.srcs_of(rest))),
        Plan.keeps.srcs(cs, world, rs, Plan.srcs_of(List.append(&2, Plan.Got, b, rest))),
        Equal.cong(List<&2, Plan.Kept>, List<&2, Plan.Kept>, r => List.append(&2, Plan.Kept, kb, r),
          Plan.keeps.batches(cs, world, rs, tl), Plan.keeps.srcs(cs, world, rs, Plan.srcs_of(rest)),
          lk.batches(cs, world, rs, tl)),
        Equal.trans(List<&2, Plan.Kept>,
          List.append(&2, Plan.Kept, kb, Plan.keeps.srcs(cs, world, rs, Plan.srcs_of(rest))),
          Plan.keeps.srcs(cs, world, rs, List.append(&2, Src.Src, Plan.srcs_of(b), Plan.srcs_of(rest))),
          Plan.keeps.srcs(cs, world, rs, Plan.srcs_of(List.append(&2, Plan.Got, b, rest))),
          Equal.sym(List<&2, Plan.Kept>,
            Plan.keeps.srcs(cs, world, rs, List.append(&2, Src.Src, Plan.srcs_of(b), Plan.srcs_of(rest))),
            List.append(&2, Plan.Kept, kb, Plan.keeps.srcs(cs, world, rs, Plan.srcs_of(rest))),
            lk.keeps.app(cs, world, rs, Plan.srcs_of(b), Plan.srcs_of(rest))),
          Equal.cong(List<&2, Src.Src>, List<&2, Plan.Kept>, z => Plan.keeps.srcs(cs, world, rs, z),
            List.append(&2, Src.Src, Plan.srcs_of(b), Plan.srcs_of(rest)),
            Plan.srcs_of(List.append(&2, Plan.Got, b, rest)),
            Equal.sym(List<&2, Src.Src>, Plan.srcs_of(List.append(&2, Plan.Got, b, rest)),
              List.append(&2, Src.Src, Plan.srcs_of(b), Plan.srcs_of(rest)), lk.srcs.app(b, rest)))))

# so the batches of the sources keep what parsing every source first keeps
law lk.all:
  for +cs: List<&2, Plan.Conf>
  for +world: W.World
  for +rs: Plan.Roles
  for +gs: List<&2, Plan.Got>
  for +used: U32
  for +max: U32
  {Plan.keeps.batches(cs, world, rs, Plan.batches(gs, used, max))
    == Plan.keeps.srcs(cs, world, rs, Plan.srcs_of(gs)) : List<&2, Plan.Kept>}

def lk.all(cs, world, rs, gs, used, max):
  e = Laws.batches_keep_sources(gs, used, max)
  %e : {Plan.keeps.batches(cs, world, rs, Plan.batches(gs, used, max))
    == Plan.keeps.srcs(cs, world, rs, Plan.srcs_of(_)) : List<&2, Plan.Kept>}
  lk.batches(cs, world, rs, Plan.batches(gs, used, max))

# the marks kept are each source's, as Noqa.of_srcs reads them
law lk.marks:
  for +cs: List<&2, Plan.Conf>
  for +world: W.World
  for +rs: Plan.Roles
  for ss: List<&2, Src.Src>
  {Plan.keeps.marks(Plan.keeps.srcs(cs, world, rs, ss)) == Noqa.of_srcs(ss) : List<&2, Noqa.Marks>}

def lk.marks(cs, world, rs, ss):
  match rs:
    case Plan.Roles{+run, +own}:
      match ss:
        case Nil{}:
          {==}
        case Con{Src.Src{+path, +text, +toks, +tree, +bound, +items}, +tl}:
          Equal.cong(List<&2, Noqa.Marks>, List<&2, Noqa.Marks>, r => Noqa.file(path, toks) <> r,
            Plan.keeps.marks(Plan.keeps.srcs(cs, world, Plan.Roles{run, own}, tl)), Noqa.of_srcs(tl),
            lk.marks(cs, world, Plan.Roles{run, own}, tl))

# the findings kept are the per-file rules' on each source, told its role
# among the run's marks
law lk.found:
  for +cs: List<&2, Plan.Conf>
  for +world: W.World
  for +run: List<&2, Role.Mark>
  for +own: List<&2, Role.Mark>
  for ss: List<&2, Src.Src>
  {Plan.keeps.found(Plan.keeps.srcs(cs, world, Plan.Roles{run, own}, ss))
    == Plan.per_file.live(cs, world, run, ss) : List<&2, F.Finding>}

def lk.found(cs, world, run, own, ss):
  match ss:
    case Nil{}:
      {==}
    case Con{Src.Src{+path, +text, +toks, +tree, +bound, +items}, +tl}:
      Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
        r => List.concat(&2, F.Finding, [Rules.on.role.live(Plan.config.at(cs, world, path), Role.of(run, path),
          Src.Src{path, text, toks, tree, bound, items}), r]),
        Plan.keeps.found(Plan.keeps.srcs(cs, world, Plan.Roles{run, own}, tl)),
        Plan.per_file.live(cs, world, run, tl), lk.found(cs, world, run, own, tl))

# the digests kept are each source's, told its role among the sources' own
# marks
law lk.digests:
  for +cs: List<&2, Plan.Conf>
  for +world: W.World
  for +run: List<&2, Role.Mark>
  for +own: List<&2, Role.Mark>
  for ss: List<&2, Src.Src>
  {Plan.keeps.digests(Plan.keeps.srcs(cs, world, Plan.Roles{run, own}, ss)) == Digest.all.role(own, ss)
    : List<&2, Digest.Digest>}

def lk.digests(cs, world, run, own, ss):
  match ss:
    case Nil{}:
      {==}
    case Con{Src.Src{+path, +text, +toks, +tree, +bound, +items}, +tl}:
      Equal.cong(List<&2, Digest.Digest>, List<&2, Digest.Digest>,
        r => Digest.of.marked(own, Src.Src{path, text, toks, tree, bound, items}) <> r,
        Plan.keeps.digests(Plan.keeps.srcs(cs, world, Plan.Roles{run, own}, tl)), Digest.all.role(own, tl),
        lk.digests(cs, world, run, own, tl))

# a source's fact read from its text is the fact read off its parse
law lk.facts:
  for gs: List<&2, Plan.Got>
  {Role.facts(Plan.srcs_of(gs)) == Plan.facts.texts(gs) : List<&2, Role.Fact>}

def lk.facts(gs):
  match gs:
    case Nil{}:
      {==}
    case Con{Plan.Got{_path, None{}}, +tl}:
      lk.facts(tl)
    case Con{Plan.Got{+path, Some{+text}}, +tl}:
      Equal.cong(List<&2, Role.Fact>, List<&2, Role.Fact>, r => Role.fact.text(path, text) <> r,
        Role.facts(Plan.srcs_of(tl)), Plan.facts.texts(tl), lk.facts(tl))

# the marks picked, given the sources' own, are the marks a run reads
law lk.pick:
  for paths: List<&2, String>
  for +world: W.World
  for +s: List<&2, Src.Src>
  {Plan.marks.pick(paths, world, Role.marks(s)) == Plan.marks.run(paths, world, s) : List<&2, Role.Mark>}

def lk.pick(paths, _world, _s):
  match paths:
    case Nil{}:
      {==}
    case Con{_p, _rest}:
      {==}

def Laws.final_lean(world):
  +gs = Plan.gots(Plan.inputs(world), world)
  +s = Plan.srcs_of(gs)
  +cs = Plan.confs(world)
  +ps = W.paths.of(world)
  +own = Role.marks(s)
  +run = Plan.marks.run(ps, world, s)
  +ks = Plan.keeps.srcs(cs, world, Plan.Roles{run, own}, s)
  %lk.facts(gs) : {Plan.final.of(world, cs, gs, Plan.keeps.run(Plan.keeps.batches(cs, world,
      Plan.Roles{Plan.marks.pick(ps, world, Role.marks.facts(_)), Role.marks.facts(_)},
      Plan.batches(gs, 0, Plan.budget())))) == Plan.final.live(world) : List<&2, F.Graded>}
  %Equal.sym(List<&2, Role.Mark>, Plan.marks.pick(ps, world, own), run, lk.pick(ps, world, s))
    : {Plan.final.of(world, cs, gs, Plan.keeps.run(Plan.keeps.batches(cs, world, Plan.Roles{_, own},
      Plan.batches(gs, 0, Plan.budget())))) == Plan.final.live(world) : List<&2, F.Graded>}
  %Equal.sym(List<&2, Plan.Kept>, Plan.keeps.batches(cs, world, Plan.Roles{run, own},
      Plan.batches(gs, 0, Plan.budget())), ks, lk.all(cs, world, Plan.Roles{run, own}, gs, 0, Plan.budget()))
    : {Plan.final.of(world, cs, gs, Plan.keeps.run(_)) == Plan.final.live(world) : List<&2, F.Graded>}
  %Equal.sym(List<&2, Noqa.Marks>, Plan.keeps.marks(ks), Noqa.of_srcs(s),
      lk.marks(cs, world, Plan.Roles{run, own}, s))
    : {Plan.final.of(world, cs, gs, Plan.Run{_, Plan.keeps.found(ks), Plan.keeps.digests(ks)})
      == Plan.final.live(world) : List<&2, F.Graded>}
  %Equal.sym(List<&2, F.Finding>, Plan.keeps.found(ks), Plan.per_file.live(cs, world, run, s),
      lk.found(cs, world, run, own, s))
    : {Plan.final.of(world, cs, gs, Plan.Run{Noqa.of_srcs(s), _, Plan.keeps.digests(ks)})
      == Plan.final.live(world) : List<&2, F.Graded>}
  %Equal.sym(List<&2, Digest.Digest>, Plan.keeps.digests(ks), Digest.all.role(own, s),
      lk.digests(cs, world, run, own, s))
    : {Plan.final.of(world, cs, gs, Plan.Run{Noqa.of_srcs(s), Plan.per_file.live(cs, world, run, s), _})
      == Plan.final.live(world) : List<&2, F.Graded>}
  {==}

# a pick between two values that are the same is the first, whichever is
# taken
law lk.either:
  for b: Bool
  for +x: List<&2, F.Graded>
  for +y: List<&2, F.Graded>
  for e: {y == x : List<&2, F.Graded>}
  {Lazy.either(List<&2, F.Graded>, b, _u => x, _v => y) == x : List<&2, F.Graded>}

def lk.either(b, _x, _y, e):
  match b:
    case True{}:
      {==}
    case False{}:
      e

def Laws.final_run(world):
  lk.either(Plan.fits(world), Plan.final.live(world), Plan.final.lean(world), Laws.final_lean(world))
