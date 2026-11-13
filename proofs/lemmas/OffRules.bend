# a rule a config sets off need not be run: grading drops what it finds
import Base
import ../../src/config.bend as Config
import ../../src/finding.bend as F
import ../../src/role.bend as Role
import ../../src/src.bend as Src
import ../../src/rules.bend as Rules
import ../../src/noqa.bend as Noqa
import ../../src/syntax/lex.bend as Lex
import ../../src/syntax/tree.bend as Tree
import ../../src/syntax/bind.bend as Bind
import ../../src/syntax/outline.bend as Outline
import ../../src/lint/world.bend as W
import ../../src/lint/plan.bend as Plan
import ../../laws/OffRulesAreNotRun.bend as L1

# Off rules (laws/OffRulesAreNotRun.bend). A table entry's findings are
# named for its rule, so when the rule is off grading drops every one of
# them; grading and putting findings at a path both go through an append; so
# a table with its off entries left out grades as the whole table does. The
# planner grades a file's findings by one config, the one it left the rules
# out by.

# an off rule's findings, named for it, are all dropped by grading
law off.drop:
  for +cfg: Config.Config
  for +slug: String
  for +path: String
  for fs: List<&2, F.Finding>
  for +e: {Rules.on.off(cfg, slug) == True{} : Bool}
  {Rules.graded(cfg, Rules.on.at(path, Rules.on.slug(slug, fs))) == Nil{} : List<&2, F.Graded>}

def off.drop(cfg, slug, path, fs, e):
  match fs:
    case Nil{}:
      {==}
    case Con{F.Finding{p, l, c, n, r, m}, +rest}:
      %Equal.sym(Bool, Rules.on.off(cfg, slug), True{}, e) :
        {Bool.pick(List<&2, F.Graded>, _, Rules.graded(cfg, Rules.on.at(path, Rules.on.slug(slug, rest))),
          F.Graded{Config.level(cfg, Rules.group(slug), slug), F.Finding{path, l, c, n, slug, m}}
            <> Rules.graded(cfg, Rules.on.at(path, Rules.on.slug(slug, rest)))) == Nil{} : List<&2, F.Graded>}
      off.drop(cfg, slug, path, rest, e)

# an entry left out when its rule is off grades as the entry run: bb is
# whether the rule is off
law off.gate.at:
  for bb: Bool
  for +cfg: Config.Config
  for +slug: String
  for +path: String
  for +ww: Rules.Which
  for +rr: Role.Role
  for +ss: Src.Src
  for +eb: {Rules.on.off(cfg, slug) == bb : Bool}
  {Rules.graded(cfg, Rules.on.at(path, Rules.on.gate(bb, slug, ww, rr, ss)))
    == Rules.graded(cfg, Rules.on.at(path, Rules.on.slug(slug, Rules.on.run(ww, rr, ss)))) : List<&2, F.Graded>}

def off.gate.at(bb, cfg, slug, path, ww, rr, ss, eb):
  match bb:
    case True{}:
      Equal.sym(List<&2, F.Graded>,
        Rules.graded(cfg, Rules.on.at(path, Rules.on.slug(slug, Rules.on.run(ww, rr, ss)))), Nil{},
        off.drop(cfg, slug, path, Rules.on.run(ww, rr, ss), eb))
    case False{}:
      {==}

# putting findings at a path goes through an append
law off.at.app:
  for +path: String
  for aa: List<&2, F.Finding>
  for +bb: List<&2, F.Finding>
  {Rules.on.at(path, List.append(&2, F.Finding, aa, bb))
    == List.append(&2, F.Finding, Rules.on.at(path, aa), Rules.on.at(path, bb)) : List<&2, F.Finding>}

def off.at.app(path, aa, bb):
  match aa:
    case Nil{}:
      {==}
    case Con{F.Finding{p, l, c, n, r, m}, +rest}:
      Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>, z => F.Finding{path, l, c, n, r, m} <> z,
        Rules.on.at(path, List.append(&2, F.Finding, rest, bb)),
        List.append(&2, F.Finding, Rules.on.at(path, rest), Rules.on.at(path, bb)), off.at.app(path, rest, bb))

# a pick between a list and one more in front of it goes through an append
law off.pick.app:
  for bb: Bool
  for -gg: F.Graded
  for -xs: List<&2, F.Graded>
  for -ys: List<&2, F.Graded>
  {Bool.pick(List<&2, F.Graded>, bb, List.append(&2, F.Graded, xs, ys), gg <> List.append(&2, F.Graded, xs, ys))
    == List.append(&2, F.Graded, Bool.pick(List<&2, F.Graded>, bb, xs, gg <> xs), ys) : List<&2, F.Graded>}

def off.pick.app(bb, _gg, _xs, _ys):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# grading goes through an append
law off.graded.app:
  for +cfg: Config.Config
  for aa: List<&2, F.Finding>
  for +bb: List<&2, F.Finding>
  {Rules.graded(cfg, List.append(&2, F.Finding, aa, bb))
    == List.append(&2, F.Graded, Rules.graded(cfg, aa), Rules.graded(cfg, bb)) : List<&2, F.Graded>}

def off.graded.app(cfg, aa, bb):
  match aa:
    case Nil{}:
      {==}
    case Con{F.Finding{+p, +l, +c, +n, +r, +m}, +rest}:
      %Equal.sym(List<&2, F.Graded>, Rules.graded(cfg, List.append(&2, F.Finding, rest, bb)),
        List.append(&2, F.Graded, Rules.graded(cfg, rest), Rules.graded(cfg, bb)), off.graded.app(cfg, rest, bb)) :
        {Bool.pick(List<&2, F.Graded>, Config.is_off(Config.level(cfg, Rules.group(r), r)), _,
          F.Graded{Config.level(cfg, Rules.group(r), r), F.Finding{p, l, c, n, r, m}} <> _)
          == List.append(&2, F.Graded, Rules.graded(cfg, F.Finding{p, l, c, n, r, m} <> rest), Rules.graded(cfg, bb))
          : List<&2, F.Graded>}
      off.pick.app(Config.is_off(Config.level(cfg, Rules.group(r), r)),
        F.Graded{Config.level(cfg, Rules.group(r), r), F.Finding{p, l, c, n, r, m}},
        Rules.graded(cfg, rest), Rules.graded(cfg, bb))

# grading findings put at a path goes through an append
law off.both.app:
  for +cfg: Config.Config
  for +path: String
  for +aa: List<&2, F.Finding>
  for +bb: List<&2, F.Finding>
  {Rules.graded(cfg, Rules.on.at(path, List.append(&2, F.Finding, aa, bb)))
    == List.append(&2, F.Graded, Rules.graded(cfg, Rules.on.at(path, aa)), Rules.graded(cfg, Rules.on.at(path, bb)))
    : List<&2, F.Graded>}

def off.both.app(cfg, path, aa, bb):
  Equal.trans(List<&2, F.Graded>,
    Rules.graded(cfg, Rules.on.at(path, List.append(&2, F.Finding, aa, bb))),
    Rules.graded(cfg, List.append(&2, F.Finding, Rules.on.at(path, aa), Rules.on.at(path, bb))),
    List.append(&2, F.Graded, Rules.graded(cfg, Rules.on.at(path, aa)), Rules.graded(cfg, Rules.on.at(path, bb))),
    Equal.cong(List<&2, F.Finding>, List<&2, F.Graded>, z => Rules.graded(cfg, z),
      Rules.on.at(path, List.append(&2, F.Finding, aa, bb)),
      List.append(&2, F.Finding, Rules.on.at(path, aa), Rules.on.at(path, bb)), off.at.app(path, aa, bb)),
    off.graded.app(cfg, Rules.on.at(path, aa), Rules.on.at(path, bb)))

# two appends equal part by part are equal
law off.two:
  for -a1: List<&2, F.Graded>
  for -a2: List<&2, F.Graded>
  for -b1: List<&2, F.Graded>
  for -b2: List<&2, F.Graded>
  for ea: {a1 == a2 : List<&2, F.Graded>}
  for eb: {b1 == b2 : List<&2, F.Graded>}
  {List.append(&2, F.Graded, a1, b1) == List.append(&2, F.Graded, a2, b2) : List<&2, F.Graded>}

def off.two(a1, a2, b1, b2, ea, eb):
  Equal.trans(List<&2, F.Graded>, List.append(&2, F.Graded, a1, b1), List.append(&2, F.Graded, a2, b1),
    List.append(&2, F.Graded, a2, b2),
    Equal.cong(List<&2, F.Graded>, List<&2, F.Graded>, z => List.append(&2, F.Graded, z, b1), a1, a2, ea),
    Equal.cong(List<&2, F.Graded>, List<&2, F.Graded>, z => List.append(&2, F.Graded, a2, z), b1, b2, eb))

# a table with its off entries left out grades, at a path, as the whole
# table does
law off.table:
  for rs: List<&2, Rules.Run>
  for +cfg: Config.Config
  for +path: String
  for +rr: Role.Role
  for +ss: Src.Src
  {Rules.graded(cfg, Rules.on.at(path, Rules.on.live(rs, cfg, rr, ss)))
    == Rules.graded(cfg, Rules.on.at(path, Rules.on.all(rs, rr, ss))) : List<&2, F.Graded>}

def off.table(rs, cfg, path, rr, ss):
  match rs:
    case Nil{}:
      {==}
    case Con{Rules.Run{+slug, +ww}, +rest}:
      +ga = Rules.on.gate(Rules.on.off(cfg, slug), slug, ww, rr, ss)
      +ra = Rules.on.slug(slug, Rules.on.run(ww, rr, ss))
      +gb = Rules.on.live(rest, cfg, rr, ss)
      +rb = Rules.on.all(rest, rr, ss)
      Equal.trans(List<&2, F.Graded>,
        Rules.graded(cfg, Rules.on.at(path, List.append(&2, F.Finding, ga, gb))),
        List.append(&2, F.Graded, Rules.graded(cfg, Rules.on.at(path, ga)), Rules.graded(cfg, Rules.on.at(path, gb))),
        Rules.graded(cfg, Rules.on.at(path, List.append(&2, F.Finding, ra, rb))),
        off.both.app(cfg, path, ga, gb),
        Equal.trans(List<&2, F.Graded>,
          List.append(&2, F.Graded, Rules.graded(cfg, Rules.on.at(path, ga)), Rules.graded(cfg, Rules.on.at(path, gb))),
          List.append(&2, F.Graded, Rules.graded(cfg, Rules.on.at(path, ra)), Rules.graded(cfg, Rules.on.at(path, rb))),
          Rules.graded(cfg, Rules.on.at(path, List.append(&2, F.Finding, ra, rb))),
          off.two(Rules.graded(cfg, Rules.on.at(path, ga)), Rules.graded(cfg, Rules.on.at(path, ra)),
            Rules.graded(cfg, Rules.on.at(path, gb)), Rules.graded(cfg, Rules.on.at(path, rb)),
            off.gate.at(Rules.on.off(cfg, slug), cfg, slug, path, ww, rr, ss, {==}),
            off.table(rest, cfg, path, rr, ss)),
          Equal.sym(List<&2, F.Graded>,
            Rules.graded(cfg, Rules.on.at(path, List.append(&2, F.Finding, ra, rb))),
            List.append(&2, F.Graded, Rules.graded(cfg, Rules.on.at(path, ra)),
              Rules.graded(cfg, Rules.on.at(path, rb))),
            off.both.app(cfg, path, ra, rb))))

def L1.live_grades_alike(cfg, rr, ss):
  off.table(Rules.on.table(), cfg, Rules.on.path(ss), rr, ss)

# the planner
# -----------

# an append of three, grouped either way
law pl.assoc:
  for xs: List<&2, F.Graded>
  for -ys: List<&2, F.Graded>
  for -zs: List<&2, F.Graded>
  {List.append(&2, F.Graded, xs, List.append(&2, F.Graded, ys, zs))
    == List.append(&2, F.Graded, List.append(&2, F.Graded, xs, ys), zs) : List<&2, F.Graded>}

def pl.assoc(xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, F.Graded>, List<&2, F.Graded>, z => h <> z,
        List.append(&2, F.Graded, t, List.append(&2, F.Graded, ys, zs)),
        List.append(&2, F.Graded, List.append(&2, F.Graded, t, ys), zs), pl.assoc(t, ys, zs))

# the planner's grading goes through an append
law pl.grade.app:
  for +cs: List<&2, Plan.Conf>
  for +world: W.World
  for aa: List<&2, F.Finding>
  for +bb: List<&2, F.Finding>
  {Plan.grade(cs, world, List.append(&2, F.Finding, aa, bb))
    == List.append(&2, F.Graded, Plan.grade(cs, world, aa), Plan.grade(cs, world, bb)) : List<&2, F.Graded>}

def pl.grade.app(cs, world, aa, bb):
  match aa:
    case Nil{}:
      {==}
    case Con{F.Finding{+p, +l, +c, +n, +r, +m}, +rest}:
      +xx = Rules.graded(Plan.config.at(cs, world, p), [F.Finding{p, l, c, n, r, m}])
      Equal.trans(List<&2, F.Graded>,
        List.append(&2, F.Graded, xx, Plan.grade(cs, world, List.append(&2, F.Finding, rest, bb))),
        List.append(&2, F.Graded, xx,
          List.append(&2, F.Graded, Plan.grade(cs, world, rest), Plan.grade(cs, world, bb))),
        List.append(&2, F.Graded, List.append(&2, F.Graded, xx, Plan.grade(cs, world, rest)),
          Plan.grade(cs, world, bb)),
        Equal.cong(List<&2, F.Graded>, List<&2, F.Graded>, z => List.append(&2, F.Graded, xx, z),
          Plan.grade(cs, world, List.append(&2, F.Finding, rest, bb)),
          List.append(&2, F.Graded, Plan.grade(cs, world, rest), Plan.grade(cs, world, bb)),
          pl.grade.app(cs, world, rest, bb)),
        pl.assoc(xx, Plan.grade(cs, world, rest), Plan.grade(cs, world, bb)))

# findings at one path are graded by that path's config, all of them
law pl.at:
  for +cs: List<&2, Plan.Conf>
  for +world: W.World
  for +path: String
  for fs: List<&2, F.Finding>
  {Plan.grade(cs, world, Rules.on.at(path, fs))
    == Rules.graded(Plan.config.at(cs, world, path), Rules.on.at(path, fs)) : List<&2, F.Graded>}

def pl.at(cs, world, path, fs):
  match fs:
    case Nil{}:
      {==}
    case Con{F.Finding{p, +l, +c, +n, +r, +m}, +rest}:
      +cfg = Plan.config.at(cs, world, path)
      +ff = {F.Finding{path, l, c, n, r, m} : F.Finding}
      Equal.trans(List<&2, F.Graded>,
        List.append(&2, F.Graded, Rules.graded(cfg, [ff]), Plan.grade(cs, world, Rules.on.at(path, rest))),
        List.append(&2, F.Graded, Rules.graded(cfg, [ff]), Rules.graded(cfg, Rules.on.at(path, rest))),
        Rules.graded(cfg, ff <> Rules.on.at(path, rest)),
        Equal.cong(List<&2, F.Graded>, List<&2, F.Graded>, z => List.append(&2, F.Graded, Rules.graded(cfg, [ff]), z),
          Plan.grade(cs, world, Rules.on.at(path, rest)), Rules.graded(cfg, Rules.on.at(path, rest)),
          pl.at(cs, world, path, rest)),
        Equal.sym(List<&2, F.Graded>, Rules.graded(cfg, List.append(&2, F.Finding, [ff], Rules.on.at(path, rest))),
          List.append(&2, F.Graded, Rules.graded(cfg, [ff]), Rules.graded(cfg, Rules.on.at(path, rest))),
          off.graded.app(cfg, [ff], Rules.on.at(path, rest))))

# one file: its findings with its off rules left out grade as all of them
law pl.file:
  for +cs: List<&2, Plan.Conf>
  for +world: W.World
  for +rr: Role.Role
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {Plan.grade(cs, world, Rules.on.role.live(Plan.config.at(cs, world, path), rr,
      Src.Src{path, text, toks, tree, bound, items}))
    == Plan.grade(cs, world, Rules.on.role(rr, Src.Src{path, text, toks, tree, bound, items}))
    : List<&2, F.Graded>}

def pl.file(cs, world, rr, path, text, toks, tree, bound, items):
  +cfg = Plan.config.at(cs, world, path)
  +ss = {Src.Src{path, text, toks, tree, bound, items} : Src.Src}
  +lv = Rules.on.live(Rules.on.table(), cfg, rr, ss)
  +al = Rules.on.all(Rules.on.table(), rr, ss)
  Equal.trans(List<&2, F.Graded>,
    Plan.grade(cs, world, Rules.on.at(path, lv)),
    Rules.graded(cfg, Rules.on.at(path, lv)),
    Plan.grade(cs, world, Rules.on.at(path, al)),
    pl.at(cs, world, path, lv),
    Equal.trans(List<&2, F.Graded>,
      Rules.graded(cfg, Rules.on.at(path, lv)),
      Rules.graded(cfg, Rules.on.at(path, al)),
      Plan.grade(cs, world, Rules.on.at(path, al)),
      off.table(Rules.on.table(), cfg, path, rr, ss),
      Equal.sym(List<&2, F.Graded>, Plan.grade(cs, world, Rules.on.at(path, al)),
        Rules.graded(cfg, Rules.on.at(path, al)), pl.at(cs, world, path, al))))

# two lists joined are graded each on its own
law pl.pair:
  for +cs: List<&2, Plan.Conf>
  for +world: W.World
  for +aa: List<&2, F.Finding>
  for +bb: List<&2, F.Finding>
  {Plan.grade(cs, world, List.concat(&2, F.Finding, [aa, bb]))
    == List.append(&2, F.Graded, Plan.grade(cs, world, aa),
      List.append(&2, F.Graded, Plan.grade(cs, world, bb), Nil{})) : List<&2, F.Graded>}

def pl.pair(cs, world, aa, bb):
  Equal.trans(List<&2, F.Graded>,
    Plan.grade(cs, world, List.append(&2, F.Finding, aa, List.append(&2, F.Finding, bb, Nil{}))),
    List.append(&2, F.Graded, Plan.grade(cs, world, aa),
      Plan.grade(cs, world, List.append(&2, F.Finding, bb, Nil{}))),
    List.append(&2, F.Graded, Plan.grade(cs, world, aa),
      List.append(&2, F.Graded, Plan.grade(cs, world, bb), Nil{})),
    pl.grade.app(cs, world, aa, List.append(&2, F.Finding, bb, Nil{})),
    Equal.cong(List<&2, F.Graded>, List<&2, F.Graded>, z => List.append(&2, F.Graded, Plan.grade(cs, world, aa), z),
      Plan.grade(cs, world, List.append(&2, F.Finding, bb, Nil{})),
      List.append(&2, F.Graded, Plan.grade(cs, world, bb), Nil{}), pl.grade.app(cs, world, bb, Nil{})))

# every file: the per-file findings with off rules left out grade as all of
# them
law pl.files:
  for +cs: List<&2, Plan.Conf>
  for +world: W.World
  for +ms: List<&2, Role.Mark>
  for ss: List<&2, Src.Src>
  {Plan.grade(cs, world, Plan.per_file.live(cs, world, ms, ss))
    == Plan.grade(cs, world, Plan.per_file.role(ms, ss)) : List<&2, F.Graded>}

def pl.files(cs, world, ms, ss):
  match ss:
    case Nil{}:
      {==}
    case Con{Src.Src{+path, +text, +toks, +tree, +bound, +items}, +rest}:
      +la = Rules.on.role.live(Plan.config.at(cs, world, path), Role.of(ms, path),
        Src.Src{path, text, toks, tree, bound, items})
      +ra = Rules.on.role(Role.of(ms, path), Src.Src{path, text, toks, tree, bound, items})
      +lb = Plan.per_file.live(cs, world, ms, rest)
      +rb = Plan.per_file.role(ms, rest)
      Equal.trans(List<&2, F.Graded>,
        Plan.grade(cs, world, List.concat(&2, F.Finding, [la, lb])),
        List.append(&2, F.Graded, Plan.grade(cs, world, la),
          List.append(&2, F.Graded, Plan.grade(cs, world, lb), Nil{})),
        Plan.grade(cs, world, List.concat(&2, F.Finding, [ra, rb])),
        pl.pair(cs, world, la, lb),
        Equal.trans(List<&2, F.Graded>,
          List.append(&2, F.Graded, Plan.grade(cs, world, la),
            List.append(&2, F.Graded, Plan.grade(cs, world, lb), Nil{})),
          List.append(&2, F.Graded, Plan.grade(cs, world, ra),
            List.append(&2, F.Graded, Plan.grade(cs, world, rb), Nil{})),
          Plan.grade(cs, world, List.concat(&2, F.Finding, [ra, rb])),
          off.two(Plan.grade(cs, world, la), Plan.grade(cs, world, ra),
            List.append(&2, F.Graded, Plan.grade(cs, world, lb), Nil{}),
            List.append(&2, F.Graded, Plan.grade(cs, world, rb), Nil{}),
            pl.file(cs, world, Role.of(ms, path), path, text, toks, tree, bound, items),
            Equal.cong(List<&2, F.Graded>, List<&2, F.Graded>, z => List.append(&2, F.Graded, z, Nil{}),
              Plan.grade(cs, world, lb), Plan.grade(cs, world, rb), pl.files(cs, world, ms, rest))),
          Equal.sym(List<&2, F.Graded>, Plan.grade(cs, world, List.concat(&2, F.Finding, [ra, rb])),
            List.append(&2, F.Graded, Plan.grade(cs, world, ra),
              List.append(&2, F.Graded, Plan.grade(cs, world, rb), Nil{})),
            pl.pair(cs, world, ra, rb))))

# two lists that grade alike grade alike with the same list after them
law pl.mid:
  for +cs: List<&2, Plan.Conf>
  for +world: W.World
  for +a1: List<&2, F.Finding>
  for +a2: List<&2, F.Finding>
  for +yy: List<&2, F.Finding>
  for e: {Plan.grade(cs, world, a1) == Plan.grade(cs, world, a2) : List<&2, F.Graded>}
  {Plan.grade(cs, world, List.append(&2, F.Finding, a1, yy))
    == Plan.grade(cs, world, List.append(&2, F.Finding, a2, yy)) : List<&2, F.Graded>}

def pl.mid(cs, world, a1, a2, yy, e):
  Equal.trans(List<&2, F.Graded>,
    Plan.grade(cs, world, List.append(&2, F.Finding, a1, yy)),
    List.append(&2, F.Graded, Plan.grade(cs, world, a1), Plan.grade(cs, world, yy)),
    Plan.grade(cs, world, List.append(&2, F.Finding, a2, yy)),
    pl.grade.app(cs, world, a1, yy),
    Equal.trans(List<&2, F.Graded>,
      List.append(&2, F.Graded, Plan.grade(cs, world, a1), Plan.grade(cs, world, yy)),
      List.append(&2, F.Graded, Plan.grade(cs, world, a2), Plan.grade(cs, world, yy)),
      Plan.grade(cs, world, List.append(&2, F.Finding, a2, yy)),
      Equal.cong(List<&2, F.Graded>, List<&2, F.Graded>, z => List.append(&2, F.Graded, z, Plan.grade(cs, world, yy)),
        Plan.grade(cs, world, a1), Plan.grade(cs, world, a2), e),
      Equal.sym(List<&2, F.Graded>, Plan.grade(cs, world, List.append(&2, F.Finding, a2, yy)),
        List.append(&2, F.Graded, Plan.grade(cs, world, a2), Plan.grade(cs, world, yy)),
        pl.grade.app(cs, world, a2, yy))))

# a run: everything found with off rules left out grades as everything found
law pl.found:
  for +cs: List<&2, Plan.Conf>
  for +world: W.World
  for +gs: List<&2, Plan.Got>
  for +ss: List<&2, Src.Src>
  {Plan.grade(cs, world, Plan.found.live(cs, world, gs, ss))
    == Plan.grade(cs, world, Plan.found.at(world, gs, ss)) : List<&2, F.Graded>}

def pl.found(cs, world, gs, ss):
  +uu = Plan.unread(gs)
  +ms = Plan.marks.run(W.paths.of(world), world, ss)
  +pl = Plan.per_file.live(cs, world, ms, ss)
  +pr = Plan.per_file.role(ms, ss)
  +yy = List.append(&2, F.Finding, Plan.settings(world),
    List.append(&2, F.Finding, Rules.project(ss, Plan.packages(Plan.roots(world))), Nil{}))
  Equal.trans(List<&2, F.Graded>,
    Plan.grade(cs, world, List.append(&2, F.Finding, uu, List.append(&2, F.Finding, pl, yy))),
    List.append(&2, F.Graded, Plan.grade(cs, world, uu), Plan.grade(cs, world, List.append(&2, F.Finding, pl, yy))),
    Plan.grade(cs, world, List.append(&2, F.Finding, uu, List.append(&2, F.Finding, pr, yy))),
    pl.grade.app(cs, world, uu, List.append(&2, F.Finding, pl, yy)),
    Equal.trans(List<&2, F.Graded>,
      List.append(&2, F.Graded, Plan.grade(cs, world, uu),
        Plan.grade(cs, world, List.append(&2, F.Finding, pl, yy))),
      List.append(&2, F.Graded, Plan.grade(cs, world, uu),
        Plan.grade(cs, world, List.append(&2, F.Finding, pr, yy))),
      Plan.grade(cs, world, List.append(&2, F.Finding, uu, List.append(&2, F.Finding, pr, yy))),
      Equal.cong(List<&2, F.Graded>, List<&2, F.Graded>, z => List.append(&2, F.Graded, Plan.grade(cs, world, uu), z),
        Plan.grade(cs, world, List.append(&2, F.Finding, pl, yy)),
        Plan.grade(cs, world, List.append(&2, F.Finding, pr, yy)),
        pl.mid(cs, world, pl, pr, yy, pl.files(cs, world, ms, ss))),
      Equal.sym(List<&2, F.Graded>,
        Plan.grade(cs, world, List.append(&2, F.Finding, uu, List.append(&2, F.Finding, pr, yy))),
        List.append(&2, F.Graded, Plan.grade(cs, world, uu),
          Plan.grade(cs, world, List.append(&2, F.Finding, pr, yy))),
        pl.grade.app(cs, world, uu, List.append(&2, F.Finding, pr, yy)))))

def L1.final_live(world):
  +gs = Plan.gots(Plan.inputs(world), world)
  +ss = Plan.srcs_of(gs)
  +cs = Plan.confs(world)
  Equal.cong(List<&2, F.Graded>, List<&2, F.Graded>,
    z => Plan.after(Noqa.of_srcs(ss), List.is_empty(&2, String, W.paths.of(world)), z,
      fs => Plan.grade(cs, world, fs)),
    Plan.grade(cs, world, Plan.found.live(cs, world, gs, ss)), Plan.grade(cs, world, Plan.found.at(world, gs, ss)),
    pl.found(cs, world, gs, ss))
