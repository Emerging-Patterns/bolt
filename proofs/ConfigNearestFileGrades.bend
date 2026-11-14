# proofs of laws/ConfigNearestFileGrades.bend
import Base
import ../src/lazy/lazy.bend as Lazy
import ../src/config.bend as Config
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ../laws/ConfigNearestFileGrades.bend as Laws
import ./lemmas/ReplyIndex.bend as M9

# Where a finding is graded (laws/ConfigNearestFileGrades.bend). The table lookup compares
# directories with String.eq, so the proof needs String.eq to be sound: two
# strings it calls equal are equal. That goes down to the words a U32 is made
# of, as src/syntax/PROOF.bend's ol.weq does.

def Laws.absolute_root(cwd, path, h):
  e = Equal.sym(Bool, String.starts_with(path, "/"), True{}, h)
  %e : {Bool.pick(String, _, path, cwd ++ "/" ++ path) == path : String}
  {==}

def Laws.absolute_under(cwd, path, h):
  e = Equal.sym(Bool, String.starts_with(path, "/"), False{}, h)
  %e : {Bool.pick(String, _, path, cwd ++ "/" ++ path) == cwd ++ "/" ++ path : String}
  {==}

def Laws.home_empty(_above):
  {==}

def Laws.home_here(_above):
  {==}

def Laws.home_up(_above):
  {==}

def Laws.home_down(seg, above, h_here, h_up):
  e = Equal.sym(Bool, Bool.or(String.is_empty(seg), String.eq(seg, ".")), False{}, h_here)
  %e : {Bool.pick(List<&2, String>, _, above,
      Bool.pick(List<&2, String>, String.eq(seg, ".."), Config.home.up(above), seg <> above))
    == seg <> above : List<&2, String>}
  u = Equal.sym(Bool, String.eq(seg, ".."), False{}, h_up)
  %u : {Bool.pick(List<&2, String>, _, Config.home.up(above), seg <> above) == seg <> above : List<&2, String>}
  {==}

def Laws.chain_parent(_dd, _rest):
  {==}

# Unit for False, Empty for True
def cfg4.false_ty(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

# False is never True
law cfg4.false_true:
  for e: {False{} == True{} : Bool}
  Empty

def cfg4.false_true(e):
  %e : cfg4.false_ty(_)
  Unit{}

# words that compare equal, bit by bit past the first: the rest equal, the
# first bits the same
law cfg4.weq.arm:
  for -p: Nat
  for -at: Word(p)
  for -bt: Word(p)
  for c: Cmp
  for ec: {Word.cmp(p, at, bt) == c : Cmp}
  for ih: {Cmp.is_eq(Word.cmp(p, at, bt)) == True{} : Bool} -> {at == bt : Word(p)}
  for ab: Bool
  for b: Bool
  for e: {Cmp.is_eq(Word.cmp.fin(ab, b, c)) == True{} : Bool}
  {WCon{ab, at} == WCon{b, bt} : Word.Con<p>}

def cfg4.weq.arm(p, at, bt, c, ec, ih, ab, b, e):
  match c:
    case LT{}:
      Empty.absurd({WCon{ab, at} == WCon{b, bt} : Word.Con<p>}, cfg4.false_true(e))
    case GT{}:
      Empty.absurd({WCon{ab, at} == WCon{b, bt} : Word.Con<p>}, cfg4.false_true(e))
    case EQ{}:
      match ab b:
        case False{} False{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{False{}, w}, at, bt,
            ih(Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, at, bt), EQ{}, ec)))
        case True{} True{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{True{}, w}, at, bt,
            ih(Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, at, bt), EQ{}, ec)))
        case False{} True{}:
          Empty.absurd({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, cfg4.false_true(e))
        case True{} False{}:
          Empty.absurd({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, cfg4.false_true(e))

# words that compare equal are equal
law cfg4.weq:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for e: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}
  {a == b : Word(n)}

def cfg4.weq(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          cfg4.weq.arm(p, at, bt, Word.cmp(p, at, bt), {==}, x => cfg4.weq(p, at, bt, x), ab, bb, e)

# U32s that compare equal are equal
law cfg4.ueq:
  for a: U32
  for b: U32
  for e: {U32.is_eq(a, b) == True{} : Bool}
  {a == b : U32}

def cfg4.ueq(a, b, e):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, cfg4.weq(32n, x, y, e))

# a compare whose first characters already differ answers as they do, whatever
# the rest (String.eq walks with String.order.go since bend 2.0.37)
law cfg4.go_lt:
  for a: String
  for b: String
  {String.order.go(a, b, LT{}) == LT{} : Cmp}

def cfg4.go_lt(a, b):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{_h, _t}:
      {==}
    case SCon{_h, _t} SNil{}:
      {==}
    case SCon{Chr{_x}, _t1} SCon{Chr{_y}, _t2}:
      {==}

law cfg4.go_gt:
  for a: String
  for b: String
  {String.order.go(a, b, GT{}) == GT{} : Cmp}

def cfg4.go_gt(a, b):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{_h, _t}:
      {==}
    case SCon{_h, _t} SNil{}:
      {==}
    case SCon{Chr{_x}, _t1} SCon{Chr{_y}, _t2}:
      {==}

# strings whose first characters compare as c and whose compare comes out
# equal: when c is equal and the rest are equal, they are equal
law cfg4.seq.arm:
  for +x: U32
  for +y: U32
  for +t1: String
  for +t2: String
  for c: Cmp
  for ec: {U32.cmp(x, y) == c : Cmp}
  for ih: {String.eq(t1, t2) == True{} : Bool} -> {t1 == t2 : String}
  for e: {Cmp.is_eq(String.order.go(t1, t2, c)) == True{} : Bool}
  {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}

def cfg4.seq.arm(x, y, t1, t2, c, ec, ih, e):
  match c:
    case LT{}:
      g = Equal.cong(Cmp, Bool, z => Cmp.is_eq(z), LT{}, String.order.go(t1, t2, LT{}),
        Equal.sym(Cmp, String.order.go(t1, t2, LT{}), LT{}, cfg4.go_lt(t1, t2)))
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String},
        cfg4.false_true(Equal.trans(Bool, False{}, Cmp.is_eq(String.order.go(t1, t2, LT{})), True{}, g, e)))
    case GT{}:
      g = Equal.cong(Cmp, Bool, z => Cmp.is_eq(z), GT{}, String.order.go(t1, t2, GT{}),
        Equal.sym(Cmp, String.order.go(t1, t2, GT{}), GT{}, cfg4.go_gt(t1, t2)))
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String},
        cfg4.false_true(Equal.trans(Bool, False{}, Cmp.is_eq(String.order.go(t1, t2, GT{})), True{}, g, e)))
    case EQ{}:
      et = ih(e)
      ex = cfg4.ueq(x, y, Equal.cong(Cmp, Bool, z => Cmp.is_eq(z), U32.cmp(x, y), EQ{}, ec))
      %ex : {SCon{Chr{x}, t1} == SCon{Chr{_}, t2} : String}
      %et : {SCon{Chr{x}, t1} == SCon{Chr{x}, _} : String}
      {==}

# strings that compare equal are equal
law cfg4.seq:
  for a: String
  for b: String
  for e: {String.eq(a, b) == True{} : Bool}
  {a == b : String}

def cfg4.seq(a, b, e):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      Empty.absurd({SNil{} == SCon{h, t} : String}, cfg4.false_true(e))
    case SCon{h, t} SNil{}:
      Empty.absurd({SCon{h, t} == SNil{} : String}, cfg4.false_true(e))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      cfg4.seq.arm(x, y, t1, t2, U32.cmp(x, y), {==}, z => cfg4.seq(t1, t2, z), e)

# one row of the table: its config when its directory is the one asked for,
# otherwise what the rows after it give
law cfg4.find.step:
  for b: Bool
  for +d: String
  for +dir: String
  for +world: W.World
  for -rest: List<&2, Plan.Conf>
  for h: {String.eq(d, dir) == b : Bool}
  for ih: {Plan.conf.find(rest, world, dir) == Plan.conf.near(world, dir) : Config.Config}
  {Lazy.stop(Config.Config, b, Plan.conf.near(world, d), _u => Plan.conf.find(rest, world, dir))
    == Plan.conf.near(world, dir) : Config.Config}

def cfg4.find.step(b, d, dir, world, _rest, h, ih):
  match b:
    case True{}:
      Equal.cong(String, Config.Config, z => Plan.conf.near(world, z), d, dir, cfg4.seq(d, dir, h))
    case False{}:
      ih

# the table's config for a directory, held or not, is the one conf.near works
# out for it
law cfg4.find:
  for ds: List<&2, String>
  for +world: W.World
  for +dir: String
  {Plan.conf.find(Plan.confs.at(ds, world), world, dir) == Plan.conf.near(world, dir) : Config.Config}

def cfg4.find(ds, world, dir):
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +tl}:
      cfg4.find.step(String.eq(d, dir), d, dir, world, Plan.confs.at(tl, world), {==}, cfg4.find(tl, world, dir))

# one candidate onto the rest: the World's answer for it decides
law cfg4.first.step:
  for m: Maybe<&2, W.Answer>
  for -ts: List<&2, Maybe<&2, String>>
  for -more: Config.Config
  for ih: {Config.nearest(ts) == more : Config.Config}
  {Config.nearest(W.text.got(m) <> ts) == Laws.first_read.at(m, more) : Config.Config}

def cfg4.first.step(m, _ts, _more, ih):
  match m:
    case None{}:
      ih
    case Some{a}:
      match a:
        case W.Listed{_names}:
          ih
        case W.Read{_text}:
          {==}
        case W.Unread{}:
          ih
        case W.Directory{}:
          ih

# the nearest of the texts the World holds at the candidates is the first
# candidate it read
law cfg4.first:
  for ps: List<&2, String>
  for +world: W.World
  {Config.nearest(Plan.texts.at(ps, world)) == Laws.first_read(world, ps) : Config.Config}

def cfg4.first(ps, world):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +tl}:
      cfg4.first.step(W.answer(world, W.Contents{p}), Plan.texts.at(tl, world), Laws.first_read(world, tl),
        cfg4.first(tl, world))

def Laws.nearest_grades(world, path):
  %Equal.sym(List<&2, Plan.Conf>, Plan.confs(world), Plan.confs.at(Plan.conf.dirs(Plan.inputs(world)), world),
    M9.ri.confs_spec(world)) :
    {Plan.config.at(_, world, path)
      == Laws.first_read(world, Config.chain(Config.home(W.cwd.of(world), Config.dir_of(path)))) : Config.Config}
  Equal.trans(Config.Config, Plan.config.at(Plan.confs.at(Plan.conf.dirs(Plan.inputs(world)), world), world, path),
    Plan.conf.near(world, Config.dir_of(path)),
    Laws.first_read(world, Config.chain(Config.home(W.cwd.of(world), Config.dir_of(path)))),
    cfg4.find(Plan.conf.dirs(Plan.inputs(world)), world, Config.dir_of(path)),
    cfg4.first(Config.chain(Config.home(W.cwd.of(world), Config.dir_of(path))), world))

def Laws.chain_ends_at_root(_dd):
  {==}

def Laws.root_from_the_top(_dd, _acc):
  {==}
