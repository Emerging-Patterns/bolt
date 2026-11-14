# the World's index of replies answers as the scan of them does
import Base
import ../../src/lint/world.bend as W
import ../../src/lint/plan.bend as Plan
import ../../src/config.bend as Config
import ../../src/lazy/lazy.bend as Lazy
import ./BinderIndex.bend as M1
import ./InertTextFacts.bend as M2
import ./RoleProofPicked.bend as M3

# The index (src/lint/world.bend). A reply goes down the low bits of its
# question's number to a leaf, and a lookup goes down the asked question's.
# Putting a reply in changes a lookup only when the two numbers agree in
# those bits; a reply the scan stops at asks the same question, so its number
# does agree, and the lookup's leaf holds it ahead of every later reply.

# one level of the index: a lookup that goes down bit b2 past a put that went
# down bit b1 reads the put's half when the bits agree and the half the put
# left alone when they do not
law ri.step:
  for b1: Bool
  for b2: Bool
  for -sub: W.Ix
  for -t: W.Ix
  for -rest: Bool
  for -r: W.Reply
  for -hs: W.Ix -> List<&2, W.Reply>
  for ih: {hs(sub) == Bool.pick(List<&2, W.Reply>, rest, r <> hs(W.ix.near(b1, t)), hs(W.ix.near(b1, t)))
    : List<&2, W.Reply>}
  {hs(W.ix.near(b2, W.ix.join(b1, sub, W.ix.near(Bool.not(b1), t))))
    == Bool.pick(List<&2, W.Reply>, Bool.and(M1.ix.bit(b1, b2), rest), r <> hs(W.ix.near(b2, t)),
      hs(W.ix.near(b2, t))) : List<&2, W.Reply>}

def ri.step(b1, b2, _sub, _tt, _rest, _rr, _hs, ih):
  match b1 b2:
    case True{} True{}:
      ih
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      ih

# a lookup after a put: the reply put in, at the front, when the two numbers
# agree in the bits walked, and what was there before
law ri.put:
  for d: Nat
  for +k1: U32
  for +k2: U32
  for +t: W.Ix
  for +r: W.Reply
  {W.ix.at(d, k2, W.ix.put(d, k1, t, r))
    == Bool.pick(List<&2, W.Reply>, M1.ix.bits(d, k1, k2), r <> W.ix.at(d, k2, t), W.ix.at(d, k2, t))
    : List<&2, W.Reply>}

def ri.put(d, k1, k2, t, r):
  match d:
    case 0n:
      {==}
    case 1n+p:
      ri.step(U32.is_even(k1), U32.is_even(k2),
        W.ix.put(p, U32.shr(k1), W.ix.near(U32.is_even(k1), t), r), t,
        M1.ix.bits(p, U32.shr(k1), U32.shr(k2)), r,
        x => W.ix.at(p, U32.shr(k2), x),
        ri.put(p, U32.shr(k1), U32.shr(k2), W.ix.near(U32.is_even(k1), t), r))

# two questions the scan finds alike are the same question
law ri.same:
  for a: W.Ask
  for b: W.Ask
  for e: {W.ask.eq(a, b) == True{} : Bool}
  {a == b : W.Ask}

def ri.same(a, b, e):
  match a b:
    case W.Entries{x} W.Entries{y}:
      %M3.unsafe.seq(x, y, e) : {W.Entries{x} == W.Entries{_} : W.Ask}
      {==}
    case W.Contents{x} W.Contents{y}:
      %M3.unsafe.seq(x, y, e) : {W.Contents{x} == W.Contents{_} : W.Ask}
      {==}
    case W.Entries{x} W.Contents{y}:
      Empty.absurd({W.Entries{x} == W.Contents{y} : W.Ask}, M2.inert.false_true(e))
    case W.Contents{x} W.Entries{y}:
      Empty.absurd({W.Contents{x} == W.Entries{y} : W.Ask}, M2.inert.false_true(e))

# two questions the scan finds alike have numbers alike in every bit walked
law ri.alike:
  for +qr: W.Ask
  for +q: W.Ask
  for e: {W.ask.eq(qr, q) == True{} : Bool}
  {M1.ix.bits(W.ix.depth(), W.ix.key(qr), W.ix.key(q)) == True{} : Bool}

def ri.alike(qr, q, e):
  %ri.same(qr, q, e) : {M1.ix.bits(W.ix.depth(), W.ix.key(qr), W.ix.key(_)) == True{} : Bool}
  M1.ix.bits_refl(W.ix.depth(), W.ix.key(qr))

# a test that cannot hold leaves a stop to its rest
law ri.miss:
  for s: Bool
  for -yes: Maybe<&2, W.Answer>
  for -no: Maybe<&2, W.Answer>
  for imp: {s == True{} : Bool} -> Empty
  {no == Lazy.stop(Maybe<&2, W.Answer>, s, yes, _u => no) : Maybe<&2, W.Answer>}

def ri.miss(s, yes, no, imp):
  match s:
    case True{}:
      Empty.absurd({no == Lazy.stop(Maybe<&2, W.Answer>, True{}, yes, _u => no) : Maybe<&2, W.Answer>}, imp({==}))
    case False{}:
      {==}

# a leaf that may hold the reply: the scan of it is the scan with the reply
# first, since a reply it leaves out is one the scan passes
law ri.leaf:
  for b: Bool
  for +q: W.Ask
  for +qr: W.Ask
  for +a: W.Answer
  for +more: List<&2, W.Reply>
  for imp: {W.ask.eq(qr, q) == True{} : Bool} -> {b == True{} : Bool}
  {W.answer.in(Bool.pick(List<&2, W.Reply>, b, W.Reply{qr, a} <> more, more), q)
    == W.answer.in(W.Reply{qr, a} <> more, q) : Maybe<&2, W.Answer>}

def ri.leaf(b, q, qr, a, more, imp):
  match b:
    case True{}:
      {==}
    case False{}:
      ri.miss(W.ask.eq(qr, q), Some{a}, W.answer.in(more, q), e => M2.inert.false_true(imp(e)))

# the index's leaf for a question, scanned, is the scan of the replies
law ri.scan:
  for rs: List<&2, W.Reply>
  for +q: W.Ask
  {W.answer.in(W.ix.at(W.ix.depth(), W.ix.key(q), W.ix.of(rs)), q) == W.answer.in(rs, q) : Maybe<&2, W.Answer>}

def ri.scan(rs, q):
  match rs:
    case Nil{}:
      {==}
    case Con{W.Reply{+qr, +a}, +rest}:
      %Equal.sym(List<&2, W.Reply>,
        W.ix.at(W.ix.depth(), W.ix.key(q), W.ix.put(W.ix.depth(), W.ix.key(qr), W.ix.of(rest), W.Reply{qr, a})),
        Bool.pick(List<&2, W.Reply>, M1.ix.bits(W.ix.depth(), W.ix.key(qr), W.ix.key(q)),
          W.Reply{qr, a} <> W.ix.at(W.ix.depth(), W.ix.key(q), W.ix.of(rest)),
          W.ix.at(W.ix.depth(), W.ix.key(q), W.ix.of(rest))),
        ri.put(W.ix.depth(), W.ix.key(qr), W.ix.key(q), W.ix.of(rest), W.Reply{qr, a})) :
        {W.answer.in(_, q) == W.answer.in(W.Reply{qr, a} <> rest, q) : Maybe<&2, W.Answer>}
      %Equal.sym(Maybe<&2, W.Answer>,
        W.answer.in(Bool.pick(List<&2, W.Reply>, M1.ix.bits(W.ix.depth(), W.ix.key(qr), W.ix.key(q)),
          W.Reply{qr, a} <> W.ix.at(W.ix.depth(), W.ix.key(q), W.ix.of(rest)),
          W.ix.at(W.ix.depth(), W.ix.key(q), W.ix.of(rest))), q),
        W.answer.in(W.Reply{qr, a} <> W.ix.at(W.ix.depth(), W.ix.key(q), W.ix.of(rest)), q),
        ri.leaf(M1.ix.bits(W.ix.depth(), W.ix.key(qr), W.ix.key(q)), q, qr, a,
          W.ix.at(W.ix.depth(), W.ix.key(q), W.ix.of(rest)), e => ri.alike(qr, q, e))) :
        {_ == W.answer.in(W.Reply{qr, a} <> rest, q) : Maybe<&2, W.Answer>}
      %Equal.sym(Maybe<&2, W.Answer>, W.answer.in(W.ix.at(W.ix.depth(), W.ix.key(q), W.ix.of(rest)), q),
        W.answer.in(rest, q), ri.scan(rest, q)) :
        {Lazy.stop(Maybe<&2, W.Answer>, W.ask.eq(qr, q), Some{a}, _u => _)
          == W.answer.in(W.Reply{qr, a} <> rest, q) : Maybe<&2, W.Answer>}
      {==}

# a text read off the index is the text the World holds
law ri.text:
  for world: W.World
  for +path: String
  {W.text.ix(W.ix.world(world), path) == W.text(world, path) : Maybe<&2, String>}

def ri.text(world, path):
  match world:
    case W.World{ps, cwd, rs}:
      %Equal.sym(Maybe<&2, W.Answer>,
        W.answer.in(W.ix.at(W.ix.depth(), W.ix.key(W.Contents{path}), W.ix.of(rs)), W.Contents{path}),
        W.answer.in(rs, W.Contents{path}), ri.scan(rs, W.Contents{path})) :
        {W.text.got(_) == W.text(W.World{ps, cwd, rs}, path) : Maybe<&2, String>}
      {==}

# gots off the index are gots
law ri.gots:
  for ps: List<&2, String>
  for +world: W.World
  {Plan.gots.ix(ps, W.ix.world(world)) == Plan.gots(ps, world) : List<&2, Plan.Got>}

def ri.gots(ps, world):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, rest}:
      %Equal.sym(Maybe<&2, String>, W.text.ix(W.ix.world(world), p), W.text(world, p), ri.text(world, p)) :
        {Plan.Got{p, _} <> Plan.gots.ix(rest, W.ix.world(world)) == Plan.gots(p <> rest, world)
          : List<&2, Plan.Got>}
      %Equal.sym(List<&2, Plan.Got>, Plan.gots.ix(rest, W.ix.world(world)), Plan.gots(rest, world),
        ri.gots(rest, world)) :
        {Plan.Got{p, W.text(world, p)} <> _ == Plan.gots(p <> rest, world) : List<&2, Plan.Got>}
      {==}

# texts off the index are texts.at
law ri.texts:
  for ps: List<&2, String>
  for +world: W.World
  {Plan.texts.ix(ps, W.ix.world(world)) == Plan.texts.at(ps, world) : List<&2, Maybe<&2, String>>}

def ri.texts(ps, world):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, rest}:
      %Equal.sym(Maybe<&2, String>, W.text.ix(W.ix.world(world), p), W.text(world, p), ri.text(world, p)) :
        {_ <> Plan.texts.ix(rest, W.ix.world(world)) == Plan.texts.at(p <> rest, world)
          : List<&2, Maybe<&2, String>>}
      %Equal.sym(List<&2, Maybe<&2, String>>, Plan.texts.ix(rest, W.ix.world(world)), Plan.texts.at(rest, world),
        ri.texts(rest, world)) :
        {W.text(world, p) <> _ == Plan.texts.at(p <> rest, world) : List<&2, Maybe<&2, String>>}
      {==}

# a directory's config off the index is its config
law ri.near:
  for +world: W.World
  for +dir: String
  {Plan.conf.near.ix(world, W.ix.world(world), dir) == Plan.conf.near(world, dir) : Config.Config}

def ri.near(world, dir):
  %Equal.sym(List<&2, Maybe<&2, String>>, Plan.texts.ix(Plan.conf.chain(world, dir), W.ix.world(world)),
    Plan.texts.at(Plan.conf.chain(world, dir), world), ri.texts(Plan.conf.chain(world, dir), world)) :
    {Config.nearest(_) == Plan.conf.near(world, dir) : Config.Config}
  {==}

# each directory's config off the index is confs.at
law ri.confs:
  for ds: List<&2, String>
  for +world: W.World
  {Plan.confs.at.ix(ds, world, W.ix.world(world)) == Plan.confs.at(ds, world) : List<&2, Plan.Conf>}

def ri.confs(ds, world):
  match ds:
    case Nil{}:
      {==}
    case Con{+d, rest}:
      %Equal.sym(Config.Config, Plan.conf.near.ix(world, W.ix.world(world), d), Plan.conf.near(world, d),
        ri.near(world, d)) :
        {Plan.Conf{d, _} <> Plan.confs.at.ix(rest, world, W.ix.world(world)) == Plan.confs.at(d <> rest, world)
          : List<&2, Plan.Conf>}
      %Equal.sym(List<&2, Plan.Conf>, Plan.confs.at.ix(rest, world, W.ix.world(world)), Plan.confs.at(rest, world),
        ri.confs(rest, world)) :
        {Plan.Conf{d, Plan.conf.near(world, d)} <> _ == Plan.confs.at(d <> rest, world) : List<&2, Plan.Conf>}
      {==}

# the bolt.bend each directory is graded by, off the index, is conf.used's
law ri.used:
  for ds: List<&2, String>
  for +world: W.World
  {Plan.conf.used.ix(ds, world, W.ix.world(world)) == Plan.conf.used(ds, world) : List<&2, String>}

def ri.used(ds, world):
  match ds:
    case Nil{}:
      {==}
    case Con{d, rest}:
      %Equal.sym(List<&2, Plan.Got>, Plan.gots.ix(Plan.conf.chain(world, d), W.ix.world(world)),
        Plan.gots(Plan.conf.chain(world, d), world), ri.gots(Plan.conf.chain(world, d), world)) :
        {List.append(&2, String, Plan.conf.first(_), Plan.conf.used.ix(rest, world, W.ix.world(world)))
          == Plan.conf.used(d <> rest, world) : List<&2, String>}
      %Equal.sym(List<&2, String>, Plan.conf.used.ix(rest, world, W.ix.world(world)), Plan.conf.used(rest, world),
        ri.used(rest, world)) :
        {List.append(&2, String, Plan.conf.first(Plan.gots(Plan.conf.chain(world, d), world)), _)
          == Plan.conf.used(d <> rest, world) : List<&2, String>}
      {==}

# the configs of the directories grading needs, off the index, are confs.at's
law ri.confs_spec:
  for +world: W.World
  {Plan.confs(world) == Plan.confs.at(Plan.conf.dirs(Plan.inputs(world)), world) : List<&2, Plan.Conf>}

def ri.confs_spec(world):
  ri.confs(Plan.conf.dirs(Plan.inputs(world)), world)

# the bolt.bends grading reads, off the index, are conf.used's, each once
law ri.graders_spec:
  for +world: W.World
  {Plan.graders(world) == Plan.uniq(Plan.conf.used(Plan.conf.dirs(Plan.inputs(world)), world), [])
    : List<&2, String>}

def ri.graders_spec(world):
  %Equal.sym(List<&2, String>, Plan.conf.used.ix(Plan.conf.dirs(Plan.inputs(world)), world, W.ix.world(world)),
    Plan.conf.used(Plan.conf.dirs(Plan.inputs(world)), world), ri.used(Plan.conf.dirs(Plan.inputs(world)), world)) :
    {Plan.uniq(_, []) == Plan.uniq(Plan.conf.used(Plan.conf.dirs(Plan.inputs(world)), world), []) : List<&2, String>}
  {==}
