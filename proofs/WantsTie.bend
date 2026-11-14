# proofs of laws/WantsTie.bend
import Base
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ../laws/WantsTie.bend as Laws
import ../laws/UnansweredAreOpenQuestions.bend as L1
import ./UnansweredAreOpenQuestions.bend as PU

# `and` regroups
law lint.and_assoc:
  for a: Bool
  for b: Bool
  for c: Bool
  {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}

def lint.and_assoc(a, _bb, _cc):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# a World answers two lists of questions when it answers each
law lint.all_app:
  for xs: List<&2, W.Ask>
  for +ys: List<&2, W.Ask>
  for +world: W.World
  {Laws.answered_all(world, List.append(&2, W.Ask, xs, ys))
    == Bool.and(Laws.answered_all(world, xs), Laws.answered_all(world, ys)) : Bool}

def lint.all_app(xs, ys, world):
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +tl}:
      e = Equal.sym(Bool, Laws.answered_all(world, List.append(&2, W.Ask, tl, ys)),
        Bool.and(Laws.answered_all(world, tl), Laws.answered_all(world, ys)), lint.all_app(tl, ys, world))
      %e : {Bool.and(W.answered(world, a), _)
        == Bool.and(Bool.and(W.answered(world, a), Laws.answered_all(world, tl)), Laws.answered_all(world, ys)) : Bool}
      lint.and_assoc(W.answered(world, a), Laws.answered_all(world, tl), Laws.answered_all(world, ys))

# one question onto a list the tie holds for
law lint.all_open.step:
  for b: Bool
  for +a: W.Ask
  for -more: Bool
  for +opn: List<&2, W.Ask>
  for ih: {more == List.is_empty(&2, W.Ask, opn) : Bool}
  {Bool.and(b, more) == List.is_empty(&2, W.Ask, Bool.pick(List<&2, W.Ask>, b, opn, a <> opn)) : Bool}

def lint.all_open.step(b, _a, _more, _opn, ih):
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# a World answers every question exactly when the law's walk
# (laws/UnansweredAreOpenQuestions.bend) leaves none open
law lint.all_spec:
  for xs: List<&2, W.Ask>
  for +world: W.World
  {Laws.answered_all(world, xs) == List.is_empty(&2, W.Ask, L1.open(xs, world)) : Bool}

def lint.all_spec(xs, world):
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +tl}:
      lint.all_open.step(W.answered(world, a), a, Laws.answered_all(world, tl), L1.open(tl, world),
        lint.all_spec(tl, world))

# a World answers every question exactly when none is left unanswered
law lint.all_open:
  for +xs: List<&2, W.Ask>
  for +world: W.World
  {Laws.answered_all(world, xs) == List.is_empty(&2, W.Ask, Plan.unanswered(xs, world)) : Bool}

def lint.all_open(xs, world):
  %Equal.sym(List<&2, W.Ask>, Plan.unanswered(xs, world), L1.open(xs, world), L1.unanswered_open(xs, world)) :
    {Laws.answered_all(world, xs) == List.is_empty(&2, W.Ask, _) : Bool}
  lint.all_spec(xs, world)

# wants is empty exactly when no listing and no text is open
law lint.tie_pick:
  for o: List<&2, W.Ask>
  for +world: W.World
  {Bool.and(List.is_empty(&2, W.Ask, o), List.is_empty(&2, W.Ask, Plan.unanswered(Plan.texts(world), world)))
    == List.is_empty(&2, W.Ask, Plan.wants.pick(o, world)) : Bool}

def lint.tie_pick(o, _world):
  match o:
    case Nil{}:
      {==}
    case Con{_a, _tl}:
      {==}

def Laws.wants_tie(world):
  t1 = Equal.sym(Bool, Laws.answered_all(world, Plan.looks(world)),
    Bool.and(Laws.answered_all(world, Plan.lists(world)), Laws.answered_all(world, Plan.texts(world))),
    lint.all_app(Plan.lists(world), Plan.texts(world), world))
  %t1 : {_ == List.is_empty(&2, W.Ask, Plan.wants(world)) : Bool}
  e1 = Equal.sym(Bool, Laws.answered_all(world, Plan.lists(world)),
    List.is_empty(&2, W.Ask, Plan.unanswered(Plan.lists(world), world)), lint.all_open(Plan.lists(world), world))
  %e1 : {Bool.and(_, Laws.answered_all(world, Plan.texts(world))) == List.is_empty(&2, W.Ask, Plan.wants(world))
    : Bool}
  e2 = Equal.sym(Bool, Laws.answered_all(world, Plan.texts(world)),
    List.is_empty(&2, W.Ask, Plan.unanswered(Plan.texts(world), world)), lint.all_open(Plan.texts(world), world))
  %e2 : {Bool.and(List.is_empty(&2, W.Ask, Plan.unanswered(Plan.lists(world), world)), _)
    == List.is_empty(&2, W.Ask, Plan.wants(world)) : Bool}
  lint.tie_pick(Plan.unanswered(Plan.lists(world), world), world)
