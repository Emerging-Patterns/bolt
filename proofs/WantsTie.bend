# proofs of laws/WantsTie.bend
import Base
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ../laws/WantsTie.bend as Laws

# `and` regroups
law lint.and_assoc:
  for aa: Bool
  for bb: Bool
  for cc: Bool
  {Bool.and(aa, Bool.and(bb, cc)) == Bool.and(Bool.and(aa, bb), cc) : Bool}

def lint.and_assoc(aa, _bb, _cc):
  match aa:
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
  for bb: Bool
  for +a: W.Ask
  for -more: Bool
  for +opn: List<&2, W.Ask>
  for ih: {more == List.is_empty(&2, W.Ask, opn) : Bool}
  {Bool.and(bb, more) == List.is_empty(&2, W.Ask, Bool.pick(List<&2, W.Ask>, bb, opn, a <> opn)) : Bool}

def lint.all_open.step(bb, _a, _more, _opn, ih):
  match bb:
    case True{}:
      ih
    case False{}:
      {==}

# a World answers every question exactly when none is left unanswered
law lint.all_open:
  for xs: List<&2, W.Ask>
  for +world: W.World
  {Laws.answered_all(world, xs) == List.is_empty(&2, W.Ask, Plan.unanswered(xs, world)) : Bool}

def lint.all_open(xs, world):
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +tl}:
      lint.all_open.step(W.answered(world, a), a, Laws.answered_all(world, tl), Plan.unanswered(tl, world),
        lint.all_open(tl, world))

# wants is empty exactly when no listing and no text is open
law lint.tie_pick:
  for oo: List<&2, W.Ask>
  for +world: W.World
  {Bool.and(List.is_empty(&2, W.Ask, oo), List.is_empty(&2, W.Ask, Plan.unanswered(Plan.texts(world), world)))
    == List.is_empty(&2, W.Ask, Plan.wants.pick(oo, world)) : Bool}

def lint.tie_pick(oo, _world):
  match oo:
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
