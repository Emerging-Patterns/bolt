# proofs of laws/UnansweredAreOpenQuestions.bend
import Base
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/bind.bend as Bind
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ../laws/UnansweredAreOpenQuestions.bend as Laws
import ../laws/BinderIndexFindsItems.bend as L1
import ./lemmas/BinderIndex.bend as M1
import ./lemmas/BinderIndexIsContains.bend as M2

# unanswered puts the directories the replies list and the paths they read
# each in the binder's index, and a question asks the index of its own kind.
# The index holds a name exactly when the scan of the names finds it
# (laws/BinderIndexFindsItems.bend), and the scan of the replies' directories
# (or paths) finds one exactly when some reply answers that question.

# one reply further: the scan of the names stops where the scan of the
# replies does
law ua.step:
  for b: Bool
  for -a: W.Answer
  for -h: Bool
  for -m: Maybe<&2, W.Answer>
  for ih: {h == Maybe.is_some(&2, W.Answer, m) : Bool}
  {Lazy.or_else(b, _u => h)
    == Maybe.is_some(&2, W.Answer, Lazy.stop(Maybe<&2, W.Answer>, b, Some{a}, _u => m)) : Bool}

def ua.step(b, _a, _h, _m, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# a directory is among those the replies list exactly when a reply lists it
law ua.dirs:
  for rs: List<&2, W.Reply>
  for +d: String
  {Bind.has_item(Plan.unanswered.dirs(rs), d) == Maybe.is_some(&2, W.Answer, W.answer.in(rs, W.Entries{d})) : Bool}

def ua.dirs(rs, d):
  match rs:
    case Nil{}:
      {==}
    case Con{W.Reply{W.Entries{+x}, +a}, +rest}:
      %Equal.sym(Bool, Bind.same(x, d), String.eq(x, d), M2.ic.alike(x, d)) :
        {Lazy.or_else(_, _u => Bind.has_item(Plan.unanswered.dirs(rest), d))
          == Maybe.is_some(&2, W.Answer, W.answer.in(W.Reply{W.Entries{x}, a} <> rest, W.Entries{d})) : Bool}
      ua.step(String.eq(x, d), a, Bind.has_item(Plan.unanswered.dirs(rest), d), W.answer.in(rest, W.Entries{d}),
        ua.dirs(rest, d))
    case Con{W.Reply{W.Contents{_p}, _a}, +rest}:
      ua.dirs(rest, d)

# a path is among those the replies read exactly when a reply reads it
law ua.paths:
  for rs: List<&2, W.Reply>
  for +p: String
  {Bind.has_item(Plan.unanswered.paths(rs), p) == Maybe.is_some(&2, W.Answer, W.answer.in(rs, W.Contents{p}))
    : Bool}

def ua.paths(rs, p):
  match rs:
    case Nil{}:
      {==}
    case Con{W.Reply{W.Entries{_d}, _a}, +rest}:
      ua.paths(rest, p)
    case Con{W.Reply{W.Contents{+x}, +a}, +rest}:
      %Equal.sym(Bool, Bind.same(x, p), String.eq(x, p), M2.ic.alike(x, p)) :
        {Lazy.or_else(_, _u => Bind.has_item(Plan.unanswered.paths(rest), p))
          == Maybe.is_some(&2, W.Answer, W.answer.in(W.Reply{W.Contents{x}, a} <> rest, W.Contents{p})) : Bool}
      ua.step(String.eq(x, p), a, Bind.has_item(Plan.unanswered.paths(rest), p), W.answer.in(rest, W.Contents{p}),
        ua.paths(rest, p))

# a question asks the index of its own kind what the scan of the replies
# would answer
law ua.hit:
  for aa: W.Ask
  for +rs: List<&2, W.Reply>
  {Plan.unanswered.hit(aa, Bind.index(Plan.unanswered.dirs(rs)), Bind.index(Plan.unanswered.paths(rs)))
    == Maybe.is_some(&2, W.Answer, W.answer.in(rs, aa)) : Bool}

def ua.hit(aa, rs):
  match aa:
    case W.Entries{+d}:
      Equal.trans(Bool, Bind.indexed(Bind.index(Plan.unanswered.dirs(rs)), d),
        Bind.has_item(Plan.unanswered.dirs(rs), d), Maybe.is_some(&2, W.Answer, W.answer.in(rs, W.Entries{d})),
        L1.index_finds(Plan.unanswered.dirs(rs), d), ua.dirs(rs, d))
    case W.Contents{+p}:
      Equal.trans(Bool, Bind.indexed(Bind.index(Plan.unanswered.paths(rs)), p),
        Bind.has_item(Plan.unanswered.paths(rs), p), Maybe.is_some(&2, W.Answer, W.answer.in(rs, W.Contents{p})),
        L1.index_finds(Plan.unanswered.paths(rs), p), ua.paths(rs, p))

# the walk over the indexes keeps what the law's walk over the World keeps
law ua.fast:
  for asks: List<&2, W.Ask>
  for +paths: List<&2, String>
  for +cwd: String
  for +rs: List<&2, W.Reply>
  {Plan.unanswered.fast(asks, Bind.index(Plan.unanswered.dirs(rs)), Bind.index(Plan.unanswered.paths(rs)))
    == Laws.open(asks, W.World{paths, cwd, rs}) : List<&2, W.Ask>}

def ua.fast(asks, paths, cwd, rs):
  match asks:
    case Nil{}:
      {==}
    case Con{+a, +rest}:
      +dx = Bind.index(Plan.unanswered.dirs(rs))
      +px = Bind.index(Plan.unanswered.paths(rs))
      +fast = Plan.unanswered.fast(rest, dx, px)
      %Equal.sym(Bool, Plan.unanswered.hit(a, dx, px), Maybe.is_some(&2, W.Answer, W.answer.in(rs, a)),
        ua.hit(a, rs)) :
        {Bool.pick(List<&2, W.Ask>, _, fast, a <> fast) == Laws.open(a <> rest, W.World{paths, cwd, rs})
          : List<&2, W.Ask>}
      %Equal.sym(List<&2, W.Ask>, fast, Laws.open(rest, W.World{paths, cwd, rs}), ua.fast(rest, paths, cwd, rs)) :
        {Bool.pick(List<&2, W.Ask>, Maybe.is_some(&2, W.Answer, W.answer.in(rs, a)), _, a <> _)
          == Laws.open(a <> rest, W.World{paths, cwd, rs}) : List<&2, W.Ask>}
      {==}

def Laws.unanswered_open(asks, world):
  match world:
    case W.World{+paths, +cwd, +rs}:
      ua.fast(asks, paths, cwd, rs)
