# src/lint/world: everything `bolt` reads, as one value. The planner
# (src/lint/plan.bend) is a pure function of a World; the interpreter
# (src/lint.bend) gathers one, answering each question the planner asks by
# IO, and prints the plan the planner returns. The design is
# docs/rfc/bolt-lint-planner.md.
#
# The World holds only what the lint reads: the paths named on the command
# line, the working directory they are named from, and every answer the
# interpreter gave. A question with no answer yet reads as a directory with no
# entries or a file that cannot be read.
import Base
import ../lazy/lazy.bend as Lazy

# a question the planner asks. Each is answered by one IO action: a
# directory listed (src/walk/), or a file read (src/lsp/files/).
type Ask is Data:
  Entries{dir: String}
  Contents{path: String}

# the answer to one question. A directory that cannot be opened lists as
# empty, as src/walk/dir.c answers. A text asked of a path that is a
# directory is `Directory`, not a read: it has no text.
type Answer is Data:
  Listed{names: List<&2, String>}
  Read{text: String}
  Unread{}
  Directory{}

# one question, answered
type Reply is Data:
  Reply{ask: Ask, answer: Answer}

# everything `bolt` reads: the paths named on the command line, the working
# directory (absolute) that relative paths are named from, and every answer
# the interpreter gave, in the order it gave them
type World is Data:
  World{paths: List<&2, String>, cwd: String, replies: List<&2, Reply>}

# the paths named on the command line
def paths.of(world: World) -> List<&2, String>:
  World{paths, _cwd, _replies} = world
  paths

# the working directory the run was started in
def cwd.of(world: World) -> String:
  World{_paths, cwd, _replies} = world
  cwd

# whether two questions are the same question
def ask.eq(aa: Ask, bb: Ask) -> Bool:
  match aa bb:
    case Entries{x1} Entries{y1}:
      String.eq(x1, y1)
    case Contents{x2} Contents{y2}:
      String.eq(x2, y2)
    case Entries{_x3} Contents{_y3}:
      False{}
    case Contents{_x4} Entries{_y4}:
      False{}

# the first answer given to a question
def answer.in(rs: List<&2, Reply>, +ask: Ask) -> Maybe<&2, Answer>:
  match rs:
    case Nil{}:
      None{}
    case Con{Reply{q, a}, rest}:
      Lazy.stop(Maybe<&2, Answer>, ask.eq(q, ask), Some{a}, _u => answer.in(rest, ask))

# the answer a World holds for a question, None while there is none
def answer(world: World, +ask: Ask) -> Maybe<&2, Answer>:
  World{_paths, _cwd, rs} = world
  answer.in(rs, ask)

# whether a World answers a question
def answered(world: World, +ask: Ask) -> Bool:
  Maybe.is_some(&2, Answer, answer(world, ask))

# a listing's names; anything else lists nothing
def listing.answer(aa: Answer) -> List<&2, String>:
  match aa:
    case Listed{names}:
      names
    case Read{_text}:
      []
    case Unread{}:
      []
    case Directory{}:
      []

def listing.got(mm: Maybe<&2, Answer>) -> List<&2, String>:
  match mm:
    case None{}:
      []
    case Some{aa}:
      listing.answer(aa)

# a directory's entries, a sub-directory's name ending in "/"; none while
# the directory is not listed yet
def listing(world: World, dir: String) -> List<&2, String>:
  listing.got(answer(world, Entries{dir}))

# a read's text; anything else is no text
def text.answer(aa: Answer) -> Maybe<&2, String>:
  match aa:
    case Listed{_names}:
      None{}
    case Read{tt}:
      Some{tt}
    case Unread{}:
      None{}
    case Directory{}:
      None{}

def text.got(mm: Maybe<&2, Answer>) -> Maybe<&2, String>:
  match mm:
    case None{}:
      None{}
    case Some{aa}:
      text.answer(aa)

# a file's text, or None when it could not be read, is a directory, or is
# not read yet
def text(world: World, path: String) -> Maybe<&2, String>:
  text.got(answer(world, Contents{path}))

# The replies, indexed. A question is looked up once per source, per
# bolt.bend candidate of each directory, and a scan of every reply for each
# is the questions times the replies: on a project of 4,062 files, 4.4 s to
# find which bolt.bend grades each of its 733 directories, and 3 s to read
# their configs. So the replies are put in a trie on the low bits of each
# question's number, each leaf the replies whose question lands there, in
# their order, and a lookup scans only its own leaf. Two questions alike have
# the same number, so the leaf holds every reply the scan would stop at, and
# its first such reply is the scan's (proofs/lemmas/ReplyIndex.bend).
type Ix is Data:
  INone{}
  ILeaf{rs: List<&2, Reply>}
  INode{lo: Ix, hi: Ix}

# how many bits of a question's number the index branches on
def ix.depth() -> Nat:
  12n

# a path's number: its chars folded, each onto 31 times the number so far
def ix.key.go(name: String, +acc: U32) -> U32:
  match name:
    case SNil{}:
      acc
    case SCon{Chr{x}, rest}:
      ix.key.go(rest, (acc * 31 + x : U32))

# a question's number: its path's
def ix.key(aa: Ask) -> U32:
  match aa:
    case Entries{d}:
      ix.key.go(d, 7)
    case Contents{p}:
      ix.key.go(p, 7)

# the replies at a leaf, none elsewhere
def ix.rs(ix: Ix) -> List<&2, Reply>:
  match ix:
    case INone{}:
      Nil{}
    case ILeaf{rs}:
      rs
    case INode{_lo, _hi}:
      Nil{}

# the half a bit picks: an even bit the low half
def ix.pick(bb: Bool, lo: Ix, hi: Ix) -> Ix:
  match bb:
    case True{}:
      lo
    case False{}:
      hi

# the half of a node a bit picks; none below anything else
def ix.near(bb: Bool, ix: Ix) -> Ix:
  match ix:
    case INode{lo, hi}:
      ix.pick(bb, lo, hi)
    case other:
      INone{}

# a node from the half a bit picks and the other half
def ix.join(bb: Bool, sub: Ix, far: Ix) -> Ix:
  match bb:
    case True{}:
      INode{sub, far}
    case False{}:
      INode{far, sub}

# a reply put at the front of the leaf its number's low bits lead to
def ix.put(dd: Nat, +kk: U32, +ix: Ix, rr: Reply) -> Ix:
  match dd:
    case 0n:
      ILeaf{rr <> ix.rs(ix)}
    case 1n+p:
      ix.join(U32.is_even(kk), ix.put(p, U32.shr(kk), ix.near(U32.is_even(kk), ix), rr),
        ix.near(Bool.not(U32.is_even(kk)), ix))

# the replies at the leaf a number's low bits lead to
def ix.at(dd: Nat, +kk: U32, ix: Ix) -> List<&2, Reply>:
  match dd:
    case 0n:
      ix.rs(ix)
    case 1n+p:
      ix.at(p, U32.shr(kk), ix.near(U32.is_even(kk), ix))

# the index of these replies, each leaf in their order
def ix.of(rs: List<&2, Reply>) -> Ix:
  match rs:
    case Nil{}:
      INone{}
    case Con{Reply{+q, a}, rest}:
      ix.put(ix.depth(), ix.key(q), ix.of(rest), Reply{q, a})

# a World's replies, indexed
def ix.world(world: World) -> Ix:
  World{_paths, _cwd, rs} = world
  ix.of(rs)

# the first answer to a question, read off its leaf: answer's
def answer.ix(ix: Ix, +ask: Ask) -> Maybe<&2, Answer>:
  answer.in(ix.at(ix.depth(), ix.key(ask), ix), ask)

# a file's text, read off the index: text's
def text.ix(ix: Ix, path: String) -> Maybe<&2, String>:
  text.got(answer.ix(ix, Contents{path}))
