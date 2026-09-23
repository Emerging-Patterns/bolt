# bolt/lint/world: everything `bolt` reads, as one value. The planner
# (bolt/lint/plan.bend) is a pure function of a World; the interpreter
# (bolt/lint.bend) gathers one, answering each question the planner asks by
# IO, and prints the plan the planner returns. The design is
# docs/rfc/bolt-lint-planner.md.
#
# The World holds only what the lint reads: the paths named on the command
# line, the working directory they are named from, and every answer the
# interpreter gave. A question with no answer yet reads as a directory with no
# entries or a file that cannot be read.
import Base
import ../../lazy/lazy.bend as Lazy

# a question the planner asks. Each is answered by one IO action: a
# directory listed (bolt/walk/), or a file read (bolt/lsp/files/).
type Ask is Data:
  Entries{dir: String}
  Text{path: String}

# the answer to one question. A directory that cannot be opened lists as
# empty, as bolt/walk/dir.c answers. A text asked of a path that is a
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
    case Text{x2} Text{y2}:
      String.eq(x2, y2)
    case Entries{_x3} Text{_y3}:
      False{}
    case Text{_x4} Entries{_y4}:
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
  text.got(answer(world, Text{path}))
