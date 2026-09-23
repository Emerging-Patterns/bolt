# bolt/config: what a project asks of bolt, read from the `bolt.bend` nearest
# a file (its own directory, resolved against the working directory by `home`,
# then each parent up to the root: `chain`, read by the caller, then
# `nearest`). The file is plain Bend that
# `bend` can check: a def a setting, its body one string. A group sets every
# rule in it, a rule set by name wins over its group, and an unset group has
# its default (correctness at error, pedantic off, the rest at warn):
#
#     # every rule an error
#     def correctness() -> String:
#       "error"
#     def style() -> String:
#       "error"
#     # but width is advice here
#     def space() -> String:
#       "warn"
#
# A level is "off", "warn" or "error".
import Base
import ../lazy/lazy.bend as Lazy
import ../syntax/lex.bend as Lex
import ../syntax/tree.bend as Tree
import ../syntax/bind.bend as Bind

# how much a finding matters
type Level is Data:
  Off{}
  Warn{}
  Error{}

# a name (a group's or a rule's) at a level
type Set is Data:
  Set{name: String, level: Level}

# the settings, in file order
type Config is Data:
  Config{sets: List<&2, Set>}

# no file: the defaults
def none() -> Config:
  Config{[]}

# the word for a level, as a finding is shown
def show(ll: Level) -> String:
  match ll:
    case Off{}:
      "off"
    case Warn{}:
      "warning"
    case Error{}:
      "error"

# is it an error?
def is_error(ll: Level) -> Bool:
  match ll:
    case Error{}:
      True{}
    case other:
      False{}

# is it off?
def is_off(ll: Level) -> Bool:
  match ll:
    case Off{}:
      True{}
    case other:
      False{}

# reading the file
# ----------------

# a level by its word; an unknown word is an error, so a typo shows
def of_word(+ww: String) -> Level:
  Bool.pick(Level, String.eq(ww, "off"), Off{}, Bool.pick(Level, String.eq(ww, "warn"), Warn{}, Error{}))

# a string literal's text, its quotes dropped
def unquote(+tt: String) -> String:
  Bool.pick(String, Bool.and(String.starts_with(tt, "\""), String.ends_with(tt, "\"")),
    String.take(String.drop(tt, 1n), (String.length(tt) - 2n : Nat)), tt)

# the first string among the tokens
def first_str(toks: List<&2, Lex.Tok>) -> Maybe<&2, String>:
  match toks:
    case Nil{}:
      None{}
    case Con{Lex.Tok{Lex.TStr{}, t, l, c}, rest}:
      Some{unquote(t)}
    case Con{h, rest}:
      first_str(rest)

# a def's name and the string it returns, as a setting
def setting(name: Maybe<&2, String>, word: Maybe<&2, String>) -> List<&2, Set>:
  match name word:
    case Some{n} Some{w}:
      [Set{n, of_word(w)}]
    case a b:
      []

# every `def x(): "level"` of a tree
def sets(root: Tree.Node) -> List<&2, Set>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest}:
      List.append(&2, Set, setting(Bind.declared(kids), first_str(Tree.leaves(body))), sets(rest))
    case Tree.NCons{h, rest}:
      sets(rest)
    case other:
      Nil{}

# a bolt.bend's text as a config
def parse(text: String) -> Config:
  Config{sets(Tree.parse(text))}

# a path's directory, with its slash; `` at the top
def dir_of.go(cs: List<&2, Char>, +acc: List<&2, Char>, best: List<&2, Char>) -> String:
  match cs:
    case Nil{}:
      String.from_list(List.reverse(&2, Char, best))
    case Con{'/', t}:
      dir_of.go(t, '/' <> acc, '/' <> acc)
    case Con{c, t}:
      dir_of.go(t, c <> acc, best)

# a path's directory, with its slash; `` at the top
def dir_of(path: String) -> String:
  dir_of.go(String.to_list(path), [], [])

# the parent directory of a directory (`a/b/` -> `a/`; `` -> ``)
def parent(+dir: String) -> String:
  dir_of(String.take(dir, (String.length(dir) - 1n : Nat)))

# the top: nothing above `` or `/`
def is_top(+dir: String) -> Bool:
  Bool.or(String.is_empty(dir), String.eq(dir, "/"))

# the bolt.bend of a directory and of each parent, nearest first
def candidates(fuel: Nat, +dir: String) -> List<&2, String>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      (dir ++ "bolt.bend") <> Lazy.stop(List<&2, String>, is_top(dir), [], _u => candidates(f, parent(dir)))

# resolving a path
# ----------------
# A path is resolved against the working directory before its candidates are
# taken, so the file's own directory and its real parents are tried wherever
# bolt runs from: `a.bend` from `/w/p/sub` is graded by `/w/p/sub/bolt.bend`,
# then `/w/p/bolt.bend`, `/w/bolt.bend` and `/bolt.bend`. `.` and `..` are read
# lexically, as ruff and `path.resolve` in node read them: a symbolic link is
# not followed.

# a path from the root: itself when it starts there, otherwise under the
# working directory
def absolute(+cwd: String, +path: String) -> String:
  Bool.pick(String, String.starts_with(path, "/"), path, cwd ++ "/" ++ path)

# the directories above the innermost one; none above the root
def home.up(above: List<&2, String>) -> List<&2, String>:
  match above:
    case Nil{}:
      Nil{}
    case Con{_d, rest}:
      rest

# a path's segment read onto the directories before it, innermost first: an
# empty segment (from `//` or the `/` a directory ends in) and `.` stay where
# they are, `..` goes up one (never above the root), and a name goes into it
def home.step(+seg: String, +above: List<&2, String>) -> List<&2, String>:
  Bool.pick(List<&2, String>, Bool.or(String.is_empty(seg), String.eq(seg, ".")), above,
    Bool.pick(List<&2, String>, String.eq(seg, ".."), home.up(above), seg <> above))

# the directories a path names, innermost first: its segments, split at `/`,
# each read by `home.step` onto those before it (seg holds the segment being
# read, reversed)
def home.segs(cs: List<&2, Char>, seg: List<&2, Char>, above: List<&2, String>) -> List<&2, String>:
  match cs:
    case Nil{}:
      home.step(String.from_list(List.reverse(&2, Char, seg)), above)
    case Con{'/', t}:
      home.segs(t, [], home.step(String.from_list(List.reverse(&2, Char, seg)), above))
    case Con{c, t}:
      home.segs(t, c <> seg, above)

# a directory resolved against the working directory, as the names of the
# directories from the root to it, innermost first: `sub/../p3/` under
# `/w/p1` is `[p3, w]`, and `` is the working directory itself
def home(cwd: String, dir: String) -> List<&2, String>:
  home.segs(String.to_list(absolute(cwd, dir)), [], [])

# directories, innermost first, as a path from the root ending in `/`
def root(ds: List<&2, String>, acc: String) -> String:
  match ds:
    case Nil{}:
      "/" ++ acc
    case Con{d, rest}:
      root(rest, d ++ "/" ++ acc)

# the bolt.bend of a resolved directory (innermost first, as `home` gives it)
# and of each parent up to the root, nearest first: `[p3, w]` is
# `/w/p3/bolt.bend`, `/w/bolt.bend`, `/bolt.bend`
def chain(ds: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      ["/bolt.bend"]
    case Con{d, +rest}:
      (root(d <> rest, "") ++ "bolt.bend") <> chain(rest)

# the first file that was there, parsed; none, the defaults
def nearest(rs: List<&2, Maybe<&2, String>>) -> Config:
  match rs:
    case Nil{}:
      none()
    case Con{Some{text}, rest}:
      parse(text)
    case Con{None{}, rest}:
      nearest(rest)

# levels
# ------

# the level a name is set to, when it is
def set_level(sets: List<&2, Set>, +name: String) -> Maybe<&2, Level>:
  match sets:
    case Nil{}:
      None{}
    case Con{Set{+n, l}, rest}:
      +more = set_level(rest, name)
      Bool.pick(Maybe<&2, Level>, String.eq(n, name), Some{l}, more)

# a group's level when nothing sets it
def default(+group: String) -> Level:
  Bool.pick(Level, String.eq(group, "correctness"), Error{},
    Bool.pick(Level, String.eq(group, "pedantic"), Off{}, Warn{}))

# a rule only its own setting turns on: a group setting, or the group's
# default, would put new findings on projects that never asked for it
def opt_in(+rule: String) -> Bool:
  String.eq(rule, "trace")

# the rule's own setting, else its group's, else the group's default; an
# opt-in rule's own setting, else off
def level.of(+sets: List<&2, Set>, +group: String, +rule: String) -> Level:
  Maybe.default(&2, Level, set_level(sets, rule),
    Lazy.stop(Level, opt_in(rule), Off{}, _u => Maybe.default(&2, Level, set_level(sets, group), default(group))))

# the rule's own setting, else its group's, else the group's default
def level(cfg: Config, group: String, rule: String) -> Level:
  Config{ss} = cfg
  level.of(ss, group, rule)
