# src/config: what a project asks of bolt, read from the `bolt.bend` nearest
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
# A level is "off", "warn" or "error". A setting whose name is no rule's slug
# and no group is `unknown`, and sets nothing.
#
# A def whose body is a number sets a limit, the most a rule lets by:
#
#     # a one-character name may be read 30 lines below its binder here
#     def reach_max() -> U32:
#       30
#
# A rule with a limit names it `<slug>_max`; unset, the rule's own default
# holds. A number bolt cannot read as a U32 is 0, so a typo shows.
import Base
import ./lazy/lazy.bend as Lazy
import ./syntax/lex.bend as Lex
import ./rchars.bend as Rchars
import ./syntax/tree.bend as Tree
import ./syntax/bind.bend as Bind
import ./codes.bend as Codes

# how much a finding matters
type Level is Data:
  Off{}
  Warn{}
  Error{}

# a name (a group's or a rule's) at a level
type LevelSet is Data:
  LevelSet{name: String, level: Level}

# a limit's name (`reach_max`) and the most it lets by
type Limit is Data:
  Limit{name: String, max: U32}

# the settings and the limits, each in file order
type Config is Data:
  Config{sets: List<&2, LevelSet>, lims: List<&2, Limit>}

# no file: the defaults
def none() -> Config:
  Config{[], []}

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

# a setting as a bolt.bend writes it: the def's name, the word its body
# returns, and the line of its `def` (0-based)
type Setting is Data:
  Setting{name: String, word: String, line: U32}

# a def's name and the string it returns, at its line, as a setting
def setting(name: Maybe<&2, String>, word: Maybe<&2, String>, +line: U32) -> List<&2, Setting>:
  match name word:
    case Some{n} Some{w}:
      [Setting{n, w, line}]
    case _a _b:
      []

# every `def x(): "level"` of a tree
def settings.go(root: Tree.Node) -> List<&2, Setting>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, +kids, body}, rest}:
      +ln = Tree.line(kids)
      List.append(&2, Setting, setting(Bind.declared(kids), first_str(Tree.leaves(body)), ln), settings.go(rest))
    case Tree.NCons{_h, rest}:
      settings.go(rest)
    case _other:
      Nil{}

# every setting of a bolt.bend's text, in file order
def settings(text: String) -> List<&2, Setting>:
  settings.go(Tree.parse(text))

# each setting as the level it sets its name to
def levels(ss: List<&2, Setting>) -> List<&2, LevelSet>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{Setting{n, w, _line}, rest}:
      LevelSet{n, of_word(w)} <> levels(rest)

# the first number among the tokens
def first_num(toks: List<&2, Lex.Tok>) -> Maybe<&2, String>:
  match toks:
    case Nil{}:
      None{}
    case Con{Lex.Tok{Lex.TNum{}, t, l, c}, rest}:
      Some{t}
    case Con{h, rest}:
      first_num(rest)

# a number as a limit reads it: 0 when it is no U32, so a typo shows
def limit.read(word: String) -> U32:
  Maybe.default(&2, U32, U32.read(word), 0)

# a def's name and the number it returns, as a limit
def limit.one(name: Maybe<&2, String>, word: Maybe<&2, String>) -> List<&2, Limit>:
  match name word:
    case Some{n} Some{w}:
      [Limit{n, limit.read(w)}]
    case _a _b:
      []

# every `def x_max(): 30` of a tree
def limits.go(root: Tree.Node) -> List<&2, Limit>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest}:
      List.append(&2, Limit, limit.one(Bind.declared(kids), first_num(Tree.leaves(body))), limits.go(rest))
    case Tree.NCons{_h, rest}:
      limits.go(rest)
    case _other:
      Nil{}

# every limit of a bolt.bend's text, in file order
def limits(text: String) -> List<&2, Limit>:
  limits.go(Tree.parse(text))

# a bolt.bend's text as a config: its settings, each at its level, and its
# limits
def parse(+text: String) -> Config:
  Config{levels(settings(text)), limits(text)}

# unknown names
# -------------
# A name a bolt.bend may set is a rule's slug or a group, as the code table
# (src/codes.bend) lists them; a setting of any other name sets nothing, so
# `setting` (C011) reports it.

# some row of the table has the name as its group
def known.group(rows: List<&2, Codes.Entry>, +name: String) -> Bool:
  match rows:
    case Nil{}:
      False{}
    case Con{Codes.Entry{_s, _id, +grp}, rest}:
      Lazy.or_else(String.eq(grp, name), _u => known.group(rest, name))

# some row of the table has the name as its slug or its group
def known.in(+rows: List<&2, Codes.Entry>, +name: String) -> Bool:
  +slug = Maybe.is_some(&2, Codes.Entry, Codes.find(rows, name))
  +grp = known.group(rows, name)
  Bool.or(slug, grp)

# the settings, in order, whose name no row of the table has as its slug or
# its group
def unknown.in(ss: List<&2, Setting>, +rows: List<&2, Codes.Entry>) -> List<&2, Setting>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{Setting{+n, w, line}, rest}:
      +more = unknown.in(rest, rows)
      Bool.pick(List<&2, Setting>, known.in(rows, n),
        more, Setting{n, w, line} <> more)

# the settings, in order, whose name is neither a rule's slug nor a group of
# the code table
def unknown(ss: List<&2, Setting>) -> List<&2, Setting>:
  unknown.in(ss, Codes.table())

# a path's directory, with its slash; `` at the top
def dir_of.go(cs: List<&2, Char>, +acc: List<&2, Char>, best: List<&2, Char>) -> String:
  match cs:
    case Nil{}:
      Rchars.text(best)
    case Con{'/', t}:
      dir_of.go(t, '/' <> acc, '/' <> acc)
    case Con{c, t}:
      dir_of.go(t, c <> acc, best)

# a path's directory, with its slash; `` at the top
def dir_of(path: String) -> String:
  dir_of.go(String.to_list(path), [], [])

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
      home.step(Rchars.text(seg), above)
    case Con{'/', t}:
      home.segs(t, [], home.step(Rchars.text(seg), above))
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

# the level a name is set to, when it is; hit: the setting before sets
# named it, so the search stops there
def set_level.go(sets: List<&2, LevelSet>, +name: String, hit: Maybe<&2, Level>) -> Maybe<&2, Level>:
  match sets:
    case Nil{}:
      hit
    case Con{LevelSet{+n, l}, rest}:
      match hit:
        case Some{x}:
          Some{x}
        case None{}:
          set_level.go(rest, name, Bool.pick(Maybe<&2, Level>, String.eq(n, name), Some{l}, None{}))

# the level a name is set to, when it is: the first setting that names it
def set_level(sets: List<&2, LevelSet>, +name: String) -> Maybe<&2, Level>:
  set_level.go(sets, name, None{})

# a group's level when nothing sets it
def default(+group: String) -> Level:
  Bool.pick(Level, String.eq(group, "correctness"), Error{},
    Bool.pick(Level, String.eq(group, "pedantic"), Off{}, Warn{}))

# a rule only its own setting turns on: a group setting, or the group's
# default, would put new findings on projects that never asked for it
# (`thunk`, `transcong`, and the laws' `coverage` and `closed`, which are a
# project's policy rather than defects)
def opt_in(+rule: String) -> Bool:
  List.contains(~String, ~String.eq, ["thunk", "transcong", "coverage", "closed"], rule)

# the rule's own setting, else its group's, else the group's default; an
# opt-in rule's own setting, else off
def level.of(+sets: List<&2, LevelSet>, +group: String, +rule: String) -> Level:
  Maybe.default(&2, Level, set_level(sets, rule),
    Lazy.stop(Level, opt_in(rule), Off{}, _u => Maybe.default(&2, Level, set_level(sets, group), default(group))))

# the rule's own setting, else its group's, else the group's default
def level(cfg: Config, group: String, rule: String) -> Level:
  Config{ss, _lims} = cfg
  level.of(ss, group, rule)

# limits
# ------

# the first limit of the name, else the base
def limit.of(lims: List<&2, Limit>, +name: String, base: U32) -> U32:
  match lims:
    case Nil{}:
      base
    case Con{Limit{n, m}, rest}:
      Lazy.stop(U32, String.eq(n, name), m, _u => limit.of(rest, name, base))

# the limit a config sets for a name: its first of that name, else the
# rule's own default
def limit(cfg: Config, name: String, base: U32) -> U32:
  Config{_ss, lims} = cfg
  limit.of(lims, name, base)
