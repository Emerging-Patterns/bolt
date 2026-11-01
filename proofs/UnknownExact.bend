# proofs of laws/UnknownExact.bend
import Base
import ../src/lazy/lazy.bend as Lazy
import ../src/config.bend as Config
import ../src/codes.bend as Codes
import ../laws/UnknownExact.bend as Laws

# Unknown names (laws/ConfigUnknownSettingsFound.bend). config.bend looks a slug up with Codes.find and
# a group with an early-exit fold; the spec folds both strictly. Each step
# lemma takes the comparison it branches on as a variable and cases on it.

# one row onto the slug lookup: the table finds a row exactly when the spec
# says one has the slug
law cfg7.slug.step:
  for bb: Bool
  for -row: Codes.Entry
  for rest: List<&2, Codes.Entry>
  for +name: String
  for -sl: Bool
  for ih: {Maybe.is_some(&2, Codes.Entry, Codes.find(rest, name)) == sl : Bool}
  {Maybe.is_some(&2, Codes.Entry, Lazy.stop(Maybe<&2, Codes.Entry>, bb, Some{row}, _u => Codes.find(rest, name)))
    == Bool.or(bb, sl) : Bool}

def cfg7.slug.step(bb, _row, _rest, _name, _sl, ih):
  match bb:
    case True{}:
      {==}
    case False{}:
      ih

# the table finds a row by a slug exactly when some row has it
law cfg7.slug:
  for rows: List<&2, Codes.Entry>
  for +name: String
  {Maybe.is_some(&2, Codes.Entry, Codes.find(rows, name)) == Laws.slug_in(rows, name) : Bool}

def cfg7.slug(rows, name):
  match rows:
    case Nil{}:
      {==}
    case Con{Codes.Entry{+s, +id, +grp}, +tl}:
      cfg7.slug.step(String.eq(s, name), Codes.Entry{s, id, grp}, tl, name, Laws.slug_in(tl, name), cfg7.slug(tl, name))

# one row onto the group lookup
law cfg7.group.step:
  for bb: Bool
  for rest: List<&2, Codes.Entry>
  for +name: String
  for -gl: Bool
  for ih: {Config.known.group(rest, name) == gl : Bool}
  {Lazy.or_else(bb, _u => Config.known.group(rest, name)) == Bool.or(bb, gl) : Bool}

def cfg7.group.step(bb, _rest, _name, _gl, ih):
  match bb:
    case True{}:
      {==}
    case False{}:
      ih

# a name is some row's group exactly when the spec says so
law cfg7.group:
  for rows: List<&2, Codes.Entry>
  for +name: String
  {Config.known.group(rows, name) == Laws.group_in(rows, name) : Bool}

def cfg7.group(rows, name):
  match rows:
    case Nil{}:
      {==}
    case Con{Codes.Entry{_s, _id, +grp}, +tl}:
      cfg7.group.step(String.eq(grp, name), tl, name, Laws.group_in(tl, name), cfg7.group(tl, name))

# a name is known exactly when some row has it as its slug or its group
law cfg7.known:
  for +rows: List<&2, Codes.Entry>
  for +name: String
  {Config.known.in(rows, name) == Bool.or(Laws.slug_in(rows, name), Laws.group_in(rows, name)) : Bool}

def cfg7.known(rows, name):
  a = Equal.sym(Bool, Maybe.is_some(&2, Codes.Entry, Codes.find(rows, name)), Laws.slug_in(rows, name),
    cfg7.slug(rows, name))
  %a : {Bool.or(_, Config.known.group(rows, name)) == Bool.or(Laws.slug_in(rows, name), Laws.group_in(rows, name))
    : Bool}
  b = Equal.sym(Bool, Config.known.group(rows, name), Laws.group_in(rows, name), cfg7.group(rows, name))
  %b : {Bool.or(Laws.slug_in(rows, name), _) == Bool.or(Laws.slug_in(rows, name), Laws.group_in(rows, name)) : Bool}
  {==}

def Laws.unknown_exact(ss):
  match ss:
    case Nil{}:
      {==}
    case Con{Config.Setting{+n, +w, +line}, +tl}:
      k = Equal.sym(Bool, Config.known.in(Codes.table(), n),
        Bool.or(Laws.slug_in(Codes.table(), n), Laws.group_in(Codes.table(), n)), cfg7.known(Codes.table(), n))
      %k : {Bool.pick(List<&2, Config.Setting>, _, Config.unknown.in(tl, Codes.table()),
          Config.Setting{n, w, line} <> Config.unknown.in(tl, Codes.table()))
        == Laws.unknown_of(Config.Setting{n, w, line} <> tl) : List<&2, Config.Setting>}
      r = Equal.sym(List<&2, Config.Setting>, Config.unknown.in(tl, Codes.table()), Laws.unknown_of(tl),
        Laws.unknown_exact(tl))
      %r : {Bool.pick(List<&2, Config.Setting>,
          Bool.or(Laws.slug_in(Codes.table(), n), Laws.group_in(Codes.table(), n)),
          _, Config.Setting{n, w, line} <> _)
        == Laws.unknown_of(Config.Setting{n, w, line} <> tl) : List<&2, Config.Setting>}
      {==}
