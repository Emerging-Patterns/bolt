# Where a name is. The language server's hover, definition, references and
# rename all start from a position in the text and ask the binder what is
# there (laws/LspNavigationUsesBinder.bend). A name covers the positions from
# its first column up to, and not including, the column past its last char,
# on its own line. The binder at a position is the first binder that starts
# exactly there. A binder's sites are its own position and then the position
# of every use that resolves to it, in the order of the uses. Positions are
# ordered by line, then by column.
import Base
import ../src/syntax/bind.bend as Bind

# does a use resolve to a binder of the file? Law vocabulary: bolt never
# calls it
def positions.is_local(tt: Bind.Target) -> Bool:
  match tt:
    case Bind.TLocal{_l, _c}:
      True{}
    case _other:
      False{}

# LAW: a name at (l2, c2) covers (line, col) exactly when they are on one
# line and col is at or after the name's first column and before the column
# past its last char
law covers_its_own_chars:
  for +l2: U32
  for +c2: U32
  for +name: String
  for +line: U32
  for +col: U32
  {Bind.covers(l2, c2, name, line, col)
    == Bool.and(U32.is_eq(l2, line),
      Bool.and(U32.is_le(c2, col), U32.is_lt(col, (c2 + U32.from_nat(String.length(name)) : U32)))) : Bool}

# LAW: one position comes before another when its line does, or on the same
# line when its column does
law before_by_line_then_column:
  for +l1: U32
  for +c1: U32
  for +l2: U32
  for +c2: U32
  {Bind.before(l1, c1, l2, c2) == Bool.or(U32.is_lt(l1, l2), Bool.and(U32.is_eq(l1, l2), U32.is_lt(c1, c2)))
    : Bool}

# LAW: a search for a position stops at the first binder that is not before
# it
law seek_stops_at_or_after:
  for name: String
  for +l: U32
  for +c: U32
  for kind: Bind.BindKind
  for note: String
  for rest: List<&2, Bind.Bind>
  for +line: U32
  for +col: U32
  {Bind.seek.stop(Bind.Bind{name, l, c, kind, note} <> rest, line, col) == Bool.not(Bind.before(l, c, line, col))
    : Bool}

# LAW: with no binder left, the search stops
law seek_stops_at_the_end:
  for cur: List<&2, Bind.Bind>
  for +line: U32
  for +col: U32
  for e: {List.is_empty(&2, Bind.Bind, cur) == True{} : Bool}
  {Bind.seek.stop(cur, line, col) == True{} : Bool}

# LAW: the binder at the head of a cursor is the one at a position exactly
# when it starts on that line at that column
law seek_head_at_position:
  for name: String
  for +l: U32
  for +c: U32
  for kind: Bind.BindKind
  for note: String
  for rest: List<&2, Bind.Bind>
  for +line: U32
  for +col: U32
  {Bind.seek.head(Bind.Bind{name, l, c, kind, note} <> rest, line, col)
    == Bool.pick(Maybe<&2, Bind.Bind>, Bool.and(U32.is_eq(l, line), U32.is_eq(c, col)),
      Some{Bind.Bind{name, l, c, kind, note}}, None{}) : Maybe<&2, Bind.Bind>}

# LAW: looking for the binder at a position, a binder that starts exactly
# there is found, and any other is passed over
law binder_found_where_it_starts:
  for name: String
  for +l: U32
  for +c: U32
  for kind: Bind.BindKind
  for note: String
  for rest: List<&2, Bind.Bind>
  for +line: U32
  for +col: U32
  {Bind.binder.go(Bind.Bind{name, l, c, kind, note} <> rest, line, col, None{})
    == Bind.binder.go(rest, line, col,
      Bool.pick(Maybe<&2, Bind.Bind>, Bool.and(U32.is_eq(l, line), U32.is_eq(c, col)),
        Some{Bind.Bind{name, l, c, kind, note}}, None{})) : Maybe<&2, Bind.Bind>}

# LAW: once a binder is found the search keeps it: the first one wins
law binder_first_wins:
  for binds: List<&2, Bind.Bind>
  for +line: U32
  for +col: U32
  for xx: Bind.Bind
  {Bind.binder.go(binds, line, col, Some{xx}) == Some{xx} : Maybe<&2, Bind.Bind>}

# LAW: a use that resolves to the binder at (line, col) is one of its sites,
# at the use's own position, in the order of the uses
law sites_take_local_uses:
  for name: String
  for l: U32
  for c: U32
  for +tl: U32
  for +tc: U32
  for rest: List<&2, Bind.Use>
  for +line: U32
  for +col: U32
  {Bind.sites.go(Bind.Use{name, l, c, Bind.TLocal{tl, tc}} <> rest, line, col)
    == Bool.pick(List<&2, Bind.Pos>, Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col)),
      Bind.Pos{l, c} <> Bind.sites.go(rest, line, col), Bind.sites.go(rest, line, col)) : List<&2, Bind.Pos>}

# LAW: a use that resolves to anything else (an item, an alias, nothing
# known) is no binder's site
law sites_skip_other_uses:
  for name: String
  for l: U32
  for c: U32
  for tt: Bind.Target
  for rest: List<&2, Bind.Use>
  for +line: U32
  for +col: U32
  for e: {positions.is_local(tt) == False{} : Bool}
  {Bind.sites.go(Bind.Use{name, l, c, tt} <> rest, line, col) == Bind.sites.go(rest, line, col)
    : List<&2, Bind.Pos>}

# LAW: a binder's sites are its own position, then its uses'
law sites_start_at_the_binder:
  for binds: List<&2, Bind.Bind>
  for uses: List<&2, Bind.Use>
  for scopes: List<&2, Bind.Scope>
  for +line: U32
  for +col: U32
  {Bind.sites(Bind.Bound{binds, uses, scopes}, line, col) == Bind.Pos{line, col} <> Bind.sites.go(uses, line, col)
    : List<&2, Bind.Pos>}
