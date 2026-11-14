# Where a name is. The language server's hover, definition, references and
# rename all start from a position in the text and ask the binder what is
# there (laws/LspNavigationUsesBinder.bend). A name covers the positions from
# its first column up to, and not including, the column past its last char,
# on its own line. The binder at a position is the first binder that starts
# exactly there. A binder's sites are its own position and then the position
# of every use that resolves to it, in the order of the uses. An item's
# sites are every declaration of an item or a constructor by its name, then
# every use that resolves to an item by its name, each in order. A name not
# of the file has as its sites every use of that name that does not resolve
# to a local binder. Positions are ordered by line, then by column.
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

# does a binder declare an item or a constructor? Law vocabulary: bolt never
# calls it
def positions.is_item(kk: Bind.BindKind) -> Bool:
  match kk:
    case Bind.KItem{}:
      True{}
    case Bind.KCtor{}:
      True{}
    case _other:
      False{}

# does a use resolve to an item of the file? Law vocabulary: bolt never
# calls it
def positions.is_item_use(tt: Bind.Target) -> Bool:
  match tt:
    case Bind.TItem{_n}:
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

# LAW: an item or constructor declared by the name is one of the item's
# sites, at its own position, in the order of the binders
law item_sites_take_named_items:
  for +n: String
  for +l: U32
  for +c: U32
  for kind: Bind.BindKind
  for note: String
  for rest: List<&2, Bind.Bind>
  for +name: String
  for e: {positions.is_item(kind) == True{} : Bool}
  {Bind.item_sites.binds(Bind.Bind{n, l, c, kind, note} <> rest, name)
    == Bool.pick(List<&2, Bind.Pos>, String.eq(n, name),
      Bind.Pos{l, c} <> Bind.item_sites.binds(rest, name), Bind.item_sites.binds(rest, name)) : List<&2, Bind.Pos>}

# LAW: any other binder (a parameter, a local, a field..) is no item's site
law item_sites_skip_other_binds:
  for n: String
  for l: U32
  for c: U32
  for kind: Bind.BindKind
  for note: String
  for rest: List<&2, Bind.Bind>
  for +name: String
  for e: {positions.is_item(kind) == False{} : Bool}
  {Bind.item_sites.binds(Bind.Bind{n, l, c, kind, note} <> rest, name) == Bind.item_sites.binds(rest, name)
    : List<&2, Bind.Pos>}

# LAW: a use that resolves to the item by its name is one of its sites, at
# the use's own position, in the order of the uses
law item_sites_take_named_uses:
  for n: String
  for +l: U32
  for +c: U32
  for +t: String
  for rest: List<&2, Bind.Use>
  for +name: String
  {Bind.item_sites.uses(Bind.Use{n, l, c, Bind.TItem{t}} <> rest, name)
    == Bool.pick(List<&2, Bind.Pos>, String.eq(t, name),
      Bind.Pos{l, c} <> Bind.item_sites.uses(rest, name), Bind.item_sites.uses(rest, name)) : List<&2, Bind.Pos>}

# LAW: a use that resolves to anything but an item is no item's site
law item_sites_skip_other_uses:
  for n: String
  for l: U32
  for c: U32
  for tt: Bind.Target
  for rest: List<&2, Bind.Use>
  for +name: String
  for e: {positions.is_item_use(tt) == False{} : Bool}
  {Bind.item_sites.uses(Bind.Use{n, l, c, tt} <> rest, name) == Bind.item_sites.uses(rest, name)
    : List<&2, Bind.Pos>}

# LAW: an item's sites are its declarations, then its uses
law item_sites_binds_then_uses:
  for binds: List<&2, Bind.Bind>
  for uses: List<&2, Bind.Use>
  for scopes: List<&2, Bind.Scope>
  for +name: String
  {Bind.item_sites(Bind.Bound{binds, uses, scopes}, name)
    == List.append(&2, Bind.Pos, Bind.item_sites.binds(binds, name), Bind.item_sites.uses(uses, name))
    : List<&2, Bind.Pos>}

# LAW: a use that resolves to a local binder is no foreign name's site
law named_sites_skip_local_uses:
  for n: String
  for l: U32
  for c: U32
  for tl: U32
  for tc: U32
  for rest: List<&2, Bind.Use>
  for +name: String
  {Bind.named_sites.go(Bind.Use{n, l, c, Bind.TLocal{tl, tc}} <> rest, name) == Bind.named_sites.go(rest, name)
    : List<&2, Bind.Pos>}

# LAW: any other use of the name is one of its sites, at the use's own
# position, in the order of the uses
law named_sites_take_named_uses:
  for +n: String
  for +l: U32
  for +c: U32
  for tt: Bind.Target
  for rest: List<&2, Bind.Use>
  for +name: String
  for e: {positions.is_local(tt) == False{} : Bool}
  {Bind.named_sites.go(Bind.Use{n, l, c, tt} <> rest, name)
    == Bool.pick(List<&2, Bind.Pos>, String.eq(n, name),
      Bind.Pos{l, c} <> Bind.named_sites.go(rest, name), Bind.named_sites.go(rest, name)) : List<&2, Bind.Pos>}

# LAW: a foreign name's sites are read off the uses alone
law named_sites_read_uses:
  for binds: List<&2, Bind.Bind>
  for uses: List<&2, Bind.Use>
  for scopes: List<&2, Bind.Scope>
  for +name: String
  {Bind.named_sites(Bind.Bound{binds, uses, scopes}, name) == Bind.named_sites.go(uses, name) : List<&2, Bind.Pos>}

# LAW: a use whose name covers the position is the one found, and the search
# goes on only to hand it back
law use_at_takes_the_use_that_covers:
  for +name: String
  for +ll: U32
  for +cc: U32
  for +tg: Bind.Target
  for +rest: List<&2, Bind.Use>
  for +line: U32
  for +col: U32
  for e: {Bind.covers(ll, cc, name, line, col) == True{} : Bool}
  {Bind.use_at.go(Bind.Use{name, ll, cc, tg} <> rest, line, col, None{})
    == Bind.use_at.go(rest, line, col, Some{Bind.SUse{Bind.Use{name, ll, cc, tg}}}) : Maybe<&2, Bind.Site>}

# LAW: a use that does not cover it is passed over
law use_at_passes_other_uses:
  for +name: String
  for +ll: U32
  for +cc: U32
  for +tg: Bind.Target
  for +rest: List<&2, Bind.Use>
  for +line: U32
  for +col: U32
  for e: {Bind.covers(ll, cc, name, line, col) == False{} : Bool}
  {Bind.use_at.go(Bind.Use{name, ll, cc, tg} <> rest, line, col, None{})
    == Bind.use_at.go(rest, line, col, None{}) : Maybe<&2, Bind.Site>}

# LAW: the names in scope at a line are those of the last statement at or
# above it: a scope on or before the line replaces what was found
law visible_takes_a_scope_at_or_above:
  for +line: U32
  for +env: List<&2, Bind.Bind>
  for +rest: List<&2, Bind.Scope>
  for +qline: U32
  for +best: List<&2, Bind.Bind>
  for e: {U32.is_le(line, qline) == True{} : Bool}
  {Bind.visible.go(Bind.Scope{line, env} <> rest, qline, best) == Bind.visible.go(rest, qline, env)
    : List<&2, Bind.Bind>}

# LAW: a scope below the line leaves it
law visible_passes_a_scope_below:
  for +line: U32
  for +env: List<&2, Bind.Bind>
  for +rest: List<&2, Bind.Scope>
  for +qline: U32
  for +best: List<&2, Bind.Bind>
  for e: {U32.is_le(line, qline) == False{} : Bool}
  {Bind.visible.go(Bind.Scope{line, env} <> rest, qline, best) == Bind.visible.go(rest, qline, best)
    : List<&2, Bind.Bind>}

# LAW: a binder at or past the line last read takes its note from the lines
# read forward from there, and the next binder reads on from its line
law annotate_reads_forward:
  for +name: String
  for +line: U32
  for +col: U32
  for +kind: Bind.BindKind
  for +note: String
  for +rest: List<&2, Bind.Bind>
  for +lines: List<&2, String>
  for +at: U32
  for +cur: List<&2, String>
  for e: {U32.is_ge(line, at) == True{} : Bool}
  {Bind.annotate.go(Bind.Bind{name, line, col, kind, note} <> rest, lines, at, cur)
    == Bind.Bind{name, line, col, kind,
      Bind.note_for(kind, note, _w => Bind.stripped(Bind.annotate.head(Bind.annotate.ahead(line, at, cur))))}
      <> Bind.annotate.go(rest, lines, line, Bind.annotate.ahead(line, at, cur)) : List<&2, Bind.Bind>}

# LAW: a binder behind that line reads its own line from the top, and the
# next binder reads on from where the reading stood
law annotate_reads_back:
  for +name: String
  for +line: U32
  for +col: U32
  for +kind: Bind.BindKind
  for +note: String
  for +rest: List<&2, Bind.Bind>
  for +lines: List<&2, String>
  for +at: U32
  for +cur: List<&2, String>
  for e: {U32.is_ge(line, at) == False{} : Bool}
  {Bind.annotate.go(Bind.Bind{name, line, col, kind, note} <> rest, lines, at, cur)
    == Bind.Bind{name, line, col, kind,
      Bind.note_for(kind, note, _w => Bind.stripped(Bind.annotate.back(lines, line)))}
      <> Bind.annotate.go(rest, lines, at, cur) : List<&2, Bind.Bind>}

# LAW: a scope's binder that stands before the one read last is looked up
# from the first binder again
law refresh_starts_over_for_an_earlier_binder:
  for +name: String
  for +ll: U32
  for +cc: U32
  for +kind: Bind.BindKind
  for +note: String
  for +rest: List<&2, Bind.Bind>
  for +binds: List<&2, Bind.Bind>
  for +cur: List<&2, Bind.Bind>
  for +tl: U32
  for +tc: U32
  for +acc: List<&2, Bind.Bind>
  for e: {Bind.before(ll, cc, tl, tc) == True{} : Bool}
  {Bind.refresh.go(Bind.Bind{name, ll, cc, kind, note} <> rest, binds, cur, tl, tc, acc)
    == Bind.refresh.go(rest, binds, Bind.seek(binds, ll, cc, Bind.seek.stop(binds, ll, cc)), ll, cc,
      Bind.noted(Bind.seek.head(Bind.seek(binds, ll, cc, Bind.seek.stop(binds, ll, cc)), ll, cc),
        Bind.Bind{name, ll, cc, kind, note}) <> acc) : List<&2, Bind.Bind>}

# LAW: any other is looked up on from where the last one was found
law refresh_reads_on_for_a_later_binder:
  for +name: String
  for +ll: U32
  for +cc: U32
  for +kind: Bind.BindKind
  for +note: String
  for +rest: List<&2, Bind.Bind>
  for +binds: List<&2, Bind.Bind>
  for +cur: List<&2, Bind.Bind>
  for +tl: U32
  for +tc: U32
  for +acc: List<&2, Bind.Bind>
  for e: {Bind.before(ll, cc, tl, tc) == False{} : Bool}
  {Bind.refresh.go(Bind.Bind{name, ll, cc, kind, note} <> rest, binds, cur, tl, tc, acc)
    == Bind.refresh.go(rest, binds, Bind.seek(cur, ll, cc, Bind.seek.stop(cur, ll, cc)), ll, cc,
      Bind.noted(Bind.seek.head(Bind.seek(cur, ll, cc, Bind.seek.stop(cur, ll, cc)), ll, cc),
        Bind.Bind{name, ll, cc, kind, note}) <> acc) : List<&2, Bind.Bind>}
