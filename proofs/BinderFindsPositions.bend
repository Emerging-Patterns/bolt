# proofs of laws/BinderFindsPositions.bend
import Base
import ../src/syntax/bind.bend as Bind
import ../src/lazy/lazy.bend as Lazy
import ../laws/BinderFindsPositions.bend as Laws
import ./lemmas/BoolEmptiness.bend as M1

def Laws.covers_its_own_chars(_l2, _c2, _name, _line, _col):
  {==}

def Laws.before_by_line_then_column(_l1, _c1, _l2, _c2):
  {==}

def Laws.seek_stops_at_or_after(_name, _l, _c, _kind, _note, _rest, _line, _col):
  {==}

def Laws.seek_stops_at_the_end(cur, line, col, e):
  match cur:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Bind.seek.stop(cur, line, col) == True{} : Bool}, M1.false_true(e))

def Laws.seek_head_at_position(_name, _l, _c, _kind, _note, _rest, _line, _col):
  {==}

def Laws.binder_found_where_it_starts(_name, _l, _c, _kind, _note, _rest, _line, _col):
  {==}

def Laws.binder_first_wins(binds, _line, _col, _xx):
  match binds:
    case Nil{}:
      {==}
    case Con{Bind.Bind{_name, _l, _c, _kind, _note}, _rest}:
      {==}

def Laws.sites_take_local_uses(_name, _l, _c, _tl, _tc, _rest, _line, _col):
  {==}

def Laws.sites_skip_other_uses(name, l, c, t, rest, line, col, e):
  match t:
    case Bind.TLocal{tl, tc}:
      Empty.absurd({Bind.sites.go(Bind.Use{name, l, c, Bind.TLocal{tl, tc}} <> rest, line, col)
        == Bind.sites.go(rest, line, col) : List<&2, Bind.Pos>}, M1.true_false(e))
    case Bind.TItem{_n}:
      {==}
    case Bind.TQual{_a, _n}:
      {==}
    case Bind.TFree{}:
      {==}

def Laws.sites_start_at_the_binder(_binds, _uses, _scopes, _line, _col):
  {==}

def Laws.item_sites_take_named_items(n, l, c, kind, note, rest, name, e):
  match kind:
    case Bind.KItem{}:
      {==}
    case Bind.KCtor{}:
      {==}
    case Bind.KParam{}:
      Empty.absurd({Bind.item_sites.binds(Bind.Bind{n, l, c, Bind.KParam{}, note} <> rest, name)
        == Bool.pick(List<&2, Bind.Pos>, String.eq(n, name),
          Bind.Pos{l, c} <> Bind.item_sites.binds(rest, name), Bind.item_sites.binds(rest, name)) : List<&2, Bind.Pos>},
        M1.false_true(e))
    case Bind.KTypeParam{}:
      Empty.absurd({Bind.item_sites.binds(Bind.Bind{n, l, c, Bind.KTypeParam{}, note} <> rest, name)
        == Bool.pick(List<&2, Bind.Pos>, String.eq(n, name),
          Bind.Pos{l, c} <> Bind.item_sites.binds(rest, name), Bind.item_sites.binds(rest, name)) : List<&2, Bind.Pos>},
        M1.false_true(e))
    case Bind.KField{}:
      Empty.absurd({Bind.item_sites.binds(Bind.Bind{n, l, c, Bind.KField{}, note} <> rest, name)
        == Bool.pick(List<&2, Bind.Pos>, String.eq(n, name),
          Bind.Pos{l, c} <> Bind.item_sites.binds(rest, name), Bind.item_sites.binds(rest, name)) : List<&2, Bind.Pos>},
        M1.false_true(e))
    case Bind.KLocal{}:
      Empty.absurd({Bind.item_sites.binds(Bind.Bind{n, l, c, Bind.KLocal{}, note} <> rest, name)
        == Bool.pick(List<&2, Bind.Pos>, String.eq(n, name),
          Bind.Pos{l, c} <> Bind.item_sites.binds(rest, name), Bind.item_sites.binds(rest, name)) : List<&2, Bind.Pos>},
        M1.false_true(e))
    case Bind.KPat{}:
      Empty.absurd({Bind.item_sites.binds(Bind.Bind{n, l, c, Bind.KPat{}, note} <> rest, name)
        == Bool.pick(List<&2, Bind.Pos>, String.eq(n, name),
          Bind.Pos{l, c} <> Bind.item_sites.binds(rest, name), Bind.item_sites.binds(rest, name)) : List<&2, Bind.Pos>},
        M1.false_true(e))
    case Bind.KFor{}:
      Empty.absurd({Bind.item_sites.binds(Bind.Bind{n, l, c, Bind.KFor{}, note} <> rest, name)
        == Bool.pick(List<&2, Bind.Pos>, String.eq(n, name),
          Bind.Pos{l, c} <> Bind.item_sites.binds(rest, name), Bind.item_sites.binds(rest, name)) : List<&2, Bind.Pos>},
        M1.false_true(e))
    case Bind.KTypeVar{}:
      Empty.absurd({Bind.item_sites.binds(Bind.Bind{n, l, c, Bind.KTypeVar{}, note} <> rest, name)
        == Bool.pick(List<&2, Bind.Pos>, String.eq(n, name),
          Bind.Pos{l, c} <> Bind.item_sites.binds(rest, name), Bind.item_sites.binds(rest, name)) : List<&2, Bind.Pos>},
        M1.false_true(e))

def Laws.item_sites_skip_other_binds(n, l, c, kind, note, rest, name, e):
  match kind:
    case Bind.KItem{}:
      Empty.absurd({Bind.item_sites.binds(Bind.Bind{n, l, c, Bind.KItem{}, note} <> rest, name)
        == Bind.item_sites.binds(rest, name) : List<&2, Bind.Pos>}, M1.true_false(e))
    case Bind.KCtor{}:
      Empty.absurd({Bind.item_sites.binds(Bind.Bind{n, l, c, Bind.KCtor{}, note} <> rest, name)
        == Bind.item_sites.binds(rest, name) : List<&2, Bind.Pos>}, M1.true_false(e))
    case Bind.KParam{}:
      {==}
    case Bind.KTypeParam{}:
      {==}
    case Bind.KField{}:
      {==}
    case Bind.KLocal{}:
      {==}
    case Bind.KPat{}:
      {==}
    case Bind.KFor{}:
      {==}
    case Bind.KTypeVar{}:
      {==}

def Laws.item_sites_take_named_uses(_n, _l, _c, _t, _rest, _name):
  {==}

def Laws.item_sites_skip_other_uses(n, l, c, tt, rest, name, e):
  match tt:
    case Bind.TLocal{_tl, _tc}:
      {==}
    case Bind.TItem{t}:
      Empty.absurd({Bind.item_sites.uses(Bind.Use{n, l, c, Bind.TItem{t}} <> rest, name)
        == Bind.item_sites.uses(rest, name) : List<&2, Bind.Pos>}, M1.true_false(e))
    case Bind.TQual{_a, _n}:
      {==}
    case Bind.TFree{}:
      {==}

def Laws.item_sites_binds_then_uses(_binds, _uses, _scopes, _name):
  {==}

def Laws.named_sites_skip_local_uses(_n, _l, _c, _tl, _tc, _rest, _name):
  {==}

def Laws.named_sites_take_named_uses(n, l, c, t, rest, name, e):
  match t:
    case Bind.TLocal{tl, tc}:
      Empty.absurd({Bind.named_sites.go(Bind.Use{n, l, c, Bind.TLocal{tl, tc}} <> rest, name)
        == Bool.pick(List<&2, Bind.Pos>, String.eq(n, name),
          Bind.Pos{l, c} <> Bind.named_sites.go(rest, name), Bind.named_sites.go(rest, name)) : List<&2, Bind.Pos>},
        M1.true_false(e))
    case Bind.TItem{_t}:
      {==}
    case Bind.TQual{_a, _t}:
      {==}
    case Bind.TFree{}:
      {==}

def Laws.named_sites_read_uses(_binds, _uses, _scopes, _name):
  {==}

def Laws.use_at_takes_the_use_that_covers(name, l, c, tg, rest, line, col, e):
  %Equal.sym(Bool, Bind.covers(l, c, name, line, col), True{}, e) :
    {Bind.use_at.go(rest, line, col,
      Bool.pick(Maybe<&2, Bind.Site>, _, Some{Bind.SUse{Bind.Use{name, l, c, tg}}}, None{}))
      == Bind.use_at.go(rest, line, col, Some{Bind.SUse{Bind.Use{name, l, c, tg}}}) : Maybe<&2, Bind.Site>}
  {==}

def Laws.use_at_passes_other_uses(name, l, c, tg, rest, line, col, e):
  %Equal.sym(Bool, Bind.covers(l, c, name, line, col), False{}, e) :
    {Bind.use_at.go(rest, line, col,
      Bool.pick(Maybe<&2, Bind.Site>, _, Some{Bind.SUse{Bind.Use{name, l, c, tg}}}, None{}))
      == Bind.use_at.go(rest, line, col, None{}) : Maybe<&2, Bind.Site>}
  {==}

def Laws.visible_takes_a_scope_at_or_above(line, env, rest, qline, best, e):
  %Equal.sym(Bool, U32.is_le(line, qline), True{}, e) :
    {Bind.visible.go(rest, qline, Bool.pick(List<&2, Bind.Bind>, _, env, best)) == Bind.visible.go(rest, qline, env)
      : List<&2, Bind.Bind>}
  {==}

def Laws.visible_passes_a_scope_below(line, env, rest, qline, best, e):
  %Equal.sym(Bool, U32.is_le(line, qline), False{}, e) :
    {Bind.visible.go(rest, qline, Bool.pick(List<&2, Bind.Bind>, _, env, best)) == Bind.visible.go(rest, qline, best)
      : List<&2, Bind.Bind>}
  {==}

def Laws.annotate_reads_forward(name, line, col, kind, note, rest, lines, at, cur, e):
  %Equal.sym(Bool, U32.is_ge(line, at), True{}, e) :
    {Bind.Bind{name, line, col, kind,
      Bind.note_for(kind, note, _w => Bind.stripped(Lazy.either(String, _,
        _u => Bind.annotate.head(Lazy.either(List<&2, String>, _, _u2 => Bind.annotate.ahead(line, at, cur),
          _v2 => cur)),
        _v => Bind.annotate.back(lines, line))))}
      <> Bind.annotate.go(rest, lines, Bool.pick(U32, _, line, at),
        Lazy.either(List<&2, String>, _, _u => Bind.annotate.ahead(line, at, cur), _v => cur))
      == Bind.Bind{name, line, col, kind,
        Bind.note_for(kind, note, _w => Bind.stripped(Bind.annotate.head(Bind.annotate.ahead(line, at, cur))))}
        <> Bind.annotate.go(rest, lines, line, Bind.annotate.ahead(line, at, cur)) : List<&2, Bind.Bind>}
  {==}

def Laws.annotate_reads_back(name, line, col, kind, note, rest, lines, at, cur, e):
  %Equal.sym(Bool, U32.is_ge(line, at), False{}, e) :
    {Bind.Bind{name, line, col, kind,
      Bind.note_for(kind, note, _w => Bind.stripped(Lazy.either(String, _,
        _u => Bind.annotate.head(Lazy.either(List<&2, String>, _, _u2 => Bind.annotate.ahead(line, at, cur),
          _v2 => cur)),
        _v => Bind.annotate.back(lines, line))))}
      <> Bind.annotate.go(rest, lines, Bool.pick(U32, _, line, at),
        Lazy.either(List<&2, String>, _, _u => Bind.annotate.ahead(line, at, cur), _v => cur))
      == Bind.Bind{name, line, col, kind,
        Bind.note_for(kind, note, _w => Bind.stripped(Bind.annotate.back(lines, line)))}
        <> Bind.annotate.go(rest, lines, at, cur) : List<&2, Bind.Bind>}
  {==}

def Laws.refresh_starts_over_for_an_earlier_binder(name, l, c, kind, note, rest, binds, cur, tl, tc, acc, e):
  %Equal.sym(Bool, Bind.before(l, c, tl, tc), True{}, e) :
    {Bind.refresh.go(rest, binds,
      Bind.seek(Bool.pick(List<&2, Bind.Bind>, _, binds, cur), l, c,
        Bind.seek.stop(Bool.pick(List<&2, Bind.Bind>, _, binds, cur), l, c)), l, c,
      Bind.noted(Bind.seek.head(Bind.seek(Bool.pick(List<&2, Bind.Bind>, _, binds, cur), l, c,
        Bind.seek.stop(Bool.pick(List<&2, Bind.Bind>, _, binds, cur), l, c)), l, c),
        Bind.Bind{name, l, c, kind, note}) <> acc)
      == Bind.refresh.go(rest, binds, Bind.seek(binds, l, c, Bind.seek.stop(binds, l, c)), l, c,
        Bind.noted(Bind.seek.head(Bind.seek(binds, l, c, Bind.seek.stop(binds, l, c)), l, c),
          Bind.Bind{name, l, c, kind, note}) <> acc) : List<&2, Bind.Bind>}
  {==}

def Laws.refresh_reads_on_for_a_later_binder(name, l, c, kind, note, rest, binds, cur, tl, tc, acc, e):
  %Equal.sym(Bool, Bind.before(l, c, tl, tc), False{}, e) :
    {Bind.refresh.go(rest, binds,
      Bind.seek(Bool.pick(List<&2, Bind.Bind>, _, binds, cur), l, c,
        Bind.seek.stop(Bool.pick(List<&2, Bind.Bind>, _, binds, cur), l, c)), l, c,
      Bind.noted(Bind.seek.head(Bind.seek(Bool.pick(List<&2, Bind.Bind>, _, binds, cur), l, c,
        Bind.seek.stop(Bool.pick(List<&2, Bind.Bind>, _, binds, cur), l, c)), l, c),
        Bind.Bind{name, l, c, kind, note}) <> acc)
      == Bind.refresh.go(rest, binds, Bind.seek(cur, l, c, Bind.seek.stop(cur, l, c)), l, c,
        Bind.noted(Bind.seek.head(Bind.seek(cur, l, c, Bind.seek.stop(cur, l, c)), l, c),
          Bind.Bind{name, l, c, kind, note}) <> acc) : List<&2, Bind.Bind>}
  {==}
