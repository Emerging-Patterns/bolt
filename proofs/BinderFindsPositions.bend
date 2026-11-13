# proofs of laws/BinderFindsPositions.bend
import Base
import ../src/syntax/bind.bend as Bind
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

def Laws.sites_skip_other_uses(name, l, c, tt, rest, line, col, e):
  match tt:
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

def Laws.named_sites_take_named_uses(n, l, c, tt, rest, name, e):
  match tt:
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
