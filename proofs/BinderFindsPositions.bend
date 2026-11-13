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
