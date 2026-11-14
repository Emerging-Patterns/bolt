# proofs of laws/LspSemanticTokensFollowTheLegend.bend
import Base
import ../laws/LspSemanticTokensFollowTheLegend.bend as Laws
import ../src/syntax/bind.bend as Bind
import ../src/lsp/semantic.bend as Semantic

def Laws.token_on_the_same_line(line, col, len, typ, rest, pl, pc, e):
  %Equal.sym(Bool, U32.is_eq(line, pl), True{}, e) :
    {(line - pl : U32) <> (Bool.pick(U32, _, (col - pc : U32), col)
      <> (len <> (typ <> (0 <> Semantic.encode(rest, line, col)))))
      == (line - pl : U32) <> ((col - pc : U32) <> (len <> (typ <> (0 <> Semantic.encode(rest, line, col)))))
      : List<&2, U32>}
  {==}

def Laws.token_on_a_new_line(line, col, len, typ, rest, pl, pc, e):
  %Equal.sym(Bool, U32.is_eq(line, pl), False{}, e) :
    {(line - pl : U32) <> (Bool.pick(U32, _, (col - pc : U32), col)
      <> (len <> (typ <> (0 <> Semantic.encode(rest, line, col)))))
      == (line - pl : U32) <> (col <> (len <> (typ <> (0 <> Semantic.encode(rest, line, col))))) : List<&2, U32>}
  {==}

# an item's index names its entry, whichever way the capital test goes
law item_entry:
  for b: Bool
  {Laws.semantic.entry(Bool.pick(U32, b, 2, 1)) == Some{Bool.pick(String, b, "type", "function")}
    : Maybe<&2, String>}

def item_entry(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.kind_names_its_legend_entry(k, name):
  match k:
    case Bind.KItem{}:
      item_entry(Semantic.upper_first(String.to_list(name)))
    case Bind.KCtor{}:
      {==}
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

# a shape's index names its entry, whichever way its three tests go
law shape_entry:
  for upper: Bool
  for braced: Bool
  for dotted: Bool
  {Laws.semantic.entry(Bool.pick(U32, upper, Bool.pick(U32, braced, 3, 2), Bool.pick(U32, dotted, 1, 5)))
    == Some{Laws.semantic.shape_name(upper, braced, dotted)} : Maybe<&2, String>}

def shape_entry(upper, braced, dotted):
  match upper:
    case True{}:
      match braced:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match dotted:
        case True{}:
          {==}
        case False{}:
          {==}

def Laws.shape_names_its_legend_entry(name, braced):
  shape_entry(Semantic.upper_first(Semantic.last_segment(String.to_list(name), [])), braced,
    String.contains(name, "."))

def Laws.name_takes_its_binder_or_use(_binds, _uses, _all, _name, _line, _col, _braced):
  {==}

def Laws.index_bit_set_goes_low(_lo, _hi):
  {==}

def Laws.index_bit_clear_goes_high(_lo, _hi):
  {==}
