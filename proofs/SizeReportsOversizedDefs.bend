# proofs of laws/SizeReportsOversizedDefs.bend
import Base
import ../src/finding.bend as F
import ../src/paths.bend as Paths
import ../src/src.bend as Src
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/style/size.bend as Size
import ../laws/SizeReportsOversizedDefs.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

# a def that is exempt adds nothing, and one that is not adds one exactly
# when it is over
law size.step:
  for x: Bool
  for g: Bool
  for -dim: Size.Dim
  for -name: String
  for -line: U32
  for -size: U32
  for -max: U32
  for -path: String
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding,
      Lazy.stop(List<&2, F.Finding>, x, more, _u => Size.found(g, dim, name, line, size, max, path, more)))
    == Bool.pick(Nat, Bool.and(Bool.not(x), g), 1n+m, m) : Nat}

def size.step(x, g, _dim, _name, _line, _size, _max, _path, more, m, ih):
  match x:
    case True{}:
      ih
    case False{}:
      match g:
        case True{}:
          Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
        case False{}:
          ih

def Laws.size_counts(ds, dim, path, max):
  match ds:
    case Nil{}:
      {==}
    case Con{Calls.Def{name, +sig, +body}, +rest}:
      size.step(Calls.exempt(path, sig), U32.is_gt(Size.measure(dim, sig, body), max), dim, name, Tree.line(sig),
        Size.measure(dim, sig, body), max, path, Size.check.go(rest, dim, path, max),
        Laws.over_count(rest, dim, path, max), Laws.size_counts(rest, dim, path, max))

# the walk gathers nothing in a law file
law size.none:
  for ds: List<&2, Calls.Def>
  for +dim: Size.Dim
  for +path: String
  for +max: U32
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {Size.check.go(ds, dim, path, max) == Nil{} : List<&2, F.Finding>}

def size.none(ds, dim, path, max, e):
  match ds:
    case Nil{}:
      {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      s = Equal.sym(Bool, Calls.exempt(path, sig), True{}, M1.ex.calls(path, sig, e))
      %s : {Lazy.stop(List<&2, F.Finding>, _, Size.check.go(rest, dim, path, max),
          _u => Size.sized(dim, name, Tree.line(sig), Size.measure(dim, sig, body), max, path,
            Size.check.go(rest, dim, path, max)))
        == Nil{} : List<&2, F.Finding>}
      size.none(rest, dim, path, max, e)

def Laws.size_exempt(dim, max, path, _text, _toks, tree, _bound, _items, e):
  size.none(Calls.defs(tree), dim, path, max, e)

def Laws.role_size(dim, max, path, text, toks, tree, bound, items):
  M1.role.skip_named(path, _u => Size.check(dim, Src.Src{path, text, toks, tree, bound, items}, max),
    e => Laws.size_exempt(dim, max, path, text, toks, tree, bound, items, e))

def Laws.arity_skips_type_parameter(pp, ps, acc, e):
  s = Equal.sym(Bool, String.is_empty(Calls.param_name(pp)), True{}, e)
  %s : {Size.arity.go(ps, Bool.pick(U32, _, acc, (acc + 1 : U32))) == Size.arity.go(ps, acc) : U32}
  {==}

def Laws.arity_counts_named_parameter(pp, ps, acc, e):
  s = Equal.sym(Bool, String.is_empty(Calls.param_name(pp)), False{}, e)
  %s : {Size.arity.go(ps, Bool.pick(U32, _, acc, (acc + 1 : U32))) == Size.arity.go(ps, (acc + 1 : U32)) : U32}
  {==}

def Laws.last_takes_later_line(_k, _t, l, _c, best, e):
  s = Equal.sym(Bool, U32.is_gt(l, best), True{}, e)
  %s : {Bool.pick(U32, _, l, best) == l : U32}
  {==}

def Laws.last_keeps_earlier_line(_k, _t, l, _c, best, e):
  s = Equal.sym(Bool, U32.is_gt(l, best), False{}, e)
  %s : {Bool.pick(U32, _, l, best) == best : U32}
  {==}

def Laws.depth_block_goes_down(_kind, kids, body, rest, at, best, e):
  s = Equal.sym(Bool, Calls.has_colon(kids), True{}, e)
  %s : {Size.depth(rest, at, Size.depth(body, Size.depth.under(_, at), Size.most(at, best)))
    == Size.depth(rest, at, Size.depth(body, (at + 1 : U32), Size.most(at, best))) : U32}
  {==}

def Laws.depth_wrapped_line_stays(_kind, kids, body, rest, at, best, e):
  s = Equal.sym(Bool, Calls.has_colon(kids), False{}, e)
  %s : {Size.depth(rest, at, Size.depth(body, Size.depth.under(_, at), Size.most(at, best)))
    == Size.depth(rest, at, Size.depth(body, at, Size.most(at, best))) : U32}
  {==}
