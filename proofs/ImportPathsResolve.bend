# proofs of laws/ImportPathsResolve.bend
import Base
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/imports.bend as Imports
import ../src/syntax/outline.bend as Outline
import ../laws/ImportPathsResolve.bend as Laws
import ./lemmas/BoolEmptiness.bend as M1

# import paths (laws/ImportPathsResolve.bend). Each law is one arm of the
# code read for the segment or item it names; a hypothesis about a test
# rewrites that test to the value it is given.

def Laws.put_pops(_h, _t):
  {==}

def Laws.put_stays_at_top(acc, e):
  match acc:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Imports.norm.put("..", acc) == Nil{} : List<&2, String>}, M1.false_true(e))

def Laws.put_skips_dot(acc):
  match acc:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      {==}

def Laws.put_skips_empty(acc):
  match acc:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      {==}

def Laws.put_keeps(ss, acc, e1, e2, e3):
  match acc:
    case Nil{}:
      %Equal.sym(Bool, String.eq(ss, ".."), False{}, e1) :
        {Bool.pick(List<&2, String>, Bool.or(_, Bool.or(String.eq(ss, "."), String.is_empty(ss))), [], [ss])
          == ss <> Nil{} : List<&2, String>}
      %Equal.sym(Bool, String.eq(ss, "."), False{}, e2) :
        {Bool.pick(List<&2, String>, Bool.or(False{}, Bool.or(_, String.is_empty(ss))), [], [ss])
          == ss <> Nil{} : List<&2, String>}
      %Equal.sym(Bool, String.is_empty(ss), False{}, e3) :
        {Bool.pick(List<&2, String>, Bool.or(False{}, Bool.or(False{}, _)), [], [ss]) == ss <> Nil{}
          : List<&2, String>}
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, String.eq(ss, ".."), False{}, e1) :
        {Bool.pick(List<&2, String>, _, t,
          Bool.pick(List<&2, String>, Bool.or(String.eq(ss, "."), String.is_empty(ss)), h <> t, ss <> (h <> t)))
          == ss <> (h <> t) : List<&2, String>}
      %Equal.sym(Bool, String.eq(ss, "."), False{}, e2) :
        {Bool.pick(List<&2, String>, Bool.or(_, String.is_empty(ss)), h <> t, ss <> (h <> t)) == ss <> (h <> t)
          : List<&2, String>}
      %Equal.sym(Bool, String.is_empty(ss), False{}, e3) :
        {Bool.pick(List<&2, String>, Bool.or(False{}, _), h <> t, ss <> (h <> t)) == ss <> (h <> t)
          : List<&2, String>}
      {==}

def Laws.go_reads_in_order(_s, _rest, _acc):
  {==}

def Laws.go_ends_in_order(_acc):
  {==}

def Laws.norm_reads_segments(_path):
  {==}

def Laws.init_keeps_first(_h, _m, _t):
  {==}

def Laws.init_drops_last(_h):
  {==}

def Laws.dir_is_all_but_last(_path):
  {==}

def Laws.resolve_from_directory(_from, _rel):
  {==}

def Laws.targets_take_relative(_name, _line, _sig, _doc, path, rest, from, e):
  %Equal.sym(Bool, String.starts_with(path, "."), True{}, e) :
    {Lazy.stop(List<&2, String>, Bool.not(_), Imports.targets(rest, from),
      _u => Imports.resolve(from, path) <> Imports.targets(rest, from))
      == Imports.resolve(from, path) <> Imports.targets(rest, from) : List<&2, String>}
  {==}

def Laws.targets_skip_packages(_name, _line, _sig, _doc, path, rest, from, e):
  %Equal.sym(Bool, String.starts_with(path, "."), False{}, e) :
    {Lazy.stop(List<&2, String>, Bool.not(_), Imports.targets(rest, from),
      _u => Imports.resolve(from, path) <> Imports.targets(rest, from))
      == Imports.targets(rest, from) : List<&2, String>}
  {==}

def Laws.targets_skip_other_items(kk, name, line, sig, doc, path, rest, from, e):
  match kk:
    case Outline.IImport{}:
      Empty.absurd({Imports.targets(Outline.Item{Outline.IImport{}, name, line, sig, doc, path} <> rest, from)
        == Imports.targets(rest, from) : List<&2, String>}, M1.true_false(e))
    case Outline.IDef{}:
      {==}
    case Outline.ILaw{}:
      {==}
    case Outline.IType{}:
      {==}
    case Outline.ICtor{}:
      {==}
    case Outline.ILocal{}:
      {==}
