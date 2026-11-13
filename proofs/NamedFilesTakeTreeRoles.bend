# proofs of laws/NamedFilesTakeTreeRoles.bend
import Base
import ../src/src.bend as Src
import ../src/role.bend as Role
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ../src/rules/imports.bend as Imports
import ../laws/NamedFilesTakeTreeRoles.bend as Laws

def Laws.abs_keeps_rooted(cwd, path, e):
  %Equal.sym(Bool, String.starts_with(path, "/"), True{}, e) :
    {Imports.norm(Bool.pick(String, _, path, cwd ++ "/" ++ path)) == Imports.norm(path) : String}
  {==}

def Laws.abs_resolves_relative(cwd, path, e):
  %Equal.sym(Bool, String.starts_with(path, "/"), False{}, e) :
    {Imports.norm(Bool.pick(String, _, path, cwd ++ "/" ++ path)) == Imports.norm(cwd ++ "/" ++ path) : String}
  {==}

def Laws.norms_in_order(_p, _rest, _cwd):
  {==}

def Laws.facts_of_read(_path, _text, _rest, _cwd):
  {==}

def Laws.facts_of_unread(_path, _rest, _cwd):
  {==}

def Laws.marks_keyed_as_spelled(_p, _rest, _cwd, _ms):
  {==}

def Laws.marks_named_read_the_tree(_world):
  {==}

def Laws.marks_run_named(_p, _rest, _world, _ss):
  {==}

def Laws.marks_run_whole_tree(_world, _ss):
  {==}

def Laws.unseen_drops_seen(p, rest, cwd, seen, e):
  %Equal.sym(Bool, Imports.has(seen, Plan.abs(cwd, p)), True{}, e) :
    {Bool.pick(List<&2, String>, _, Plan.unseen(rest, cwd, seen), p <> Plan.unseen(rest, cwd, seen))
      == Plan.unseen(rest, cwd, seen) : List<&2, String>}
  {==}

def Laws.unseen_keeps_new(p, rest, cwd, seen, e):
  %Equal.sym(Bool, Imports.has(seen, Plan.abs(cwd, p)), False{}, e) :
    {Bool.pick(List<&2, String>, _, Plan.unseen(rest, cwd, seen), p <> Plan.unseen(rest, cwd, seen))
      == p <> Plan.unseen(rest, cwd, seen) : List<&2, String>}
  {==}

def Laws.graph_found_then_named(_world):
  {==}
