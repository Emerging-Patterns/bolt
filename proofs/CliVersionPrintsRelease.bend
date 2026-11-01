# proofs of laws/CliVersionPrintsRelease.bend
import Base
import ../laws/CliVersionPrintsRelease.bend as Laws

def Laws.version_release(rel, rev, h):
  e = Equal.sym(Bool, String.is_empty(rev), True{}, h)
  %e : {Bool.pick(String, _, rel, rel ++ " (" ++ rev ++ ")") == rel : String}
  {==}

def Laws.version_commit(rel, rev, h):
  e = Equal.sym(Bool, String.is_empty(rev), False{}, h)
  %e : {Bool.pick(String, _, rel, rel ++ " (" ++ rev ++ ")") == rel ++ " (" ++ rev ++ ")" : String}
  {==}
