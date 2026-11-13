# proofs of laws/PathsNameFiles.bend
import Base
import ../src/lazy/lazy.bend as Lazy
import ../src/paths.bend as Paths
import ../laws/PathsNameFiles.bend as Laws

# paths (laws/PathsNameFiles.bend). The search for a `tests` directory stops
# at the first one it finds; a stop at the first True is the plain or.
law pn.or_else:
  for c: Bool
  for -x: Bool
  {Lazy.or_else(c, _u => x) == Bool.or(c, x) : Bool}

def pn.or_else(c, _x):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# a test that needs a second conjunct that is False fails
law pn.and_false:
  for c: Bool
  {Bool.or(Bool.and(c, False{}), False{}) == False{} : Bool}

def pn.and_false(c):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.base_reads_on(_s, _rest, _last):
  {==}

def Laws.base_ends(_last):
  {==}

def Laws.base_is_last_segment(_path):
  {==}

def Laws.tested_finds_a_directory(s, rest):
  pn.or_else(Bool.and(String.eq(s, "tests"), Bool.not(List.is_empty(&2, String, rest))), Paths.tested(rest))

def Laws.tested_needs_a_file_below(s):
  Equal.trans(Bool, Paths.tested(s <> Nil{}), Bool.or(Bool.and(String.eq(s, "tests"), False{}), False{}), False{},
    Laws.tested_finds_a_directory(s, Nil{}), pn.and_false(String.eq(s, "tests")))

def Laws.is_test_reads_segments(_path):
  {==}

def Laws.is_laws_by_name(_path):
  {==}

def Laws.is_proof_by_name(_path):
  {==}

def Laws.is_law_file_either(_path):
  {==}
