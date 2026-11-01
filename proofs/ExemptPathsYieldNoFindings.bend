# proofs of laws/ExemptPathsYieldNoFindings.bend
import Base
import ../src/finding.bend as F
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/calls.bend as Calls
import ../laws/ExemptPathsYieldNoFindings.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1

# an or whose second side ends in a true or holds whatever the rest is
law ex.or_true:
  for a: Bool
  for b: Bool
  {Bool.or(a, Bool.or(b, True{})) == True{} : Bool}

def ex.or_true(a, b):
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def Laws.untyped_exempt(path, sig, e):
  %Equal.sym(Bool, Calls.typed(sig), False{}, e) :
    {Bool.or(Paths.is_law_file(path), Bool.or(Calls.returns_proof(sig), Bool.not(_))) == True{} : Bool}
  ex.or_true(Paths.is_law_file(path), Calls.returns_proof(sig))

# scan
# ----
