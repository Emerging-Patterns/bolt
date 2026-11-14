# False is never True and the Unit/Empty types for it
import Base

# Unit for False, Empty for True
def false_ty(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

# False is never True
law false_true:
  for e: {False{} == True{} : Bool}
  Empty

def false_true(e):
  %e : false_ty(_)
  Unit{}

# True is never False
law true_false:
  for e: {True{} == False{} : Bool}
  Empty

def true_false(e):
  false_true(Equal.sym(Bool, True{}, False{}, e))
