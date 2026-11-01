# spaces vocabulary for the noqa comment laws
import Base
import ../../src/rules/laws/law.bend as Law

# n spaces. Law vocabulary.
def nq.spaces(nn: Nat) -> String:
  match nn:
    case 0n:
      ""
    case 1n+p:
      SCon{' ', nq.spaces(p)}
