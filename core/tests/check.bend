# check: the kit under its own reporters -- the dogfood loop
import Base
import ../check/kit.bend as Check
import ../check/print.bend as Print
import ../check/quiet.bend as Quiet

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_u32(~Print.new(), "equal numbers pass", 7, 7)
    Check.eq_u32(~Print.new(), "unequal numbers fail", 1, 2)
    Check.eq_str(~Print.new(), "equal strings pass", "a" ++ "b", "ab")
    Check.eq_str(~Print.new(), "unequal strings fail", "a", "b")
    Check.eq_u32(~Quiet.new(), "the quiet reporter says nothing", 1, 2)

#|ok equal numbers pass
#|FAIL unequal numbers fail
#|ok equal strings pass
#|FAIL unequal strings fail
