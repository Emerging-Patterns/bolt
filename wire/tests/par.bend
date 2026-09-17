# par: the fold over injected monoids and leaves, on the GPU
import Base
import ../monoid/sum.bend as Sum
import ../monoid/xor.bend as Xor
import ../leaf/one.bend as One
import ../leaf/index.bend as Index
import ../par/fold.bend as Par
import ../check/kit.bend as Check
import ../check/print.bend as Print

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_u32(~Print.new(), "sum of ones", Par.fold!(~Sum.new(), ~One.new(), 20n, 0), 1048576)
    Check.eq_u32(~Print.new(), "sum of indices", Par.fold!(~Sum.new(), ~Index.new(), 10n, 0), 523776)
    Check.eq_u32(~Print.new(), "xor of indices", Par.fold!(~Xor.new(), ~Index.new(), 10n, 0), 0)

#|ok sum of ones
#|ok sum of indices
#|ok xor of indices
