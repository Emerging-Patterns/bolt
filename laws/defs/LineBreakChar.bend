# whether a char is a line break
import Base

# is the char a line break? '\n', code point 10
def breaks(c: Char) -> Bool:
  U32.is_eq(Char.to_u32(c), 10)
