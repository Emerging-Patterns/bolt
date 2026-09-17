# syntax/word: the name under a position
import Base
import ../word.bend as Word
import ../../wire/check/kit.bend as Check
import ../../wire/check/print.bend as Report

def source() -> String:
  "import Base\n  Frame.decode(body) ++ Nat.show(List.length(&2, U32, rest))\n"

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str(~Report.new(), "inside a qualified name", Word.at(source(), 1, 9), "Frame.decode")
    Check.eq_str(~Report.new(), "at a name's first char", Word.at(source(), 1, 2), "Frame.decode")
    Check.eq_str(~Report.new(), "right after a name", Word.at(source(), 1, 14), "Frame.decode")
    Check.eq_str(~Report.new(), "a plain name", Word.at(source(), 1, 16), "body")
    Check.eq_str(~Report.new(), "a name deep in the line", Word.at(source(), 1, 40), "List.length")
    Check.eq_str(~Report.new(), "on an operator there is none", Word.at(source(), 1, 23), "")
    Check.eq_str(~Report.new(), "past the end of the line", Word.at(source(), 1, 500), "")
    Check.eq_str(~Report.new(), "past the end of the text", Word.at(source(), 9, 0), "")
    Check.eq_str(~Report.new(), "the first line", Word.at(source(), 0, 8), "Base")
    Check.eq_str(~Report.new(), "typed so far, mid-name", Word.before(source(), 1, 10), "Frame.de")
    Check.eq_str(~Report.new(), "typed so far, after an alias dot", Word.before(source(), 1, 8), "Frame.")
    Check.eq_str(~Report.new(), "nothing typed after a paren", Word.before(source(), 1, 15), "")

#|ok inside a qualified name
#|ok at a name's first char
#|ok right after a name
#|ok a plain name
#|ok a name deep in the line
#|ok on an operator there is none
#|ok past the end of the line
#|ok past the end of the text
#|ok the first line
#|ok typed so far, mid-name
#|ok typed so far, after an alias dot
#|ok nothing typed after a paren
