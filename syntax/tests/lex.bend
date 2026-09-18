# syntax/lex: source to tokens with positions; every char lands in one token
import Base
import ../lex.bend as Lex
import ../../wire/check/kit.bend as Check
import ../../wire/check/print.bend as Report

def source() -> String:
  "def f(+x: U32) -> List<&2, U32>: # note\n  case 1n+p:\n    M.go(x, \"a\\\"b\", 'c') ++ {==} <> 1.5\n  y = a[5] <- 42\n"

def kind(k: Lex.TokKind) -> String:
  match k:
    case Lex.TName{}:
      "n"
    case Lex.TUpper{}:
      "N"
    case Lex.TDotted{}:
      "d"
    case Lex.TWild{}:
      "w"
    case Lex.TKey{}:
      "k"
    case Lex.TColon{}:
      ":"
    case Lex.TEq{}:
      "="
    case Lex.TBind{}:
      "<"
    case Lex.TArrow{}:
      ">"
    case Lex.TLam{}:
      "l"
    case Lex.TAll{}:
      "@"
    case Lex.TAmp{}:
      "&"
    case Lex.TNum{}:
      "#"
    case Lex.TStr{}:
      "s"
    case Lex.TChar{}:
      "c"
    case Lex.TComment{}:
      "%"
    case Lex.TSpace{}:
      "_"
    case Lex.TNewline{}:
      "/"
    case Lex.TOp{}:
      "o"
    case Lex.TOpen{}:
      "("
    case Lex.TClose{}:
      ")"
    case Lex.TComma{}:
      ","

# the significant tokens of a line, as kind:text
def show.go(toks: List<&2, Lex.Tok>, +line: U32) -> List<&2, String>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{+k, text, l, c}, t}:
      +rest = show.go(t, line)
      Bool.pick(List<&2, String>, Bool.and(U32.is_eq(l, line), Lex.significant(k)),
        (kind(k) ++ ":" ++ text ++ "@" ++ U32.show(c)) <> rest, rest)

def show(line: U32) -> String:
  String.join(show.go(Lex.tokens(source()), line), " ")

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str(~Report.new(), "lossless", Lex.text(Lex.tokens(source())), source())
    Check.eq_str(~Report.new(), "lossless on an unclosed string", Lex.text(Lex.tokens("x = \"abc\ny = 'q\nz")), "x = \"abc\ny = 'q\nz")
    IO.print(show(0))
    IO.print(show(1))
    IO.print(show(2))
    IO.print(show(3))

#|ok lossless
#|ok lossless on an unclosed string
#|k:def@0 n:f@4 (:(@5 o:+@6 n:x@7 :::@8 N:U32@10 ):)@13 >:->@15 N:List@18 o:<&@22 #:2@24 ,:,@25 N:U32@27 o:>@30 :::@31
#|k:case@2 #:1n@7 o:+@9 n:p@10 :::@11
#|d:M.go@4 (:(@8 n:x@9 ,:,@10 s:"a\"b"@12 ,:,@18 c:'c'@20 ):)@23 o:++@25 (:{@28 o:==@29 ):}@31 o:<>@33 #:1.5@36
#|n:y@2 =:=@4 n:a@6 (:[@7 #:5@8 ):]@9 <:<-@11 #:42@14
