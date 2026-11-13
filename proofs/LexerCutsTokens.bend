# proofs of laws/LexerCutsTokens.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../laws/LexerCutsTokens.bend as Laws
import ./lemmas/BoolEmptiness.bend as M1

def Laws.continues_by_mode_and_class(mm, cls):
  match mm:
    case Lex.Fresh{}:
      match cls:
        case Lex.CAlpha{}:
          {==}
        case Lex.CDigit{}:
          {==}
        case Lex.CDot{}:
          {==}
        case Lex.CQuote{}:
          {==}
        case Lex.CTick{}:
          {==}
        case Lex.CBack{}:
          {==}
        case Lex.CHash{}:
          {==}
        case Lex.CSpace{}:
          {==}
        case Lex.CNewline{}:
          {==}
        case Lex.COp{}:
          {==}
        case Lex.CColon{}:
          {==}
        case Lex.COpen{}:
          {==}
        case Lex.CClose{}:
          {==}
        case Lex.CComma{}:
          {==}
    case Lex.InName{}:
      match cls:
        case Lex.CAlpha{}:
          {==}
        case Lex.CDigit{}:
          {==}
        case Lex.CDot{}:
          {==}
        case Lex.CQuote{}:
          {==}
        case Lex.CTick{}:
          {==}
        case Lex.CBack{}:
          {==}
        case Lex.CHash{}:
          {==}
        case Lex.CSpace{}:
          {==}
        case Lex.CNewline{}:
          {==}
        case Lex.COp{}:
          {==}
        case Lex.CColon{}:
          {==}
        case Lex.COpen{}:
          {==}
        case Lex.CClose{}:
          {==}
        case Lex.CComma{}:
          {==}
    case Lex.InNum{}:
      match cls:
        case Lex.CAlpha{}:
          {==}
        case Lex.CDigit{}:
          {==}
        case Lex.CDot{}:
          {==}
        case Lex.CQuote{}:
          {==}
        case Lex.CTick{}:
          {==}
        case Lex.CBack{}:
          {==}
        case Lex.CHash{}:
          {==}
        case Lex.CSpace{}:
          {==}
        case Lex.CNewline{}:
          {==}
        case Lex.COp{}:
          {==}
        case Lex.CColon{}:
          {==}
        case Lex.COpen{}:
          {==}
        case Lex.CClose{}:
          {==}
        case Lex.CComma{}:
          {==}
    case Lex.InStr{}:
      match cls:
        case Lex.CAlpha{}:
          {==}
        case Lex.CDigit{}:
          {==}
        case Lex.CDot{}:
          {==}
        case Lex.CQuote{}:
          {==}
        case Lex.CTick{}:
          {==}
        case Lex.CBack{}:
          {==}
        case Lex.CHash{}:
          {==}
        case Lex.CSpace{}:
          {==}
        case Lex.CNewline{}:
          {==}
        case Lex.COp{}:
          {==}
        case Lex.CColon{}:
          {==}
        case Lex.COpen{}:
          {==}
        case Lex.CClose{}:
          {==}
        case Lex.CComma{}:
          {==}
    case Lex.InStrEsc{}:
      match cls:
        case Lex.CAlpha{}:
          {==}
        case Lex.CDigit{}:
          {==}
        case Lex.CDot{}:
          {==}
        case Lex.CQuote{}:
          {==}
        case Lex.CTick{}:
          {==}
        case Lex.CBack{}:
          {==}
        case Lex.CHash{}:
          {==}
        case Lex.CSpace{}:
          {==}
        case Lex.CNewline{}:
          {==}
        case Lex.COp{}:
          {==}
        case Lex.CColon{}:
          {==}
        case Lex.COpen{}:
          {==}
        case Lex.CClose{}:
          {==}
        case Lex.CComma{}:
          {==}
    case Lex.InChar{}:
      match cls:
        case Lex.CAlpha{}:
          {==}
        case Lex.CDigit{}:
          {==}
        case Lex.CDot{}:
          {==}
        case Lex.CQuote{}:
          {==}
        case Lex.CTick{}:
          {==}
        case Lex.CBack{}:
          {==}
        case Lex.CHash{}:
          {==}
        case Lex.CSpace{}:
          {==}
        case Lex.CNewline{}:
          {==}
        case Lex.COp{}:
          {==}
        case Lex.CColon{}:
          {==}
        case Lex.COpen{}:
          {==}
        case Lex.CClose{}:
          {==}
        case Lex.CComma{}:
          {==}
    case Lex.InCharEsc{}:
      match cls:
        case Lex.CAlpha{}:
          {==}
        case Lex.CDigit{}:
          {==}
        case Lex.CDot{}:
          {==}
        case Lex.CQuote{}:
          {==}
        case Lex.CTick{}:
          {==}
        case Lex.CBack{}:
          {==}
        case Lex.CHash{}:
          {==}
        case Lex.CSpace{}:
          {==}
        case Lex.CNewline{}:
          {==}
        case Lex.COp{}:
          {==}
        case Lex.CColon{}:
          {==}
        case Lex.COpen{}:
          {==}
        case Lex.CClose{}:
          {==}
        case Lex.CComma{}:
          {==}
    case Lex.InComment{}:
      match cls:
        case Lex.CAlpha{}:
          {==}
        case Lex.CDigit{}:
          {==}
        case Lex.CDot{}:
          {==}
        case Lex.CQuote{}:
          {==}
        case Lex.CTick{}:
          {==}
        case Lex.CBack{}:
          {==}
        case Lex.CHash{}:
          {==}
        case Lex.CSpace{}:
          {==}
        case Lex.CNewline{}:
          {==}
        case Lex.COp{}:
          {==}
        case Lex.CColon{}:
          {==}
        case Lex.COpen{}:
          {==}
        case Lex.CClose{}:
          {==}
        case Lex.CComma{}:
          {==}
    case Lex.InSpace{}:
      match cls:
        case Lex.CAlpha{}:
          {==}
        case Lex.CDigit{}:
          {==}
        case Lex.CDot{}:
          {==}
        case Lex.CQuote{}:
          {==}
        case Lex.CTick{}:
          {==}
        case Lex.CBack{}:
          {==}
        case Lex.CHash{}:
          {==}
        case Lex.CSpace{}:
          {==}
        case Lex.CNewline{}:
          {==}
        case Lex.COp{}:
          {==}
        case Lex.CColon{}:
          {==}
        case Lex.COpen{}:
          {==}
        case Lex.CClose{}:
          {==}
        case Lex.CComma{}:
          {==}
    case Lex.InOp{}:
      match cls:
        case Lex.CAlpha{}:
          {==}
        case Lex.CDigit{}:
          {==}
        case Lex.CDot{}:
          {==}
        case Lex.CQuote{}:
          {==}
        case Lex.CTick{}:
          {==}
        case Lex.CBack{}:
          {==}
        case Lex.CHash{}:
          {==}
        case Lex.CSpace{}:
          {==}
        case Lex.CNewline{}:
          {==}
        case Lex.COp{}:
          {==}
        case Lex.CColon{}:
          {==}
        case Lex.COpen{}:
          {==}
        case Lex.CClose{}:
          {==}
        case Lex.CComma{}:
          {==}

def Laws.operator_kind_by_text(_tt):
  {==}

def Laws.upper_first_char(_c, _t):
  {==}

def Laws.upper_first_needs_a_char(cs, e):
  match cs:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Lex.upper_first(cs) == False{} : Bool}, M1.false_true(e))
