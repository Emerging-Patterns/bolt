# Where one token ends and the next begins, and what kind a whole one is.
# The lexer reads a char at a time inside a mode, and a char either continues
# the token it is inside of or ends it. laws/LexRoundTripsText.bend says the
# tokens' texts join back into the source whatever the cuts are; this file is
# where the cuts fall. A name goes on through letters, digits and dots. A
# number goes on through digits, dots and letters (`12n`, `1.5`). A string
# goes on through everything until its closing quote ends it. A char literal
# and a comment go on through everything but a newline. Spaces run together,
# and so do operator chars and dots. A fresh token continues nothing.
import Base
import ../src/syntax/lex.bend as Lex

# does a char of this class continue the token of this mode? Law vocabulary:
# bolt never calls it
def lexes.continues(mm: Lex.Mode, cls: Lex.Class) -> Bool:
  match mm cls:
    case Lex.Fresh{} c:
      False{}
    case Lex.InName{} Lex.CAlpha{}:
      True{}
    case Lex.InName{} Lex.CDigit{}:
      True{}
    case Lex.InName{} Lex.CDot{}:
      True{}
    case Lex.InNum{} Lex.CDigit{}:
      True{}
    case Lex.InNum{} Lex.CDot{}:
      True{}
    case Lex.InNum{} Lex.CAlpha{}:
      True{}
    case Lex.InStr{} c:
      True{}
    case Lex.InStrEsc{} c:
      True{}
    case Lex.InChar{} Lex.CNewline{}:
      False{}
    case Lex.InChar{} c:
      True{}
    case Lex.InCharEsc{} Lex.CNewline{}:
      False{}
    case Lex.InCharEsc{} c:
      True{}
    case Lex.InComment{} Lex.CNewline{}:
      False{}
    case Lex.InComment{} c:
      True{}
    case Lex.InSpace{} Lex.CSpace{}:
      True{}
    case Lex.InOp{} Lex.COp{}:
      True{}
    case Lex.InOp{} Lex.CDot{}:
      True{}
    case m c:
      False{}

# an operator's kind by its whole text: `:`, `=`, `<-`, `->` and `=>` each
# have their own, `@`, `@+` and `@-` are the binder mark, `&` its own, and
# any other is a plain operator. Law vocabulary: bolt never calls it
def lexes.op_kind(+tt: String) -> Lex.TokKind:
  Bool.pick(Lex.TokKind, String.eq(tt, ":"), Lex.TColon{},
    Bool.pick(Lex.TokKind, String.eq(tt, "="), Lex.TEq{},
      Bool.pick(Lex.TokKind, String.eq(tt, "<-"), Lex.TBind{},
        Bool.pick(Lex.TokKind, String.eq(tt, "->"), Lex.TArrow{},
          Bool.pick(Lex.TokKind, String.eq(tt, "=>"), Lex.TLam{},
            Bool.pick(Lex.TokKind, Bool.or(String.eq(tt, "@"), Bool.or(String.eq(tt, "@+"), String.eq(tt, "@-"))),
              Lex.TAll{},
              Bool.pick(Lex.TokKind, String.eq(tt, "&"), Lex.TAmp{}, Lex.TOp{})))))))

# LAW: a char continues the token it follows exactly as the table above says
law continues_by_mode_and_class:
  for mm: Lex.Mode
  for cls: Lex.Class
  {Lex.continues(mm, cls) == lexes.continues(mm, cls) : Bool}

# LAW: an operator's kind is read off its whole text
law operator_kind_by_text:
  for +tt: String
  {Lex.refine_op(tt) == lexes.op_kind(tt) : Lex.TokKind}

# LAW: a name is capitalized when its first char is a capital
law upper_first_char:
  for c: Char
  for t: List<&2, Char>
  {Lex.upper_first(c <> t) == Char.is_upper(c) : Bool}

# LAW: no chars are not capitalized
law upper_first_needs_a_char:
  for cs: List<&2, Char>
  for e: {List.is_empty(&2, Char, cs) == True{} : Bool}
  {Lex.upper_first(cs) == False{} : Bool}
