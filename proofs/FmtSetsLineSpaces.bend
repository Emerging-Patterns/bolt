# proofs of laws/FmtSetsLineSpaces.bend
import Base
import ../src/fmt/line.bend as Line
import ../src/syntax/lex.bend as Lex
import ../laws/FmtSetsLineSpaces.bend as Laws
import ./lemmas/BoolEmptiness.bend as M1

def Laws.commas_place_every_comma(toks):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, t, l, c}, +rest}:
      match k:
        case Lex.TName{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TUpper{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TDotted{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TWild{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TKey{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TNum{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TStr{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TChar{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TComment{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TSpace{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TNewline{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TOp{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TColon{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TEq{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TBind{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TArrow{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TLam{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TAll{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TAmp{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TOpen{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TClose{}:
          Laws.commas_place_every_comma(rest)
        case Lex.TComma{}:
          match rest:
            case Nil{}:
              {==}
            case Con{Lex.Tok{k2, +t2, +l2, +c2}, +more}:
              match k2:
                case Lex.TName{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TName{}, t2, l2, c2} <> more)
                case Lex.TUpper{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TUpper{}, t2, l2, c2} <> more)
                case Lex.TDotted{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TDotted{}, t2, l2, c2} <> more)
                case Lex.TWild{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TWild{}, t2, l2, c2} <> more)
                case Lex.TKey{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TKey{}, t2, l2, c2} <> more)
                case Lex.TNum{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TNum{}, t2, l2, c2} <> more)
                case Lex.TStr{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TStr{}, t2, l2, c2} <> more)
                case Lex.TChar{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TChar{}, t2, l2, c2} <> more)
                case Lex.TComment{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TComment{}, t2, l2, c2} <> more)
                case Lex.TSpace{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TSpace{}, t2, l2, c2} <> more)
                case Lex.TNewline{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TNewline{}, t2, l2, c2} <> more)
                case Lex.TOp{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TOp{}, t2, l2, c2} <> more)
                case Lex.TColon{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TColon{}, t2, l2, c2} <> more)
                case Lex.TEq{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TEq{}, t2, l2, c2} <> more)
                case Lex.TBind{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TBind{}, t2, l2, c2} <> more)
                case Lex.TArrow{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TArrow{}, t2, l2, c2} <> more)
                case Lex.TLam{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TLam{}, t2, l2, c2} <> more)
                case Lex.TAll{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TAll{}, t2, l2, c2} <> more)
                case Lex.TAmp{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TAmp{}, t2, l2, c2} <> more)
                case Lex.TOpen{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TOpen{}, t2, l2, c2} <> more)
                case Lex.TClose{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TClose{}, t2, l2, c2} <> more)
                case Lex.TComma{}:
                  Laws.commas_place_every_comma(Lex.Tok{Lex.TComma{}, t2, l2, c2} <> more)

def Laws.commas_leave_placed(toks, e):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, +t, +l, +c}, +rest}:
      match k:
        case Lex.TName{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TName{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TUpper{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TUpper{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TDotted{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TDotted{}, t, l, c} <> z,
            Line.commas(rest), rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TWild{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TWild{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TKey{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TKey{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TNum{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TNum{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TStr{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TStr{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TChar{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TChar{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TComment{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TComment{}, t, l, c} <> z,
            Line.commas(rest), rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TSpace{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TSpace{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TNewline{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TNewline{}, t, l, c} <> z,
            Line.commas(rest), rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TOp{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TOp{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TColon{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TColon{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TEq{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TEq{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TBind{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TBind{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TArrow{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TArrow{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TLam{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TLam{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TAll{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TAll{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TAmp{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TAmp{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TOpen{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TOpen{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TClose{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TClose{}, t, l, c} <> z, Line.commas(rest),
            rest,
            Laws.commas_leave_placed(rest, e))
        case Lex.TComma{}:
          match rest:
            case Nil{}:
              {==}
            case Con{Lex.Tok{k2, +t2, +l2, +c2}, +more}:
              match k2:
                case Lex.TName{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TName{}, t2, l2, c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TName{}, t2, l2, c2} <> more : List<&2, Lex.Tok>},
                    M1.false_true(e))
                case Lex.TUpper{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TUpper{}, t2, l2, c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TUpper{}, t2, l2, c2} <> more : List<&2, Lex.Tok>},
                    M1.false_true(e))
                case Lex.TDotted{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TDotted{}, t2, l2,
                    c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TDotted{}, t2, l2, c2} <> more : List<&2,
                      Lex.Tok>},
                    M1.false_true(e))
                case Lex.TWild{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TWild{}, t2, l2, c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TWild{}, t2, l2, c2} <> more : List<&2, Lex.Tok>},
                    M1.false_true(e))
                case Lex.TKey{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TKey{}, t2, l2, c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TKey{}, t2, l2, c2} <> more : List<&2, Lex.Tok>},
                    M1.false_true(e))
                case Lex.TNum{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TNum{}, t2, l2, c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TNum{}, t2, l2, c2} <> more : List<&2, Lex.Tok>},
                    M1.false_true(e))
                case Lex.TStr{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TStr{}, t2, l2, c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TStr{}, t2, l2, c2} <> more : List<&2, Lex.Tok>},
                    M1.false_true(e))
                case Lex.TChar{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TChar{}, t2, l2, c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TChar{}, t2, l2, c2} <> more : List<&2, Lex.Tok>},
                    M1.false_true(e))
                case Lex.TComment{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TComment{}, t2, l2,
                    c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TComment{}, t2, l2, c2} <> more : List<&2,
                      Lex.Tok>},
                    M1.false_true(e))
                case Lex.TSpace{}:
                  Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TComma{}, t, l, c} <> z,
                    Line.commas(Lex.Tok{Lex.TSpace{}, t2, l2, c2} <> more), Lex.Tok{Lex.TSpace{}, t2, l2, c2} <> more,
                    Laws.commas_leave_placed(Lex.Tok{Lex.TSpace{}, t2, l2, c2} <> more, e))
                case Lex.TNewline{}:
                  Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TComma{}, t, l, c} <> z,
                    Line.commas(Lex.Tok{Lex.TNewline{}, t2, l2, c2} <> more), Lex.Tok{Lex.TNewline{}, t2, l2,
                      c2} <> more,
                    Laws.commas_leave_placed(Lex.Tok{Lex.TNewline{}, t2, l2, c2} <> more, e))
                case Lex.TOp{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TOp{}, t2, l2, c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TOp{}, t2, l2, c2} <> more : List<&2, Lex.Tok>},
                    M1.false_true(e))
                case Lex.TColon{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TColon{}, t2, l2, c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TColon{}, t2, l2, c2} <> more : List<&2, Lex.Tok>},
                    M1.false_true(e))
                case Lex.TEq{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TEq{}, t2, l2, c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TEq{}, t2, l2, c2} <> more : List<&2, Lex.Tok>},
                    M1.false_true(e))
                case Lex.TBind{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TBind{}, t2, l2, c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TBind{}, t2, l2, c2} <> more : List<&2, Lex.Tok>},
                    M1.false_true(e))
                case Lex.TArrow{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TArrow{}, t2, l2, c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TArrow{}, t2, l2, c2} <> more : List<&2, Lex.Tok>},
                    M1.false_true(e))
                case Lex.TLam{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TLam{}, t2, l2, c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TLam{}, t2, l2, c2} <> more : List<&2, Lex.Tok>},
                    M1.false_true(e))
                case Lex.TAll{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TAll{}, t2, l2, c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TAll{}, t2, l2, c2} <> more : List<&2, Lex.Tok>},
                    M1.false_true(e))
                case Lex.TAmp{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TAmp{}, t2, l2, c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TAmp{}, t2, l2, c2} <> more : List<&2, Lex.Tok>},
                    M1.false_true(e))
                case Lex.TOpen{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TOpen{}, t2, l2, c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TOpen{}, t2, l2, c2} <> more : List<&2, Lex.Tok>},
                    M1.false_true(e))
                case Lex.TClose{}:
                  Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TComma{}, t, l, c} <> z,
                    Line.commas(Lex.Tok{Lex.TClose{}, t2, l2, c2} <> more), Lex.Tok{Lex.TClose{}, t2, l2, c2} <> more,
                    Laws.commas_leave_placed(Lex.Tok{Lex.TClose{}, t2, l2, c2} <> more, e))
                case Lex.TComma{}:
                  Empty.absurd({Line.commas(Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TComma{}, t2, l2, c2} <> more)
                    == Lex.Tok{Lex.TComma{}, t, l, c} <> Lex.Tok{Lex.TComma{}, t2, l2, c2} <> more : List<&2, Lex.Tok>},
                    M1.false_true(e))

def Laws.commas_twice_is_once(toks):
  Laws.commas_leave_placed(Line.commas(toks), Laws.commas_place_every_comma(toks))

# a gap after a comma is a space or nothing: the tokens that are no space are the rest's
law ls.gap:
  for b: Bool
  for -more: List<&2, Lex.Tok>
  {Laws.unspaced(Line.commas.gap(b, more)) == Laws.unspaced(more) : List<&2, Lex.Tok>}

def ls.gap(b, _more):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.commas_add_only_spaces(toks):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, +t, +l, +c}, +rest}:
      match k:
        case Lex.TName{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TName{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TUpper{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TUpper{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TDotted{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TDotted{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TWild{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TWild{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TKey{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TKey{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TNum{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TNum{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TStr{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TStr{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TChar{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TChar{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TComment{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TComment{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TSpace{}:
          Laws.commas_add_only_spaces(rest)
        case Lex.TNewline{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TNewline{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TOp{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TOp{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TColon{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TColon{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TEq{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TEq{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TBind{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TBind{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TArrow{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TArrow{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TLam{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TLam{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TAll{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TAll{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TAmp{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TAmp{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TOpen{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TOpen{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TClose{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TClose{}, t, l, c} <> z,
            Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest), Laws.commas_add_only_spaces(rest))
        case Lex.TComma{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TComma{}, t, l, c} <> z,
            Laws.unspaced(Line.commas.gap(Line.commas.bare(rest), Line.commas(rest))), Laws.unspaced(rest),
            Equal.trans(List<&2, Lex.Tok>, Laws.unspaced(Line.commas.gap(Line.commas.bare(rest), Line.commas(rest))),
              Laws.unspaced(Line.commas(rest)), Laws.unspaced(rest),
              ls.gap(Line.commas.bare(rest), Line.commas(rest)), Laws.commas_add_only_spaces(rest)))

# a space token passes: at the head of its line always, and elsewhere because
# runs made it one space, or a comment follows it; the rest is as the tokens
# after it are
law ls.space:
  for lead: Bool
  for rest: List<&2, Lex.Tok>
  for -t: String
  for ih: {Laws.single(Line.runs(rest, False{}), False{}) == True{} : Bool}
  {Bool.and(Bool.or(lead, Bool.or(Laws.noted(Line.runs(rest, False{})),
      String.eq(Line.runs.text(Bool.or(lead, Line.runs.noted(rest)), t), " "))),
    Laws.single(Line.runs(rest, False{}), False{})) == True{} : Bool}

def ls.space(lead, rest, _t, ih):
  match lead:
    case True{}:
      ih
    case False{}:
      match rest:
        case Nil{}:
          {==}
        case Con{Lex.Tok{k, t2, l, c}, more}:
          match k:
            case Lex.TName{}:
              ih
            case Lex.TUpper{}:
              ih
            case Lex.TDotted{}:
              ih
            case Lex.TWild{}:
              ih
            case Lex.TKey{}:
              ih
            case Lex.TNum{}:
              ih
            case Lex.TStr{}:
              ih
            case Lex.TChar{}:
              ih
            case Lex.TComment{}:
              ih
            case Lex.TSpace{}:
              ih
            case Lex.TNewline{}:
              ih
            case Lex.TOp{}:
              ih
            case Lex.TColon{}:
              ih
            case Lex.TEq{}:
              ih
            case Lex.TBind{}:
              ih
            case Lex.TArrow{}:
              ih
            case Lex.TLam{}:
              ih
            case Lex.TAll{}:
              ih
            case Lex.TAmp{}:
              ih
            case Lex.TOpen{}:
              ih
            case Lex.TClose{}:
              ih
            case Lex.TComma{}:
              ih

def Laws.runs_leave_one_space(toks, lead):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, t, l, c}, +rest}:
      match k:
        case Lex.TName{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TUpper{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TDotted{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TWild{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TKey{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TNum{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TStr{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TChar{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TComment{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TSpace{}:
          ls.space(lead, rest, t, Laws.runs_leave_one_space(rest, False{}))
        case Lex.TNewline{}:
          Laws.runs_leave_one_space(rest, True{})
        case Lex.TOp{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TColon{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TEq{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TBind{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TArrow{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TLam{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TAll{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TAmp{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TOpen{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TClose{}:
          Laws.runs_leave_one_space(rest, False{})
        case Lex.TComma{}:
          Laws.runs_leave_one_space(rest, False{})

# what runs gives opens with a comment exactly when what it took does
law ls.noted:
  for rest: List<&2, Lex.Tok>
  for -lead: Bool
  {Line.runs.noted(Line.runs(rest, lead)) == Line.runs.noted(rest) : Bool}

def ls.noted(rest, _lead):
  match rest:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, t, l, c}, more}:
      match k:
        case Lex.TName{}:
          {==}
        case Lex.TUpper{}:
          {==}
        case Lex.TDotted{}:
          {==}
        case Lex.TWild{}:
          {==}
        case Lex.TKey{}:
          {==}
        case Lex.TNum{}:
          {==}
        case Lex.TStr{}:
          {==}
        case Lex.TChar{}:
          {==}
        case Lex.TComment{}:
          {==}
        case Lex.TSpace{}:
          {==}
        case Lex.TNewline{}:
          {==}
        case Lex.TOp{}:
          {==}
        case Lex.TColon{}:
          {==}
        case Lex.TEq{}:
          {==}
        case Lex.TBind{}:
          {==}
        case Lex.TArrow{}:
          {==}
        case Lex.TLam{}:
          {==}
        case Lex.TAll{}:
          {==}
        case Lex.TAmp{}:
          {==}
        case Lex.TOpen{}:
          {==}
        case Lex.TClose{}:
          {==}
        case Lex.TComma{}:
          {==}

# a space's text set twice the same way is set once
law ls.text:
  for keep: Bool
  for -t: String
  {Line.runs.text(keep, Line.runs.text(keep, t)) == Line.runs.text(keep, t) : String}

def ls.text(keep, _t):
  match keep:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.runs_twice_is_once(toks, lead):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, +t, +l, +c}, +rest}:
      match k:
        case Lex.TName{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TName{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TUpper{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TUpper{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TDotted{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TDotted{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TWild{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TWild{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TKey{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TKey{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TNum{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TNum{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TStr{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TStr{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TChar{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TChar{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TComment{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TComment{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TSpace{}:
          +keep = Bool.or(lead, Line.runs.noted(rest))
          n = Equal.sym(Bool, Line.runs.noted(Line.runs(rest, False{})), Line.runs.noted(rest), ls.noted(rest, False{}))
          %n : {Lex.Tok{Lex.TSpace{}, Line.runs.text(Bool.or(lead, _), Line.runs.text(keep, t)), l, c}
              <> Line.runs(Line.runs(rest, False{}), False{})
            == Lex.Tok{Lex.TSpace{}, Line.runs.text(keep, t), l, c} <> Line.runs(rest, False{}) : List<&2, Lex.Tok>}
          x = Equal.sym(String, Line.runs.text(keep, Line.runs.text(keep, t)), Line.runs.text(keep, t), ls.text(keep,
            t))
          %x : {Lex.Tok{Lex.TSpace{}, _, l, c} <> Line.runs(Line.runs(rest, False{}), False{})
            == Lex.Tok{Lex.TSpace{}, Line.runs.text(keep, t), l, c} <> Line.runs(rest, False{}) : List<&2, Lex.Tok>}
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TSpace{}, Line.runs.text(keep, t), l,
            c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}),
            Laws.runs_twice_is_once(rest, False{}))
        case Lex.TNewline{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TNewline{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, True{}), True{}), Line.runs(rest, True{}), Laws.runs_twice_is_once(rest, True{}))
        case Lex.TOp{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TOp{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TColon{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TColon{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TEq{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TEq{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TBind{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TBind{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TArrow{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TArrow{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TLam{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TLam{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TAll{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TAll{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TAmp{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TAmp{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TOpen{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TOpen{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TClose{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TClose{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))
        case Lex.TComma{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TComma{}, t, l, c} <> z,
            Line.runs(Line.runs(rest, False{}), False{}), Line.runs(rest, False{}), Laws.runs_twice_is_once(rest,
              False{}))

def Laws.runs_change_only_space_text(toks, _lead):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, +t, +l, +c}, +rest}:
      match k:
        case Lex.TName{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TName{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TUpper{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TUpper{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TDotted{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TDotted{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TWild{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TWild{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TKey{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TKey{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TNum{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TNum{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TStr{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TStr{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TChar{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TChar{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TComment{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TComment{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TSpace{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TSpace{}, "", l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TNewline{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TNewline{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, True{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, True{}))
        case Lex.TOp{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TOp{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TColon{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TColon{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TEq{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TEq{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TBind{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TBind{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TArrow{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TArrow{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TLam{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TLam{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TAll{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TAll{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TAmp{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TAmp{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TOpen{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TOpen{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TClose{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TClose{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))
        case Lex.TComma{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TComma{}, t, l, c} <> z,
            Laws.blanked(Line.runs(rest, False{})), Laws.blanked(rest), Laws.runs_change_only_space_text(rest, False{}))

def Laws.runs_keep_indent(_t, _l, _c, _rest):
  {==}

def Laws.runs_keep_space_before_comment(_t, _l, _c, _ct, _cl, _cc, _rest, lead):
  match lead:
    case True{}:
      {==}
    case False{}:
      {==}
