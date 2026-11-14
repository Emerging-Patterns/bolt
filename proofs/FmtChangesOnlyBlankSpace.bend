# proofs of laws/FmtChangesOnlyBlankSpace.bend
import Base
import ../src/fmt.bend as Fmt
import ../src/fmt/head.bend as Head
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/lex.bend as Lex
import ../laws/FmtChangesOnlyBlankSpace.bend as Laws

# a gap is blank space: it adds no code
law hd.gap:
  for gp: Head.Gap
  for -more: List<&2, Lex.Tok>
  {Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(gp), more)) == Laws.code(more) : List<&2, Lex.Tok>}

def hd.gap(gp, _more):
  match gp:
    case Head.GNone{}:
      {==}
    case Head.GOne{}:
      {==}
    case Head.GTwo{}:
      {==}
    case Head.GLine{}:
      {==}
    case Head.GDent{}:
      {==}
    case Head.GKeep{sp}:
      {==}

# a token that is no code adds none, written or dropped
law hd.blank:
  for st: Head.State
  for -k: Lex.TokKind
  for -t: String
  for -l: U32
  for -c: U32
  for -more: List<&2, Lex.Tok>
  for e: {Lex.significant(k) == False{} : Bool}
  {Laws.code(Head.blank(st, Lex.Tok{k, t, l, c}, more)) == Laws.code(more) : List<&2, Lex.Tok>}

def hd.blank(st, k, t, _l, _c, more, e):
  match st:
    case Head.Out{}:
      s = Equal.sym(Bool, Lex.significant(k), False{}, e)
      %s : {Bool.pick(List<&2, Lex.Tok>, _, Lex.Tok{k, t, 0, 0} <> Laws.code(more), Laws.code(more)) == Laws.code(more)
        : List<&2, Lex.Tok>}
      {==}
    case Head.In{wk, glued, pv, brk, sp, depth}:
      {==}

def Laws.heads_keep_code(toks, st):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, +t, +l, +c}, +rest}:
      match k:
        case Lex.TName{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TName{}, t, l, c})),
              Lex.Tok{Lex.TName{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TName{}, t, l, c},
              rest)))),
            Laws.code(Lex.Tok{Lex.TName{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TName{}, t,
              l, c}, rest))), Laws.code(Lex.Tok{Lex.TName{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TName{}, t, l, c}), Lex.Tok{Lex.TName{}, t, l,
              c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TName{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TName{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TName{}, t, l, c}, rest))), Laws.code(rest),
                Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TName{}, t, l, c}, rest))))
        case Lex.TUpper{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TUpper{}, t, l, c})),
              Lex.Tok{Lex.TUpper{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TUpper{}, t, l, c},
              rest)))),
            Laws.code(Lex.Tok{Lex.TUpper{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TUpper{}, t,
              l, c}, rest))), Laws.code(Lex.Tok{Lex.TUpper{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TUpper{}, t, l, c}), Lex.Tok{Lex.TUpper{}, t, l,
              c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TUpper{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TUpper{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TUpper{}, t, l, c}, rest))),
                Laws.code(rest), Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TUpper{}, t, l, c}, rest))))
        case Lex.TDotted{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TDotted{}, t, l, c})),
              Lex.Tok{Lex.TDotted{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TDotted{}, t, l,
              c}, rest)))),
            Laws.code(Lex.Tok{Lex.TDotted{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TDotted{},
              t, l, c}, rest))), Laws.code(Lex.Tok{Lex.TDotted{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TDotted{}, t, l, c}), Lex.Tok{Lex.TDotted{}, t, l,
              c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TDotted{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TDotted{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TDotted{}, t, l, c}, rest))),
                Laws.code(rest), Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TDotted{}, t, l, c}, rest))))
        case Lex.TWild{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TWild{}, t, l, c})),
              Lex.Tok{Lex.TWild{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TWild{}, t, l, c},
              rest)))),
            Laws.code(Lex.Tok{Lex.TWild{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TWild{}, t,
              l, c}, rest))), Laws.code(Lex.Tok{Lex.TWild{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TWild{}, t, l, c}), Lex.Tok{Lex.TWild{}, t, l,
              c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TWild{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TWild{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TWild{}, t, l, c}, rest))), Laws.code(rest),
                Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TWild{}, t, l, c}, rest))))
        case Lex.TKey{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TKey{}, t, l, c})),
              Lex.Tok{Lex.TKey{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TKey{}, t, l, c},
              rest)))),
            Laws.code(Lex.Tok{Lex.TKey{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TKey{}, t, l,
              c}, rest))), Laws.code(Lex.Tok{Lex.TKey{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TKey{}, t, l, c}), Lex.Tok{Lex.TKey{}, t, l, c} <> Head.heads.go(rest,
              Head.on_mark(st, Lex.Tok{Lex.TKey{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TKey{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TKey{}, t, l, c}, rest))), Laws.code(rest),
                Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TKey{}, t, l, c}, rest))))
        case Lex.TNum{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TNum{}, t, l, c})),
              Lex.Tok{Lex.TNum{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TNum{}, t, l, c},
              rest)))),
            Laws.code(Lex.Tok{Lex.TNum{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TNum{}, t, l,
              c}, rest))), Laws.code(Lex.Tok{Lex.TNum{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TNum{}, t, l, c}), Lex.Tok{Lex.TNum{}, t, l, c} <> Head.heads.go(rest,
              Head.on_mark(st, Lex.Tok{Lex.TNum{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TNum{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TNum{}, t, l, c}, rest))), Laws.code(rest),
                Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TNum{}, t, l, c}, rest))))
        case Lex.TStr{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TStr{}, t, l, c})),
              Lex.Tok{Lex.TStr{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TStr{}, t, l, c},
              rest)))),
            Laws.code(Lex.Tok{Lex.TStr{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TStr{}, t, l,
              c}, rest))), Laws.code(Lex.Tok{Lex.TStr{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TStr{}, t, l, c}), Lex.Tok{Lex.TStr{}, t, l, c} <> Head.heads.go(rest,
              Head.on_mark(st, Lex.Tok{Lex.TStr{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TStr{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TStr{}, t, l, c}, rest))), Laws.code(rest),
                Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TStr{}, t, l, c}, rest))))
        case Lex.TChar{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TChar{}, t, l, c})),
              Lex.Tok{Lex.TChar{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TChar{}, t, l, c},
              rest)))),
            Laws.code(Lex.Tok{Lex.TChar{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TChar{}, t,
              l, c}, rest))), Laws.code(Lex.Tok{Lex.TChar{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TChar{}, t, l, c}), Lex.Tok{Lex.TChar{}, t, l,
              c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TChar{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TChar{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TChar{}, t, l, c}, rest))), Laws.code(rest),
                Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TChar{}, t, l, c}, rest))))
        case Lex.TOp{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TOp{}, t, l, c})),
              Lex.Tok{Lex.TOp{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TOp{}, t, l, c}, rest)))),
            Laws.code(Lex.Tok{Lex.TOp{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TOp{}, t, l,
              c}, rest))), Laws.code(Lex.Tok{Lex.TOp{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TOp{}, t, l, c}), Lex.Tok{Lex.TOp{}, t, l, c} <> Head.heads.go(rest,
              Head.on_mark(st, Lex.Tok{Lex.TOp{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TOp{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TOp{}, t, l, c}, rest))), Laws.code(rest),
                Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TOp{}, t, l, c}, rest))))
        case Lex.TColon{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TColon{}, t, l, c})),
              Lex.Tok{Lex.TColon{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TColon{}, t, l, c},
              rest)))),
            Laws.code(Lex.Tok{Lex.TColon{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TColon{}, t,
              l, c}, rest))), Laws.code(Lex.Tok{Lex.TColon{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TColon{}, t, l, c}), Lex.Tok{Lex.TColon{}, t, l,
              c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TColon{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TColon{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TColon{}, t, l, c}, rest))),
                Laws.code(rest), Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TColon{}, t, l, c}, rest))))
        case Lex.TEq{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TEq{}, t, l, c})),
              Lex.Tok{Lex.TEq{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TEq{}, t, l, c}, rest)))),
            Laws.code(Lex.Tok{Lex.TEq{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TEq{}, t, l,
              c}, rest))), Laws.code(Lex.Tok{Lex.TEq{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TEq{}, t, l, c}), Lex.Tok{Lex.TEq{}, t, l, c} <> Head.heads.go(rest,
              Head.on_mark(st, Lex.Tok{Lex.TEq{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TEq{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TEq{}, t, l, c}, rest))), Laws.code(rest),
                Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TEq{}, t, l, c}, rest))))
        case Lex.TBind{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TBind{}, t, l, c})),
              Lex.Tok{Lex.TBind{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TBind{}, t, l, c},
              rest)))),
            Laws.code(Lex.Tok{Lex.TBind{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TBind{}, t,
              l, c}, rest))), Laws.code(Lex.Tok{Lex.TBind{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TBind{}, t, l, c}), Lex.Tok{Lex.TBind{}, t, l,
              c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TBind{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TBind{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TBind{}, t, l, c}, rest))), Laws.code(rest),
                Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TBind{}, t, l, c}, rest))))
        case Lex.TArrow{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TArrow{}, t, l, c})),
              Lex.Tok{Lex.TArrow{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TArrow{}, t, l, c},
              rest)))),
            Laws.code(Lex.Tok{Lex.TArrow{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TArrow{}, t,
              l, c}, rest))), Laws.code(Lex.Tok{Lex.TArrow{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TArrow{}, t, l, c}), Lex.Tok{Lex.TArrow{}, t, l,
              c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TArrow{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TArrow{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TArrow{}, t, l, c}, rest))),
                Laws.code(rest), Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TArrow{}, t, l, c}, rest))))
        case Lex.TLam{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TLam{}, t, l, c})),
              Lex.Tok{Lex.TLam{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TLam{}, t, l, c},
              rest)))),
            Laws.code(Lex.Tok{Lex.TLam{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TLam{}, t, l,
              c}, rest))), Laws.code(Lex.Tok{Lex.TLam{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TLam{}, t, l, c}), Lex.Tok{Lex.TLam{}, t, l, c} <> Head.heads.go(rest,
              Head.on_mark(st, Lex.Tok{Lex.TLam{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TLam{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TLam{}, t, l, c}, rest))), Laws.code(rest),
                Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TLam{}, t, l, c}, rest))))
        case Lex.TAll{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TAll{}, t, l, c})),
              Lex.Tok{Lex.TAll{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TAll{}, t, l, c},
              rest)))),
            Laws.code(Lex.Tok{Lex.TAll{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TAll{}, t, l,
              c}, rest))), Laws.code(Lex.Tok{Lex.TAll{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TAll{}, t, l, c}), Lex.Tok{Lex.TAll{}, t, l, c} <> Head.heads.go(rest,
              Head.on_mark(st, Lex.Tok{Lex.TAll{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TAll{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TAll{}, t, l, c}, rest))), Laws.code(rest),
                Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TAll{}, t, l, c}, rest))))
        case Lex.TAmp{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TAmp{}, t, l, c})),
              Lex.Tok{Lex.TAmp{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TAmp{}, t, l, c},
              rest)))),
            Laws.code(Lex.Tok{Lex.TAmp{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TAmp{}, t, l,
              c}, rest))), Laws.code(Lex.Tok{Lex.TAmp{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TAmp{}, t, l, c}), Lex.Tok{Lex.TAmp{}, t, l, c} <> Head.heads.go(rest,
              Head.on_mark(st, Lex.Tok{Lex.TAmp{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TAmp{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TAmp{}, t, l, c}, rest))), Laws.code(rest),
                Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TAmp{}, t, l, c}, rest))))
        case Lex.TOpen{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TOpen{}, t, l, c})),
              Lex.Tok{Lex.TOpen{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TOpen{}, t, l, c},
              rest)))),
            Laws.code(Lex.Tok{Lex.TOpen{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TOpen{}, t,
              l, c}, rest))), Laws.code(Lex.Tok{Lex.TOpen{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TOpen{}, t, l, c}), Lex.Tok{Lex.TOpen{}, t, l,
              c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TOpen{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TOpen{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TOpen{}, t, l, c}, rest))), Laws.code(rest),
                Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TOpen{}, t, l, c}, rest))))
        case Lex.TClose{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TClose{}, t, l, c})),
              Lex.Tok{Lex.TClose{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TClose{}, t, l, c},
              rest)))),
            Laws.code(Lex.Tok{Lex.TClose{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TClose{}, t,
              l, c}, rest))), Laws.code(Lex.Tok{Lex.TClose{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TClose{}, t, l, c}), Lex.Tok{Lex.TClose{}, t, l,
              c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TClose{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TClose{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TClose{}, t, l, c}, rest))),
                Laws.code(rest), Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TClose{}, t, l, c}, rest))))
        case Lex.TComma{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TComma{}, t, l, c})),
              Lex.Tok{Lex.TComma{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TComma{}, t, l, c},
              rest)))),
            Laws.code(Lex.Tok{Lex.TComma{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TComma{}, t,
              l, c}, rest))), Laws.code(Lex.Tok{Lex.TComma{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TComma{}, t, l, c}), Lex.Tok{Lex.TComma{}, t, l,
              c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TComma{}, t, l, c}, rest))),
            Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TComma{}, t, 0, 0} <> z,
              Laws.code(Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TComma{}, t, l, c}, rest))),
                Laws.code(rest), Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TComma{}, t, l, c}, rest))))
        case Lex.TComment{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(List.append(&2, Lex.Tok, Head.gap.toks(Head.gap_at(st, Lex.Tok{Lex.TComment{}, t, l, c})),
              Lex.Tok{Lex.TComment{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TComment{}, t, l,
              c}, rest)))),
            Laws.code(Lex.Tok{Lex.TComment{}, t, l, c} <> Head.heads.go(rest, Head.on_mark(st,
              Lex.Tok{Lex.TComment{}, t, l, c}, rest))), Laws.code(Lex.Tok{Lex.TComment{}, t, l, c} <> rest),
            hd.gap(Head.gap_at(st, Lex.Tok{Lex.TComment{}, t, l, c}), Lex.Tok{Lex.TComment{}, t, l,
              c} <> Head.heads.go(rest, Head.on_mark(st, Lex.Tok{Lex.TComment{}, t, l, c}, rest))),
            Laws.heads_keep_code(rest, Head.on_mark(st, Lex.Tok{Lex.TComment{}, t, l, c}, rest)))
        case Lex.TSpace{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(Head.blank(st, Lex.Tok{Lex.TSpace{}, t, l, c}, Head.heads.go(rest, Head.on_space(st, t)))),
            Laws.code(Head.heads.go(rest, Head.on_space(st, t))), Laws.code(rest),
            hd.blank(st, Lex.TSpace{}, t, l, c, Head.heads.go(rest, Head.on_space(st, t)), {==}),
            Laws.heads_keep_code(rest, Head.on_space(st, t)))
        case Lex.TNewline{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(Head.blank(st, Lex.Tok{Lex.TNewline{}, t, l, c}, Head.heads.go(rest, Head.on_line(st)))),
            Laws.code(Head.heads.go(rest, Head.on_line(st))), Laws.code(rest),
            hd.blank(st, Lex.TNewline{}, t, l, c, Head.heads.go(rest, Head.on_line(st)), {==}),
            Laws.heads_keep_code(rest, Head.on_line(st)))

def Laws.heads_pass_other_tokens(k, t, l, c, rest, e):
  match k:
    case Lex.TKey{}:
      s = Equal.sym(Bool, Bool.and(U32.is_eq(c, 0), String.eq(t, "def")), False{}, e)
      %s : {Lex.Tok{Lex.TKey{}, t, l, c} <> Head.heads.go(rest, Lazy.either(Head.State,
          Lazy.and_then(_, _u => Head.needs(rest, 0, 3, False{})), _v => Head.entered(Lex.Tok{Lex.TKey{}, t, l, c}),
          _w => Head.Out{}))
        == Lex.Tok{Lex.TKey{}, t, l, c} <> Head.heads.go(rest, Head.Out{}) : List<&2, Lex.Tok>}
      {==}
    case Lex.TName{}:
      {==}
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      {==}
    case Lex.TWild{}:
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

# an early-exit and whose other side is False is False
law hd.never:
  for b: Bool
  {Lazy.and_then(b, _u => False{}) == False{} : Bool}

def hd.never(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.heads_leave_fitting_header(t, l, c, rest, e):
  s = Equal.sym(Bool, Head.needs(rest, 0, 3, False{}), False{}, e)
  %s : {Lex.Tok{Lex.TKey{}, t, l, c} <> Head.heads.go(rest, Lazy.either(Head.State,
      Lazy.and_then(Bool.and(U32.is_eq(c, 0), String.eq(t, "def")), _u => _),
      _v => Head.entered(Lex.Tok{Lex.TKey{}, t, l, c}), _w => Head.Out{}))
    == Lex.Tok{Lex.TKey{}, t, l, c} <> Head.heads.go(rest, Head.Out{}) : List<&2, Lex.Tok>}
  n = Equal.sym(Bool, Lazy.and_then(Bool.and(U32.is_eq(c, 0), String.eq(t, "def")), _u => False{}), False{},
    hd.never(Bool.and(U32.is_eq(c, 0), String.eq(t, "def"))))
  %n : {Lex.Tok{Lex.TKey{}, t, l, c} <> Head.heads.go(rest, Lazy.either(Head.State, _,
      _v => Head.entered(Lex.Tok{Lex.TKey{}, t, l, c}), _w => Head.Out{}))
    == Lex.Tok{Lex.TKey{}, t, l, c} <> Head.heads.go(rest, Head.Out{}) : List<&2, Lex.Tok>}
  {==}

# a space token adds no code, kept or dropped
law fmt.space:
  for b: Bool
  for -t: String
  for -l: U32
  for -c: U32
  for -more: List<&2, Lex.Tok>
  {Laws.code(Fmt.trim.keep(b, Lex.TSpace{}, t, l, c, more)) == Laws.code(more) : List<&2, Lex.Tok>}

def fmt.space(b, _t, _l, _c, _more):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.trim_keeps_code(toks):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, +t, l, c}, +rest}:
      match k:
        case Lex.TName{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TName{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TUpper{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TUpper{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TDotted{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TDotted{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TWild{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TWild{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TKey{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TKey{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TNum{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TNum{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TStr{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TStr{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TChar{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TChar{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TOp{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TOp{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TColon{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TColon{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TEq{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TEq{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TBind{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TBind{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TArrow{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TArrow{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TLam{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TLam{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TAll{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TAll{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TAmp{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TAmp{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TOpen{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TOpen{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TClose{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TClose{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TComma{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TComma{}, t, 0, 0} <> z,
            Laws.code(Fmt.trim(rest)), Laws.code(rest), Laws.trim_keeps_code(rest))
        case Lex.TComment{}:
          Laws.trim_keeps_code(rest)
        case Lex.TNewline{}:
          Laws.trim_keeps_code(rest)
        case Lex.TSpace{}:
          Equal.trans(List<&2, Lex.Tok>, Laws.code(Fmt.trim.keep(Fmt.trim.ends(rest), Lex.TSpace{}, t, l, c,
            Fmt.trim(rest))),
            Laws.code(Fmt.trim(rest)), Laws.code(rest), fmt.space(Fmt.trim.ends(rest), t, l, c, Fmt.trim(rest)),
            Laws.trim_keeps_code(rest))

# a newline adds no code, kept or dropped, whichever run the rest is read at
law fmt.newline:
  for b: Bool
  for -t: String
  for -l: U32
  for -c: U32
  for -rest: List<&2, Lex.Tok>
  for -run: U32
  for ih1: {Laws.code(Fmt.squeeze(rest, run)) == Laws.code(rest) : List<&2, Lex.Tok>}
  for ih2: {Laws.code(Fmt.squeeze(rest, (run + 1 : U32))) == Laws.code(rest) : List<&2, Lex.Tok>}
  {Laws.code(Bool.pick(List<&2, Lex.Tok>, b, Fmt.squeeze(rest, Bool.pick(U32, b, run, (run + 1 : U32))),
      Lex.Tok{Lex.TNewline{}, t, l, c} <> Fmt.squeeze(rest, Bool.pick(U32, b, run, (run + 1 : U32)))))
    == Laws.code(rest) : List<&2, Lex.Tok>}

def fmt.newline(b, _t, _l, _c, _rest, _run, ih1, ih2):
  match b:
    case True{}:
      ih1
    case False{}:
      ih2

def Laws.squeeze_keeps_code(toks, run):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, +t, +l, +c}, +rest}:
      match k:
        case Lex.TName{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TName{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TUpper{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TUpper{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TDotted{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TDotted{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TWild{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TWild{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TKey{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TKey{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TNum{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TNum{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TStr{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TStr{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TChar{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TChar{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TOp{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TOp{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TColon{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TColon{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TEq{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TEq{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TBind{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TBind{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TArrow{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TArrow{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TLam{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TLam{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TAll{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TAll{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TAmp{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TAmp{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TOpen{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TOpen{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TClose{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TClose{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TComma{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TComma{}, t, 0, 0} <> z,
            Laws.code(Fmt.squeeze(rest, 0)), Laws.code(rest), Laws.squeeze_keeps_code(rest, 0))
        case Lex.TComment{}:
          Laws.squeeze_keeps_code(rest, 0)
        case Lex.TSpace{}:
          Laws.squeeze_keeps_code(rest, 0)
        case Lex.TNewline{}:
          fmt.newline(U32.is_ge(run, 2), t, l, c, rest, run, Laws.squeeze_keeps_code(rest, run),
            Laws.squeeze_keeps_code(rest, (run + 1 : U32)))

# newlines alone hold no code: taking them for nothing keeps the code
law fmt.only:
  for toks: List<&2, Lex.Tok>
  {Laws.code(Bool.pick(List<&2, Lex.Tok>, Fmt.close.only(toks), Nil{}, toks)) == Laws.code(toks) : List<&2, Lex.Tok>}

# a newline in front of newlines alone is still no code
law fmt.only.step:
  for b: Bool
  for -t: String
  for -l: U32
  for -c: U32
  for -rest: List<&2, Lex.Tok>
  {Laws.code(Bool.pick(List<&2, Lex.Tok>, b, Nil{}, Lex.Tok{Lex.TNewline{}, t, l, c} <> rest))
    == Laws.code(Bool.pick(List<&2, Lex.Tok>, b, Nil{}, rest)) : List<&2, Lex.Tok>}

def fmt.only.step(b, _t, _l, _c, _rest):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def fmt.only(toks):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, +t, +l, +c}, +rest}:
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
        case Lex.TComment{}:
          {==}
        case Lex.TSpace{}:
          {==}
        case Lex.TNewline{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(Bool.pick(List<&2, Lex.Tok>, Fmt.close.only(rest), Nil{}, Lex.Tok{Lex.TNewline{}, t, l,
              c} <> rest)),
            Laws.code(Bool.pick(List<&2, Lex.Tok>, Fmt.close.only(rest), Nil{}, rest)), Laws.code(rest),
            fmt.only.step(Fmt.close.only(rest), t, l, c, rest), fmt.only(rest))

# the newlines a file ends in, made one, hold the code of what they were
law fmt.end:
  for b: Bool
  for -t: String
  for -l: U32
  for -c: U32
  for -rest: List<&2, Lex.Tok>
  for ih: {Laws.code(Fmt.close.go(rest)) == Laws.code(rest) : List<&2, Lex.Tok>}
  {Laws.code(Lazy.stop(List<&2, Lex.Tok>, b, [Fmt.close.newline()],
      _v => Lex.Tok{Lex.TNewline{}, t, l, c} <> Fmt.close.go(rest)))
    == Laws.code(Bool.pick(List<&2, Lex.Tok>, b, Nil{}, rest)) : List<&2, Lex.Tok>}

def fmt.end(b, _t, _l, _c, _rest, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# close's walk keeps the code
law fmt.close:
  for toks: List<&2, Lex.Tok>
  {Laws.code(Fmt.close.go(toks)) == Laws.code(toks) : List<&2, Lex.Tok>}

def fmt.close(toks):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, +t, +l, +c}, +rest}:
      match k:
        case Lex.TName{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TName{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TUpper{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TUpper{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TDotted{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TDotted{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TWild{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TWild{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TKey{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TKey{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TNum{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TNum{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TStr{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TStr{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TChar{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TChar{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TOp{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TOp{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TColon{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TColon{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TEq{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TEq{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TBind{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TBind{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TArrow{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TArrow{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TLam{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TLam{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TAll{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TAll{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TAmp{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TAmp{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TOpen{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TOpen{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TClose{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TClose{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TComma{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, z => Lex.Tok{Lex.TComma{}, t, 0, 0} <> z,
            Laws.code(Fmt.close.go(rest)), Laws.code(rest), fmt.close(rest))
        case Lex.TComment{}:
          fmt.close(rest)
        case Lex.TSpace{}:
          fmt.close(rest)
        case Lex.TNewline{}:
          Equal.trans(List<&2, Lex.Tok>,
            Laws.code(Lazy.stop(List<&2, Lex.Tok>, Fmt.close.only(rest), [Fmt.close.newline()],
              _v => Lex.Tok{Lex.TNewline{}, t, l, c} <> Fmt.close.go(rest))),
            Laws.code(Bool.pick(List<&2, Lex.Tok>, Fmt.close.only(rest), Nil{}, rest)), Laws.code(rest),
            fmt.end(Fmt.close.only(rest), t, l, c, rest, fmt.close(rest)), fmt.only(rest))

# whichever of two token lists is taken, the code is the first's when the
# second's is
law fmt.either:
  for b: Bool
  for -x: List<&2, Lex.Tok>
  for -y: List<&2, Lex.Tok>
  for e: {Laws.code(y) == Laws.code(x) : List<&2, Lex.Tok>}
  {Laws.code(Lazy.either(List<&2, Lex.Tok>, b, _u => x, _v => y)) == Laws.code(x) : List<&2, Lex.Tok>}

def fmt.either(b, _x, _y, e):
  match b:
    case True{}:
      {==}
    case False{}:
      e

def Laws.close_keeps_code(toks):
  match toks:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      fmt.either(Fmt.close.shut(h <> t), h <> t, Fmt.close.go(h <> t), fmt.close(h <> t))

def Laws.close_adds_final_newline(k, t, l, c, e, b):
  s = Equal.sym(Bool, Fmt.is_newline(k), False{}, e)
  %s : {Lazy.either(List<&2, Lex.Tok>, Bool.and(Bool.not(_), Fmt.close.broken(t)), _u => [Lex.Tok{k, t, l, c}],
      _v => Lazy.stop(List<&2, Lex.Tok>, Lazy.and_then(_, _w => Fmt.close.only(Nil{})), [Fmt.close.newline()],
        _z => Lex.Tok{k, t, l, c} <> Fmt.close.go(Nil{})))
    == [Lex.Tok{k, t, l, c}, Fmt.close.newline()] : List<&2, Lex.Tok>}
  n = Equal.sym(Bool, Fmt.close.broken(t), False{}, b)
  %n : {Lazy.either(List<&2, Lex.Tok>, _, _u => [Lex.Tok{k, t, l, c}],
      _v => [Lex.Tok{k, t, l, c}, Fmt.close.newline()])
    == [Lex.Tok{k, t, l, c}, Fmt.close.newline()] : List<&2, Lex.Tok>}
  {==}

def Laws.close_leaves_unclosed_string(toks, e):
  match toks:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      s = Equal.sym(Bool, Fmt.close.shut(h <> t), True{}, e)
      %s : {Lazy.either(List<&2, Lex.Tok>, _, _u => h <> t, _v => Fmt.close.go(h <> t)) == h <> t
        : List<&2, Lex.Tok>}
      {==}

# newlines alone are newlines alone
law fmt.all:
  for kn: Nat
  {Fmt.close.only(Laws.newlines(kn)) == True{} : Bool}

def fmt.all(kn):
  match kn:
    case 0n:
      {==}
    case 1n+p:
      fmt.all(p)

def Laws.close_newlines_to_one(kn):
  match kn:
    case 0n:
      {==}
    case 1n+p:
      s = Equal.sym(Bool, Fmt.close.only(Laws.newlines(p)), True{}, fmt.all(p))
      %s : {Lazy.stop(List<&2, Lex.Tok>, _, [Fmt.close.newline()],
          _v => Lex.Tok{Lex.TNewline{}, "\n", 0, 0} <> Fmt.close.go(Laws.newlines(p)))
        == [Fmt.close.newline()] : List<&2, Lex.Tok>}
      {==}

def Laws.fmt_keeps_code(toks):
  +hd = Head.heads(toks)
  Equal.trans(List<&2, Lex.Tok>, Laws.code(Fmt.close(Fmt.squeeze(Fmt.trim(hd), Fmt.squeeze.most()))),
    Laws.code(Fmt.squeeze(Fmt.trim(hd), Fmt.squeeze.most())), Laws.code(toks),
    Laws.close_keeps_code(Fmt.squeeze(Fmt.trim(hd), Fmt.squeeze.most())),
    Equal.trans(List<&2, Lex.Tok>, Laws.code(Fmt.squeeze(Fmt.trim(hd), Fmt.squeeze.most())), Laws.code(Fmt.trim(hd)),
      Laws.code(toks), Laws.squeeze_keeps_code(Fmt.trim(hd), Fmt.squeeze.most()),
      Equal.trans(List<&2, Lex.Tok>, Laws.code(Fmt.trim(hd)), Laws.code(hd), Laws.code(toks), Laws.trim_keeps_code(hd),
        Laws.heads_keep_code(toks, Head.Out{}))))
