# proofs of laws/FmtPlansEdits.bend
import Base
import ../src/fmt.bend as Fmt
import ../src/lazy/lazy.bend as Lazy
import ../src/fmt/plan.bend as Fp
import ../src/lint/plan.bend as Lint
import ../laws/FmtPlansEdits.bend as Laws

def Laws.fmt_reads_lint_inputs(_check, _world):
  {==}

def Laws.fmt_check_writes_nothing(_gs):
  {==}

def Laws.fmt_writes_every_edit(_gs):
  {==}

def Laws.fmt_same_text_no_edit(path, text, rest, e):
  s = Equal.sym(Bool, String.eq(Fmt.text(text), text), True{}, e)
  %s : {Fp.edits.of(Fp.Fated{path, Lazy.either(Fp.Fate, _, _u => Fp.FSame{}, _v => Fp.fate.changed(Fp.safe(text),
    Fmt.text(text)))} <> Fp.fates(rest)) == Fp.edits(rest) : List<&2, Fp.Edit>}
  {==}

def Laws.fmt_changed_text_one_edit(path, text, rest, e, ok):
  s = Equal.sym(Bool, String.eq(Fmt.text(text), text), False{}, e)
  %s : {Fp.edits.of(Fp.Fated{path, Lazy.either(Fp.Fate, _, _u => Fp.FSame{}, _v => Fp.fate.changed(Fp.safe(text),
    Fmt.text(text)))} <> Fp.fates(rest)) == Fp.Edit{path, Fmt.text(text)} <> Fp.edits(rest)
    : List<&2, Fp.Edit>}
  k = Equal.sym(Bool, Fp.safe(text), True{}, ok)
  %k : {Fp.edits.of(Fp.Fated{path, Fp.fate.changed(_, Fmt.text(text))} <> Fp.fates(rest))
    == Fp.Edit{path, Fmt.text(text)} <> Fp.edits(rest) : List<&2, Fp.Edit>}
  {==}

def Laws.fmt_not_utf8_no_edit(path, text, rest, e, ok):
  s = Equal.sym(Bool, String.eq(Fmt.text(text), text), False{}, e)
  %s : {Fp.edits.of(Fp.Fated{path, Lazy.either(Fp.Fate, _, _u => Fp.FSame{}, _v => Fp.fate.changed(Fp.safe(text),
    Fmt.text(text)))} <> Fp.fates(rest)) == Fp.edits(rest) : List<&2, Fp.Edit>}
  k = Equal.sym(Bool, Fp.safe(text), False{}, ok)
  %k : {Fp.edits.of(Fp.Fated{path, Fp.fate.changed(_, Fmt.text(text))} <> Fp.fates(rest)) == Fp.edits(rest)
    : List<&2, Fp.Edit>}
  {==}

def Laws.fmt_unread_no_edit(_path, _rest):
  {==}

def Laws.fmt_check_fails_on_change(_path, _text, _es, bad):
  match bad:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def Laws.fmt_unread_fails(check, es, _path, _bad):
  match check:
    case True{}:
      match es:
        case Nil{}:
          {==}
        case Con{h, t}:
          {==}
    case False{}:
      {==}

def Laws.fmt_write_succeeds(_es):
  {==}

# checking or not, no edit, no skipped file and no unread path is the clean
# plan
law fp.clean:
  for check: Bool
  {Fp.Plan{Fp.written(check, Nil{}), Fp.lines.or(List.append(&2, String, Fp.said("cannot read", Nil{}),
      List.append(&2, String, Fp.said("skipped (not UTF-8)", Nil{}), Fp.said(Fp.word(check), Fp.paths(Nil{}))))),
      Fp.exit(check, Nil{}, Nil{})}
    == Fp.Plan{Nil{}, ["clean"], 0} : Fp.Plan}

def fp.clean(check):
  match check:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.fmt_clean(check, gs, e1, e2, e3):
  s1 = Equal.sym(List<&2, Fp.Edit>, Fp.edits(gs), Nil{}, e1)
  %s1 : {Fp.Plan{Fp.written(check, _), Fp.lines.or(List.append(&2, String, Fp.said("cannot read", Fp.unread(gs)),
      List.append(&2, String, Fp.said("skipped (not UTF-8)", Fp.skipped(gs)), Fp.said(Fp.word(check), Fp.paths(_))))),
      Fp.exit(check, _, Fp.unread(gs))}
    == Fp.Plan{Nil{}, ["clean"], 0} : Fp.Plan}
  s2 = Equal.sym(List<&2, String>, Fp.unread(gs), Nil{}, e2)
  %s2 : {Fp.Plan{Fp.written(check, Nil{}), Fp.lines.or(List.append(&2, String, Fp.said("cannot read", _),
      List.append(&2, String, Fp.said("skipped (not UTF-8)", Fp.skipped(gs)),
        Fp.said(Fp.word(check), Fp.paths(Nil{}))))), Fp.exit(check, Nil{}, _)}
    == Fp.Plan{Nil{}, ["clean"], 0} : Fp.Plan}
  s3 = Equal.sym(List<&2, String>, Fp.skipped(gs), Nil{}, e3)
  %s3 : {Fp.Plan{Fp.written(check, Nil{}), Fp.lines.or(List.append(&2, String, Fp.said("cannot read", Nil{}),
      List.append(&2, String, Fp.said("skipped (not UTF-8)", _), Fp.said(Fp.word(check), Fp.paths(Nil{}))))),
      Fp.exit(check, Nil{}, Nil{})}
    == Fp.Plan{Nil{}, ["clean"], 0} : Fp.Plan}
  fp.clean(check)
