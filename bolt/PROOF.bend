# bolt: the proofs. `bend PROOF.bend` is the gate.
import Base
import ../lazy/lazy.bend as Lazy
import ./config.bend as Config
import ./finding.bend as F
import ./rules.bend as Rules
import ./LAWS.bend as Laws

def Laws.set_level_none(_name):
  {==}

def Laws.set_level_first(sets, name, nn, ll, h):
  e = Equal.sym(Bool, String.eq(nn, name), True{}, h)
  %e : {Bool.pick(Maybe<&2, Config.Level>, _, Some{ll}, Config.set_level(sets, name)) == Some{ll}
    : Maybe<&2, Config.Level>}
  {==}

def Laws.set_level_skip(sets, name, nn, ll, h):
  e = Equal.sym(Bool, String.eq(nn, name), False{}, h)
  %e : {Bool.pick(Maybe<&2, Config.Level>, _, Some{ll}, Config.set_level(sets, name))
    == Config.set_level(sets, name) : Maybe<&2, Config.Level>}
  {==}

def Laws.level_own(sets, group, rule, l, h):
  e = Equal.sym(Maybe<&2, Config.Level>, Config.set_level(sets, rule), Some{l}, h)
  %e : {Maybe.default(&2, Config.Level, _,
    Lazy.stop(Config.Level, Config.opt_in(rule), Config.Off{},
      _u => Maybe.default(&2, Config.Level, Config.set_level(sets, group), Config.default(group))))
    == l : Config.Level}
  {==}

def Laws.level_group(sets, group, rule, l, h_rule, h_opt, h_group):
  r = Equal.sym(Maybe<&2, Config.Level>, Config.set_level(sets, rule), None{}, h_rule)
  %r : {Maybe.default(&2, Config.Level, _,
    Lazy.stop(Config.Level, Config.opt_in(rule), Config.Off{},
      _u => Maybe.default(&2, Config.Level, Config.set_level(sets, group), Config.default(group))))
    == l : Config.Level}
  o = Equal.sym(Bool, Config.opt_in(rule), False{}, h_opt)
  %o : {Lazy.stop(Config.Level, _, Config.Off{},
      _u => Maybe.default(&2, Config.Level, Config.set_level(sets, group), Config.default(group)))
    == l : Config.Level}
  g = Equal.sym(Maybe<&2, Config.Level>, Config.set_level(sets, group), Some{l}, h_group)
  %g : {Maybe.default(&2, Config.Level, _, Config.default(group)) == l : Config.Level}
  {==}

def Laws.level_default(sets, group, rule, h_rule, h_opt, h_group):
  r = Equal.sym(Maybe<&2, Config.Level>, Config.set_level(sets, rule), None{}, h_rule)
  %r : {Maybe.default(&2, Config.Level, _,
    Lazy.stop(Config.Level, Config.opt_in(rule), Config.Off{},
      _u => Maybe.default(&2, Config.Level, Config.set_level(sets, group), Config.default(group))))
    == Config.default(group) : Config.Level}
  o = Equal.sym(Bool, Config.opt_in(rule), False{}, h_opt)
  %o : {Lazy.stop(Config.Level, _, Config.Off{},
      _u => Maybe.default(&2, Config.Level, Config.set_level(sets, group), Config.default(group)))
    == Config.default(group) : Config.Level}
  g = Equal.sym(Maybe<&2, Config.Level>, Config.set_level(sets, group), None{}, h_group)
  %g : {Maybe.default(&2, Config.Level, _, Config.default(group)) == Config.default(group) : Config.Level}
  {==}

# one finding graded the way the rest were: grading's pick agrees with keep
law grade.step:
  for ll: Config.Level
  for -ff: F.Finding
  for -a: List<&2, F.Graded>
  for -b: List<&2, F.Graded>
  for e: {a == b : List<&2, F.Graded>}
  {Bool.pick(List<&2, F.Graded>, Config.is_off(ll), a, F.Graded{ll, ff} <> a)
    == Laws.keep(ll, ff, b) : List<&2, F.Graded>}

def grade.step(ll, ff, a, _b, e):
  match ll:
    case Config.Off{}:
      e
    case Config.Warn{}:
      %e : {F.Graded{Config.Warn{}, ff} <> a == F.Graded{Config.Warn{}, ff} <> _ : List<&2, F.Graded>}
      {==}
    case Config.Error{}:
      %e : {F.Graded{Config.Error{}, ff} <> a == F.Graded{Config.Error{}, ff} <> _ : List<&2, F.Graded>}
      {==}

def Laws.graded_keeps(cfg, fs):
  match fs:
    case Nil{}:
      {==}
    case Con{F.Finding{path, line, col, len, +rule, msg}, rest}:
      grade.step(Config.level(cfg, Rules.group(rule), rule), F.Finding{path, line, col, len, rule, msg},
        Rules.graded(cfg, rest), Laws.kept(cfg, rest), Laws.graded_keeps(cfg, rest))

def Laws.word_error(ww, h_off, h_warn):
  o = Equal.sym(Bool, String.eq(ww, "off"), False{}, h_off)
  %o : {Bool.pick(Config.Level, _, Config.Off{},
      Bool.pick(Config.Level, String.eq(ww, "warn"), Config.Warn{}, Config.Error{}))
    == Config.Error{} : Config.Level}
  w = Equal.sym(Bool, String.eq(ww, "warn"), False{}, h_warn)
  %w : {Bool.pick(Config.Level, _, Config.Warn{}, Config.Error{}) == Config.Error{} : Config.Level}
  {==}

def Laws.default_correctness(group, h):
  e = Equal.sym(String, group, "correctness", h)
  %e : {Config.default(_) == Config.Error{} : Config.Level}
  {==}

def Laws.default_pedantic(group, h):
  e = Equal.sym(String, group, "pedantic", h)
  %e : {Config.default(_) == Config.Off{} : Config.Level}
  {==}

def Laws.default_rest(group, h_c, h_p):
  c = Equal.sym(Bool, String.eq(group, "correctness"), False{}, h_c)
  %c : {Bool.pick(Config.Level, _, Config.Error{},
      Bool.pick(Config.Level, String.eq(group, "pedantic"), Config.Off{}, Config.Warn{}))
    == Config.Warn{} : Config.Level}
  p = Equal.sym(Bool, String.eq(group, "pedantic"), False{}, h_p)
  %p : {Bool.pick(Config.Level, _, Config.Off{}, Config.Warn{}) == Config.Warn{} : Config.Level}
  {==}

def Laws.opt_in_off(sets, group, rule, h_opt, h_rule):
  r = Equal.sym(Maybe<&2, Config.Level>, Config.set_level(sets, rule), None{}, h_rule)
  %r : {Maybe.default(&2, Config.Level, _,
    Lazy.stop(Config.Level, Config.opt_in(rule), Config.Off{},
      _u => Maybe.default(&2, Config.Level, Config.set_level(sets, group), Config.default(group))))
    == Config.Off{} : Config.Level}
  o = Equal.sym(Bool, Config.opt_in(rule), True{}, h_opt)
  %o : {Lazy.stop(Config.Level, _, Config.Off{},
      _u => Maybe.default(&2, Config.Level, Config.set_level(sets, group), Config.default(group)))
    == Config.Off{} : Config.Level}
  {==}
