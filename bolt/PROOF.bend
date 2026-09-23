# bolt: the proofs. `bend PROOF.bend` is the gate.
import Base
import ../lazy/lazy.bend as Lazy
import ./config.bend as Config
import ./finding.bend as F
import ./rules.bend as Rules
import ./src.bend as Src
import ./lint/world.bend as W
import ./lint/plan.bend as Plan
import ./rules/digest.bend as Digest
import ./rules/laws/law.bend as Law
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

# one arm per row of the code table (29), each checked by evaluation, and one
# past its end, where both sides are none: a new rule is a new arm here
def Laws.slug_finds_row(n):
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n:
      {==}
    case 17n:
      {==}
    case 18n:
      {==}
    case 19n:
      {==}
    case 20n:
      {==}
    case 21n:
      {==}
    case 22n:
      {==}
    case 23n:
      {==}
    case 24n:
      {==}
    case 25n:
      {==}
    case 26n:
      {==}
    case 27n:
      {==}
    case 28n:
      {==}
    case 29n+_p:
      {==}

# the same arms, looked up by code
def Laws.code_finds_row(n):
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n:
      {==}
    case 17n:
      {==}
    case 18n:
      {==}
    case 19n:
      {==}
    case 20n:
      {==}
    case 21n:
      {==}
    case 22n:
      {==}
    case 23n:
      {==}
    case 24n:
      {==}
    case 25n:
      {==}
    case 26n:
      {==}
    case 27n:
      {==}
    case 28n:
      {==}
    case 29n+_p:
      {==}

def Laws.shown(_path, _line, _col, _len, _rule, _msg, _level):
  {==}

# The lint planner. Every proof below is by induction over a list the
# planner folds (the questions, the source paths, the findings, the graded
# findings), with a step lemma that takes the one computed value the step
# branches on as a variable and cases on it.

# appending nothing leaves a list as it was
law lint.app_nil:
  for -A: Kind(&2)
  for xs: List<&2, A>
  {List.append(&2, A, xs, []) == xs : List<&2, A>}

def lint.app_nil(A, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{hd, +tl}:
      Equal.cong(List<&2, A>, List<&2, A>, rr => hd <> rr, List.append(&2, A, tl, []), tl, lint.app_nil(A, tl))

# `and` regroups
law lint.and_assoc:
  for aa: Bool
  for bb: Bool
  for cc: Bool
  {Bool.and(aa, Bool.and(bb, cc)) == Bool.and(Bool.and(aa, bb), cc) : Bool}

def lint.and_assoc(aa, _bb, _cc):
  match aa:
    case True{}:
      {==}
    case False{}:
      {==}

# a World answers two lists of questions when it answers each
law lint.all_app:
  for xs: List<&2, W.Ask>
  for +ys: List<&2, W.Ask>
  for +world: W.World
  {Laws.answered_all(world, List.append(&2, W.Ask, xs, ys))
    == Bool.and(Laws.answered_all(world, xs), Laws.answered_all(world, ys)) : Bool}

def lint.all_app(xs, ys, world):
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +tl}:
      e = Equal.sym(Bool, Laws.answered_all(world, List.append(&2, W.Ask, tl, ys)),
        Bool.and(Laws.answered_all(world, tl), Laws.answered_all(world, ys)), lint.all_app(tl, ys, world))
      %e : {Bool.and(W.answered(world, a), _)
        == Bool.and(Bool.and(W.answered(world, a), Laws.answered_all(world, tl)), Laws.answered_all(world, ys)) : Bool}
      lint.and_assoc(W.answered(world, a), Laws.answered_all(world, tl), Laws.answered_all(world, ys))

# one question onto a list the tie holds for
law lint.all_open.step:
  for bb: Bool
  for +a: W.Ask
  for -more: Bool
  for +opn: List<&2, W.Ask>
  for ih: {more == List.is_empty(&2, W.Ask, opn) : Bool}
  {Bool.and(bb, more) == List.is_empty(&2, W.Ask, Bool.pick(List<&2, W.Ask>, bb, opn, a <> opn)) : Bool}

def lint.all_open.step(bb, _a, _more, _opn, ih):
  match bb:
    case True{}:
      ih
    case False{}:
      {==}

# a World answers every question exactly when none is left unanswered
law lint.all_open:
  for xs: List<&2, W.Ask>
  for +world: W.World
  {Laws.answered_all(world, xs) == List.is_empty(&2, W.Ask, Plan.unanswered(xs, world)) : Bool}

def lint.all_open(xs, world):
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +tl}:
      lint.all_open.step(W.answered(world, a), a, Laws.answered_all(world, tl), Plan.unanswered(tl, world),
        lint.all_open(tl, world))

# wants is empty exactly when no listing and no text is open
law lint.tie_pick:
  for oo: List<&2, W.Ask>
  for +world: W.World
  {Bool.and(List.is_empty(&2, W.Ask, oo), List.is_empty(&2, W.Ask, Plan.unanswered(Plan.texts(world), world)))
    == List.is_empty(&2, W.Ask, Plan.wants.pick(oo, world)) : Bool}

def lint.tie_pick(oo, _world):
  match oo:
    case Nil{}:
      {==}
    case Con{_a, _tl}:
      {==}

def Laws.wants_tie(world):
  t1 = Equal.sym(Bool, Laws.answered_all(world, Plan.looks(world)),
    Bool.and(Laws.answered_all(world, Plan.lists(world)), Laws.answered_all(world, Plan.texts(world))),
    lint.all_app(Plan.lists(world), Plan.texts(world), world))
  %t1 : {_ == List.is_empty(&2, W.Ask, Plan.wants(world)) : Bool}
  e1 = Equal.sym(Bool, Laws.answered_all(world, Plan.lists(world)),
    List.is_empty(&2, W.Ask, Plan.unanswered(Plan.lists(world), world)), lint.all_open(Plan.lists(world), world))
  %e1 : {Bool.and(_, Laws.answered_all(world, Plan.texts(world))) == List.is_empty(&2, W.Ask, Plan.wants(world))
    : Bool}
  e2 = Equal.sym(Bool, Laws.answered_all(world, Plan.texts(world)),
    List.is_empty(&2, W.Ask, Plan.unanswered(Plan.texts(world), world)), lint.all_open(Plan.texts(world), world))
  %e2 : {Bool.and(List.is_empty(&2, W.Ask, Plan.unanswered(Plan.lists(world), world)), _)
    == List.is_empty(&2, W.Ask, Plan.wants(world)) : Bool}
  lint.tie_pick(Plan.unanswered(Plan.lists(world), world), world)

# one path onto a list with no bolt.bend, kept or dropped as the planner
# decides
law lint.no_config.pick:
  for bb: Bool
  for +p: String
  for +more: List<&2, String>
  for h: {Plan.is_config(p) == bb : Bool}
  for ih: {Laws.no_config(more) == True{} : Bool}
  {Laws.no_config(Bool.pick(List<&2, String>, bb, more, p <> more)) == True{} : Bool}

def lint.no_config.pick(bb, p, more, h, ih):
  match bb:
    case True{}:
      ih
    case False{}:
      e = Equal.sym(Bool, Plan.is_config(p), False{}, h)
      %e : {Bool.and(Bool.not(_), Laws.no_config(more)) == True{} : Bool}
      ih

# no source the planner keeps is a bolt.bend
law lint.no_config:
  for ps: List<&2, String>
  {Laws.no_config(Plan.sources(ps)) == True{} : Bool}

def lint.no_config(ps):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +tl}:
      lint.no_config.pick(Plan.is_config(p), p, Plan.sources(tl), {==}, lint.no_config(tl))

def Laws.no_config_linted(world):
  lint.no_config(Plan.files(world))

# one source onto the read failures
law lint.unread.step:
  for +path: String
  for mm: Maybe<&2, String>
  for gs: List<&2, Plan.Got>
  for -us: List<&2, F.Finding>
  for ih: {Plan.unread(gs) == us : List<&2, F.Finding>}
  {Plan.unread(Plan.Got{path, mm} <> gs) == List.append(&2, F.Finding, Laws.unread_at(path, mm), us)
    : List<&2, F.Finding>}

def lint.unread.step(path, mm, gs, us, ih):
  match mm:
    case None{}:
      Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
        rr => F.Finding{path, 0, 0, 0, "read", "Cannot read this file."} <> rr, Plan.unread(gs), us, ih)
    case Some{_text}:
      ih

# the planner's read failures are the spec's
law lint.unread:
  for ps: List<&2, String>
  for +world: W.World
  {Plan.unread(Plan.gots(ps, world)) == Laws.unread_all(world, ps) : List<&2, F.Finding>}

def lint.unread(ps, world):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +tl}:
      lint.unread.step(p, W.text(world, p), Plan.gots(tl, world), Laws.unread_all(world, tl), lint.unread(tl, world))

# one source onto the parsed sources
law lint.parsed.step:
  for +path: String
  for mm: Maybe<&2, String>
  for gs: List<&2, Plan.Got>
  for -ss: List<&2, Src.Src>
  for ih: {Plan.srcs_of(gs) == ss : List<&2, Src.Src>}
  {Plan.srcs_of(Plan.Got{path, mm} <> gs) == List.append(&2, Src.Src, Laws.parsed_at(path, mm), ss)
    : List<&2, Src.Src>}

def lint.parsed.step(path, mm, gs, ss, ih):
  match mm:
    case None{}:
      ih
    case Some{text}:
      Equal.cong(List<&2, Src.Src>, List<&2, Src.Src>, rr => Src.of(path, text) <> rr, Plan.srcs_of(gs), ss, ih)

# the planner parses each source it has a text for, in order
law lint.parsed:
  for ps: List<&2, String>
  for +world: W.World
  {Plan.srcs_of(Plan.gots(ps, world)) == Laws.parsed_all(world, ps) : List<&2, Src.Src>}

def lint.parsed(ps, world):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +tl}:
      lint.parsed.step(p, W.text(world, p), Plan.gots(tl, world), Laws.parsed_all(world, tl), lint.parsed(tl, world))

# one source onto the per-file findings
law lint.on.step:
  for +path: String
  for mm: Maybe<&2, String>
  for +gs: List<&2, Plan.Got>
  for -os: List<&2, F.Finding>
  for ih: {Plan.per_file(Plan.srcs_of(gs)) == os : List<&2, F.Finding>}
  {Plan.per_file(Plan.srcs_of(Plan.Got{path, mm} <> gs)) == List.append(&2, F.Finding, Laws.on_at(path, mm), os)
    : List<&2, F.Finding>}

def lint.on.step(path, mm, gs, os, ih):
  match mm:
    case None{}:
      ih
    case Some{text}:
      Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
        rr => List.append(&2, F.Finding, Rules.on(Src.of(path, text)), rr),
        List.append(&2, F.Finding, Plan.per_file(Plan.srcs_of(gs)), []), os,
        Equal.trans(List<&2, F.Finding>, List.append(&2, F.Finding, Plan.per_file(Plan.srcs_of(gs)), []),
          Plan.per_file(Plan.srcs_of(gs)), os, lint.app_nil(F.Finding, Plan.per_file(Plan.srcs_of(gs))), ih))

# the planner's per-file findings are each source's alone, in order
law lint.on:
  for ps: List<&2, String>
  for +world: W.World
  {Plan.per_file(Plan.srcs_of(Plan.gots(ps, world))) == Laws.on_all(world, ps) : List<&2, F.Finding>}

def lint.on(ps, world):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +tl}:
      lint.on.step(p, W.text(world, p), Plan.gots(tl, world), Laws.on_all(world, tl), lint.on(tl, world))

def Laws.scope_findings(world):
  n = Equal.sym(List<&2, F.Finding>,
    List.append(&2, F.Finding, Rules.project(Plan.srcs_of(Plan.gots(Plan.inputs(world), world)),
      List.is_empty(&2, String, W.paths.of(world)), W.text(world, "SPEC.md")), []),
    Rules.project(Plan.srcs_of(Plan.gots(Plan.inputs(world), world)),
      List.is_empty(&2, String, W.paths.of(world)), W.text(world, "SPEC.md")),
    lint.app_nil(F.Finding, Rules.project(Plan.srcs_of(Plan.gots(Plan.inputs(world), world)),
      List.is_empty(&2, String, W.paths.of(world)), W.text(world, "SPEC.md"))))
  %n : {List.append(&2, F.Finding, Plan.unread(Plan.gots(Plan.inputs(world), world)),
      List.append(&2, F.Finding, Plan.per_file(Plan.srcs_of(Plan.gots(Plan.inputs(world), world))), _))
    == Laws.in_scope(world) : List<&2, F.Finding>}
  a = Equal.sym(List<&2, F.Finding>, Plan.unread(Plan.gots(Plan.inputs(world), world)),
    Laws.unread_all(world, Plan.inputs(world)), lint.unread(Plan.inputs(world), world))
  %a : {List.append(&2, F.Finding, _,
      List.append(&2, F.Finding, Plan.per_file(Plan.srcs_of(Plan.gots(Plan.inputs(world), world))),
        Rules.project(Plan.srcs_of(Plan.gots(Plan.inputs(world), world)),
          List.is_empty(&2, String, W.paths.of(world)), W.text(world, "SPEC.md"))))
    == Laws.in_scope(world) : List<&2, F.Finding>}
  b = Equal.sym(List<&2, F.Finding>, Plan.per_file(Plan.srcs_of(Plan.gots(Plan.inputs(world), world))),
    Laws.on_all(world, Plan.inputs(world)), lint.on(Plan.inputs(world), world))
  %b : {List.append(&2, F.Finding, Laws.unread_all(world, Plan.inputs(world)),
      List.append(&2, F.Finding, _,
        Rules.project(Plan.srcs_of(Plan.gots(Plan.inputs(world), world)),
          List.is_empty(&2, String, W.paths.of(world)), W.text(world, "SPEC.md"))))
    == Laws.in_scope(world) : List<&2, F.Finding>}
  c = Equal.sym(List<&2, Src.Src>, Plan.srcs_of(Plan.gots(Plan.inputs(world), world)),
    Laws.parsed_all(world, Plan.inputs(world)), lint.parsed(Plan.inputs(world), world))
  %c : {List.append(&2, F.Finding, Laws.unread_all(world, Plan.inputs(world)),
      List.append(&2, F.Finding, Laws.on_all(world, Plan.inputs(world)),
        Rules.project(_, List.is_empty(&2, String, W.paths.of(world)), W.text(world, "SPEC.md"))))
    == Laws.in_scope(world) : List<&2, F.Finding>}
  {==}

# one finding graded the planner's way is graded the spec's way
law lint.grade.step:
  for ll: Config.Level
  for -ff: F.Finding
  for -a: List<&2, F.Graded>
  for -b: List<&2, F.Graded>
  for e: {a == b : List<&2, F.Graded>}
  {List.append(&2, F.Graded, Bool.pick(List<&2, F.Graded>, Config.is_off(ll), [], [F.Graded{ll, ff}]), a)
    == Laws.keep(ll, ff, b) : List<&2, F.Graded>}

def lint.grade.step(ll, ff, a, _b, e):
  match ll:
    case Config.Off{}:
      e
    case Config.Warn{}:
      %e : {F.Graded{Config.Warn{}, ff} <> a == F.Graded{Config.Warn{}, ff} <> _ : List<&2, F.Graded>}
      {==}
    case Config.Error{}:
      %e : {F.Graded{Config.Error{}, ff} <> a == F.Graded{Config.Error{}, ff} <> _ : List<&2, F.Graded>}
      {==}

# the planner grades each finding by its path's config, in order
law lint.grade:
  for +cs: List<&2, Plan.Conf>
  for +world: W.World
  for fs: List<&2, F.Finding>
  {Plan.grade(cs, world, fs) == Laws.graded_by(cs, world, fs) : List<&2, F.Graded>}

def lint.grade(cs, world, fs):
  match fs:
    case Nil{}:
      {==}
    case Con{F.Finding{+path, line, col, len, +rule, msg}, +tl}:
      lint.grade.step(Config.level(Plan.config.at(cs, world, path), Rules.group(rule), rule),
        F.Finding{path, line, col, len, rule, msg}, Plan.grade(cs, world, tl), Laws.graded_by(cs, world, tl),
        lint.grade(cs, world, tl))

# the planner's graded findings are the run's
law lint.graded:
  for +world: W.World
  {Plan.graded(world) == Laws.run_graded(world) : List<&2, F.Graded>}

def lint.graded(world):
  e = Equal.sym(List<&2, F.Finding>, Plan.found(world), Laws.in_scope(world), Laws.scope_findings(world))
  %e : {Plan.grade(Plan.confs(world), world, _) == Laws.run_graded(world) : List<&2, F.Graded>}
  lint.grade(Plan.confs(world), world, Laws.in_scope(world))

# each graded finding is its line
law lint.shown:
  for gs: List<&2, F.Graded>
  {Plan.show_all(gs) == Laws.shown_all(gs) : List<&2, String>}

def lint.shown(gs):
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +tl}:
      Equal.cong(List<&2, String>, List<&2, String>, rr => F.show_graded(g) <> rr, Plan.show_all(tl),
        Laws.shown_all(tl), lint.shown(tl))

# one graded finding onto the error count
law lint.errors.step:
  for ll: Config.Level
  for -a: U32
  for -nn: Nat
  for e: {a == U32.from_nat(nn) : U32}
  {Plan.errors.at(ll, a) == U32.from_nat(Laws.at_error.one(ll, nn)) : U32}

def lint.errors.step(ll, a, nn, e):
  match ll:
    case Config.Off{}:
      e
    case Config.Warn{}:
      e
    case Config.Error{}:
      Equal.cong(U32, U32, xx => U32.inc(xx), a, U32.from_nat(nn), e)

# the planner counts the errors
law lint.errors:
  for gs: List<&2, F.Graded>
  {Plan.errors(gs) == U32.from_nat(Laws.at_error(gs)) : U32}

def lint.errors(gs):
  match gs:
    case Nil{}:
      {==}
    case Con{F.Graded{ll, _ff}, +tl}:
      lint.errors.step(ll, Plan.errors(tl), Laws.at_error(tl), lint.errors(tl))

# one graded finding onto the warning count
law lint.warnings.step:
  for ll: Config.Level
  for -a: U32
  for -nn: Nat
  for e: {a == U32.from_nat(nn) : U32}
  {Plan.warnings.at(ll, a) == U32.from_nat(Laws.below_error.one(ll, nn)) : U32}

def lint.warnings.step(ll, a, nn, e):
  match ll:
    case Config.Off{}:
      Equal.cong(U32, U32, xx => U32.inc(xx), a, U32.from_nat(nn), e)
    case Config.Warn{}:
      Equal.cong(U32, U32, xx => U32.inc(xx), a, U32.from_nat(nn), e)
    case Config.Error{}:
      e

# the planner counts the warnings
law lint.warnings:
  for gs: List<&2, F.Graded>
  {Plan.warnings(gs) == U32.from_nat(Laws.below_error(gs)) : U32}

def lint.warnings(gs):
  match gs:
    case Nil{}:
      {==}
    case Con{F.Graded{ll, _ff}, +tl}:
      lint.warnings.step(ll, Plan.warnings(tl), Laws.below_error(tl), lint.warnings(tl))

# the planner's summary is the spec's
law lint.summary:
  for gs: List<&2, F.Graded>
  {Plan.summary(gs) == Laws.summary_of(gs) : String}

def lint.summary(gs):
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +tl}:
      e = Equal.sym(U32, Plan.errors(g <> tl), U32.from_nat(Laws.at_error(g <> tl)), lint.errors(g <> tl))
      %e : {Plan.count(_, "error") ++ ", " ++ Plan.count(Plan.warnings(g <> tl), "warning")
        == Laws.summary_of(g <> tl) : String}
      w = Equal.sym(U32, Plan.warnings(g <> tl), U32.from_nat(Laws.below_error(g <> tl)), lint.warnings(g <> tl))
      %w : {Plan.count(U32.from_nat(Laws.at_error(g <> tl)), "error") ++ ", " ++ Plan.count(_, "warning")
        == Laws.summary_of(g <> tl) : String}
      {==}

# one graded finding onto whether any is an error
law lint.has_error.step:
  for ll: Config.Level
  for -a: Bool
  for -bb: Bool
  for e: {a == bb : Bool}
  {Bool.or(Config.is_error(ll), a) == Laws.any_error.one(ll, bb) : Bool}

def lint.has_error.step(ll, _a, _bb, e):
  match ll:
    case Config.Off{}:
      e
    case Config.Warn{}:
      e
    case Config.Error{}:
      {==}

# the planner sees an error exactly when the spec does
law lint.has_error:
  for gs: List<&2, F.Graded>
  {Plan.has_error(gs) == Laws.any_error(gs) : Bool}

def lint.has_error(gs):
  match gs:
    case Nil{}:
      {==}
    case Con{F.Graded{ll, _ff}, +tl}:
      lint.has_error.step(ll, Plan.has_error(tl), Laws.any_error(tl), lint.has_error(tl))

def Laws.lines_in_order(world):
  e = Equal.sym(List<&2, F.Graded>, Plan.graded(world), Laws.run_graded(world), lint.graded(world))
  %e : {List.append(&2, String, Plan.show_all(_), [Plan.summary(_)]) == Laws.out_lines(world) : List<&2, String>}
  s = Equal.sym(List<&2, String>, Plan.show_all(Laws.run_graded(world)), Laws.shown_all(Laws.run_graded(world)),
    lint.shown(Laws.run_graded(world)))
  %s : {List.append(&2, String, _, [Plan.summary(Laws.run_graded(world))]) == Laws.out_lines(world)
    : List<&2, String>}
  m = Equal.sym(String, Plan.summary(Laws.run_graded(world)), Laws.summary_of(Laws.run_graded(world)),
    lint.summary(Laws.run_graded(world)))
  %m : {List.append(&2, String, Laws.shown_all(Laws.run_graded(world)), [_]) == Laws.out_lines(world)
    : List<&2, String>}
  {==}

# the last of a list with one more at its end is that one
law lint.last.go:
  for xs: List<&2, String>
  for -hd: String
  for +ss: String
  {List.last.go(&2, String, List.append(&2, String, xs, [ss]), hd) == ss : String}

def lint.last.go(xs, _hd, ss):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +tl}:
      lint.last.go(tl, x, ss)

# so the last line of lines then one more is that one
law lint.last:
  for xs: List<&2, String>
  for +ss: String
  {List.last(&2, String, List.append(&2, String, xs, [ss])) == Some{ss} : Maybe<&2, String>}

def lint.last(xs, ss):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +tl}:
      Equal.cong(String, Maybe<&2, String>, yy => Some{yy},
        List.last.go(&2, String, List.append(&2, String, tl, [ss]), x), ss, lint.last.go(tl, x, ss))

def Laws.last_line_summary(world):
  e = Equal.sym(List<&2, String>, Plan.lines.of(Plan.plan(world)), Laws.out_lines(world), Laws.lines_in_order(world))
  %e : {List.last(&2, String, _) == Some{Laws.summary_of(Laws.run_graded(world))} : Maybe<&2, String>}
  lint.last(Laws.shown_all(Laws.run_graded(world)), Laws.summary_of(Laws.run_graded(world)))

def Laws.exit_on_error(world):
  e = Equal.sym(List<&2, F.Graded>, Plan.graded(world), Laws.run_graded(world), lint.graded(world))
  %e : {Bool.pick(U32, Plan.has_error(_), 1, 0) == Bool.pick(U32, Laws.any_error(Laws.run_graded(world)), 1, 0) : U32}
  h = Equal.sym(Bool, Plan.has_error(Laws.run_graded(world)), Laws.any_error(Laws.run_graded(world)),
    lint.has_error(Laws.run_graded(world)))
  %h : {Bool.pick(U32, _, 1, 0) == Bool.pick(U32, Laws.any_error(Laws.run_graded(world)), 1, 0) : U32}
  {==}

def Laws.unread_one_finding(world, path, ps, h):
  e = Equal.sym(Maybe<&2, W.Answer>, W.answer(world, W.Text{path}), Some{W.Unread{}}, h)
  %e : {Plan.unread(Plan.Got{path, W.text.got(_)} <> Plan.gots(ps, world))
    == F.Finding{path, 0, 0, 0, "read", "Cannot read this file."} <> Plan.unread(Plan.gots(ps, world))
    : List<&2, F.Finding>}
  {==}

def Laws.directory_one_finding(world, path, ps, h):
  e = Equal.sym(Maybe<&2, W.Answer>, W.answer(world, W.Text{path}), Some{W.Directory{}}, h)
  %e : {Plan.unread(Plan.Got{path, W.text.got(_)} <> Plan.gots(ps, world))
    == F.Finding{path, 0, 0, 0, "read", "Cannot read this file."} <> Plan.unread(Plan.gots(ps, world))
    : List<&2, F.Finding>}
  {==}

def Laws.read_is_correctness(cfg, path, line, col, len, msg):
  grade.step(Config.level(cfg, "correctness", "read"), F.Finding{path, line, col, len, "read", msg}, [], [], {==})

# The walk (BOLT-SCOPE-1). The planner's walk threads the files it has found
# so far through its loop; the search reads its directories first. A lemma
# over every fuel, queue and accumulator ties the two: whatever the walk
# carries in comes out after the search's files, and each step's listing is
# read the same way.

# appending regroups
law scope1.assoc:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  for +zs: List<&2, String>
  {List.append(&2, String, List.append(&2, String, xs, ys), zs)
    == List.append(&2, String, xs, List.append(&2, String, ys, zs)) : List<&2, String>}

def scope1.assoc(xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case Con{hd, +tl}:
      Equal.cong(List<&2, String>, List<&2, String>, rr => hd <> rr,
        List.append(&2, String, List.append(&2, String, tl, ys), zs),
        List.append(&2, String, tl, List.append(&2, String, ys, zs)), scope1.assoc(tl, ys, zs))

# the walk descends into the directories the search does
law scope1.dirs:
  for es: List<&2, String>
  for +dir: String
  {Plan.walk.dirs(es, dir) == Laws.subdirs(es, dir) : List<&2, String>}

def scope1.dirs(es, dir):
  match es:
    case Nil{}:
      {==}
    case Con{+ee, +tl}:
      Equal.cong(List<&2, String>, List<&2, String>,
        mm => Bool.pick(List<&2, String>, Laws.descends(ee), (dir ++ "/" ++ Laws.entry_name(ee)) <> mm, mm),
        Plan.walk.dirs(tl, dir), Laws.subdirs(tl, dir), scope1.dirs(tl, dir))

# the walk finds the `.bend` files the search does
law scope1.bends:
  for es: List<&2, String>
  for +dir: String
  {Plan.walk.bends(es, dir) == Laws.bends_in(es, dir) : List<&2, String>}

def scope1.bends(es, dir):
  match es:
    case Nil{}:
      {==}
    case Con{+ee, +tl}:
      Equal.cong(List<&2, String>, List<&2, String>,
        mm => Bool.pick(List<&2, String>, String.ends_with(ee, ".bend"), (dir ++ "/" ++ ee) <> mm, mm),
        Plan.walk.bends(tl, dir), Laws.bends_in(tl, dir), scope1.bends(tl, dir))

# one directory read: what the rest of the walk finds, onto its files and
# what came before, regrouped as the search's files then what came before
law scope1.walk.step:
  for +xs: List<&2, String>
  for +bs: List<&2, String>
  for +acc: List<&2, String>
  for -found: List<&2, String>
  for ih: {found == List.append(&2, String, xs, List.append(&2, String, bs, acc)) : List<&2, String>}
  {found == List.append(&2, String, List.append(&2, String, xs, bs), acc) : List<&2, String>}

def scope1.walk.step(xs, bs, acc, found, ih):
  Equal.trans(List<&2, String>, found, List.append(&2, String, xs, List.append(&2, String, bs, acc)),
    List.append(&2, String, List.append(&2, String, xs, bs), acc), ih,
    Equal.sym(List<&2, String>, List.append(&2, String, List.append(&2, String, xs, bs), acc),
      List.append(&2, String, xs, List.append(&2, String, bs, acc)), scope1.assoc(xs, bs, acc)))

# the walk from any queue, with any fuel, finds the search's files, then
# what it carried in
law scope1.walk:
  for +fuel: Nat
  for +world: W.World
  for +queue: List<&2, String>
  for +acc: List<&2, String>
  for seen: List<&2, String>
  {Plan.walk.found(Plan.walk(fuel, world, queue, acc, seen))
    == List.append(&2, String, Laws.found_in(Laws.bfs(fuel, world, queue), world), acc) : List<&2, String>}

def scope1.walk(fuel, world, queue, acc, seen):
  match fuel:
    case 0n:
      {==}
    case 1n+ff:
      match queue:
        case Nil{}:
          {==}
        case Con{+dd, +rest}:
          d = scope1.dirs(W.listing(world, dd), dd)
          %d : {Plan.walk.found(Plan.walk(ff, world,
              List.append(&2, String, rest, Plan.walk.dirs(W.listing(world, dd), dd)),
              List.append(&2, String, Plan.walk.bends(W.listing(world, dd), dd), acc), dd <> seen))
            == List.append(&2, String, List.append(&2, String,
              Laws.found_in(Laws.bfs(ff, world, List.append(&2, String, rest, _)), world),
              Laws.bends_in(W.listing(world, dd), dd)), acc) : List<&2, String>}
          b = scope1.bends(W.listing(world, dd), dd)
          %b : {Plan.walk.found(Plan.walk(ff, world,
              List.append(&2, String, rest, Plan.walk.dirs(W.listing(world, dd), dd)),
              List.append(&2, String, Plan.walk.bends(W.listing(world, dd), dd), acc), dd <> seen))
            == List.append(&2, String, List.append(&2, String,
              Laws.found_in(Laws.bfs(ff, world,
                List.append(&2, String, rest, Plan.walk.dirs(W.listing(world, dd), dd))), world),
              _), acc) : List<&2, String>}
          scope1.walk.step(
            Laws.found_in(Laws.bfs(ff, world,
              List.append(&2, String, rest, Plan.walk.dirs(W.listing(world, dd), dd))), world),
            Plan.walk.bends(W.listing(world, dd), dd), acc,
            Plan.walk.found(Plan.walk(ff, world,
              List.append(&2, String, rest, Plan.walk.dirs(W.listing(world, dd), dd)),
              List.append(&2, String, Plan.walk.bends(W.listing(world, dd), dd), acc), dd <> seen)),
            scope1.walk(ff, world, List.append(&2, String, rest, Plan.walk.dirs(W.listing(world, dd), dd)),
              List.append(&2, String, Plan.walk.bends(W.listing(world, dd), dd), acc), dd <> seen))

def Laws.walk_bfs(reads, world):
  Equal.trans(List<&2, String>, Plan.walk.found(Plan.walk(reads, world, ["."], [], [])),
    List.append(&2, String, Laws.found_in(Laws.bfs(reads, world, ["."]), world), []),
    Laws.found_in(Laws.bfs(reads, world, ["."]), world),
    scope1.walk(reads, world, ["."], [], []),
    lint.app_nil(String, Laws.found_in(Laws.bfs(reads, world, ["."]), world)))

def Laws.walk_files(world, h):
  e = Equal.sym(List<&2, String>, W.paths.of(world), [], h)
  %e : {Plan.files.named(_, world)
    == List.sort(~String, ~String.is_le, Laws.found_in(Laws.bfs(100000n, world, ["."]), world))
    : List<&2, String>}
  Equal.cong(List<&2, String>, List<&2, String>, xs => List.sort(~String, ~String.is_le, xs),
    Plan.walk.found(Plan.tree(world)), Laws.found_in(Laws.bfs(100000n, world, ["."]), world),
    Laws.walk_bfs(100000n, world))

# Under law (BOLT-SCOPE-3). The coverage rule turns on at the first LAWS.bend
# directory it finds and then walks every file; the laws say which files it
# grades. One lemma for the walk over the files, one for the switch.

# one file onto the rule's walk: skipped when exempt, graded otherwise
law scope3.go.step:
  for exempt: Bool
  for +tops: List<&2, Digest.Top>
  for +ms: List<&2, Digest.Mention>
  for +norm: String
  for +path: String
  for -more: List<&2, F.Finding>
  for -spec: List<&2, F.Finding>
  for ih: {more == spec : List<&2, F.Finding>}
  {Lazy.stop(List<&2, F.Finding>, exempt, more,
      _u => List.append(&2, F.Finding, Law.gaps(tops, ms, norm, path), more))
    == List.append(&2, F.Finding, Laws.graded_file(exempt, tops, ms, norm, path), spec) : List<&2, F.Finding>}

def scope3.go.step(exempt, tops, ms, norm, path, more, spec, ih):
  match exempt:
    case True{}:
      ih
    case False{}:
      Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
        rr => List.append(&2, F.Finding, Law.gaps(tops, ms, norm, path), rr),
        more, spec, ih)

# the rule's walk over the files grades every file under law
law scope3.go:
  for ds: List<&2, Digest.Digest>
  for +ms: List<&2, Digest.Mention>
  {Law.check.go(ds, ms) == Laws.under_law(ds, ms) : List<&2, F.Finding>}

def scope3.go(ds, ms):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{+path, +norm, _dir, _is_laws, _is_law_file, exempt, +tops, _says, _deps, _unsafes, _laws},
      +rest}:
      scope3.go.step(exempt, tops, ms, norm, path, Law.check.go(rest, ms), Laws.under_law(rest, ms),
        scope3.go(rest, ms))

# one file onto the law directories: the rule is on exactly when some file
# so far is a LAWS.bend
law scope3.first.step:
  for is_laws: Bool
  for +ds: List<&2, Digest.Digest>
  for +dir: String
  for +dirs: List<&2, String>
  for -on: Bool
  for ih: {Law.check.first(ds, dirs) == Laws.coverage_of(on, ds, Law.named(ds)) : List<&2, F.Finding>}
  {Law.check.first(ds, Bool.pick(List<&2, String>, is_laws, dir <> dirs, dirs))
    == Laws.coverage_of(Bool.or(is_laws, on), ds, Law.named(ds)) : List<&2, F.Finding>}

def scope3.first.step(is_laws, ds, _dir, _dirs, _on, ih):
  match is_laws:
    case True{}:
      scope3.go(ds, Law.named(ds))
    case False{}:
      ih

# the rule is on over the files exactly when one of them is a LAWS.bend
law scope3.first:
  for ds: List<&2, Digest.Digest>
  for +all: List<&2, Digest.Digest>
  {Law.check.first(all, Law.law_dirs(ds)) == Laws.coverage_of(Laws.has_laws(ds), all, Law.named(all))
    : List<&2, F.Finding>}

def scope3.first(ds, all):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{_path, _norm, +dir, is_laws, _is_law_file, _exempt, _tops, _says, _deps, _unsafes, _laws},
      +rest}:
      scope3.first.step(is_laws, all, dir, Law.law_dirs(rest), Laws.has_laws(rest), scope3.first(rest, all))

def Laws.under_law_all(world):
  scope3.first(Laws.handed(world), Laws.handed(world))

# Where a finding is graded (BOLT-CFG-4). The table lookup compares
# directories with String.eq, so the proof needs String.eq to be sound: two
# strings it calls equal are equal. That goes down to the words a U32 is made
# of, as syntax/PROOF.bend's ol.weq does.

def Laws.absolute_root(cwd, path, h):
  e = Equal.sym(Bool, String.starts_with(path, "/"), True{}, h)
  %e : {Bool.pick(String, _, path, cwd ++ "/" ++ path) == path : String}
  {==}

def Laws.absolute_under(cwd, path, h):
  e = Equal.sym(Bool, String.starts_with(path, "/"), False{}, h)
  %e : {Bool.pick(String, _, path, cwd ++ "/" ++ path) == cwd ++ "/" ++ path : String}
  {==}

def Laws.home_empty(_above):
  {==}

def Laws.home_here(_above):
  {==}

def Laws.home_up(_above):
  {==}

def Laws.home_down(seg, above, h_here, h_up):
  e = Equal.sym(Bool, Bool.or(String.is_empty(seg), String.eq(seg, ".")), False{}, h_here)
  %e : {Bool.pick(List<&2, String>, _, above,
      Bool.pick(List<&2, String>, String.eq(seg, ".."), Config.home.up(above), seg <> above))
    == seg <> above : List<&2, String>}
  u = Equal.sym(Bool, String.eq(seg, ".."), False{}, h_up)
  %u : {Bool.pick(List<&2, String>, _, Config.home.up(above), seg <> above) == seg <> above : List<&2, String>}
  {==}

def Laws.chain_parent(_dd, _rest):
  {==}

# Unit for False, Empty for True
def cfg4.false_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Unit
    case True{}:
      Empty

# False is never True
law cfg4.false_true:
  for e: {False{} == True{} : Bool}
  Empty

def cfg4.false_true(e):
  %e : cfg4.false_ty(_)
  Unit{}

# words that compare equal, bit by bit past the first: the rest equal, the
# first bits the same
law cfg4.weq.arm:
  for -p: Nat
  for -at: Word(p)
  for -bt: Word(p)
  for c: Cmp
  for ec: {Word.cmp(p, at, bt) == c : Cmp}
  for ih: {Cmp.is_eq(Word.cmp(p, at, bt)) == True{} : Bool} -> {at == bt : Word(p)}
  for ab: Bool
  for bb: Bool
  for e: {Cmp.is_eq(Word.cmp.fin(ab, bb, c)) == True{} : Bool}
  {WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}

def cfg4.weq.arm(p, at, bt, c, ec, ih, ab, bb, e):
  match c:
    case LT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, cfg4.false_true(e))
    case GT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, cfg4.false_true(e))
    case EQ{}:
      match ab bb:
        case False{} False{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{False{}, w}, at, bt,
            ih(Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, at, bt), EQ{}, ec)))
        case True{} True{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{True{}, w}, at, bt,
            ih(Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, at, bt), EQ{}, ec)))
        case False{} True{}:
          Empty.absurd({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, cfg4.false_true(e))
        case True{} False{}:
          Empty.absurd({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, cfg4.false_true(e))

# words that compare equal are equal
law cfg4.weq:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for e: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}
  {a == b : Word(n)}

def cfg4.weq(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          cfg4.weq.arm(p, at, bt, Word.cmp(p, at, bt), {==}, x => cfg4.weq(p, at, bt, x), ab, bb, e)

# U32s that compare equal are equal
law cfg4.ueq:
  for a: U32
  for b: U32
  for e: {U32.is_eq(a, b) == True{} : Bool}
  {a == b : U32}

def cfg4.ueq(a, b, e):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, cfg4.weq(32n, x, y, e))

# a compare that went on past equal first characters answers as the rest's
law cfg4.rec:
  for -h1: Char
  for -h2: Char
  for rr: (String & String) & Cmp
  {String.eq.fin(String.cmp.rec(h1, h2, rr)) == String.eq.fin(rr) : Bool}

def cfg4.rec(_h1, _h2, rr):
  ((_a, _b), _c) = rr
  {==}

# strings whose first characters compare as c and whose compare comes out
# equal: when c is equal and the rest are equal, they are equal
law cfg4.seq.arm:
  for +x: U32
  for +y: U32
  for +t1: String
  for +t2: String
  for c: Cmp
  for ec: {U32.cmp(x, y) == c : Cmp}
  for ih: {String.eq(t1, t2) == True{} : Bool} -> {t1 == t2 : String}
  for e: {String.eq.fin(String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), c))) == True{} : Bool}
  {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}

def cfg4.seq.arm(x, y, t1, t2, c, ec, ih, e):
  match c:
    case LT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, cfg4.false_true(e))
    case GT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, cfg4.false_true(e))
    case EQ{}:
      r = cfg4.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))
      et = ih(Equal.trans(Bool, String.eq(t1, t2), String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))),
        True{}, Equal.sym(Bool, String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))),
          String.eq(t1, t2), r), e))
      ex = cfg4.ueq(x, y, Equal.cong(Cmp, Bool, z => Cmp.is_eq(z), U32.cmp(x, y), EQ{}, ec))
      %ex : {SCon{Chr{x}, t1} == SCon{Chr{_}, t2} : String}
      %et : {SCon{Chr{x}, t1} == SCon{Chr{x}, _} : String}
      {==}

# strings that compare equal are equal
law cfg4.seq:
  for a: String
  for b: String
  for e: {String.eq(a, b) == True{} : Bool}
  {a == b : String}

def cfg4.seq(a, b, e):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      Empty.absurd({SNil{} == SCon{h, t} : String}, cfg4.false_true(e))
    case SCon{h, t} SNil{}:
      Empty.absurd({SCon{h, t} == SNil{} : String}, cfg4.false_true(e))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      cfg4.seq.arm(x, y, t1, t2, U32.cmp(x, y), {==}, z => cfg4.seq(t1, t2, z), e)

# one row of the table: its config when its directory is the one asked for,
# otherwise what the rows after it give
law cfg4.find.step:
  for bb: Bool
  for +d: String
  for +dir: String
  for +world: W.World
  for -rest: List<&2, Plan.Conf>
  for h: {String.eq(d, dir) == bb : Bool}
  for ih: {Plan.conf.find(rest, world, dir) == Plan.conf.near(world, dir) : Config.Config}
  {Lazy.stop(Config.Config, bb, Plan.conf.near(world, d), _u => Plan.conf.find(rest, world, dir))
    == Plan.conf.near(world, dir) : Config.Config}

def cfg4.find.step(bb, d, dir, world, _rest, h, ih):
  match bb:
    case True{}:
      Equal.cong(String, Config.Config, z => Plan.conf.near(world, z), d, dir, cfg4.seq(d, dir, h))
    case False{}:
      ih

# the table's config for a directory, held or not, is the one conf.near works
# out for it
law cfg4.find:
  for ds: List<&2, String>
  for +world: W.World
  for +dir: String
  {Plan.conf.find(Plan.confs.at(ds, world), world, dir) == Plan.conf.near(world, dir) : Config.Config}

def cfg4.find(ds, world, dir):
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +tl}:
      cfg4.find.step(String.eq(d, dir), d, dir, world, Plan.confs.at(tl, world), {==}, cfg4.find(tl, world, dir))

# one candidate onto the rest: the World's answer for it decides
law cfg4.first.step:
  for mm: Maybe<&2, W.Answer>
  for -ts: List<&2, Maybe<&2, String>>
  for -more: Config.Config
  for ih: {Config.nearest(ts) == more : Config.Config}
  {Config.nearest(W.text.got(mm) <> ts) == Laws.first_read.at(mm, more) : Config.Config}

def cfg4.first.step(mm, _ts, _more, ih):
  match mm:
    case None{}:
      ih
    case Some{aa}:
      match aa:
        case W.Listed{_names}:
          ih
        case W.Read{_text}:
          {==}
        case W.Unread{}:
          ih
        case W.Directory{}:
          ih

# the nearest of the texts the World holds at the candidates is the first
# candidate it read
law cfg4.first:
  for ps: List<&2, String>
  for +world: W.World
  {Config.nearest(Plan.texts.at(ps, world)) == Laws.first_read(world, ps) : Config.Config}

def cfg4.first(ps, world):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +tl}:
      cfg4.first.step(W.answer(world, W.Text{p}), Plan.texts.at(tl, world), Laws.first_read(world, tl),
        cfg4.first(tl, world))

def Laws.nearest_grades(world, path):
  Equal.trans(Config.Config, Plan.config.at(Plan.confs(world), world, path),
    Plan.conf.near(world, Config.dir_of(path)),
    Laws.first_read(world, Config.chain(Config.home(W.cwd.of(world), Config.dir_of(path)))),
    cfg4.find(Plan.conf.dirs(Plan.inputs(world)), world, Config.dir_of(path)),
    cfg4.first(Config.chain(Config.home(W.cwd.of(world), Config.dir_of(path))), world))
