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
import ./args.bend as Args
import ./version.bend as Ver
import ./build_rev.bend as Rev
import ./check.bend as Check
import ./lsp/checker/service.bend as Checker
import ./lsp/checker/bend.bend as BendChecker
import ./lsp/report.bend as Rep
import 0xba6940aab8a335b70bf79944bd9b53c4/main.bend as Shake
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
  for +cl: List<&2, String>
  for +norm: String
  for +path: String
  for -more: List<&2, F.Finding>
  for -spec: List<&2, F.Finding>
  for ih: {more == spec : List<&2, F.Finding>}
  {Lazy.stop(List<&2, F.Finding>, exempt, more,
      _u => List.append(&2, F.Finding, Law.gaps(tops, cl, norm, path), more))
    == List.append(&2, F.Finding, Laws.graded_file(exempt, tops, cl, norm, path), spec) : List<&2, F.Finding>}

def scope3.go.step(exempt, tops, cl, norm, path, more, spec, ih):
  match exempt:
    case True{}:
      ih
    case False{}:
      Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
        rr => List.append(&2, F.Finding, Law.gaps(tops, cl, norm, path), rr),
        more, spec, ih)

# the rule's walk over the files grades every file under law
law scope3.go:
  for ds: List<&2, Digest.Digest>
  for +cl: List<&2, String>
  {Law.check.go(ds, cl) == Laws.under_law(ds, cl) : List<&2, F.Finding>}

def scope3.go(ds, cl):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{+path, +norm, _dir, _is_laws, _is_law_file, exempt, +tops, _says, _deps, _unsafes, _laws},
      +rest}:
      scope3.go.step(exempt, tops, cl, norm, path, Law.check.go(rest, cl), Laws.under_law(rest, cl),
        scope3.go(rest, cl))

# one file onto the law directories: the rule is on exactly when some file
# so far is a LAWS.bend
law scope3.first.step:
  for is_laws: Bool
  for +ds: List<&2, Digest.Digest>
  for +dir: String
  for +dirs: List<&2, String>
  for -on: Bool
  for ih: {Law.check.first(ds, dirs) == Laws.coverage_of(on, ds, Law.reached(Law.graph(ds))) : List<&2, F.Finding>}
  {Law.check.first(ds, Bool.pick(List<&2, String>, is_laws, dir <> dirs, dirs))
    == Laws.coverage_of(Bool.or(is_laws, on), ds, Law.reached(Law.graph(ds))) : List<&2, F.Finding>}

def scope3.first.step(is_laws, ds, _dir, _dirs, _on, ih):
  match is_laws:
    case True{}:
      scope3.go(ds, Law.reached(Law.graph(ds)))
    case False{}:
      ih

# the rule is on over the files exactly when one of them is a LAWS.bend
law scope3.first:
  for ds: List<&2, Digest.Digest>
  for +all: List<&2, Digest.Digest>
  {Law.check.first(all, Law.law_dirs(ds)) == Laws.coverage_of(Laws.has_laws(ds), all, Law.reached(Law.graph(all)))
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

# The command line (BOLT-CLI)
# ---------------------------
# shake walks argv one word at a time. A plain word in a free walker whose
# only positional left is the `files` rest binds one more file, and after
# `--` every word does; `help` collects the rest as a path, and an error
# keeps the walker dead. The laws below walk each shape over every word list,
# then read the finished walker back through Args.out.

# Unit for False, Empty for True: a motive that tells them apart
def cli.false_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Unit
    case True{}:
      Empty

# False is never True
law cli.false_true:
  for e: {False{} == True{} : Bool}
  Empty

def cli.false_true(e):
  %e : cli.false_ty(_)
  Unit{}

# True is never False
law cli.true_false:
  for e: {True{} == False{} : Bool}
  Empty

def cli.true_false(e):
  cli.false_true(Equal.sym(Bool, True{}, False{}, e))

# the left of a true nor is false
law cli.nor_l:
  for a: Bool
  for -b: Bool
  for h: {Bool.not(Bool.or(a, b)) == True{} : Bool}
  {a == False{} : Bool}

def cli.nor_l(a, _b, h):
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, cli.false_true(h))
    case False{}:
      {==}

# the right of a true nor is not true
law cli.nor_r:
  for a: Bool
  for b: Bool
  for h: {Bool.not(Bool.or(a, b)) == True{} : Bool}
  {Bool.not(b) == True{} : Bool}

def cli.nor_r(a, b, h):
  match a:
    case True{}:
      Empty.absurd({Bool.not(b) == True{} : Bool}, cli.false_true(h))
    case False{}:
      h

# a Bool whose negation is true is false
law cli.not_true:
  for b: Bool
  for h: {Bool.not(b) == True{} : Bool}
  {b == False{} : Bool}

def cli.not_true(b, h):
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, cli.false_true(h))
    case False{}:
      {==}

# the left of a true and is true
law cli.and_l:
  for a: Bool
  for -b: Bool
  for h: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def cli.and_l(a, _b, h):
  match a:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, cli.false_true(h))
    case True{}:
      {==}

# the right of a true and is true
law cli.and_r:
  for a: Bool
  for b: Bool
  for h: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def cli.and_r(a, b, h):
  match a:
    case False{}:
      Empty.absurd({b == True{} : Bool}, cli.false_true(h))
    case True{}:
      h

# two true Bools make a true and
law cli.and_true:
  for a: Bool
  for b: Bool
  for ha: {a == True{} : Bool}
  for hb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def cli.and_true(a, b, ha, hb):
  e = Equal.sym(Bool, a, True{}, ha)
  %e : {Bool.and(_, b) == True{} : Bool}
  hb

# a Maybe that is none is None
law cli.none_of:
  for mm: Maybe<&2, Shake.Sub>
  for h: {Maybe.is_none(&2, Shake.Sub, mm) == True{} : Bool}
  {mm == None{} : Maybe<&2, Shake.Sub>}

def cli.none_of(mm, h):
  match mm:
    case None{}:
      {==}
    case Some{s}:
      Empty.absurd({Some{s} == None{} : Maybe<&2, Shake.Sub>}, cli.false_true(h))

# a word past its first `-` test: the `--` test fails wherever the `-` one does
law cli.dash.if:
  for b: Bool
  for xt: String
  for h: {String.starts_with.if(xt, "", b) == False{} : Bool}
  {String.starts_with.if(xt, "-", b) == False{} : Bool}

def cli.dash.if(b, xt, h):
  match b:
    case False{}:
      {==}
    case True{}:
      match xt:
        case SNil{}:
          Empty.absurd({String.starts_with.if(SNil{}, "-", True{}) == False{} : Bool}, cli.true_false(h))
        case SCon{x, t}:
          Empty.absurd({String.starts_with.if(SCon{x, t}, "-", True{}) == False{} : Bool}, cli.true_false(h))

# a word that does not start with `-` does not start with `--`
law cli.dash:
  for ww: String
  for h: {String.starts_with(ww, "-") == False{} : Bool}
  {String.starts_with(ww, "--") == False{} : Bool}

def cli.dash(ww, h):
  match ww:
    case SNil{}:
      {==}
    case SCon{+x, xt}:
      cli.dash.if(Char.is_eq(x, '-'), xt, h)

# a plain word is not `--`
law cli.plain_dd:
  for +ww: String
  for h: {Laws.plain_word(ww) == True{} : Bool}
  {String.eq(ww, "--") == False{} : Bool}

def cli.plain_dd(ww, h):
  cli.nor_l(String.eq(ww, "--"), Bool.or(String.eq(ww, "help"), String.starts_with(ww, "-")), h)

# a plain word is not `help`
law cli.plain_help:
  for +ww: String
  for h: {Laws.plain_word(ww) == True{} : Bool}
  {String.eq(ww, "help") == False{} : Bool}

def cli.plain_help(ww, h):
  cli.nor_l(String.eq(ww, "help"), String.starts_with(ww, "-"),
    cli.nor_r(String.eq(ww, "--"), Bool.or(String.eq(ww, "help"), String.starts_with(ww, "-")), h))

# a plain word does not start with `-`
law cli.plain_dash:
  for +ww: String
  for h: {Laws.plain_word(ww) == True{} : Bool}
  {String.starts_with(ww, "-") == False{} : Bool}

def cli.plain_dash(ww, h):
  cli.not_true(String.starts_with(ww, "-"),
    cli.nor_r(String.eq(ww, "help"), String.starts_with(ww, "-"),
      cli.nor_r(String.eq(ww, "--"), Bool.or(String.eq(ww, "help"), String.starts_with(ww, "-")), h)))

# a spec's top-level arguments
def cli.args_of(app: Shake.Cli) -> List<&2, Shake.Arg>:
  Shake.Cli{_n, _a, _v, args, _s} = app
  args

# a spec's subcommands
def cli.subs_of(app: Shake.Cli) -> List<&2, Shake.Sub>:
  Shake.Cli{_n, _a, _v, _args, subs} = app
  subs

# the `files` rest positional, with its help line
def cli.rest(+hlp: String) -> Shake.Arg:
  Shake.Arg{"files", None{}, None{}, Shake.Rest{}, hlp, False{}, None{}, []}

# the binds a walk pushes for files, onto the ones it had, newest first
def cli.pushed(fs: List<&2, String>, bs: List<&2, Shake.Bind>) -> List<&2, Shake.Bind>:
  match fs:
    case Nil{}:
      bs
    case Con{ff, rest}:
      cli.pushed(rest, Shake.Bind{"files", ff} <> bs)

# whether a walker has seen a positional, after the words
def cli.seen(fs: List<&2, String>, seen: Bool) -> Bool:
  match fs:
    case Nil{}:
      seen
    case Con{_ff, rest}:
      cli.seen(rest, True{})

# the files as binds, in order
def cli.as_files(fs: List<&2, String>) -> List<&2, Shake.Bind>:
  match fs:
    case Nil{}:
      []
    case Con{ff, rest}:
      Shake.Bind{"files", ff} <> cli.as_files(rest)

# whether no word names one of the subcommands
def cli.unfound(+subs: List<&2, Shake.Sub>, ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+ww, rest}:
      Bool.and(Maybe.is_none(&2, Shake.Sub, Shake.find_sub(subs, ww)), cli.unfound(subs, rest))

# a word that is not `--`, not `help`, not a flag and no subcommand here
# reaches the positional it binds
law cli.word_step:
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +seen: Bool
  for h_dd: {String.eq(tok, "--") == False{} : Bool}
  for h_help: {String.eq(tok, "help") == False{} : Bool}
  for +h_dash: {String.starts_with(tok, "-") == False{} : Bool}
  for h_sub: {Shake.find_sub(subs, tok) == None{} : Maybe<&2, Shake.Sub>}
  {Shake.parse.step(tok, Shake.St{Shake.Free{}, args, specs, subs, path, bs, pos, False{}, seen})
    == Shake.parse.take_pos(tok, args, specs, subs, path, bs, pos, False{}) : Shake.St}

def cli.word_step(tok, args, specs, subs, path, bs, pos, seen, h_dd, h_help, h_dash, h_sub):
  e1 = Equal.sym(Bool, String.eq(tok, "--"), False{}, h_dd)
  %e1 : {Shake.parse.step.end(_, tok, args, specs, subs, path, bs, pos, seen)
    == Shake.parse.take_pos(tok, args, specs, subs, path, bs, pos, False{}) : Shake.St}
  e2 = Equal.sym(Bool, String.eq(tok, "help"), False{}, h_help)
  %e2 : {Shake.parse.step.help(Bool.and(_, Bool.not(seen)), tok, args, specs, subs, path, bs, pos, seen)
    == Shake.parse.take_pos(tok, args, specs, subs, path, bs, pos, False{}) : Shake.St}
  e3 = Equal.sym(Bool, String.starts_with(tok, "--"), False{}, cli.dash(tok, h_dash))
  %e3 : {Shake.parse.step.kind.go(_, String.starts_with(tok, "-"), tok, args, specs, subs, path, bs, pos, seen)
    == Shake.parse.take_pos(tok, args, specs, subs, path, bs, pos, False{}) : Shake.St}
  e4 = Equal.sym(Bool, String.starts_with(tok, "-"), False{}, h_dash)
  %e4 : {Shake.parse.step.kind.go(False{}, _, tok, args, specs, subs, path, bs, pos, seen)
    == Shake.parse.take_pos(tok, args, specs, subs, path, bs, pos, False{}) : Shake.St}
  e5 = Equal.sym(Maybe<&2, Shake.Sub>, Shake.find_sub(subs, tok), None{}, h_sub)
  %e5 : {Shake.parse.word.go(_, tok, args, specs, subs, path, bs, pos, False{}, seen)
    == Shake.parse.take_pos(tok, args, specs, subs, path, bs, pos, False{}) : Shake.St}
  {==}

# plain words, none a subcommand here, each bind one more file
law cli.walk_plain:
  for fs: List<&2, String>
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, Shake.Bind>
  for +hlp: String
  for +seen: Bool
  for +hp: {Laws.all_plain(fs) == True{} : Bool}
  for +hu: {cli.unfound(subs, fs) == True{} : Bool}
  {Shake.parse.walk(fs, Shake.St{Shake.Free{}, args, specs, subs, path, bs, [cli.rest(hlp)], False{}, seen})
    == Shake.St{Shake.Free{}, args, specs, subs, path, cli.pushed(fs, bs), [cli.rest(hlp)], False{},
      cli.seen(fs, seen)} : Shake.St}

def cli.walk_plain(fs, args, specs, subs, path, bs, hlp, seen, hp, hu):
  match fs:
    case Nil{}:
      {==}
    case Con{+ww, +tl}:
      +pl = cli.and_l(Laws.plain_word(ww), Laws.all_plain(tl), hp)
      su = cli.and_l(Maybe.is_none(&2, Shake.Sub, Shake.find_sub(subs, ww)), cli.unfound(subs, tl), hu)
      e = Equal.sym(Shake.St,
        Shake.parse.step(ww, Shake.St{Shake.Free{}, args, specs, subs, path, bs, [cli.rest(hlp)], False{}, seen}),
        Shake.parse.take_pos(ww, args, specs, subs, path, bs, [cli.rest(hlp)], False{}),
        cli.word_step(ww, args, specs, subs, path, bs, [cli.rest(hlp)], seen, cli.plain_dd(ww, pl),
          cli.plain_help(ww, pl), cli.plain_dash(ww, pl), cli.none_of(Shake.find_sub(subs, ww), su)))
      %e : {Shake.parse.walk(tl, _)
        == Shake.St{Shake.Free{}, args, specs, subs, path, cli.pushed(tl, Shake.Bind{"files", ww} <> bs),
          [cli.rest(hlp)], False{}, cli.seen(tl, True{})} : Shake.St}
      cli.walk_plain(tl, args, specs, subs, path, Shake.Bind{"files", ww} <> bs, hlp, True{},
        cli.and_r(Laws.plain_word(ww), Laws.all_plain(tl), hp),
        cli.and_r(Maybe.is_none(&2, Shake.Sub, Shake.find_sub(subs, ww)), cli.unfound(subs, tl), hu))

# after `--`, every word binds one more file
law cli.walk_raw:
  for fs: List<&2, String>
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for bs: List<&2, Shake.Bind>
  for +hlp: String
  for seen: Bool
  {Shake.parse.walk(fs, Shake.St{Shake.Free{}, args, specs, subs, path, bs, [cli.rest(hlp)], True{}, seen})
    == Shake.St{Shake.Free{}, args, specs, subs, path, cli.pushed(fs, bs), [cli.rest(hlp)], True{},
      cli.seen(fs, seen)} : Shake.St}

def cli.walk_raw(fs, args, specs, subs, path, bs, hlp, _seen):
  match fs:
    case Nil{}:
      {==}
    case Con{ww, tl}:
      cli.walk_raw(tl, args, specs, subs, path, Shake.Bind{"files", ww} <> bs, hlp, True{})

# a dead walker stays as it is
law cli.walk_dead:
  for ws: List<&2, String>
  for +ee: Shake.ParseErr
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  {Shake.parse.walk(ws, Shake.St{Shake.Dead{ee}, args, specs, subs, path, bs, pos, raw, seen})
    == Shake.St{Shake.Dead{ee}, args, specs, subs, path, bs, pos, raw, seen} : Shake.St}

def cli.walk_dead(ws, ee, args, specs, subs, path, bs, pos, raw, seen):
  match ws:
    case Nil{}:
      {==}
    case Con{_ww, tl}:
      cli.walk_dead(tl, ee, args, specs, subs, path, bs, pos, raw, seen)

# appending nothing leaves a list as it is
law cli.append_nil:
  for -A: Data
  for xs: List<&2, A>
  {List.append(&2, A, xs, []) == xs : List<&2, A>}

def cli.append_nil(A, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, tl}:
      %cli.append_nil(A, tl) : {x <> List.append(&2, A, tl, []) == x <> _ : List<&2, A>}
      {==}

# appending one word, then more, is appending them all
law cli.append_one:
  for xs: List<&2, String>
  for +pp: String
  for +tl: List<&2, String>
  {List.append(&2, String, List.append(&2, String, xs, [pp]), tl) == List.append(&2, String, xs, pp <> tl)
    : List<&2, String>}

def cli.append_one(xs, pp, tl):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, rest}:
      %cli.append_one(rest, pp, tl) : {x <> List.append(&2, String, List.append(&2, String, rest, [pp]), tl)
        == x <> _ : List<&2, String>}
      {==}

# a help walker collects every word onto its path
law cli.walk_help:
  for ps: List<&2, String>
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  {Shake.parse.walk(ps, Shake.St{Shake.Help{}, args, specs, subs, path, bs, pos, raw, seen})
    == Shake.St{Shake.Help{}, args, specs, subs, List.append(&2, String, path, ps), bs, pos, raw, seen}
    : Shake.St}

def cli.walk_help(ps, args, specs, subs, path, bs, pos, raw, seen):
  match ps:
    case Nil{}:
      %cli.append_nil(String, path) : {Shake.St{Shake.Help{}, args, specs, subs, _, bs, pos, raw, seen}
        == Shake.St{Shake.Help{}, args, specs, subs, List.append(&2, String, path, []), bs, pos, raw, seen}
        : Shake.St}
      {==}
    case Con{+pp, +tl}:
      %cli.append_one(path, pp, tl) : {Shake.parse.walk(tl,
          Shake.St{Shake.Help{}, args, specs, subs, List.append(&2, String, path, [pp]), bs, pos, raw, seen})
        == Shake.St{Shake.Help{}, args, specs, subs, _, bs, pos, raw, seen} : Shake.St}
      cli.walk_help(tl, args, specs, subs, List.append(&2, String, path, [pp]), bs, pos, raw, seen)

# the pushed binds, reversed onto more, are the older binds reversed onto
# the files in order and then more
law cli.rev_pushed:
  for fs: List<&2, String>
  for bs: List<&2, Shake.Bind>
  for acc: List<&2, Shake.Bind>
  {List.reverse.go(&2, Shake.Bind, cli.pushed(fs, bs), acc)
    == List.reverse.go(&2, Shake.Bind, bs, List.append(&2, Shake.Bind, cli.as_files(fs), acc))
    : List<&2, Shake.Bind>}

def cli.rev_pushed(fs, bs, acc):
  match fs:
    case Nil{}:
      {==}
    case Con{ff, tl}:
      cli.rev_pushed(tl, Shake.Bind{"files", ff} <> bs, acc)

# file binds hold no version
law cli.no_version:
  for fs: List<&2, String>
  {Shake.get.bind(cli.as_files(fs), "version") == "" : String}

def cli.no_version(fs):
  match fs:
    case Nil{}:
      {==}
    case Con{_ff, tl}:
      cli.no_version(tl)

# file binds read back as the files
law cli.files_back:
  for fs: List<&2, String>
  {Shake.get_all.bind(cli.as_files(fs), "files") == fs : List<&2, String>}

def cli.files_back(fs):
  match fs:
    case Nil{}:
      {==}
    case Con{+ff, tl}:
      %cli.files_back(tl) : {ff <> Shake.get_all.bind(cli.as_files(tl), "files") == ff <> _ : List<&2, String>}
      {==}

# a parse that bound only files runs its command over them
law cli.files_out:
  for +fs: List<&2, String>
  for +path: List<&2, String>
  {Args.out.done(Shake.Matched{path, List.reverse(&2, Shake.Bind, cli.pushed(fs, []))})
    == Args.Go{Args.command(String.join(path, "/")), fs} : Args.Out}

def cli.files_out(fs, path):
  e1 = Equal.sym(List<&2, Shake.Bind>, List.reverse.go(&2, Shake.Bind, cli.pushed(fs, []), []),
    List.append(&2, Shake.Bind, cli.as_files(fs), []), cli.rev_pushed(fs, [], []))
  %e1 : {Args.out.done(Shake.Matched{path, _}) == Args.Go{Args.command(String.join(path, "/")), fs} : Args.Out}
  e2 = Equal.sym(List<&2, Shake.Bind>, List.append(&2, Shake.Bind, cli.as_files(fs), []), cli.as_files(fs),
    cli.append_nil(Shake.Bind, cli.as_files(fs)))
  %e2 : {Args.out.done(Shake.Matched{path, _}) == Args.Go{Args.command(String.join(path, "/")), fs} : Args.Out}
  e3 = Equal.sym(String, Shake.get.bind(cli.as_files(fs), "version"), "", cli.no_version(fs))
  %e3 : {Args.out.run(String.eq(_, "true"), Shake.Matched{path, cli.as_files(fs)})
    == Args.Go{Args.command(String.join(path, "/")), fs} : Args.Out}
  e4 = Equal.sym(List<&2, String>, Shake.get_all.bind(cli.as_files(fs), "files"), fs, cli.files_back(fs))
  %e4 : {Args.Go{Args.command(String.join(path, "/")), _} == Args.Go{Args.command(String.join(path, "/")), fs}
    : Args.Out}
  {==}

# no word names a subcommand when there are none
law cli.unfound_nil:
  for ws: List<&2, String>
  {cli.unfound([], ws) == True{} : Bool}

def cli.unfound_nil(ws):
  match ws:
    case Nil{}:
      {==}
    case Con{_ww, tl}:
      cli.unfound_nil(tl)

# loose words are plain
law cli.loose_plain:
  for ws: List<&2, String>
  for +h: {Laws.all_loose(ws) == True{} : Bool}
  {Laws.all_plain(ws) == True{} : Bool}

def cli.loose_plain(ws, h):
  match ws:
    case Nil{}:
      {==}
    case Con{+ww, +tl}:
      cli.and_true(Laws.plain_word(ww), Laws.all_plain(tl),
        cli.and_l(Laws.plain_word(ww),
          Bool.not(Bool.or(String.eq("lint", ww), Bool.or(String.eq("check", ww), String.eq("lsp", ww)))),
          cli.and_l(Laws.loose_word(ww), Laws.all_loose(tl), h)),
        cli.loose_plain(tl, cli.and_r(Laws.loose_word(ww), Laws.all_loose(tl), h)))

# a lookup among three subcommands, none of whose names match, finds none
law cli.miss3:
  for a: Bool
  for b: Bool
  for c: Bool
  for -x: Shake.Sub
  for -y: Shake.Sub
  for -z: Shake.Sub
  for h: {Bool.not(Bool.or(a, Bool.or(b, c))) == True{} : Bool}
  {Maybe.is_none(&2, Shake.Sub, Bool.pick(Maybe<&2, Shake.Sub>, a, Some{x},
    Bool.pick(Maybe<&2, Shake.Sub>, b, Some{y}, Bool.pick(Maybe<&2, Shake.Sub>, c, Some{z}, None{}))))
    == True{} : Bool}

def cli.miss3(a, b, c, x, y, z, h):
  match a b c:
    case True{} _b _c:
      Empty.absurd({Maybe.is_none(&2, Shake.Sub, Bool.pick(Maybe<&2, Shake.Sub>, True{}, Some{x},
        Bool.pick(Maybe<&2, Shake.Sub>, _b, Some{y}, Bool.pick(Maybe<&2, Shake.Sub>, _c, Some{z}, None{}))))
        == True{} : Bool}, cli.false_true(h))
    case False{} True{} _c:
      Empty.absurd({Maybe.is_none(&2, Shake.Sub, Bool.pick(Maybe<&2, Shake.Sub>, False{}, Some{x},
        Bool.pick(Maybe<&2, Shake.Sub>, True{}, Some{y}, Bool.pick(Maybe<&2, Shake.Sub>, _c, Some{z}, None{}))))
        == True{} : Bool}, cli.false_true(h))
    case False{} False{} True{}:
      Empty.absurd({Maybe.is_none(&2, Shake.Sub, Bool.pick(Maybe<&2, Shake.Sub>, False{}, Some{x},
        Bool.pick(Maybe<&2, Shake.Sub>, False{}, Some{y}, Bool.pick(Maybe<&2, Shake.Sub>, True{}, Some{z}, None{}))))
        == True{} : Bool}, cli.false_true(h))
    case False{} False{} False{}:
      {==}

# loose words name no subcommand of bolt's
law cli.loose_unfound:
  for ws: List<&2, String>
  for +h: {Laws.all_loose(ws) == True{} : Bool}
  {cli.unfound(cli.subs_of(Args.spec()), ws) == True{} : Bool}

def cli.loose_unfound(ws, h):
  match ws:
    case Nil{}:
      {==}
    case Con{+ww, +tl}:
      cli.and_true(Maybe.is_none(&2, Shake.Sub, Shake.find_sub(cli.subs_of(Args.spec()), ww)),
        cli.unfound(cli.subs_of(Args.spec()), tl),
        cli.miss3(String.eq("lint", ww), String.eq("check", ww), String.eq("lsp", ww),
          Shake.sub("lint", "Lint files", [Args.spec.files("Files to lint")], []),
          Shake.sub("check", "Check files", [Args.spec.files("Files to check")], []),
          Shake.sub("lsp", "Serve an editor over stdio", [], []),
          cli.and_r(Laws.plain_word(ww),
            Bool.not(Bool.or(String.eq("lint", ww), Bool.or(String.eq("check", ww), String.eq("lsp", ww)))),
            cli.and_l(Laws.loose_word(ww), Laws.all_loose(tl), h))),
        cli.loose_unfound(tl, cli.and_r(Laws.loose_word(ww), Laws.all_loose(tl), h)))

def Laws.cli_bare(fs, h):
  e = Equal.sym(Shake.St,
    Shake.parse.walk(fs, Shake.St{Shake.Free{}, cli.args_of(Args.spec()), cli.args_of(Args.spec()),
      cli.subs_of(Args.spec()), [], [], [cli.rest("Files to lint")], False{}, False{}}),
    Shake.St{Shake.Free{}, cli.args_of(Args.spec()), cli.args_of(Args.spec()), cli.subs_of(Args.spec()), [],
      cli.pushed(fs, []), [cli.rest("Files to lint")], False{}, cli.seen(fs, False{})},
    cli.walk_plain(fs, cli.args_of(Args.spec()), cli.args_of(Args.spec()), cli.subs_of(Args.spec()), [], [],
      "Files to lint", False{}, cli.loose_plain(fs, h), cli.loose_unfound(fs, h)))
  %e : {Args.out(Shake.parse.finish(_)) == Args.Go{Args.CLint{}, fs} : Args.Out}
  cli.files_out(fs, [])

def Laws.cli_bare_raw(fs):
  e = Equal.sym(Shake.St,
    Shake.parse.walk(fs, Shake.St{Shake.Free{}, cli.args_of(Args.spec()), cli.args_of(Args.spec()),
      cli.subs_of(Args.spec()), [], [], [cli.rest("Files to lint")], True{}, False{}}),
    Shake.St{Shake.Free{}, cli.args_of(Args.spec()), cli.args_of(Args.spec()), cli.subs_of(Args.spec()), [],
      cli.pushed(fs, []), [cli.rest("Files to lint")], True{}, cli.seen(fs, False{})},
    cli.walk_raw(fs, cli.args_of(Args.spec()), cli.args_of(Args.spec()), cli.subs_of(Args.spec()), [], [],
      "Files to lint", False{}))
  %e : {Args.out(Shake.parse.finish(_)) == Args.Go{Args.CLint{}, fs} : Args.Out}
  cli.files_out(fs, [])

# the specs a subcommand's walker holds: bolt's own, then the command's
def cli.specs_in(+hlp: String) -> List<&2, Shake.Arg>:
  List.append(&2, Shake.Arg, cli.args_of(Args.spec()), [cli.rest(hlp)])

# the walk after a files subcommand's name, over plain words
law cli.sub_plain:
  for +fs: List<&2, String>
  for +name: String
  for +hlp: String
  for h: {Laws.all_plain(fs) == True{} : Bool}
  {Shake.parse.walk(fs, Shake.St{Shake.Free{}, [cli.rest(hlp)], cli.specs_in(hlp), [], [name], [],
      [cli.rest(hlp)], False{}, False{}})
    == Shake.St{Shake.Free{}, [cli.rest(hlp)], cli.specs_in(hlp), [], [name], cli.pushed(fs, []),
      [cli.rest(hlp)], False{}, cli.seen(fs, False{})} : Shake.St}

def cli.sub_plain(fs, name, hlp, h):
  cli.walk_plain(fs, [cli.rest(hlp)], cli.specs_in(hlp), [], [name], [], hlp, False{}, h, cli.unfound_nil(fs))

def Laws.cli_lint(fs, h):
  e = Equal.sym(Shake.St,
    Shake.parse.walk(fs, Shake.St{Shake.Free{}, [cli.rest("Files to lint")], cli.specs_in("Files to lint"), [],
      ["lint"], [], [cli.rest("Files to lint")], False{}, False{}}),
    Shake.St{Shake.Free{}, [cli.rest("Files to lint")], cli.specs_in("Files to lint"), [], ["lint"],
      cli.pushed(fs, []), [cli.rest("Files to lint")], False{}, cli.seen(fs, False{})},
    cli.sub_plain(fs, "lint", "Files to lint", h))
  %e : {Args.out(Shake.parse.finish(_)) == Args.Go{Args.CLint{}, fs} : Args.Out}
  cli.files_out(fs, ["lint"])

def Laws.cli_check(fs, h):
  e = Equal.sym(Shake.St,
    Shake.parse.walk(fs, Shake.St{Shake.Free{}, [cli.rest("Files to check")], cli.specs_in("Files to check"), [],
      ["check"], [], [cli.rest("Files to check")], False{}, False{}}),
    Shake.St{Shake.Free{}, [cli.rest("Files to check")], cli.specs_in("Files to check"), [], ["check"],
      cli.pushed(fs, []), [cli.rest("Files to check")], False{}, cli.seen(fs, False{})},
    cli.sub_plain(fs, "check", "Files to check", h))
  %e : {Args.out(Shake.parse.finish(_)) == Args.Go{Args.CCheck{}, fs} : Args.Out}
  cli.files_out(fs, ["check"])

def Laws.cli_lint_raw(fs):
  e = Equal.sym(Shake.St,
    Shake.parse.walk(fs, Shake.St{Shake.Free{}, [cli.rest("Files to lint")], cli.specs_in("Files to lint"), [],
      ["lint"], [], [cli.rest("Files to lint")], True{}, False{}}),
    Shake.St{Shake.Free{}, [cli.rest("Files to lint")], cli.specs_in("Files to lint"), [], ["lint"],
      cli.pushed(fs, []), [cli.rest("Files to lint")], True{}, cli.seen(fs, False{})},
    cli.walk_raw(fs, [cli.rest("Files to lint")], cli.specs_in("Files to lint"), [], ["lint"], [],
      "Files to lint", False{}))
  %e : {Args.out(Shake.parse.finish(_)) == Args.Go{Args.CLint{}, fs} : Args.Out}
  cli.files_out(fs, ["lint"])

def Laws.cli_check_raw(fs):
  e = Equal.sym(Shake.St,
    Shake.parse.walk(fs, Shake.St{Shake.Free{}, [cli.rest("Files to check")], cli.specs_in("Files to check"), [],
      ["check"], [], [cli.rest("Files to check")], True{}, False{}}),
    Shake.St{Shake.Free{}, [cli.rest("Files to check")], cli.specs_in("Files to check"), [], ["check"],
      cli.pushed(fs, []), [cli.rest("Files to check")], True{}, cli.seen(fs, False{})},
    cli.walk_raw(fs, [cli.rest("Files to check")], cli.specs_in("Files to check"), [], ["check"], [],
      "Files to check", False{}))
  %e : {Args.out(Shake.parse.finish(_)) == Args.Go{Args.CCheck{}, fs} : Args.Out}
  cli.files_out(fs, ["check"])

# the specs the `lsp` walker holds: bolt's own, and none of its own
def cli.specs_lsp() -> List<&2, Shake.Arg>:
  List.append(&2, Shake.Arg, cli.args_of(Args.spec()), [])

def Laws.cli_lsp(ws, h):
  match ws:
    case Nil{}:
      {==}
    case Con{+ww, +tl}:
      +pl = cli.and_l(Laws.plain_word(ww), Laws.all_plain(tl), h)
      e1 = Equal.sym(Shake.St,
        Shake.parse.step(ww, Shake.St{Shake.Free{}, [], cli.specs_lsp(), [], ["lsp"], [], [], False{}, False{}}),
        Shake.parse.take_pos(ww, [], cli.specs_lsp(), [], ["lsp"], [], [], False{}),
        cli.word_step(ww, [], cli.specs_lsp(), [], ["lsp"], [], [], False{}, cli.plain_dd(ww, pl),
          cli.plain_help(ww, pl), cli.plain_dash(ww, pl), {==}))
      %e1 : {Args.out(Shake.parse.finish(Shake.parse.walk(tl, _)))
        == Args.Stop{Args.Err{}, Args.err_text(Shake.Unexpected{ww}), 1} : Args.Out}
      e2 = Equal.sym(Shake.St,
        Shake.parse.walk(tl, Shake.St{Shake.Dead{Shake.Unexpected{ww}}, [], cli.specs_lsp(), [], ["lsp"], [], [],
          False{}, True{}}),
        Shake.St{Shake.Dead{Shake.Unexpected{ww}}, [], cli.specs_lsp(), [], ["lsp"], [], [], False{}, True{}},
        cli.walk_dead(tl, Shake.Unexpected{ww}, [], cli.specs_lsp(), [], ["lsp"], [], [], False{}, True{}))
      %e2 : {Args.out(Shake.parse.finish(_)) == Args.Stop{Args.Err{}, Args.err_text(Shake.Unexpected{ww}), 1}
        : Args.Out}
      {==}

def Laws.cli_help(ps):
  e = Equal.sym(Shake.St,
    Shake.parse.walk(ps, Shake.St{Shake.Help{}, cli.args_of(Args.spec()), cli.args_of(Args.spec()),
      cli.subs_of(Args.spec()), [], [], [cli.rest("Files to lint")], False{}, False{}}),
    Shake.St{Shake.Help{}, cli.args_of(Args.spec()), cli.args_of(Args.spec()), cli.subs_of(Args.spec()),
      List.append(&2, String, [], ps), [], [cli.rest("Files to lint")], False{}, False{}},
    cli.walk_help(ps, cli.args_of(Args.spec()), cli.args_of(Args.spec()), cli.subs_of(Args.spec()), [], [],
      [cli.rest("Files to lint")], False{}, False{}))
  %e : {Args.out(Shake.parse.finish(_)) == Args.Stop{Args.Page{}, Args.help_text(ps), 0} : Args.Out}
  {==}

def Laws.cli_version(fs, h):
  e1 = Equal.sym(Shake.St,
    Shake.parse.walk(fs, Shake.St{Shake.Free{}, cli.args_of(Args.spec()), cli.args_of(Args.spec()),
      cli.subs_of(Args.spec()), [], [Shake.Bind{"version", "true"}], [cli.rest("Files to lint")], False{},
      False{}}),
    Shake.St{Shake.Free{}, cli.args_of(Args.spec()), cli.args_of(Args.spec()), cli.subs_of(Args.spec()), [],
      cli.pushed(fs, [Shake.Bind{"version", "true"}]), [cli.rest("Files to lint")], False{},
      cli.seen(fs, False{})},
    cli.walk_plain(fs, cli.args_of(Args.spec()), cli.args_of(Args.spec()), cli.subs_of(Args.spec()), [],
      [Shake.Bind{"version", "true"}], "Files to lint", False{}, cli.loose_plain(fs, h), cli.loose_unfound(fs, h)))
  %e1 : {Args.out(Shake.parse.finish(_))
    == Args.Stop{Args.Line{}, "bolt " ++ Args.version.at(Ver.text(), Rev.text()), 0} : Args.Out}
  e2 = Equal.sym(List<&2, Shake.Bind>,
    List.reverse.go(&2, Shake.Bind, cli.pushed(fs, [Shake.Bind{"version", "true"}]), []),
    List.reverse.go(&2, Shake.Bind, [Shake.Bind{"version", "true"}],
      List.append(&2, Shake.Bind, cli.as_files(fs), [])),
    cli.rev_pushed(fs, [Shake.Bind{"version", "true"}], []))
  %e2 : {Args.out.done(Shake.Matched{[], _})
    == Args.Stop{Args.Line{}, "bolt " ++ Args.version.at(Ver.text(), Rev.text()), 0} : Args.Out}
  {==}

# a failed parse that asks for no usage stops on its error with 1
law cli.err_stop:
  for +ee: Shake.ParseErr
  for h: {Laws.asks_help(ee) == False{} : Bool}
  {Args.out.fail(ee) == Args.Stop{Args.Err{}, Args.err_text(ee), 1} : Args.Out}

def cli.err_stop(ee, h):
  match ee:
    case Shake.UnknownFlag{_ww}:
      {==}
    case Shake.Missing{_nn}:
      {==}
    case Shake.BadValue{_nn, _vv}:
      {==}
    case Shake.NeedHelp{path}:
      Empty.absurd({Args.out.fail(Shake.NeedHelp{path})
        == Args.Stop{Args.Err{}, Args.err_text(Shake.NeedHelp{path}), 1} : Args.Out}, cli.true_false(h))
    case Shake.Unexpected{_ww}:
      {==}

def Laws.cli_error_exits(av, ee, h, h_help):
  e = Equal.sym(Result<&2, &2, Shake.ParseErr, Shake.Matched>, Args.parse(av), Fail{ee}, h)
  %e : {Args.out(_) == Args.Stop{Args.Err{}, Args.err_text(ee), 1} : Args.Out}
  cli.err_stop(ee, h_help)

def Laws.cli_help_exits(av, ps, h):
  e = Equal.sym(Result<&2, &2, Shake.ParseErr, Shake.Matched>, Args.parse(av), Fail{Shake.NeedHelp{ps}}, h)
  %e : {Args.out(_) == Args.Stop{Args.Page{}, Args.help_text(ps), 0} : Args.Out}
  {==}

def Laws.cli_version_exits(av, mm, h, h_ver):
  e = Equal.sym(Result<&2, &2, Shake.ParseErr, Shake.Matched>, Args.parse(av), Done{mm}, h)
  %e : {Args.out(_)
    == Args.Stop{Args.Line{}, "bolt " ++ Args.version.at(Ver.text(), Rev.text()), 0} : Args.Out}
  v = Equal.sym(Bool, Shake.on(mm, "version"), True{}, h_ver)
  %v : {Args.out.run(_, mm)
    == Args.Stop{Args.Line{}, "bolt " ++ Args.version.at(Ver.text(), Rev.text()), 0} : Args.Out}
  {==}

def Laws.cli_runs(av, mm, h, h_ver):
  e = Equal.sym(Result<&2, &2, Shake.ParseErr, Shake.Matched>, Args.parse(av), Done{mm}, h)
  %e : {Args.out(_)
    == Args.Go{Args.command(String.join(Shake.path_of(mm), "/")), Shake.get_all(mm, "files")} : Args.Out}
  v = Equal.sym(Bool, Shake.on(mm, "version"), False{}, h_ver)
  %v : {Args.out.run(_, mm)
    == Args.Go{Args.command(String.join(Shake.path_of(mm), "/")), Shake.get_all(mm, "files")} : Args.Out}
  {==}

def Laws.version_release(rel, rev, h):
  e = Equal.sym(Bool, String.is_empty(rev), True{}, h)
  %e : {Bool.pick(String, _, rel, rel ++ " (" ++ rev ++ ")") == rel : String}
  {==}

def Laws.version_commit(rel, rev, h):
  e = Equal.sym(Bool, String.is_empty(rev), False{}, h)
  %e : {Bool.pick(String, _, rel, rel ++ " (" ++ rev ++ ")") == rel ++ " (" ++ rev ++ ")" : String}
  {==}

# a file's error lines, then more, are its lines onto more
law chk.file:
  for ds: List<&2, Rep.Diag>
  for +path: String
  for +more: List<&2, String>
  {List.append(&2, String, Check.show_all(ds, path), more) == Laws.chk_file(ds, path, more) : List<&2, String>}

def chk.file(ds, path, more):
  match ds:
    case Nil{}:
      {==}
    case Con{Rep.Diag{+line, +msg}, rest}:
      %chk.file(rest, path, more) : {List.append(&2, String, Check.show_all(Rep.Diag{line, msg} <> rest, path), more)
        == Laws.chk_line(path, Rep.Diag{line, msg}) <> _ : List<&2, String>}
      {==}

def Laws.check_lines(runs):
  match runs:
    case Nil{}:
      {==}
    case Con{Check.Run{+path, +ds}, +rest}:
      %Laws.check_lines(rest) : {List.append(&2, String, Check.show_all(ds, path), Check.lines_of(rest))
        == Laws.chk_file(ds, path, _) : List<&2, String>}
      chk.file(ds, path, Check.lines_of(rest))
    case Con{Check.Failed{+path}, +rest}:
      %Laws.check_lines(rest) : {(path ++ ":1:1: error: could not run bend") <> Check.lines_of(rest)
        == (path ++ ":1:1: error: could not run bend") <> _ : List<&2, String>}
      {==}

# the length of two lists appended is the sum of their lengths
law chk.len_append:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  {List.length(&2, String, List.append(&2, String, xs, ys))
    == Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)) : Nat}

def chk.len_append(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{_x, tl}:
      %chk.len_append(tl, ys) : {1n+List.length(&2, String, List.append(&2, String, tl, ys)) == 1n+_ : Nat}
      {==}

# a file has one error line per diagnostic
law chk.len_show:
  for ds: List<&2, Rep.Diag>
  for +path: String
  {List.length(&2, String, Check.show_all(ds, path)) == List.length(&2, Rep.Diag, ds) : Nat}

def chk.len_show(ds, path):
  match ds:
    case Nil{}:
      {==}
    case Con{Rep.Diag{_line, _msg}, tl}:
      %chk.len_show(tl, path) : {1n+List.length(&2, String, Check.show_all(tl, path)) == 1n+_ : Nat}
      {==}

def Laws.check_one_each(runs):
  match runs:
    case Nil{}:
      {==}
    case Con{Check.Run{+path, +ds}, +rest}:
      %Laws.check_one_each(rest) : {List.length(&2, String,
          List.append(&2, String, Check.show_all(ds, path), Check.lines_of(rest)))
        == Nat.add(List.length(&2, Rep.Diag, ds), _) : Nat}
      %chk.len_show(ds, path) : {List.length(&2, String,
          List.append(&2, String, Check.show_all(ds, path), Check.lines_of(rest)))
        == Nat.add(_, List.length(&2, String, Check.lines_of(rest))) : Nat}
      chk.len_append(Check.show_all(ds, path), Check.lines_of(rest))
    case Con{Check.Failed{_path}, +rest}:
      %Laws.check_one_each(rest) : {1n+List.length(&2, String, Check.lines_of(rest)) == 1n+_ : Nat}
      {==}

# a Nat's type when it is zero: inhabited only at zero
def chk.zero_ty(nn: Nat) -> Type:
  match nn:
    case 0n:
      Unit
    case 1n+_p:
      Empty

# a successor is never zero
law chk.succ_zero:
  for nn: Nat
  for e: {1n+nn == 0n : Nat}
  Empty

def chk.succ_zero(nn, e):
  e2 = Equal.sym(Nat, 1n+nn, 0n, e)
  %e2 : chk.zero_ty(_)
  Unit{}

# a list of no length is empty
law chk.nil:
  for xs: List<&2, String>
  for h: {List.length(&2, String, xs) == 0n : Nat}
  {xs == [] : List<&2, String>}

def chk.nil(xs, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +tl}:
      Empty.absurd({x <> tl == [] : List<&2, String>}, chk.succ_zero(List.length(&2, String, tl), h))

def Laws.check_clean(runs, h):
  +e1 = Equal.trans(Nat, List.length(&2, String, Check.lines_of(runs)), Laws.chk_count(runs), 0n,
    Laws.check_one_each(runs), h)
  e2 = Equal.sym(Nat, List.length(&2, String, Check.lines_of(runs)), 0n, e1)
  %e2 : {Check.out.at(Check.lines_of(runs), _) == Check.Out{["clean"], 0} : Check.Out}
  e3 = Equal.sym(List<&2, String>, Check.lines_of(runs), [], chk.nil(Check.lines_of(runs), e1))
  %e3 : {Check.Out{List.append(&2, String, _, ["clean"]), 0} == Check.Out{["clean"], 0} : Check.Out}
  {==}

def Laws.check_one(runs, h):
  e1 = Equal.sym(Nat, List.length(&2, String, Check.lines_of(runs)), 1n,
    Equal.trans(Nat, List.length(&2, String, Check.lines_of(runs)), Laws.chk_count(runs), 1n,
      Laws.check_one_each(runs), h))
  %e1 : {Check.out.at(Check.lines_of(runs), _)
    == Check.Out{List.append(&2, String, Laws.chk_lines(runs), ["1 error, 0 warnings"]), 1} : Check.Out}
  %Laws.check_lines(runs) : {Check.Out{List.append(&2, String, Check.lines_of(runs), ["1 error, 0 warnings"]), 1}
    == Check.Out{List.append(&2, String, _, ["1 error, 0 warnings"]), 1} : Check.Out}
  {==}

def Laws.check_many(runs, more, h):
  e1 = Equal.sym(Nat, List.length(&2, String, Check.lines_of(runs)), 2n+more,
    Equal.trans(Nat, List.length(&2, String, Check.lines_of(runs)), Laws.chk_count(runs), 2n+more,
      Laws.check_one_each(runs), h))
  %e1 : {Check.out.at(Check.lines_of(runs), _)
    == Check.Out{List.append(&2, String, Laws.chk_lines(runs),
      [U32.show(U32.from_nat(2n+more)) ++ " errors, 0 warnings"]), 1} : Check.Out}
  %Laws.check_lines(runs) : {Check.Out{List.append(&2, String, Check.lines_of(runs),
      [U32.show(U32.from_nat(2n+more)) ++ " errors, 0 warnings"]), 1}
    == Check.Out{List.append(&2, String, _, [U32.show(U32.from_nat(2n+more)) ++ " errors, 0 warnings"]), 1}
    : Check.Out}
  {==}

# a count past zero exits 1, whatever the lines
law chk.code_succ:
  for ls: List<&2, String>
  for nn: Nat
  {Laws.chk_code(Check.out.at(ls, 1n+nn)) == 1 : U32}

def chk.code_succ(_ls, nn):
  match nn:
    case 0n:
      {==}
    case 1n+_p:
      {==}

def Laws.check_unrun_error(path, runs):
  chk.code_succ((path ++ ":1:1: error: could not run bend") <> Check.lines_of(runs),
    List.length(&2, String, Check.lines_of(runs)))

def Laws.check_run_of(_path, _ds):
  {==}

def Laws.check_run_unrun(_path):
  {==}

def Laws.check_exec_ran(_text):
  {==}

def Laws.check_exec_unrun(_text):
  {==}

def Laws.check_exec_died(text, h):
  %Equal.sym(List<&2, Rep.Diag>, Rep.parse(text), [], h) : {BendChecker.died(_) == Checker.Unrun{} : Checker.Answer}
  {==}

def Laws.check_exec_died_reported(text, dd, ds, h):
  %Equal.sym(List<&2, Rep.Diag>, Rep.parse(text), dd <> ds, h) : {BendChecker.died(_)
    == Checker.Checked{dd <> ds} : Checker.Answer}
  {==}

# neither tag is no check
law chk.untagged:
  for ran: Bool
  for killed: Bool
  for text: String
  for h: {Bool.or(ran, killed) == False{} : Bool}
  {BendChecker.answer.tag(ran, killed, text) == Checker.Unrun{} : Checker.Answer}

def chk.untagged(ran, killed, text, h):
  match ran killed:
    case True{} _k:
      Empty.absurd({BendChecker.answer.tag(True{}, _k, text) == Checker.Unrun{} : Checker.Answer},
        cli.true_false(h))
    case False{} True{}:
      Empty.absurd({BendChecker.answer.tag(False{}, True{}, text) == Checker.Unrun{} : Checker.Answer},
        cli.true_false(h))
    case False{} False{}:
      {==}

def Laws.check_exec_untagged(cc, text, h):
  chk.untagged(Char.is_eq(cc, 'r'), Char.is_eq(cc, 's'), text, h)

def Laws.check_proof_unrun(_ds):
  {==}

# The line bend marks (BOLT-CHK-1). chk.report's text is its lines, each
# ended by a newline (mk.lines); Rep.parse walks them a line at a time, and
# each error's lines leave the parser's state holding that error, the one
# before it flushed (mk.block, mk.flush).

# a string opens with the empty string
law mk.sw_nil:
  for ss: String
  {String.starts_with(ss, SNil{}) == True{} : Bool}

def mk.sw_nil(ss):
  match ss:
    case SNil{}:
      {==}
    case SCon{_hh, _tt}:
      {==}

# a line's first character, the rest split at newlines: the character is no
# newline, as the line holds none
law mk.split.at:
  for +cc: Char
  for +tt: String
  for +rr: String
  for bb: Bool
  for hh: {String.contains.if(tt, "\n", String.starts_with.if(tt, SNil{}, bb)) == False{} : Bool}
  for ih: {String.contains(tt, "\n") == False{} : Bool}
    -> {String.split(String.append(tt, SCon{'\n', rr}), '\n') == tt <> String.split(rr, '\n') : List<&2,
      String>}
  {String.split.fin(cc, String.split(String.append(tt, SCon{'\n', rr}), '\n'), bb)
    == SCon{cc, tt} <> String.split(rr, '\n') : List<&2, String>}

def mk.split.at(cc, tt, rr, bb, hh, ih):
  match bb:
    case True{}:
      Empty.absurd({String.split.fin(cc, String.split(String.append(tt, SCon{'\n', rr}), '\n'), True{})
          == SCon{cc, tt} <> String.split(rr, '\n') : List<&2, String>},
        cli.true_false(Equal.trans(Bool, True{}, String.contains.if(tt, "\n", String.starts_with(tt,
          SNil{})), False{},
          Equal.sym(Bool, String.contains.if(tt, "\n", String.starts_with(tt, SNil{})), True{},
            Equal.cong(Bool, Bool, xx => String.contains.if(tt, "\n", xx), String.starts_with(tt, SNil{}),
              True{},
              mk.sw_nil(tt))),
          hh)))
    case False{}:
      Equal.cong(List<&2, String>, List<&2, String>, xs => String.split.push(cc, xs),
        String.split(String.append(tt, SCon{'\n', rr}), '\n'), tt <> String.split(rr, '\n'), ih(hh))

# a line with no newline in it, then a newline: split there, the line comes
# out whole
law mk.split:
  for ll: String
  for +rr: String
  for hh: {String.contains(ll, "\n") == False{} : Bool}
  {String.split(String.append(ll, SCon{'\n', rr}), '\n') == ll <> String.split(rr, '\n') : List<&2, String>}

def mk.split(ll, rr, hh):
  match ll:
    case SNil{}:
      {==}
    case SCon{+cc, +tt}:
      mk.split.at(cc, tt, rr, Char.is_eq(cc, '\n'), hh, xx => mk.split(tt, rr, xx))

# a report's text splits into its lines, and the empty line after the last
# newline
law mk.lines:
  for +ls: List<&2, String>
  for flat: Laws.chk.flat(ls)
  {String.split(Laws.chk.text(ls), '\n') == List.append(&2, String, ls, [""]) : List<&2, String>}

def mk.lines(ls, flat):
  match ls:
    case Nil{}:
      {==}
    case Con{+ll, +rest}:
      (h1, h2) = flat
      Equal.trans(List<&2, String>, String.split(String.append(ll, SCon{'\n', Laws.chk.text(rest)}), '\n'),
        ll <> String.split(Laws.chk.text(rest), '\n'), ll <> List.append(&2, String, rest, [""]),
        mk.split(ll, Laws.chk.text(rest), h1),
        Equal.cong(List<&2, String>, List<&2, String>, xs => ll <> xs, String.split(Laws.chk.text(rest),
          '\n'),
          List.append(&2, String, rest, [""]), mk.lines(rest, h2)))

# the parser over two runs of lines is the parser over the first, then the
# second
law mk.run_app:
  for aa: List<&2, String>
  for bb: List<&2, String>
  for st: Rep.St
  {Rep.run(List.append(&2, String, aa, bb), st) == Rep.run(bb, Rep.run(aa, st)) : Rep.St}

def mk.run_app(aa, bb, st):
  match aa:
    case Nil{}:
      {==}
    case Con{ll, rest}:
      mk.run_app(rest, bb, Rep.step(ll, st))

# an empty line changes nothing
law mk.blank:
  for st: Rep.St
  {Rep.step("", st) == st : Rep.St}

def mk.blank(st):
  match st:
    case Rep.St{seen, located, _msg, _line, _place, _out}:
      match seen located:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}

# what a state flushes: its diagnostics so far, reversed, the pending one on
# top
def mk.pend(st: Rep.St) -> List<&2, Rep.Diag>:
  Rep.St{seen, _located, msg, line, place, out} = st
  Rep.flush(seen, msg, line, place, out)

# the parser's answer is what its last state flushes, in order
law mk.finish:
  for st: Rep.St
  {Rep.finish(st) == List.reverse(&2, Rep.Diag, mk.pend(st)) : List<&2, Rep.Diag>}

def mk.finish(st):
  match st:
    case Rep.St{_seen, _located, _msg, _line, _place, _out}:
      {==}

# reversing onto acc, then onto ys: acc back in order, then the list, then ys
law mk.rev_go:
  for -A: Kind(&2)
  for xs: List<&2, A>
  for acc: List<&2, A>
  for ys: List<&2, A>
  {List.reverse.go(&2, A, List.reverse.go(&2, A, xs, acc), ys)
    == List.reverse.go(&2, A, acc, List.append(&2, A, xs, ys)) : List<&2, A>}

def mk.rev_go(A, xs, acc, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{xx, rest}:
      mk.rev_go(A, rest, xx <> acc, ys)

# a list reversed twice is itself
law mk.rev_rev:
  for -A: Kind(&2)
  for +xs: List<&2, A>
  {List.reverse(&2, A, List.reverse(&2, A, xs)) == xs : List<&2, A>}

def mk.rev_rev(A, xs):
  Equal.trans(List<&2, A>, List.reverse(&2, A, List.reverse(&2, A, xs)), List.append(&2, A, xs, []), xs,
    mk.rev_go(A, xs, [], []), lint.app_nil(A, xs))

# two lists reversed onto acc: the first, then the second
law mk.rev_app:
  for -A: Kind(&2)
  for xs: List<&2, A>
  for ys: List<&2, A>
  for acc: List<&2, A>
  {List.reverse.go(&2, A, List.append(&2, A, xs, ys), acc)
    == List.reverse.go(&2, A, ys, List.reverse.go(&2, A, xs, acc)) : List<&2, A>}

def mk.rev_app(A, xs, ys, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{xx, rest}:
      mk.rev_app(A, rest, ys, xx <> acc)

# a digit is not whitespace
law mk.digit_trim:
  for dd: Laws.chk.Dig
  for +xx: String
  {String.trim_start(SCon{Laws.chk.digit(dd), xx}) == SCon{Laws.chk.digit(dd), xx} : String}

def mk.digit_trim(dd, _xx):
  match dd:
    case Laws.ChkD0{}:
      {==}
    case Laws.ChkD1{}:
      {==}
    case Laws.ChkD2{}:
      {==}
    case Laws.ChkD3{}:
      {==}
    case Laws.ChkD4{}:
      {==}
    case Laws.ChkD5{}:
      {==}
    case Laws.ChkD6{}:
      {==}
    case Laws.ChkD7{}:
      {==}
    case Laws.ChkD8{}:
      {==}
    case Laws.ChkD9{}:
      {==}

# a number's padding trims away, down to its first digit
law mk.pad_trim:
  for kk: Nat
  for dd: Laws.chk.Dig
  for +xx: String
  {String.trim_start(String.append(Laws.chk.pad(kk), SCon{Laws.chk.digit(dd), xx}))
    == SCon{Laws.chk.digit(dd), xx} : String}

def mk.pad_trim(kk, dd, xx):
  match kk:
    case 0n:
      mk.digit_trim(dd, xx)
    case 1n+pp:
      mk.pad_trim(pp, dd, xx)

# the marker reader counts a digit and reads on
law mk.go_digit:
  for dd: Laws.chk.Dig
  for +xx: String
  for +whole: String
  for +kk: Nat
  {Rep.marker.go(SCon{Laws.chk.digit(dd), xx}, whole, kk) == Rep.marker.go(xx, whole, 1n+kk) : Maybe<&2, U32>}

def mk.go_digit(dd, _xx, _whole, _kk):
  match dd:
    case Laws.ChkD0{}:
      {==}
    case Laws.ChkD1{}:
      {==}
    case Laws.ChkD2{}:
      {==}
    case Laws.ChkD3{}:
      {==}
    case Laws.ChkD4{}:
      {==}
    case Laws.ChkD5{}:
      {==}
    case Laws.ChkD6{}:
      {==}
    case Laws.ChkD7{}:
      {==}
    case Laws.ChkD8{}:
      {==}
    case Laws.ChkD9{}:
      {==}

# one more on the right is one more
law mk.add_succ:
  for aa: Nat
  for +bb: Nat
  {Nat.add(aa, 1n+bb) == 1n+Nat.add(aa, bb) : Nat}

def mk.add_succ(aa, bb):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 1n+bb), 1n+Nat.add(pp, bb), mk.add_succ(pp, bb))

# nothing on the right adds nothing
law mk.add_zero:
  for aa: Nat
  {Nat.add(aa, 0n) == aa : Nat}

def mk.add_zero(aa):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 0n), pp, mk.add_zero(pp))

# the marker reader counts a numeral's digits and reads on past them
law mk.digits:
  for ds: List<&2, Laws.chk.Dig>
  for +rr: String
  for +whole: String
  for +kk: Nat
  {Rep.marker.go(String.append(Laws.chk.num(ds), rr), whole, kk)
    == Rep.marker.go(rr, whole, Nat.add(List.length(&2, Laws.chk.Dig, ds), kk)) : Maybe<&2, U32>}

def mk.digits(ds, rr, whole, kk):
  match ds:
    case Nil{}:
      {==}
    case Con{dd, +rest}:
      Equal.trans(Maybe<&2, U32>,
        Rep.marker.go(SCon{Laws.chk.digit(dd), String.append(Laws.chk.num(rest), rr)}, whole, kk),
        Rep.marker.go(String.append(Laws.chk.num(rest), rr), whole, 1n+kk),
        Rep.marker.go(rr, whole, 1n+Nat.add(List.length(&2, Laws.chk.Dig, rest), kk)),
        mk.go_digit(dd, String.append(Laws.chk.num(rest), rr), whole, kk),
        Equal.trans(Maybe<&2, U32>, Rep.marker.go(String.append(Laws.chk.num(rest), rr), whole, 1n+kk),
          Rep.marker.go(rr, whole, Nat.add(List.length(&2, Laws.chk.Dig, rest), 1n+kk)),
          Rep.marker.go(rr, whole, 1n+Nat.add(List.length(&2, Laws.chk.Dig, rest), kk)),
          mk.digits(rest, rr, whole, 1n+kk),
          Equal.cong(Nat, Maybe<&2, U32>, xx => Rep.marker.go(rr, whole, xx),
            Nat.add(List.length(&2, Laws.chk.Dig, rest), 1n+kk), 1n+Nat.add(List.length(&2, Laws.chk.Dig,
              rest), kk),
            mk.add_succ(List.length(&2, Laws.chk.Dig, rest), kk))))

# as many characters as a numeral has digits, taken from the numeral and what
# follows it, are the numeral
law mk.take:
  for ds: List<&2, Laws.chk.Dig>
  for +rr: String
  {String.take(String.append(Laws.chk.num(ds), SCon{'>', rr}), List.length(&2, Laws.chk.Dig, ds))
    == Laws.chk.num(ds) : String}

def mk.take(ds, rr):
  match ds:
    case Nil{}:
      {==}
    case Con{dd, +rest}:
      Equal.cong(String, String, xx => SCon{Laws.chk.digit(dd), xx},
        String.take(String.append(Laws.chk.num(rest), SCon{'>', rr}), List.length(&2, Laws.chk.Dig, rest)),
        Laws.chk.num(rest), mk.take(rest, rr))

# the marked line marks the number its numeral reads as
law mk.mark:
  for +pad: Nat
  for +first: Laws.chk.Dig
  for +rest: List<&2, Laws.chk.Dig>
  for +code: String
  {Rep.marker(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code},
    ">| ")) == U32.read(Laws.chk.num(first <> rest))
    : Maybe<&2, U32>}

def mk.mark(pad, first, rest, code):
  Equal.trans(Maybe<&2, U32>,
    Rep.marker(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ")),
    Rep.marker.go(String.append(Laws.chk.num(first <> rest), ">| " ++ code),
      String.append(Laws.chk.num(first <> rest), ">| " ++ code), 0n),
    U32.read(Laws.chk.num(first <> rest)),
    Equal.cong(String, Maybe<&2, U32>, xx => Rep.marker.go(xx, xx, 0n),
      String.trim_start(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ")),
      String.append(Laws.chk.num(first <> rest), ">| " ++ code),
      mk.pad_trim(pad, first, String.append(Laws.chk.num(rest), ">| " ++ code))),
    Equal.trans(Maybe<&2, U32>,
      Rep.marker.go(String.append(Laws.chk.num(first <> rest), ">| " ++ code),
        String.append(Laws.chk.num(first <> rest), ">| " ++ code), 0n),
      U32.read(String.take(String.append(Laws.chk.num(first <> rest), ">| " ++ code),
        Nat.add(List.length(&2, Laws.chk.Dig, first <> rest), 0n))),
      U32.read(Laws.chk.num(first <> rest)),
      mk.digits(first <> rest, ">| " ++ code, String.append(Laws.chk.num(first <> rest), ">| " ++ code), 0n),
      Equal.trans(Maybe<&2, U32>,
        U32.read(String.take(String.append(Laws.chk.num(first <> rest), ">| " ++ code),
          Nat.add(List.length(&2, Laws.chk.Dig, first <> rest), 0n))),
        U32.read(String.take(String.append(Laws.chk.num(first <> rest), ">| " ++ code),
          List.length(&2, Laws.chk.Dig, first <> rest))),
        U32.read(Laws.chk.num(first <> rest)),
        Equal.cong(Nat, Maybe<&2, U32>,
          xx => U32.read(String.take(String.append(Laws.chk.num(first <> rest), ">| " ++ code), xx)),
          Nat.add(List.length(&2, Laws.chk.Dig, first <> rest), 0n), List.length(&2, Laws.chk.Dig,
            first <> rest),
          mk.add_zero(List.length(&2, Laws.chk.Dig, first <> rest))),
        Equal.cong(String, Maybe<&2, U32>, xx => U32.read(xx),
          String.take(String.append(Laws.chk.num(first <> rest), ">| " ++ code),
            List.length(&2, Laws.chk.Dig, first <> rest)),
          Laws.chk.num(first <> rest), mk.take(first <> rest, "| " ++ code)))))

# a line of context marks nothing, whatever its code holds
law mk.ctx:
  for +pad: Nat
  for +first: Laws.chk.Dig
  for +rest: List<&2, Laws.chk.Dig>
  for +code: String
  {Rep.marker(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, " | ")) == None{} : Maybe<&2, U32>}

def mk.ctx(pad, first, rest, code):
  Equal.trans(Maybe<&2, U32>,
    Rep.marker(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, " | ")),
    Rep.marker.go(String.append(Laws.chk.num(first <> rest), " | " ++ code),
      String.append(Laws.chk.num(first <> rest), " | " ++ code), 0n),
    None{},
    Equal.cong(String, Maybe<&2, U32>, xx => Rep.marker.go(xx, xx, 0n),
      String.trim_start(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, " | ")),
      String.append(Laws.chk.num(first <> rest), " | " ++ code),
      mk.pad_trim(pad, first, String.append(Laws.chk.num(rest), " | " ++ code))),
    mk.digits(first <> rest, " | " ++ code, String.append(Laws.chk.num(first <> rest), " | " ++ code), 0n))

# a source line is no Error or Location line
law mk.classify:
  for +ss: Laws.chk.Src
  for +sep: String
  {Rep.classify(Laws.chk.src(ss, sep)) == Rep.KOther{Laws.chk.src(ss, sep)} : Rep.Line}

def mk.classify(ss, _sep):
  match ss:
    case Laws.ChkSrc{pad, first, _rest, _code}:
      match pad first:
        case 1n+_pp _first:
          {==}
        case 0n Laws.ChkD0{}:
          {==}
        case 0n Laws.ChkD1{}:
          {==}
        case 0n Laws.ChkD2{}:
          {==}
        case 0n Laws.ChkD3{}:
          {==}
        case 0n Laws.ChkD4{}:
          {==}
        case 0n Laws.ChkD5{}:
          {==}
        case 0n Laws.ChkD6{}:
          {==}
        case 0n Laws.ChkD7{}:
          {==}
        case 0n Laws.ChkD8{}:
          {==}
        case 0n Laws.ChkD9{}:
          {==}

# a line of context, after the Location line, leaves the state as it was
law mk.context:
  for mm: Maybe<&2, Laws.chk.Src>
  for +msg: List<&2, String>
  for +line: U32
  for +place: String
  for +out: List<&2, Rep.Diag>
  {Rep.run(Laws.chk.context(mm), Rep.St{True{}, True{}, msg, line, place, out})
    == Rep.St{True{}, True{}, msg, line, place, out} : Rep.St}

def mk.context(mm, msg, line, place, out):
  match mm:
    case None{}:
      {==}
    case Some{Laws.ChkSrc{+pad, +first, +rest, +code}}:
      Equal.trans(Rep.St,
        Rep.step.go(Rep.classify(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, " | ")), True{}, True{},
          msg, line, place, out),
        Rep.St{True{}, True{}, msg,
          Maybe.default(&2, U32, Rep.marker(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, " | ")),
            line), place, out},
        Rep.St{True{}, True{}, msg, line, place, out},
        Equal.cong(Rep.Line, Rep.St, kk => Rep.step.go(kk, True{}, True{}, msg, line, place, out),
          Rep.classify(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, " | ")),
          Rep.KOther{Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, " | ")},
          mk.classify(Laws.ChkSrc{pad, first, rest, code}, " | ")),
        Equal.cong(Maybe<&2, U32>, Rep.St,
          mm => Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, mm, line), place, out},
          Rep.marker(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, " | ")), None{},
          mk.ctx(pad, first, rest, code)))

# the marked line, after the Location line, sets the line to the number it
# marks, or leaves it when the numeral does not read
law mk.mark_step:
  for +pad: Nat
  for +first: Laws.chk.Dig
  for +rest: List<&2, Laws.chk.Dig>
  for +code: String
  for +msg: List<&2, String>
  for +line: U32
  for +place: String
  for +out: List<&2, Rep.Diag>
  {Rep.step(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| "), Rep.St{True{}, True{}, msg, line,
    place, out})
    == Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, U32.read(Laws.chk.num(first <> rest)), line),
      place, out}
    : Rep.St}

def mk.mark_step(pad, first, rest, code, msg, line, place, out):
  Equal.trans(Rep.St,
    Rep.step.go(Rep.classify(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ")), True{}, True{},
      msg, line, place, out),
    Rep.St{True{}, True{}, msg,
      Maybe.default(&2, U32, Rep.marker(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ")), line),
        place, out},
    Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, U32.read(Laws.chk.num(first <> rest)), line), place,
      out},
    Equal.cong(Rep.Line, Rep.St, kk => Rep.step.go(kk, True{}, True{}, msg, line, place, out),
      Rep.classify(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ")),
      Rep.KOther{Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ")},
      mk.classify(Laws.ChkSrc{pad, first, rest, code}, ">| ")),
    Equal.cong(Maybe<&2, U32>, Rep.St,
      mm => Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, mm, line), place, out},
      Rep.marker(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ")),
        U32.read(Laws.chk.num(first <> rest)),
      mk.mark(pad, first, rest, code)))

# an excerpt, after the Location line, sets the line to the number it marks
law mk.span:
  for mm: Maybe<&2, Laws.chk.Span>
  for +msg: List<&2, String>
  for +place: String
  for +out: List<&2, Rep.Diag>
  {Rep.run(Laws.chk.span(mm), Rep.St{True{}, True{}, msg, 0, place, out})
    == Rep.St{True{}, True{}, msg, Laws.chk.marks(mm), place, out} : Rep.St}

def mk.span(mm, msg, place, out):
  match mm:
    case None{}:
      {==}
    case Some{Laws.ChkSpan{+before, Laws.ChkSrc{+pad, +first, +rest, +code}, +after}}:
      Equal.trans(Rep.St,
        Rep.run(List.append(&2, String, Laws.chk.context(before),
          Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ") <> Laws.chk.context(after)),
          Rep.St{True{}, True{}, msg, 0, place, out}),
        Rep.run(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ") <> Laws.chk.context(after),
          Rep.run(Laws.chk.context(before), Rep.St{True{}, True{}, msg, 0, place, out})),
        Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, U32.read(Laws.chk.num(first <> rest)), 0), place,
          out},
        mk.run_app(Laws.chk.context(before),
          Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ") <> Laws.chk.context(after),
          Rep.St{True{}, True{}, msg, 0, place, out}),
        Equal.trans(Rep.St,
          Rep.run(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ") <> Laws.chk.context(after),
            Rep.run(Laws.chk.context(before), Rep.St{True{}, True{}, msg, 0, place, out})),
          Rep.run(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ") <> Laws.chk.context(after),
            Rep.St{True{}, True{}, msg, 0, place, out}),
          Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, U32.read(Laws.chk.num(first <> rest)), 0),
            place, out},
          Equal.cong(Rep.St, Rep.St,
            ss => Rep.run(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code},
              ">| ") <> Laws.chk.context(after), ss),
            Rep.run(Laws.chk.context(before), Rep.St{True{}, True{}, msg, 0, place, out}),
            Rep.St{True{}, True{}, msg, 0, place, out},
            mk.context(before, msg, 0, place, out)),
          Equal.trans(Rep.St,
            Rep.run(Laws.chk.context(after),
              Rep.step(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| "), Rep.St{True{}, True{}, msg,
                0, place, out})),
            Rep.run(Laws.chk.context(after),
              Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, U32.read(Laws.chk.num(first <> rest)), 0),
                place, out}),
            Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, U32.read(Laws.chk.num(first <> rest)), 0),
              place, out},
            Equal.cong(Rep.St, Rep.St, ss => Rep.run(Laws.chk.context(after), ss),
              Rep.step(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| "), Rep.St{True{}, True{}, msg,
                0, place, out}),
              Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, U32.read(Laws.chk.num(first <> rest)), 0),
                place, out},
              mk.mark_step(pad, first, rest, code, msg, 0, place, out)),
            mk.context(after, msg, Maybe.default(&2, U32, U32.read(Laws.chk.num(first <> rest)), 0), place,
              out))))

# bend's note, after the Location line, leaves the state as it was
law mk.note_loc:
  for nb: Bool
  for +msg: List<&2, String>
  for +line: U32
  for +place: String
  for +out: List<&2, Rep.Diag>
  {Rep.run(Laws.chk.note(nb), Rep.St{True{}, True{}, msg, line, place, out})
    == Rep.St{True{}, True{}, msg, line, place, out} : Rep.St}

def mk.note_loc(nb, _msg, _line, _place, _out):
  match nb:
    case False{}:
      {==}
    case True{}:
      {==}

# bend's note, with no Location line before it, joins the message
law mk.note_unloc:
  for nb: Bool
  for +msg: List<&2, String>
  for +line: U32
  for +place: String
  for +out: List<&2, Rep.Diag>
  {Rep.run(Laws.chk.note(nb), Rep.St{True{}, False{}, msg, line, place, out})
    == Rep.St{True{}, False{}, List.reverse.go(&2, String, Laws.chk.note(nb), msg), line, place,
      out} : Rep.St}

def mk.note_unloc(nb, _msg, _line, _place, _out):
  match nb:
    case False{}:
      {==}
    case True{}:
      {==}

# a `- text` line reads as its text
law mk.clean:
  for +text: String
  {Rep.clean("- " ++ text) == text : String}

def mk.clean(text):
  match text:
    case SNil{}:
      {==}
    case SCon{_hh, _tt}:
      {==}

# a line neither empty nor the nag joins the message
law mk.push.at:
  for aa: Bool
  for bb: Bool
  for -text: String
  for -msg: List<&2, String>
  for ea: {aa == False{} : Bool}
  for eb: {bb == False{} : Bool}
  {Bool.pick(List<&2, String>, Bool.or(aa, bb), msg, text <> msg) == text <> msg : List<&2, String>}

def mk.push.at(aa, bb, text, msg, ea, eb):
  match aa bb:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({Bool.pick(List<&2, String>, True{}, msg, text <> msg) == text <> msg : List<&2, String>},
        cli.true_false(eb))
    case True{} _bb:
      Empty.absurd({Bool.pick(List<&2, String>, True{}, msg, text <> msg) == text <> msg : List<&2, String>},
        cli.true_false(ea))

# a message line joins the message
law mk.push:
  for +text: String
  for +msg: List<&2, String>
  for e1: {String.is_empty(text) == False{} : Bool}
  for e2: {String.contains(text, "is available: run bend update") == False{} : Bool}
  {Rep.push(text, msg) == text <> msg : List<&2, String>}

def mk.push(text, msg, e1, e2):
  mk.push.at(String.is_empty(text), String.contains(text, "is available: run bend update"), text, msg, e1, e2)

# the message lines, after `Error:`, each join the message
law mk.parts:
  for ps: List<&2, Laws.chk.Part>
  for +msg: List<&2, String>
  for +line: U32
  for +place: String
  for +out: List<&2, Rep.Diag>
  for ok: Laws.chk.parts_ok(ps)
  {Rep.run(Laws.chk.parts(ps), Rep.St{True{}, False{}, msg, line, place, out})
    == Rep.St{True{}, False{}, List.reverse.go(&2, String, Laws.chk.texts(ps), msg), line, place,
      out} : Rep.St}

def mk.parts(ps, msg, line, place, out, ok):
  match ps:
    case Nil{}:
      {==}
    case Con{Laws.ChkItem{+text}, +rest}:
      ((e1, e2), okr) = ok
      Equal.trans(Rep.St,
        Rep.run(Laws.chk.parts(rest), Rep.St{True{}, False{}, Rep.push(Rep.clean("- " ++ text), msg), line,
          place, out}),
        Rep.run(Laws.chk.parts(rest), Rep.St{True{}, False{}, text <> msg, line, place, out}),
        Rep.St{True{}, False{}, List.reverse.go(&2, String, Laws.chk.texts(rest), text <> msg), line, place,
          out},
        Equal.cong(List<&2, String>, Rep.St,
          mm => Rep.run(Laws.chk.parts(rest), Rep.St{True{}, False{}, mm, line, place, out}),
          Rep.push(Rep.clean("- " ++ text), msg), text <> msg,
          Equal.trans(List<&2, String>, Rep.push(Rep.clean("- " ++ text), msg), Rep.push(text, msg),
            text <> msg,
            Equal.cong(String, List<&2, String>, xx => Rep.push(xx, msg), Rep.clean("- " ++ text), text,
              mk.clean(text)),
            mk.push(text, msg, e1, e2))),
        mk.parts(rest, text <> msg, line, place, out, okr))
    case Con{Laws.ChkCtx{}, rest}:
      mk.parts(rest, "Context:" <> msg, line, place, out, ok)

# whether bend said where an error is
def mk.located(at: Maybe<&2, Laws.chk.Where>) -> Bool:
  match at:
    case None{}:
      False{}
    case Some{_ww}:
      True{}

# the Location line and the excerpt set where the error is and its line
law mk.where:
  for at: Maybe<&2, Laws.chk.Where>
  for +msg: List<&2, String>
  for +out: List<&2, Rep.Diag>
  for ok: Laws.chk.name_ok(at)
  {Rep.run(Laws.chk.where(at), Rep.St{True{}, False{}, msg, 0, "", out})
    == Rep.St{True{}, mk.located(at), msg, Laws.chk.marked(at), Laws.chk.place(at), out} : Rep.St}

def mk.where(at, msg, out, ok):
  match at:
    case None{}:
      {==}
    case Some{Laws.ChkWhere{None{}, span}}:
      mk.span(span, msg, "", out)
    case Some{Laws.ChkWhere{Some{+nn}, +span}}:
      Equal.trans(Rep.St,
        Rep.run(Laws.chk.span(span), Rep.St{True{}, True{}, msg, 0, String.trim_start(nn), out}),
        Rep.run(Laws.chk.span(span), Rep.St{True{}, True{}, msg, 0, nn, out}),
        Rep.St{True{}, True{}, msg, Laws.chk.marks(span), nn, out},
        Equal.cong(String, Rep.St, pp => Rep.run(Laws.chk.span(span), Rep.St{True{}, True{}, msg, 0, pp,
          out}),
          String.trim_start(nn), nn, ok),
        mk.span(span, msg, nn, out))

# the state after an error's lines: the error pending, what came before it
# flushed to out
def mk.after(ee: Laws.chk.Err, out: List<&2, Rep.Diag>) -> Rep.St:
  Laws.ChkErr{parts, +at, note} = ee
  Rep.St{True{}, mk.located(at),
    List.reverse.go(&2, String, Laws.chk.said(at, Laws.chk.texts(parts), Laws.chk.note(note)), []),
    Laws.chk.marked(at), Laws.chk.place(at), out}

# bend's note, last in an error's lines, leaves the message it said
law mk.block.note:
  for at: Maybe<&2, Laws.chk.Where>
  for +ts: List<&2, String>
  for +nb: Bool
  for +out: List<&2, Rep.Diag>
  {Rep.run(Laws.chk.note(nb),
      Rep.St{True{}, mk.located(at), List.reverse.go(&2, String, ts, []), Laws.chk.marked(at),
        Laws.chk.place(at), out})
    == Rep.St{True{}, mk.located(at), List.reverse.go(&2, String, Laws.chk.said(at, ts, Laws.chk.note(nb)),
      []),
      Laws.chk.marked(at), Laws.chk.place(at), out} : Rep.St}

def mk.block.note(at, ts, nb, out):
  match at:
    case None{}:
      Equal.trans(Rep.St,
        Rep.run(Laws.chk.note(nb), Rep.St{True{}, False{}, List.reverse.go(&2, String, ts, []), 0, "", out}),
        Rep.St{True{}, False{}, List.reverse.go(&2, String, Laws.chk.note(nb), List.reverse.go(&2, String,
          ts, [])),
          0, "", out},
        Rep.St{True{}, False{}, List.reverse.go(&2, String, List.append(&2, String, ts, Laws.chk.note(nb)),
          []),
          0, "", out},
        mk.note_unloc(nb, List.reverse.go(&2, String, ts, []), 0, "", out),
        Equal.cong(List<&2, String>, Rep.St, mm => Rep.St{True{}, False{}, mm, 0, "", out},
          List.reverse.go(&2, String, Laws.chk.note(nb), List.reverse.go(&2, String, ts, [])),
          List.reverse.go(&2, String, List.append(&2, String, ts, Laws.chk.note(nb)), []),
          Equal.sym(List<&2, String>,
            List.reverse.go(&2, String, List.append(&2, String, ts, Laws.chk.note(nb)), []),
            List.reverse.go(&2, String, Laws.chk.note(nb), List.reverse.go(&2, String, ts, [])),
            mk.rev_app(String, ts, Laws.chk.note(nb), []))))
    case Some{+ww}:
      mk.note_loc(nb, List.reverse.go(&2, String, ts, []), Laws.chk.marked(Some{ww}),
        Laws.chk.place(Some{ww}), out)

# an error's lines leave the parser holding that error, what came before it
# flushed
law mk.block:
  for ee: Laws.chk.Err
  for st: Rep.St
  for okp: Laws.chk.parts_ok(Laws.chk.err_parts(ee))
  for okn: Laws.chk.name_ok(Laws.chk.err_at(ee))
  {Rep.run(Laws.chk.lines(ee), st) == mk.after(ee, mk.pend(st)) : Rep.St}

def mk.block(ee, st, okp, okn):
  match ee st:
    case Laws.ChkErr{+parts, +at, +note} Rep.St{+seen, +located, +msg, +line, +place, +out}:
      +flushed = Rep.flush(seen, msg, line, place, out)
      +said = List.reverse.go(&2, String, Laws.chk.texts(parts), [])
      +lp = Laws.chk.parts(parts)
      +lw = Laws.chk.where(at)
      +ln = Laws.chk.note(note)
      Equal.trans(Rep.St,
        Rep.run(List.append(&2, String, lp, List.append(&2, String, lw, ln)), Rep.St{True{}, False{}, [], 0,
          "", flushed}),
        Rep.run(List.append(&2, String, lw, ln), Rep.run(lp, Rep.St{True{}, False{}, [], 0, "", flushed})),
        mk.after(Laws.ChkErr{parts, at, note}, flushed),
        mk.run_app(lp, List.append(&2, String, lw, ln), Rep.St{True{}, False{}, [], 0, "", flushed}),
        Equal.trans(Rep.St,
          Rep.run(List.append(&2, String, lw, ln), Rep.run(lp, Rep.St{True{}, False{}, [], 0, "", flushed})),
          Rep.run(List.append(&2, String, lw, ln), Rep.St{True{}, False{}, said, 0, "", flushed}),
          mk.after(Laws.ChkErr{parts, at, note}, flushed),
          Equal.cong(Rep.St, Rep.St, ss => Rep.run(List.append(&2, String, lw, ln), ss),
            Rep.run(lp, Rep.St{True{}, False{}, [], 0, "", flushed}), Rep.St{True{}, False{}, said, 0, "",
              flushed},
            mk.parts(parts, [], 0, "", flushed, okp)),
          Equal.trans(Rep.St,
            Rep.run(List.append(&2, String, lw, ln), Rep.St{True{}, False{}, said, 0, "", flushed}),
            Rep.run(ln, Rep.run(lw, Rep.St{True{}, False{}, said, 0, "", flushed})),
            mk.after(Laws.ChkErr{parts, at, note}, flushed),
            mk.run_app(lw, ln, Rep.St{True{}, False{}, said, 0, "", flushed}),
            Equal.trans(Rep.St,
              Rep.run(ln, Rep.run(lw, Rep.St{True{}, False{}, said, 0, "", flushed})),
              Rep.run(ln, Rep.St{True{}, mk.located(at), said, Laws.chk.marked(at), Laws.chk.place(at),
                flushed}),
              mk.after(Laws.ChkErr{parts, at, note}, flushed),
              Equal.cong(Rep.St, Rep.St, ss => Rep.run(ln, ss),
                Rep.run(lw, Rep.St{True{}, False{}, said, 0, "", flushed}),
                Rep.St{True{}, mk.located(at), said, Laws.chk.marked(at), Laws.chk.place(at), flushed},
                mk.where(at, said, flushed, okn)),
              mk.block.note(at, Laws.chk.texts(parts), note, flushed)))))

# the parser's message for an error is the message it said
law mk.message:
  for +place: String
  for +ts: List<&2, String>
  {Rep.message(place, List.reverse.go(&2, String, ts, [])) == Laws.chk.message(place, ts) : String}

def mk.message(place, ts):
  Equal.cong(List<&2, String>, String, xs => Laws.chk.message(place, xs),
    List.reverse(&2, String, List.reverse(&2, String, ts)), ts, mk.rev_rev(String, ts))

# a message that is not "no main to run" is flushed as a diagnostic
law mk.flush.pick:
  for bb: Bool
  for eb: {bb == False{} : Bool}
  for -yes: List<&2, Rep.Diag>
  for -no: List<&2, Rep.Diag>
  {Bool.pick(List<&2, Rep.Diag>, Bool.and(True{}, Bool.not(bb)), yes, no) == yes : List<&2, Rep.Diag>}

def mk.flush.pick(bb, eb, yes, no):
  match bb:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({Bool.pick(List<&2, Rep.Diag>, False{}, yes, no) == yes : List<&2, Rep.Diag>},
        cli.true_false(eb))

# the parser's message, equal to the one said, flushed as a diagnostic
law mk.flush.at:
  for +text: String
  for +spec: String
  for et: {text == spec : String}
  for hmain: {String.eq(spec, "no main to run") == False{} : Bool}
  for +line: U32
  for +out: List<&2, Rep.Diag>
  {Bool.pick(List<&2, Rep.Diag>, Bool.and(True{}, Bool.not(String.eq(text, "no main to run"))),
      Rep.Diag{line, text} <> out, out) == Rep.Diag{line, spec} <> out : List<&2, Rep.Diag>}

def mk.flush.at(text, spec, et, hmain, line, out):
  %Equal.sym(String, text, spec, et) : {Bool.pick(List<&2, Rep.Diag>, Bool.and(True{}, Bool.not(String.eq(_,
    "no main to run"))),
      Rep.Diag{line, _} <> out, out) == Rep.Diag{line, spec} <> out : List<&2, Rep.Diag>}
  mk.flush.pick(String.eq(spec, "no main to run"), hmain, Rep.Diag{line, spec} <> out, out)

# the error the parser holds after its lines flushes as its diagnostic
law mk.flush:
  for ee: Laws.chk.Err
  for +out: List<&2, Rep.Diag>
  for hmain: {String.eq(Laws.chk.msg(ee), "no main to run") == False{} : Bool}
  {mk.pend(mk.after(ee, out)) == Laws.chk.diag(ee) <> out : List<&2, Rep.Diag>}

def mk.flush(ee, out, hmain):
  match ee:
    case Laws.ChkErr{+parts, +at, +note}:
      mk.flush.at(
        Rep.message(Laws.chk.place(at),
          List.reverse.go(&2, String, Laws.chk.said(at, Laws.chk.texts(parts), Laws.chk.note(note)), [])),
        Laws.chk.msg(Laws.ChkErr{parts, at, note}),
        mk.message(Laws.chk.place(at), Laws.chk.said(at, Laws.chk.texts(parts), Laws.chk.note(note))),
        hmain, Rep.line_of(Laws.chk.place(at), Laws.chk.marked(at)), out)

# every error's lines, one after another: each flushes as its diagnostic
law mk.all:
  for es: List<&2, Laws.chk.Err>
  for +st: Rep.St
  for fits: Laws.chk.fits(es)
  {mk.pend(Rep.run(Laws.chk.all(es), st))
    == List.reverse.go(&2, Rep.Diag, Laws.chk.diags(es), mk.pend(st)) : List<&2, Rep.Diag>}

def mk.all(es, st, fits):
  match es:
    case Nil{}:
      {==}
    case Con{+ee, +rest}:
      (((okp, okn), hmain), okr) = fits
      Equal.trans(List<&2, Rep.Diag>,
        mk.pend(Rep.run(List.append(&2, String, Laws.chk.lines(ee), Laws.chk.all(rest)), st)),
        mk.pend(Rep.run(Laws.chk.all(rest), Rep.run(Laws.chk.lines(ee), st))),
        List.reverse.go(&2, Rep.Diag, Laws.chk.diags(rest), Laws.chk.diag(ee) <> mk.pend(st)),
        Equal.cong(Rep.St, List<&2, Rep.Diag>, ss => mk.pend(ss),
          Rep.run(List.append(&2, String, Laws.chk.lines(ee), Laws.chk.all(rest)), st),
          Rep.run(Laws.chk.all(rest), Rep.run(Laws.chk.lines(ee), st)),
          mk.run_app(Laws.chk.lines(ee), Laws.chk.all(rest), st)),
        Equal.trans(List<&2, Rep.Diag>,
          mk.pend(Rep.run(Laws.chk.all(rest), Rep.run(Laws.chk.lines(ee), st))),
          mk.pend(Rep.run(Laws.chk.all(rest), mk.after(ee, mk.pend(st)))),
          List.reverse.go(&2, Rep.Diag, Laws.chk.diags(rest), Laws.chk.diag(ee) <> mk.pend(st)),
          Equal.cong(Rep.St, List<&2, Rep.Diag>, ss => mk.pend(Rep.run(Laws.chk.all(rest), ss)),
            Rep.run(Laws.chk.lines(ee), st), mk.after(ee, mk.pend(st)), mk.block(ee, st, okp, okn)),
          Equal.trans(List<&2, Rep.Diag>,
            mk.pend(Rep.run(Laws.chk.all(rest), mk.after(ee, mk.pend(st)))),
            List.reverse.go(&2, Rep.Diag, Laws.chk.diags(rest), mk.pend(mk.after(ee, mk.pend(st)))),
            List.reverse.go(&2, Rep.Diag, Laws.chk.diags(rest), Laws.chk.diag(ee) <> mk.pend(st)),
            mk.all(rest, mk.after(ee, mk.pend(st)), okr),
            Equal.cong(List<&2, Rep.Diag>, List<&2, Rep.Diag>, ds => List.reverse.go(&2, Rep.Diag,
              Laws.chk.diags(rest), ds),
              mk.pend(mk.after(ee, mk.pend(st))), Laws.chk.diag(ee) <> mk.pend(st), mk.flush(ee,
                mk.pend(st), hmain)))))

def Laws.check_marked(es, flat, fits):
  +init = {Rep.St{False{}, False{}, [], 0, "", []} : Rep.St}
  +ls = Laws.chk.all(es)
  Equal.trans(List<&2, Rep.Diag>,
    Rep.finish(Rep.run(String.split(Laws.chk.text(ls), '\n'), init)),
    Rep.finish(Rep.run(List.append(&2, String, ls, [""]), init)),
    Laws.chk.diags(es),
    Equal.cong(List<&2, String>, List<&2, Rep.Diag>, xs => Rep.finish(Rep.run(xs, init)),
      String.split(Laws.chk.text(ls), '\n'), List.append(&2, String, ls, [""]), mk.lines(ls, flat)),
    Equal.trans(List<&2, Rep.Diag>,
      Rep.finish(Rep.run(List.append(&2, String, ls, [""]), init)),
      Rep.finish(Rep.run([""], Rep.run(ls, init))),
      Laws.chk.diags(es),
      Equal.cong(Rep.St, List<&2, Rep.Diag>, ss => Rep.finish(ss),
        Rep.run(List.append(&2, String, ls, [""]), init), Rep.run([""], Rep.run(ls, init)),
        mk.run_app(ls, [""], init)),
      Equal.trans(List<&2, Rep.Diag>,
        Rep.finish(Rep.step("", Rep.run(ls, init))),
        Rep.finish(Rep.run(ls, init)),
        Laws.chk.diags(es),
        Equal.cong(Rep.St, List<&2, Rep.Diag>, ss => Rep.finish(ss),
          Rep.step("", Rep.run(ls, init)), Rep.run(ls, init), mk.blank(Rep.run(ls, init))),
        Equal.trans(List<&2, Rep.Diag>,
          Rep.finish(Rep.run(ls, init)),
          List.reverse(&2, Rep.Diag, mk.pend(Rep.run(ls, init))),
          Laws.chk.diags(es),
          mk.finish(Rep.run(ls, init)),
          Equal.trans(List<&2, Rep.Diag>,
            List.reverse(&2, Rep.Diag, mk.pend(Rep.run(ls, init))),
            List.reverse(&2, Rep.Diag, List.reverse(&2, Rep.Diag, Laws.chk.diags(es))),
            Laws.chk.diags(es),
            Equal.cong(List<&2, Rep.Diag>, List<&2, Rep.Diag>, ds => List.reverse(&2, Rep.Diag, ds),
              mk.pend(Rep.run(ls, init)), List.reverse(&2, Rep.Diag, Laws.chk.diags(es)),
              mk.all(es, init, fits)),
            mk.rev_rev(Rep.Diag, Laws.chk.diags(es)))))))

# a bit the same on both sides, the rest equal
law mk.wsub.arm:
  for -p: Nat
  for -h: Bool
  for -lhs: Word(p)
  for -at: Word(p)
  for e: {lhs == at : Word(p)}
  {WCon{h, lhs} == WCon{h, at} : Word.Con<p>}

def mk.wsub.arm(p, h, lhs, at, e):
  Equal.cong(Word(p), Word.Con<p>, w => WCon{h, w}, lhs, at, e)

# a word less another, plus it again, is itself: the two carries in, c and
# not c, add up to the one a subtraction borrows
law mk.wsub:
  for n: Nat
  for a: Word(n)
  for +b: Word(n)
  for c: Bool
  {Word.adc(n, Word.adc(n, a, b, True{}, c), b, False{}, Bool.not(c)) == a : Word(n)}

def mk.wsub(n, a, b, c):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+(+p):
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          mk.wsub.arm(p, False{}, Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, True{}), at,
            mk.wsub(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          mk.wsub.arm(p, False{}, Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, False{}), at,
            mk.wsub(p, at, bt, True{}))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          mk.wsub.arm(p, False{}, Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, True{}), at,
            mk.wsub(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          mk.wsub.arm(p, False{}, Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, True{}), at,
            mk.wsub(p, at, bt, False{}))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          mk.wsub.arm(p, True{}, Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, False{}), at,
            mk.wsub(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          mk.wsub.arm(p, True{}, Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, False{}), at,
            mk.wsub(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          mk.wsub.arm(p, True{}, Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, True{}), at,
            mk.wsub(p, at, bt, False{}))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          mk.wsub.arm(p, True{}, Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, False{}), at,
            mk.wsub(p, at, bt, True{}))

# a number less one, plus one, is itself
law mk.usub:
  for a: U32
  {U32.add(U32.sub(a, 1), 1) == a : U32}

def mk.usub(a):
  match a:
    case U32{w}:
      Equal.cong(Word(32n), U32, x => U32{x},
        Word.adc(32n, Word.adc(32n, w, WCon{True{}, Word.zero(31n)}, True{}, True{}), WCon{True{},
          Word.zero(31n)},
          False{}, False{}), w, mk.wsub(32n, w, WCon{True{}, Word.zero(31n)}, True{}))

# the printed number is the 0-based line plus one
law mk.shown:
  for bb: Bool
  for +vv: U32
  {U32.add(Bool.pick(U32, bb, 0, (vv - 1 : U32)), 1) == Bool.pick(U32, bb, 1, vv) : U32}

def mk.shown(bb, vv):
  match bb:
    case True{}:
      {==}
    case False{}:
      mk.usub(vv)

# each diagnostic printed: on the number chk.shown says, with its message
law mk.show_all:
  for es: List<&2, Laws.chk.Err>
  for +path: String
  {Check.show_all(Laws.chk.diags(es), path) == Laws.chk.printed(es, path) : List<&2, String>}

def mk.show_all(es, path):
  match es:
    case Nil{}:
      {==}
    case Con{+ee, +rest}:
      +place = Laws.chk.place(Laws.chk.err_at(ee))
      +vv = Laws.chk.marked(Laws.chk.err_at(ee))
      +msg = Laws.chk.msg(ee)
      Equal.trans(List<&2, String>,
        (path ++ ":" ++ U32.show((Laws.chk.row(place, vv) + 1 : U32)) ++ ":1: error: " ++ Check.message(msg))
          <> Check.show_all(Laws.chk.diags(rest), path),
        (path ++ ":" ++ U32.show(Laws.chk.shown(place, vv)) ++ ":1: error: " ++ Check.message(msg))
          <> Check.show_all(Laws.chk.diags(rest), path),
        Laws.chk.printed(Con{ee, rest}, path),
        Equal.cong(U32, List<&2, String>,
          xx => (path ++ ":" ++ U32.show(xx) ++ ":1: error: " ++ Check.message(msg))
            <> Check.show_all(Laws.chk.diags(rest), path),
          (Laws.chk.row(place, vv) + 1 : U32), Laws.chk.shown(place, vv),
          mk.shown(Bool.or(String.contains(place, "/"), U32.is_eq(vv, 0)), vv)),
        Equal.cong(List<&2, String>, List<&2, String>,
          xs => (path ++ ":" ++ U32.show(Laws.chk.shown(place,
            vv)) ++ ":1: error: " ++ Check.message(msg)) <> xs,
          Check.show_all(Laws.chk.diags(rest), path), Laws.chk.printed(rest, path), mk.show_all(rest, path)))

def Laws.check_marked_line(path, es, flat, fits):
  Equal.trans(List<&2, String>,
    List.append(&2, String, Check.show_all(Rep.parse(Laws.chk.report(es)), path), []),
    List.append(&2, String, Check.show_all(Laws.chk.diags(es), path), []),
    Laws.chk.printed(es, path),
    Equal.cong(List<&2, Rep.Diag>, List<&2, String>, ds => List.append(&2, String, Check.show_all(ds, path),
      []),
      Rep.parse(Laws.chk.report(es)), Laws.chk.diags(es), Laws.check_marked(es, flat, fits)),
    Equal.trans(List<&2, String>,
      List.append(&2, String, Check.show_all(Laws.chk.diags(es), path), []),
      Check.show_all(Laws.chk.diags(es), path),
      Laws.chk.printed(es, path),
      lint.app_nil(String, Check.show_all(Laws.chk.diags(es), path)),
      mk.show_all(es, path)))

# an error in a file named by a path prints on line 1, headed by that file
law mk.import.at:
  for bb: Bool
  for eb: {bb == True{} : Bool}
  for +path: String
  for +name: String
  for +vv: U32
  for +body: String
  {[path ++ ":" ++ U32.show(Bool.pick(U32, Bool.or(bb, U32.is_eq(vv, 0)), 1, vv)) ++ ":1: error: "
      ++ Check.message(Bool.pick(String, bb, "in " ++ name ++ ":\n" ++ body, body))]
    == [path ++ ":1:1: error: " ++ Check.message("in " ++ name ++ ":\n" ++ body)] : List<&2, String>}

def mk.import.at(bb, eb, path, name, vv, body):
  match bb:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({[path ++ ":" ++ U32.show(Bool.pick(U32, Bool.or(False{}, U32.is_eq(vv, 0)), 1,
        vv)) ++ ":1: error: "
          ++ Check.message(Bool.pick(String, False{}, "in " ++ name ++ ":\n" ++ body, body))]
        == [path ++ ":1:1: error: " ++ Check.message("in " ++ name ++ ":\n" ++ body)] : List<&2, String>},
        cli.false_true(eb))

def Laws.check_import_first(path, parts, name, span, note, slash, flat, fits):
  Equal.trans(List<&2, String>,
    Check.lines_of([Check.Run{path, Rep.parse(Laws.chk.report([Laws.ChkErr{parts,
      Some{Laws.ChkWhere{Some{name}, span}}, note}]))}]),
    Laws.chk.printed([Laws.ChkErr{parts, Some{Laws.ChkWhere{Some{name}, span}}, note}], path),
    [path ++ ":1:1: error: " ++ Check.message("in " ++ name ++ ":\n" ++ String.join(Laws.chk.texts(parts),
      "\n"))],
    Laws.check_marked_line(path, [Laws.ChkErr{parts, Some{Laws.ChkWhere{Some{name}, span}}, note}], flat,
      fits),
    mk.import.at(String.contains(name, "/"), slash, path, name, Laws.chk.marks(span),
      String.join(Laws.chk.texts(parts), "\n")))
