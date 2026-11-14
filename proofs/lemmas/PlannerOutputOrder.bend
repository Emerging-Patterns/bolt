# planner errors, grading and shown lines come out in order
import Base
import ../../src/config.bend as Config
import ../../src/finding.bend as F
import ../../src/rules.bend as Rules
import ../../src/src.bend as Src
import ../../src/lint/world.bend as W
import ../../src/lint/plan.bend as Plan
import ../../src/noqa.bend as Noqa
import ../../laws/LinesInOrder.bend as L1
import ../../laws/ScopeRulesSeeTheirInputs.bend as L2
import ../../laws/defs/GradedFindingCounts.bend as D1
import ../../laws/defs/GradingKeepsFindings.bend as D2
import ./PlannerPerFileFindings.bend as M1
import ../../laws/OffRulesAreNotRun.bend as L3
import ./OffRules.bend as M2

# one finding graded the planner's way is graded the spec's way
law lint.grade.step:
  for l: Config.Level
  for -f: F.Finding
  for -a: List<&2, F.Graded>
  for -b: List<&2, F.Graded>
  for e: {a == b : List<&2, F.Graded>}
  {List.append(&2, F.Graded, Bool.pick(List<&2, F.Graded>, Config.is_off(l), [], [F.Graded{l, f}]), a)
    == D2.keep(l, f, b) : List<&2, F.Graded>}

def lint.grade.step(l, f, a, _b, e):
  match l:
    case Config.Off{}:
      e
    case Config.Warn{}:
      %e : {F.Graded{Config.Warn{}, f} <> a == F.Graded{Config.Warn{}, f} <> _ : List<&2, F.Graded>}
      {==}
    case Config.Error{}:
      %e : {F.Graded{Config.Error{}, f} <> a == F.Graded{Config.Error{}, f} <> _ : List<&2, F.Graded>}
      {==}

# the planner grades each finding by its path's config, in order
law lint.grade:
  for +cs: List<&2, Plan.Conf>
  for +world: W.World
  for fs: List<&2, F.Finding>
  {Plan.grade(cs, world, fs) == D1.graded_by(cs, world, fs) : List<&2, F.Graded>}

def lint.grade(cs, world, fs):
  match fs:
    case Nil{}:
      {==}
    case Con{F.Finding{+path, line, col, len, +rule, msg}, +tl}:
      lint.grade.step(Config.level(Plan.config.at(cs, world, path), Rules.group(rule), rule),
        F.Finding{path, line, col, len, rule, msg}, Plan.grade(cs, world, tl), D1.graded_by(cs, world, tl),
        lint.grade(cs, world, tl))

# the planner's graded findings, before any mark is read, are the run's
law lint.graded:
  for +world: W.World
  {Plan.grade(Plan.confs(world), world, Plan.found(world)) == D1.run_raw(world) : List<&2, F.Graded>}

def lint.graded(world):
  e = Equal.sym(List<&2, F.Finding>, Plan.found(world), D1.in_scope(world), L2.scope_findings(world))
  %e : {Plan.grade(Plan.confs(world), world, _) == D1.run_raw(world) : List<&2, F.Graded>}
  lint.grade(Plan.confs(world), world, D1.in_scope(world))

# the planner's final findings, the marks read and `noqa` run, are the run's
law lint.final:
  for +world: W.World
  {Plan.final(world) == D1.run_graded(world) : List<&2, F.Graded>}

def lint.final(world):
  e = Equal.sym(List<&2, F.Graded>, Plan.grade(Plan.confs(world), world, Plan.found(world)), D1.run_raw(world),
    lint.graded(world))
  %e : {List.append(&2, F.Graded, Noqa.keep(Noqa.of_srcs(Plan.srcs_of(Plan.gots(Plan.inputs(world), world))), _),
      Plan.grade(Plan.confs(world), world,
        Plan.noqa(Noqa.of_srcs(Plan.srcs_of(Plan.gots(Plan.inputs(world), world))),
          List.is_empty(&2, String, W.paths.of(world)), _)))
    == D1.run_graded(world) : List<&2, F.Graded>}
  c = Equal.sym(List<&2, Src.Src>, Plan.srcs_of(Plan.gots(Plan.inputs(world), world)),
    D1.parsed_all(world, Plan.inputs(world)), M1.lint.parsed(Plan.inputs(world), world))
  %c : {List.append(&2, F.Graded, Noqa.keep(Noqa.of_srcs(_), D1.run_raw(world)),
      Plan.grade(Plan.confs(world), world,
        Plan.noqa(Noqa.of_srcs(_), List.is_empty(&2, String, W.paths.of(world)), D1.run_raw(world))))
    == D1.run_graded(world) : List<&2, F.Graded>}
  Equal.cong(List<&2, F.Graded>, List<&2, F.Graded>,
    r => List.append(&2, F.Graded, Noqa.keep(D1.marks_all(world), D1.run_raw(world)), r),
    Plan.grade(Plan.confs(world), world,
      Plan.noqa(D1.marks_all(world), List.is_empty(&2, String, W.paths.of(world)), D1.run_raw(world))),
    D1.graded_by(Plan.confs(world), world,
      Plan.noqa(D1.marks_all(world), List.is_empty(&2, String, W.paths.of(world)), D1.run_raw(world))),
    lint.grade(Plan.confs(world), world,
      Plan.noqa(D1.marks_all(world), List.is_empty(&2, String, W.paths.of(world)), D1.run_raw(world))))

# the planner's final findings with each file's off rules not run are the
# run's too
law lint.final.live:
  for +world: W.World
  {Plan.final.live(world) == D1.run_graded(world) : List<&2, F.Graded>}

def lint.final.live(world):
  Equal.trans(List<&2, F.Graded>, Plan.final.live(world), Plan.final(world), D1.run_graded(world),
    L3.final_live(world), lint.final(world))

# each graded finding is its line
law lint.shown:
  for gs: List<&2, F.Graded>
  {Plan.show_all(gs) == L1.shown_all(gs) : List<&2, String>}

def lint.shown(gs):
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +tl}:
      Equal.cong(List<&2, String>, List<&2, String>, r => F.show_graded(g) <> r, Plan.show_all(tl),
        L1.shown_all(tl), lint.shown(tl))

# one graded finding onto the error count
law lint.errors.step:
  for l: Config.Level
  for -a: U32
  for -n: Nat
  for e: {a == U32.from_nat(n) : U32}
  {Plan.errors.at(l, a) == U32.from_nat(D1.at_error.one(l, n)) : U32}

def lint.errors.step(l, a, n, e):
  match l:
    case Config.Off{}:
      e
    case Config.Warn{}:
      e
    case Config.Error{}:
      Equal.cong(U32, U32, x => U32.inc(x), a, U32.from_nat(n), e)

# the planner counts the errors
law lint.errors:
  for gs: List<&2, F.Graded>
  {Plan.errors(gs) == U32.from_nat(D1.at_error(gs)) : U32}

def lint.errors(gs):
  match gs:
    case Nil{}:
      {==}
    case Con{F.Graded{l, _ff}, +tl}:
      lint.errors.step(l, Plan.errors(tl), D1.at_error(tl), lint.errors(tl))

# one graded finding onto the warning count
law lint.warnings.step:
  for l: Config.Level
  for -a: U32
  for -n: Nat
  for e: {a == U32.from_nat(n) : U32}
  {Plan.warnings.at(l, a) == U32.from_nat(D1.below_error.one(l, n)) : U32}

def lint.warnings.step(l, a, n, e):
  match l:
    case Config.Off{}:
      Equal.cong(U32, U32, x => U32.inc(x), a, U32.from_nat(n), e)
    case Config.Warn{}:
      Equal.cong(U32, U32, x => U32.inc(x), a, U32.from_nat(n), e)
    case Config.Error{}:
      e

# the planner counts the warnings
law lint.warnings:
  for gs: List<&2, F.Graded>
  {Plan.warnings(gs) == U32.from_nat(D1.below_error(gs)) : U32}

def lint.warnings(gs):
  match gs:
    case Nil{}:
      {==}
    case Con{F.Graded{l, _ff}, +tl}:
      lint.warnings.step(l, Plan.warnings(tl), D1.below_error(tl), lint.warnings(tl))

# the planner's summary is the spec's
law lint.summary:
  for gs: List<&2, F.Graded>
  {Plan.summary(gs) == D1.summary_of(gs) : String}

def lint.summary(gs):
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +tl}:
      e = Equal.sym(U32, Plan.errors(g <> tl), U32.from_nat(D1.at_error(g <> tl)), lint.errors(g <> tl))
      %e : {Plan.count(_, "error") ++ ", " ++ Plan.count(Plan.warnings(g <> tl), "warning")
        == D1.summary_of(g <> tl) : String}
      w = Equal.sym(U32, Plan.warnings(g <> tl), U32.from_nat(D1.below_error(g <> tl)), lint.warnings(g <> tl))
      %w : {Plan.count(U32.from_nat(D1.at_error(g <> tl)), "error") ++ ", " ++ Plan.count(_, "warning")
        == D1.summary_of(g <> tl) : String}
      {==}

def L1.lines_in_order(world):
  e = Equal.sym(List<&2, F.Graded>, Plan.final.live(world), D1.run_graded(world), lint.final.live(world))
  %e : {List.append(&2, String, Plan.show_all(_), [Plan.summary(_)]) == L1.out_lines(world) : List<&2, String>}
  s = Equal.sym(List<&2, String>, Plan.show_all(D1.run_graded(world)), L1.shown_all(D1.run_graded(world)),
    lint.shown(D1.run_graded(world)))
  %s : {List.append(&2, String, _, [Plan.summary(D1.run_graded(world))]) == L1.out_lines(world)
    : List<&2, String>}
  m = Equal.sym(String, Plan.summary(D1.run_graded(world)), D1.summary_of(D1.run_graded(world)),
    lint.summary(D1.run_graded(world)))
  %m : {List.append(&2, String, L1.shown_all(D1.run_graded(world)), [_]) == L1.out_lines(world)
    : List<&2, String>}
  {==}
