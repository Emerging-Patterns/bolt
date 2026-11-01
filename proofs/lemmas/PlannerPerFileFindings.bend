# per-file parse, unread and scope findings of the lint planner
import Base
import ../../src/finding.bend as F
import ../../src/rules.bend as Rules
import ../../src/src.bend as Src
import ../../src/role.bend as Role
import ../../src/lint/world.bend as W
import ../../src/lint/plan.bend as Plan
import ../../laws/PackageDirs.bend as L1
import ../../laws/PackagesScoped.bend as L2
import ../../laws/ScopeRulesSeeTheirInputs.bend as L3
import ../../laws/SettingReportsUnknownNames.bend as L4
import ../../laws/defs/GradedFindingCounts.bend as D1
import ../../laws/defs/ScopeWalkFiles.bend as D2
import ./PackageDirsLists.bend as M1
import ./PackageRootLookup.bend as M2
import ./PlannerWalkInduction.bend as M3
import ./SettingRuleFindings.bend as M4

# one source onto the read failures
law lint.unread.step:
  for +path: String
  for mm: Maybe<&2, String>
  for gs: List<&2, Plan.Got>
  for -us: List<&2, F.Finding>
  for ih: {Plan.unread(gs) == us : List<&2, F.Finding>}
  {Plan.unread(Plan.Got{path, mm} <> gs) == List.append(&2, F.Finding, D1.unread_at(path, mm), us)
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
  {Plan.unread(Plan.gots(ps, world)) == D1.unread_all(world, ps) : List<&2, F.Finding>}

def lint.unread(ps, world):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +tl}:
      lint.unread.step(p, W.text(world, p), Plan.gots(tl, world), D1.unread_all(world, tl), lint.unread(tl, world))

# one source onto the parsed sources
law lint.parsed.step:
  for +path: String
  for mm: Maybe<&2, String>
  for gs: List<&2, Plan.Got>
  for -ss: List<&2, Src.Src>
  for ih: {Plan.srcs_of(gs) == ss : List<&2, Src.Src>}
  {Plan.srcs_of(Plan.Got{path, mm} <> gs) == List.append(&2, Src.Src, D1.parsed_at(path, mm), ss)
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
  {Plan.srcs_of(Plan.gots(ps, world)) == D1.parsed_all(world, ps) : List<&2, Src.Src>}

def lint.parsed(ps, world):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +tl}:
      lint.parsed.step(p, W.text(world, p), Plan.gots(tl, world), D1.parsed_all(world, tl), lint.parsed(tl, world))

# one source onto the per-file findings
law lint.on.step:
  for +ms: List<&2, Role.Mark>
  for +path: String
  for mm: Maybe<&2, String>
  for +gs: List<&2, Plan.Got>
  for -os: List<&2, F.Finding>
  for ih: {Plan.per_file.role(ms, Plan.srcs_of(gs)) == os : List<&2, F.Finding>}
  {Plan.per_file.role(ms, Plan.srcs_of(Plan.Got{path, mm} <> gs))
    == List.append(&2, F.Finding, D1.on_at(ms, path, mm), os) : List<&2, F.Finding>}

def lint.on.step(ms, path, mm, gs, os, ih):
  match mm:
    case None{}:
      ih
    case Some{text}:
      Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
        rr => List.append(&2, F.Finding, Rules.on.role(Role.of(ms, path), Src.of(path, text)), rr),
        List.append(&2, F.Finding, Plan.per_file.role(ms, Plan.srcs_of(gs)), []), os,
        Equal.trans(List<&2, F.Finding>, List.append(&2, F.Finding, Plan.per_file.role(ms, Plan.srcs_of(gs)), []),
          Plan.per_file.role(ms, Plan.srcs_of(gs)), os,
          M3.lint.app_nil(F.Finding, Plan.per_file.role(ms, Plan.srcs_of(gs))), ih))

# the planner's per-file findings are each source's with its role, in order
law lint.on:
  for +ms: List<&2, Role.Mark>
  for ps: List<&2, String>
  for +world: W.World
  {Plan.per_file.role(ms, Plan.srcs_of(Plan.gots(ps, world))) == D1.on_all(ms, world, ps) : List<&2, F.Finding>}

def lint.on(ms, ps, world):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +tl}:
      lint.on.step(ms, p, W.text(world, p), Plan.gots(tl, world), D1.on_all(ms, world, tl), lint.on(ms, tl, world))

def L3.scope_findings(world):
  n = Equal.sym(List<&2, F.Finding>,
    List.append(&2, F.Finding, Rules.project(Plan.srcs_of(Plan.gots(Plan.inputs(world), world)),
        Plan.packages(Plan.roots(world))), []),
    Rules.project(Plan.srcs_of(Plan.gots(Plan.inputs(world), world)), Plan.packages(Plan.roots(world))),
    M3.lint.app_nil(F.Finding, Rules.project(Plan.srcs_of(Plan.gots(Plan.inputs(world), world)),
        Plan.packages(Plan.roots(world)))))
  %n : {List.append(&2, F.Finding, Plan.unread(Plan.gots(Plan.inputs(world), world)),
      List.append(&2, F.Finding, Plan.per_file.role(Plan.marks.run(W.paths.of(world), world,
          Plan.srcs_of(Plan.gots(Plan.inputs(world), world))),
        Plan.srcs_of(Plan.gots(Plan.inputs(world), world))),
        List.append(&2, F.Finding, Plan.settings(world), _)))
    == D1.in_scope(world) : List<&2, F.Finding>}
  a = Equal.sym(List<&2, F.Finding>, Plan.unread(Plan.gots(Plan.inputs(world), world)),
    D1.unread_all(world, Plan.inputs(world)), lint.unread(Plan.inputs(world), world))
  %a : {List.append(&2, F.Finding, _,
      List.append(&2, F.Finding, Plan.per_file.role(Plan.marks.run(W.paths.of(world), world,
          Plan.srcs_of(Plan.gots(Plan.inputs(world), world))),
        Plan.srcs_of(Plan.gots(Plan.inputs(world), world))),
        List.append(&2, F.Finding, Plan.settings(world),
          Rules.project(Plan.srcs_of(Plan.gots(Plan.inputs(world), world)), Plan.packages(Plan.roots(world))))))
    == D1.in_scope(world) : List<&2, F.Finding>}
  b = Equal.sym(List<&2, F.Finding>, Plan.per_file.role(Plan.marks.run(W.paths.of(world), world,
      Plan.srcs_of(Plan.gots(Plan.inputs(world), world))),
        Plan.srcs_of(Plan.gots(Plan.inputs(world), world))),
    D1.on_all(Plan.marks.run(W.paths.of(world), world, Plan.srcs_of(Plan.gots(Plan.inputs(world), world))),
        world, Plan.inputs(world)),
    lint.on(Plan.marks.run(W.paths.of(world), world, Plan.srcs_of(Plan.gots(Plan.inputs(world), world))),
        Plan.inputs(world), world))
  %b : {List.append(&2, F.Finding, D1.unread_all(world, Plan.inputs(world)),
      List.append(&2, F.Finding, _, List.append(&2, F.Finding, Plan.settings(world),
        Rules.project(Plan.srcs_of(Plan.gots(Plan.inputs(world), world)), Plan.packages(Plan.roots(world))))))
    == D1.in_scope(world) : List<&2, F.Finding>}
  t = Equal.sym(List<&2, F.Finding>, Plan.settings(world), D1.settings_found(world), L4.setting_reports(world))
  %t : {List.append(&2, F.Finding, D1.unread_all(world, Plan.inputs(world)),
      List.append(&2, F.Finding, D1.on_all(Plan.marks.run(W.paths.of(world), world,
          Plan.srcs_of(Plan.gots(Plan.inputs(world), world))), world,
        Plan.inputs(world)), List.append(&2, F.Finding, _,
        Rules.project(Plan.srcs_of(Plan.gots(Plan.inputs(world), world)), Plan.packages(Plan.roots(world))))))
    == D1.in_scope(world) : List<&2, F.Finding>}
  c = Equal.sym(List<&2, Src.Src>, Plan.srcs_of(Plan.gots(Plan.inputs(world), world)),
    D1.parsed_all(world, Plan.inputs(world)), lint.parsed(Plan.inputs(world), world))
  %c : {List.append(&2, F.Finding, D1.unread_all(world, Plan.inputs(world)),
      List.append(&2, F.Finding, D1.on_all(Plan.marks.run(W.paths.of(world), world,
          Plan.srcs_of(Plan.gots(Plan.inputs(world), world))), world,
        Plan.inputs(world)),
        List.append(&2, F.Finding, D1.settings_found(world),
          Rules.project(_, Plan.packages(Plan.roots(world))))))
    == D1.in_scope(world) : List<&2, F.Finding>}
  k = Equal.sym(List<&2, String>, Plan.packages(Plan.roots(world)), D1.pkgs(Plan.roots(world)),
    L1.package_dirs(Plan.roots(world)))
  %k : {List.append(&2, F.Finding, D1.unread_all(world, Plan.inputs(world)),
      List.append(&2, F.Finding, D1.on_all(Plan.marks.run(W.paths.of(world), world,
          Plan.srcs_of(Plan.gots(Plan.inputs(world), world))), world,
        Plan.inputs(world)),
        List.append(&2, F.Finding, D1.settings_found(world),
          Rules.project(D1.parsed_all(world, Plan.inputs(world)), _))))
    == D1.in_scope(world) : List<&2, F.Finding>}
  q = Equal.sym(List<&2, F.Finding>,
    Rules.project(D1.parsed_all(world, Plan.inputs(world)), D1.pkgs(Plan.roots(world))),
    D2.packed(D1.parsed_all(world, Plan.inputs(world)), D1.pkgs(Plan.roots(world))),
    L2.packages_scoped(D1.parsed_all(world, Plan.inputs(world)), D1.pkgs(Plan.roots(world))))
  %q : {List.append(&2, F.Finding, D1.unread_all(world, Plan.inputs(world)),
      List.append(&2, F.Finding, D1.on_all(Plan.marks.run(W.paths.of(world), world,
          Plan.srcs_of(Plan.gots(Plan.inputs(world), world))), world,
        Plan.inputs(world)),
        List.append(&2, F.Finding, D1.settings_found(world), _)))
    == D1.in_scope(world) : List<&2, F.Finding>}
  z = M3.lint.app_nil(F.Finding, D2.packed(D1.parsed_all(world, Plan.inputs(world)), D1.pkgs(Plan.roots(world))))
  %z : {List.append(&2, F.Finding, D1.unread_all(world, Plan.inputs(world)),
      List.append(&2, F.Finding, D1.on_all(Plan.marks.run(W.paths.of(world), world,
          Plan.srcs_of(Plan.gots(Plan.inputs(world), world))), world,
        Plan.inputs(world)),
        List.append(&2, F.Finding, D1.settings_found(world), _)))
    == D1.in_scope(world) : List<&2, F.Finding>}
  {==}
