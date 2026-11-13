# the unknown-setting rule's findings on each bolt.bend match the spec
import Base
import ../../src/config.bend as Config
import ../../src/finding.bend as F
import ../../src/lint/world.bend as W
import ../../src/lint/plan.bend as Plan
import ../../src/rules/correctness/setting.bend as Setting
import ../../laws/SettingReportsUnknownNames.bend as L1
import ../../laws/defs/GradedFindingCounts.bend as D1
import ./ReplyIndex.bend as M9

# `setting` (laws/SettingReportsUnknownNames.bend): the planner's walk to each grading bolt.bend
# and its findings there are the spec's.

# one candidate onto the first one read
law c011.first.step:
  for +path: String
  for mm: Maybe<&2, W.Answer>
  for gs: List<&2, Plan.Got>
  for -more: List<&2, String>
  for ih: {Plan.conf.first(gs) == more : List<&2, String>}
  {Plan.conf.first(Plan.Got{path, W.text.got(mm)} <> gs) == D1.read_first.at(path, mm, more) : List<&2, String>}

def c011.first.step(_path, mm, _gs, _more, ih):
  match mm:
    case None{}:
      ih
    case Some{W.Listed{_names}}:
      ih
    case Some{W.Read{_text}}:
      {==}
    case Some{W.Unread{}}:
      ih
    case Some{W.Directory{}}:
      ih

# the planner's first read candidate is the spec's
law c011.first:
  for ps: List<&2, String>
  for +world: W.World
  {Plan.conf.first(Plan.gots(ps, world)) == D1.read_first(world, ps) : List<&2, String>}

def c011.first(ps, world):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +tl}:
      c011.first.step(p, W.answer(world, W.Contents{p}), Plan.gots(tl, world), D1.read_first(world, tl),
        c011.first(tl, world))

# the planner's grading bolt.bend of each directory is the spec's
law c011.used:
  for ds: List<&2, String>
  for +world: W.World
  {Plan.conf.used(ds, world) == D1.graders_all(world, ds) : List<&2, String>}

def c011.used(ds, world):
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +tl}:
      a = Equal.sym(List<&2, String>, Plan.conf.first(Plan.gots(Config.chain(Config.home(W.cwd.of(world), d)), world)),
        D1.read_first(world, Config.chain(Config.home(W.cwd.of(world), d))),
        c011.first(Config.chain(Config.home(W.cwd.of(world), d)), world))
      %a : {List.append(&2, String, _, Plan.conf.used(tl, world))
        == D1.graders_all(world, d <> tl) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>,
        rr => List.append(&2, String, D1.read_first(world, Config.chain(Config.home(W.cwd.of(world), d))), rr),
        Plan.conf.used(tl, world), D1.graders_all(world, tl), c011.used(tl, world))

# the rule's findings on settings are the spec's
law c011.found:
  for ss: List<&2, Config.Setting>
  for +path: String
  {Setting.found(ss, path) == D1.flagged(path, ss) : List<&2, F.Finding>}

def c011.found(ss, path):
  match ss:
    case Nil{}:
      {==}
    case Con{Config.Setting{+n, _w, +line}, +tl}:
      Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
        rr => F.Finding{path, line, 0, 0, "setting", "`" ++ n ++ "` names no rule or group, so it sets nothing."} <> rr,
        Setting.found(tl, path), D1.flagged(path, tl), c011.found(tl, path))

# one bolt.bend onto the rule's findings
law c011.at.step:
  for +path: String
  for mm: Maybe<&2, W.Answer>
  for gs: List<&2, Plan.Got>
  for -fs: List<&2, F.Finding>
  for ih: {Plan.settings.at(gs) == fs : List<&2, F.Finding>}
  {Plan.settings.at(Plan.Got{path, W.text.got(mm)} <> gs) == List.append(&2, F.Finding, D1.flagged_at(path, mm), fs)
    : List<&2, F.Finding>}

def c011.at.step(path, mm, gs, fs, ih):
  match mm:
    case None{}:
      ih
    case Some{W.Listed{_names}}:
      ih
    case Some{W.Read{+text}}:
      a = Equal.sym(List<&2, F.Finding>, Setting.found(Config.unknown(Config.settings(text)), path),
        D1.flagged(path, Config.unknown(Config.settings(text))),
        c011.found(Config.unknown(Config.settings(text)), path))
      %a : {List.append(&2, F.Finding, _, Plan.settings.at(gs))
        == List.append(&2, F.Finding, D1.flagged(path, Config.unknown(Config.settings(text))), fs)
        : List<&2, F.Finding>}
      Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
        rr => List.append(&2, F.Finding, D1.flagged(path, Config.unknown(Config.settings(text))), rr),
        Plan.settings.at(gs), fs, ih)
    case Some{W.Unread{}}:
      ih
    case Some{W.Directory{}}:
      ih

# the rule's findings on each bolt.bend are the spec's
law c011.at:
  for ps: List<&2, String>
  for +world: W.World
  {Plan.settings.at(Plan.gots(ps, world)) == D1.flagged_all(world, ps) : List<&2, F.Finding>}

def c011.at(ps, world):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +tl}:
      c011.at.step(p, W.answer(world, W.Contents{p}), Plan.gots(tl, world), D1.flagged_all(world, tl),
        c011.at(tl, world))

def L1.setting_reports(world):
  %Equal.sym(List<&2, String>, Plan.graders(world),
    Plan.uniq(Plan.conf.used(Plan.conf.dirs(Plan.inputs(world)), world), []), M9.ri.graders_spec(world)) :
    {Plan.settings.at(Plan.gots(_, world)) == D1.settings_found(world) : List<&2, F.Finding>}
  u = Equal.sym(List<&2, String>, Plan.conf.used(Plan.conf.dirs(Plan.inputs(world)), world),
    D1.graders_all(world, Plan.conf.dirs(Plan.inputs(world))), c011.used(Plan.conf.dirs(Plan.inputs(world)), world))
  %u : {Plan.settings.at(Plan.gots(Plan.uniq(_, []), world)) == D1.settings_found(world) : List<&2, F.Finding>}
  c011.at(Plan.uniq(D1.graders_all(world, Plan.conf.dirs(Plan.inputs(world))), []), world)
