# proofs of laws/LspDiagnosticsMatchCli.bend
import Base
import ../src/lsp/server.bend as Server
import ../src/lazy/lazy.bend as Lazy
import ../src/finding.bend as F
import ../src/config.bend as Config
import ../src/rules.bend as Rules
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ../src/src.bend as Src
import ../src/role.bend as Role
import ../src/rules/imports.bend as Imports
import ../src/noqa.bend as Noqa
import ../src/rules/style/noqa.bend as NoqaRule
import ../src/syntax/lex.bend as Lex
import ../src/paths.bend as Paths
import ../src/syntax/outline.bend as Outline
import ../laws/LspDiagnosticsMatchCli.bend as Laws
import ./lemmas/PublishComparisons.bend as M1

# appending nothing leaves a list as it was
law pub.app_nil:
  for -A: Kind(&2)
  for xs: List<&2, A>
  {List.append(&2, A, xs, []) == xs : List<&2, A>}

def pub.app_nil(A, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{hd, +tl}:
      Equal.cong(List<&2, A>, List<&2, A>, rr => hd <> rr, List.append(&2, A, tl, []), tl, pub.app_nil(A, tl))

# one finding graded alone and put before the rest graded is the rest graded
# with it
law pub.grade.step:
  for bb: Bool
  for -g: F.Graded
  for -a: List<&2, F.Graded>
  for -b: List<&2, F.Graded>
  for e: {a == b : List<&2, F.Graded>}
  {List.append(&2, F.Graded, Bool.pick(List<&2, F.Graded>, bb, [], [g]), a)
    == Bool.pick(List<&2, F.Graded>, bb, b, g <> b) : List<&2, F.Graded>}

def pub.grade.step(bb, g, a, _b, e):
  match bb:
    case True{}:
      e
    case False{}:
      %e : {g <> a == g <> _ : List<&2, F.Graded>}
      {==}

# findings all at one path: the CLI's grading, finding by finding, is
# grading them all by that path's config
law pub.grade_at:
  for +cs: List<&2, Plan.Conf>
  for +world: W.World
  for +path: String
  for fs: List<&2, F.Finding>
  {Plan.grade(cs, world, Rules.on.at(path, fs)) == Rules.graded(Plan.config.at(cs, world, path), Rules.on.at(path, fs))
    : List<&2, F.Graded>}

def pub.grade_at(cs, world, path, fs):
  match fs:
    case Nil{}:
      {==}
    case Con{F.Finding{_p, line, col, len, +rule, msg}, +rest}:
      pub.grade.step(Config.is_off(Config.level(Plan.config.at(cs, world, path), Rules.group(rule), rule)),
        F.Graded{Config.level(Plan.config.at(cs, world, path), Rules.group(rule), rule),
          F.Finding{path, line, col, len, rule, msg}},
        Plan.grade(cs, world, Rules.on.at(path, rest)),
        Rules.graded(Plan.config.at(cs, world, path), Rules.on.at(path, rest)),
        pub.grade_at(cs, world, path, rest))

# a table whose first row is a directory's own: its config is that row's
law pub.find_head:
  for +d: String
  for -rest: List<&2, Plan.Conf>
  for +world: W.World
  {Plan.conf.find(Plan.Conf{d, Plan.conf.near(world, d)} <> rest, world, d) == Plan.conf.near(world, d)
    : Config.Config}

def pub.find_head(d, rest, world):
  e = Equal.sym(Bool, String.eq(d, d), True{}, M1.pub.seq_refl(d))
  %e : {Lazy.stop(Config.Config, _, Plan.conf.near(world, d), _u => Plan.conf.find(rest, world, d))
    == Plan.conf.near(world, d) : Config.Config}
  {==}

# `bolt <path>` runs over that path alone, unless it is a bolt.bend
law pub.cli.named:
  for +world: W.World
  for +path: String
  for h: {W.paths.of(world) == [path] : List<&2, String>}
  {Plan.inputs(world) == Plan.sources([path]) : List<&2, String>}

def pub.cli.named(world, path, h):
  e = Equal.sym(List<&2, String>, W.paths.of(world), [path], h)
  %e : {Plan.sources(Plan.files.named(_, world)) == Plan.sources([path]) : List<&2, String>}
  {==}

# findings put at a path are graded by the CLI as by the config nearest it
law pub.grade_near:
  for +world: W.World
  for +path: String
  for fs: List<&2, F.Finding>
  {Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world, Rules.on.at(path, fs))
    == Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
      Rules.on.at(path, fs))
    : List<&2, F.Graded>}

def pub.grade_near(world, path, fs):
  Equal.trans(List<&2, F.Graded>,
    Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world, Rules.on.at(path, fs)),
    Rules.graded(Plan.config.at(Plan.confs.at(Plan.conf.dirs([path]), world), world, path), Rules.on.at(path, fs)),
    Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
      Rules.on.at(path, fs)),
    pub.grade_at(Plan.confs.at(Plan.conf.dirs([path]), world), world, path, fs),
    Equal.cong(Config.Config, List<&2, F.Graded>, c => Rules.graded(c, Rules.on.at(path, fs)),
      Plan.config.at(Plan.confs.at(Plan.conf.dirs([path]), world), world, path),
      Plan.conf.near(world, Config.dir_of(path)),
      pub.find_head(Config.dir_of(path),
        Plan.confs.at(Plan.uniq([], [Config.dir_of(path)]), world), world)))

# the graded per-file findings of a source: the LSP's, graded by the
# bolt.bend candidates it reads, are the CLI's for `bolt <path>`
law pub.gs:
  for +world: W.World
  for +path: String
  for +text: String
  {Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)), Rules.all(path, text))
    == Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world,
      Plan.per_file(Plan.srcs_of([Plan.Got{path, Some{text}}])))
    : List<&2, F.Graded>}

# a run of one file gives it its role by name: a LAWS.bend or PROOF.bend
# keeps it, and any other file is reached by no law, so it is neither
law pub.role_one:
  for +named: Role.Role
  for +nn: String
  for deps: List<&2, String>
  for +entry: Bool
  {Role.role.of(named, Role.of.norm(Role.marks.of([Role.Fact{nn, deps, named, entry}],
      Role.reach([Role.Fact{nn, deps, named, entry}], Role.roots([Role.Fact{nn, deps, named, entry}])),
      Role.reach([Role.Fact{nn, deps, named, entry}], Role.lawful([Role.Fact{nn, deps, named, entry}])),
      Role.reach([Role.Fact{nn, deps, named, entry}], Role.code([Role.Fact{nn, deps, named, entry}],
        Role.reach([Role.Fact{nn, deps, named, entry}], Role.roots([Role.Fact{nn, deps, named, entry}]))))), nn))
    == named : Role.Role}

def pub.role_one(named, _nn, _deps, _entry):
  match named:
    case Role.Plain{}:
      {==}
    case Role.Laws{}:
      {==}
    case Role.Proof{}:
      {==}

def pub.gs(world, path, text):
  +s = Src.of(path, text)
  +r = Equal.cong(Role.Role, List<&2, F.Finding>, z => List.append(&2, F.Finding, Rules.on.role(z, s), []),
    Role.of(Role.marks([s]), path), Role.of_path(path),
    pub.role_one(Role.of_path(path), Imports.norm(path),
      Imports.targets(Outline.of_tokens(text, Lex.tokens(text)), Imports.norm(path)),
      String.eq(Paths.base(path), "main.bend")))
  a = Equal.sym(List<&2, F.Finding>, Plan.per_file(Plan.srcs_of([Plan.Got{path, Some{text}}])), Rules.all(path, text),
    Equal.trans(List<&2, F.Finding>, Plan.per_file(Plan.srcs_of([Plan.Got{path, Some{text}}])),
      List.append(&2, F.Finding, Rules.all(path, text), []), Rules.all(path, text), r,
      pub.app_nil(F.Finding, Rules.all(path, text))))
  %a : {Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
      Rules.all(path, text))
    == Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world, _)
    : List<&2, F.Graded>}
  Equal.sym(List<&2, F.Graded>,
    Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world, Rules.all(path, text)),
    Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
      Rules.all(path, text)),
    pub.grade_near(world, path, Rules.on.rules(Src.of(path, text))))

# the `noqa` findings of the LSP's lint, graded by the config nearest the
# path, are graded alike by the CLI
law pub.noqa_near:
  for +world: W.World
  for +path: String
  for +text: String
  for +gs: List<&2, F.Graded>
  {Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
      Plan.noqa([Noqa.file(path, Lex.tokens(text))], False{}, gs))
    == Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world,
      Plan.noqa([Noqa.file(path, Lex.tokens(text))], False{}, gs))
    : List<&2, F.Graded>}

def pub.noqa_near(world, path, text, gs):
  a = Equal.sym(List<&2, F.Finding>,
    List.append(&2, F.Finding, Rules.on.at(path, NoqaRule.check(Noqa.marks(Lex.tokens(text)), False{}, path, gs)), []),
    Rules.on.at(path, NoqaRule.check(Noqa.marks(Lex.tokens(text)), False{}, path, gs)),
    pub.app_nil(F.Finding, Rules.on.at(path, NoqaRule.check(Noqa.marks(Lex.tokens(text)), False{}, path, gs))))
  %a : {Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)), _)
    == Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world, _)
    : List<&2, F.Graded>}
  Equal.sym(List<&2, F.Graded>,
    Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world,
      Rules.on.at(path, NoqaRule.check(Noqa.marks(Lex.tokens(text)), False{}, path, gs))),
    Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
      Rules.on.at(path, NoqaRule.check(Noqa.marks(Lex.tokens(text)), False{}, path, gs))),
    pub.grade_near(world, path, NoqaRule.check(Noqa.marks(Lex.tokens(text)), False{}, path, gs)))

# the LSP's lint and the CLI's per-file findings for a source (bb False) or
# a bolt.bend (bb True)
law pub.cli.case:
  for bb: Bool
  for +world: W.World
  for +path: String
  for +text: String
  for hc: {Plan.is_config(path) == bb : Bool}
  for ht: {W.text(world, path) == Some{text} : Maybe<&2, String>}
  {Server.pub.lint(path, text, Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world))
    == Plan.after(Noqa.of_srcs(Plan.srcs_of(Plan.gots(Bool.pick(List<&2, String>, bb, [], [path]), world))), False{},
      Plan.grade(Plan.confs.at(Plan.conf.dirs(Bool.pick(List<&2, String>, bb, [], [path])), world), world,
        Plan.per_file(Plan.srcs_of(Plan.gots(Bool.pick(List<&2, String>, bb, [], [path]), world)))),
      fs => Plan.grade(Plan.confs.at(Plan.conf.dirs(Bool.pick(List<&2, String>, bb, [], [path])), world), world, fs))
    : List<&2, F.Graded>}

def pub.cli.case(bb, world, path, text, hc, ht):
  match bb:
    case True{}:
      e = Equal.sym(Bool, Plan.is_config(path), True{}, hc)
      %e : {Bool.pick(List<&2, F.Graded>, _, [],
          Plan.after([Noqa.file(path, Lex.tokens(text))], False{},
            Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
              Rules.all(path, text)),
            fs => Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)), fs)))
        == [] : List<&2, F.Graded>}
      {==}
    case False{}:
      e = Equal.sym(Bool, Plan.is_config(path), False{}, hc)
      %e : {Bool.pick(List<&2, F.Graded>, _, [],
          Plan.after([Noqa.file(path, Lex.tokens(text))], False{},
            Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
              Rules.all(path, text)),
            fs => Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)), fs)))
        == Plan.after(Noqa.of_srcs(Plan.srcs_of(Plan.gots([path], world))), False{},
          Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world,
            Plan.per_file(Plan.srcs_of(Plan.gots([path], world)))),
          fs => Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world, fs))
        : List<&2, F.Graded>}
      t = Equal.sym(Maybe<&2, String>, W.text(world, path), Some{text}, ht)
      %t : {Plan.after([Noqa.file(path, Lex.tokens(text))], False{},
            Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
              Rules.all(path, text)),
            fs => Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)), fs))
        == Plan.after(Noqa.of_srcs(Plan.srcs_of([Plan.Got{path, _}])), False{},
          Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world,
            Plan.per_file(Plan.srcs_of([Plan.Got{path, _}]))),
          fs => Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world, fs))
        : List<&2, F.Graded>}
      g = pub.gs(world, path, text)
      %g : {Plan.after([Noqa.file(path, Lex.tokens(text))], False{},
            Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
              Rules.all(path, text)),
            fs => Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)), fs))
        == Plan.after([Noqa.file(path, Lex.tokens(text))], False{}, _,
          fs => Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world, fs))
        : List<&2, F.Graded>}
      Equal.cong(List<&2, F.Graded>, List<&2, F.Graded>,
        rr => List.append(&2, F.Graded,
          Noqa.keep([Noqa.file(path, Lex.tokens(text))],
            Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
              Rules.all(path, text))), rr),
        Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
          Plan.noqa([Noqa.file(path, Lex.tokens(text))], False{},
            Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
              Rules.all(path, text)))),
        Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world,
          Plan.noqa([Noqa.file(path, Lex.tokens(text))], False{},
            Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
              Rules.all(path, text)))),
        pub.noqa_near(world, path, text,
          Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
            Rules.all(path, text))))

def Laws.lint_is_cli(world, path, text, h, ht):
  n = Equal.sym(List<&2, String>, Plan.inputs(world), Plan.sources([path]), pub.cli.named(world, path, h))
  %n : {Server.pub.lint(path, text, Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world))
    == Plan.after(Noqa.of_srcs(Plan.srcs_of(Plan.gots(_, world))), False{},
      Plan.grade(Plan.confs.at(Plan.conf.dirs(_), world), world, Plan.per_file(Plan.srcs_of(Plan.gots(_, world)))),
      fs => Plan.grade(Plan.confs.at(Plan.conf.dirs(_), world), world, fs))
    : List<&2, F.Graded>}
  pub.cli.case(Plan.is_config(path), world, path, text, {==}, ht)
