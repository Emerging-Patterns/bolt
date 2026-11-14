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
import ../src/noqa.bend as Noqa
import ../src/rules/style/noqa.bend as NoqaRule
import ../src/syntax/lex.bend as Lex
import ../laws/LspDiagnosticsMatchCli.bend as Laws
import ./lemmas/PublishComparisons.bend as M1
import ./lemmas/ReplyIndex.bend as M9

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
      Equal.cong(List<&2, A>, List<&2, A>, r => hd <> r, List.append(&2, A, tl, []), tl, pub.app_nil(A, tl))

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

def pub.grade.step(b, g, a, _b, e):
  match b:
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

# the CLI's config for a named file is the one nearest it, which the LSP reads
law pub.conf_near:
  for +world: W.World
  for +path: String
  {Plan.config.at(Plan.confs.at(Plan.conf.dirs([path]), world), world, path)
    == Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)) : Config.Config}

def pub.conf_near(world, path):
  pub.find_head(Config.dir_of(path), Plan.confs.at(Plan.uniq([], [Config.dir_of(path)]), world), world)

# the graded per-file findings of a source: the LSP's, graded by the
# bolt.bend candidates it reads, are the CLI's for `bolt <path>`
law pub.gs:
  for +world: W.World
  for +path: String
  for +text: String
  for +ms: List<&2, Role.Mark>
  {Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
      Rules.on.role(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
        Role.of(ms, path), Src.of(path, text)))
    == Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world,
      Plan.per_file.role(Plan.confs.at(Plan.conf.dirs([path]), world), world, ms,
        Plan.srcs_of([Plan.Got{path, Some{text}}])))
    : List<&2, F.Graded>}

def pub.gs(world, path, text, ms):
  k = Equal.sym(Config.Config, Plan.config.at(Plan.confs.at(Plan.conf.dirs([path]), world), world, path),
    Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)), pub.conf_near(world, path))
  %k : {Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
      Rules.on.role(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
        Role.of(ms, path), Src.of(path, text)))
    == Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world,
      List.append(&2, F.Finding, Rules.on.role(_, Role.of(ms, path), Src.of(path, text)), []))
    : List<&2, F.Graded>}
  a = Equal.sym(List<&2, F.Finding>, List.append(&2, F.Finding,
    Rules.on.role(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
        Role.of(ms, path), Src.of(path,
      text)), []),
    Rules.on.role(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
        Role.of(ms, path), Src.of(path, text)),
    pub.app_nil(F.Finding, Rules.on.role(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
        Role.of(ms, path), Src.of(path, text))))
  %a : {Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
      Rules.on.role(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
        Role.of(ms, path), Src.of(path, text)))
    == Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world, _)
    : List<&2, F.Graded>}
  Equal.sym(List<&2, F.Graded>,
    Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world,
      Rules.on.role(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
        Role.of(ms, path),
        Src.of(path, text))),
    Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
      Rules.on.role(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
        Role.of(ms, path), Src.of(path, text))),
    pub.grade_near(world, path, Rules.on.rules.role(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world),
      path), world)),
      Role.of(ms, path), Src.of(path, text))))

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

# the LSP's lint and the CLI's per-file findings for a source (b False) or
# a bolt.bend (b True)
law pub.cli.case:
  for b: Bool
  for +world: W.World
  for +path: String
  for +text: String
  for +ms: List<&2, Role.Mark>
  for hc: {Plan.is_config(path) == b : Bool}
  for ht: {W.text(world, path) == Some{text} : Maybe<&2, String>}
  {Server.pub.lint(path, text, Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world), ms)
    == Plan.after(Noqa.of_srcs(Plan.srcs_of(Plan.gots(Bool.pick(List<&2, String>, b, [], [path]), world))), False{},
      Plan.grade(Plan.confs.at(Plan.conf.dirs(Bool.pick(List<&2, String>, b, [], [path])), world), world,
        Plan.per_file.role(Plan.confs.at(Plan.conf.dirs(Bool.pick(List<&2, String>, b, [], [path])), world), world,
          ms, Plan.srcs_of(Plan.gots(Bool.pick(List<&2, String>, b, [], [path]), world)))),
      fs => Plan.grade(Plan.confs.at(Plan.conf.dirs(Bool.pick(List<&2, String>, b, [], [path])), world), world, fs))
    : List<&2, F.Graded>}

def pub.cli.case(b, world, path, text, ms, hc, ht):
  match b:
    case True{}:
      e = Equal.sym(Bool, Plan.is_config(path), True{}, hc)
      %e : {Bool.pick(List<&2, F.Graded>, _, [],
          Plan.after([Noqa.file(path, Lex.tokens(text))], False{},
            Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
              Rules.on.role(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
        Role.of(ms, path), Src.of(path, text))),
            fs => Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)), fs)))
        == [] : List<&2, F.Graded>}
      {==}
    case False{}:
      e = Equal.sym(Bool, Plan.is_config(path), False{}, hc)
      %e : {Bool.pick(List<&2, F.Graded>, _, [],
          Plan.after([Noqa.file(path, Lex.tokens(text))], False{},
            Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
              Rules.on.role(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
        Role.of(ms, path), Src.of(path, text))),
            fs => Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)), fs)))
        == Plan.after(Noqa.of_srcs(Plan.srcs_of(Plan.gots([path], world))), False{},
          Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world,
            Plan.per_file.role(Plan.confs.at(Plan.conf.dirs([path]), world), world, ms,
              Plan.srcs_of(Plan.gots([path], world)))),
          fs => Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world, fs))
        : List<&2, F.Graded>}
      t = Equal.sym(Maybe<&2, String>, W.text(world, path), Some{text}, ht)
      %t : {Plan.after([Noqa.file(path, Lex.tokens(text))], False{},
            Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
              Rules.on.role(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
        Role.of(ms, path), Src.of(path, text))),
            fs => Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)), fs))
        == Plan.after(Noqa.of_srcs(Plan.srcs_of([Plan.Got{path, _}])), False{},
          Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world,
            Plan.per_file.role(Plan.confs.at(Plan.conf.dirs([path]), world), world, ms,
              Plan.srcs_of([Plan.Got{path, _}]))),
          fs => Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world, fs))
        : List<&2, F.Graded>}
      g = pub.gs(world, path, text, ms)
      %g : {Plan.after([Noqa.file(path, Lex.tokens(text))], False{},
            Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
              Rules.on.role(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
        Role.of(ms, path), Src.of(path, text))),
            fs => Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)), fs))
        == Plan.after([Noqa.file(path, Lex.tokens(text))], False{}, _,
          fs => Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world, fs))
        : List<&2, F.Graded>}
      Equal.cong(List<&2, F.Graded>, List<&2, F.Graded>,
        r => List.append(&2, F.Graded,
          Noqa.keep([Noqa.file(path, Lex.tokens(text))],
            Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
              Rules.on.role(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
        Role.of(ms, path), Src.of(path, text)))), r),
        Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
          Plan.noqa([Noqa.file(path, Lex.tokens(text))], False{},
            Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
              Rules.on.role(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
        Role.of(ms, path), Src.of(path, text))))),
        Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world,
          Plan.noqa([Noqa.file(path, Lex.tokens(text))], False{},
            Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
              Rules.on.role(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
        Role.of(ms, path), Src.of(path, text))))),
        pub.noqa_near(world, path, text,
          Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
            Rules.on.role(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
        Role.of(ms, path), Src.of(path, text)))))

def Laws.lint_is_cli(world, path, text, h, ht):
  %Equal.sym(List<&2, Plan.Conf>, Plan.confs(world), Plan.confs.at(Plan.conf.dirs(Plan.inputs(world)), world),
    M9.ri.confs_spec(world)) :
    {Server.pub.lint(path, text, Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world),
      Server.pub.marks(world))
      == Plan.after(Noqa.of_srcs(Plan.srcs_of(Plan.gots(Plan.inputs(world), world))), False{},
        Plan.grade(_, world, Plan.per_file.role(_, world, Plan.marks.run(W.paths.of(world), world,
          Plan.srcs_of(Plan.gots(Plan.inputs(world), world))), Plan.srcs_of(Plan.gots(Plan.inputs(world), world)))),
        fs => Plan.grade(_, world, fs))
      : List<&2, F.Graded>}
  q = Equal.sym(List<&2, String>, W.paths.of(world), [path], h)
  %q : {Server.pub.lint(path, text, Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world),
      Server.pub.marks(world))
    == Plan.after(Noqa.of_srcs(Plan.srcs_of(Plan.gots(Plan.sources(Plan.files.named(_, world)), world))), False{},
      Plan.grade(Plan.confs.at(Plan.conf.dirs(Plan.sources(Plan.files.named(_, world))), world), world,
        Plan.per_file.role(Plan.confs.at(Plan.conf.dirs(Plan.sources(Plan.files.named(_, world))), world), world,
          Plan.marks.run(_, world, Plan.srcs_of(Plan.gots(Plan.sources(Plan.files.named(_, world)),
          world))), Plan.srcs_of(Plan.gots(Plan.sources(Plan.files.named(_, world)), world)))),
      fs => Plan.grade(Plan.confs.at(Plan.conf.dirs(Plan.sources(Plan.files.named(_, world))), world), world, fs))
    : List<&2, F.Graded>}
  pub.cli.case(Plan.is_config(path), world, path, text,
    Server.pub.marks(world), {==}, ht)
