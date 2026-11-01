# Diagnostics for an open document equal the CLI's per-file findings for that
# file and text under the same bolt.bend, less what its noqa comments silence
# (laws/NoqaSilencesNamedFindings.bend), then `noqa`'s findings on them, which judge no project rule's
# code.
import Base
import ../src/lsp/server.bend as Server
import ../src/finding.bend as F
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ../src/noqa.bend as Noqa

# the CLI's per-file findings in a run, graded the CLI's way: each source's
# per-file rules, each finding at the level the bolt.bend nearest its path
# gives it (laws/ScopeRulesSeeTheirInputs.bend and laws/OutputOrderIsFixed.bend place these among the run's
# findings), less what the sources' noqa comments silence, then the `noqa`
# rule's findings as the CLI reports them, judging no project rule's code
def pub.cli(+world: W.World) -> List<&2, F.Graded>:
  +ss = Plan.srcs_of(Plan.gots(Plan.inputs(world), world))
  +cs = Plan.confs(world)
  Plan.after(Noqa.of_srcs(ss), False{}, Plan.grade(cs, world, Plan.per_file.run(W.paths.of(world), ss)),
    fs => Plan.grade(cs, world, fs))

# LAW: an open document's lint is the CLI's: over every file system and
# working directory (a World), for a document at a path whose text the CLI
# reads as the editor shows it, the LSP's findings on that text, graded by
# the bolt.bend candidates it reads from that same file system and
# directory, are exactly what `bolt <path>` grades as that file's per-file
# findings, the same noqa comments silencing the same findings and `noqa`
# reporting what the CLI reports but for a project rule's code, which the
# editor cannot judge (none for a bolt.bend, which neither lints)
law lint_is_cli:
  for +world: W.World
  for +path: String
  for +text: String
  for h: {W.paths.of(world) == [path] : List<&2, String>}
  for ht: {W.text(world, path) == Some{text} : Maybe<&2, String>}
  {Server.pub.lint(path, text, Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)) == pub.cli(world)
    : List<&2, F.Graded>}
