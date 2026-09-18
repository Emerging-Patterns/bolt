# bolt/rules: each rule on a small source, and the whole set on a clean one
import Base
import ../rules.bend as Rules
import ../rules/doc.bend as Doc
import ../rules/unused.bend as Unused
import ../rules/shadow.bend as Shadow
import ../rules/hole.bend as Hole
import ../rules/space.bend as Space
import ../rules/pick.bend as Pick
import ../rules/law.bend as Law
import ../file.bend as File
import ../config.bend as Config
import ../finding.bend as F
import ../../core/check/kit.bend as Check
import ../../core/check/print.bend as Report

def lines(fs: List<&2, F.Finding>) -> String:
  String.join(F.show_all(fs), "; ")

def undocumented() -> String:
  String.join([
    "import Base",
    "",
    "# adds one",
    "def inc(n: U32) -> U32:",
    "  (n + 1 : U32)",
    "",
    "def dec(n: U32) -> U32:",
    "  (n - 1 : U32)",
    "",
    "def dec.go(n: U32) -> U32:",
    "  n",
    "",
    "type T is Data:",
    "  K{}",
    "",
    "law l:",
    "  {1 == 1 : U32}",
    "",
    "def main() -> U32:",
    "  0"], "\n")

def unused() -> String:
  String.join([
    "def f(x: U32, -A: Type, _y: U32, z: U32) -> U32:",
    "  a = 1",
    "  b = 2",
    "  g = q => q",
    "  h = w => 3",
    "  (a + z : U32)",
    "",
    "def g(t: T) -> U32:",
    "  match t:",
    "    case K{p, r}:",
    "      p",
    "",
    "def ext(path: String) -> IO(String):",
    "  import \"./x.c\"",
    "",
    "law l:",
    "  for ih : U32",
    "  {1 == 1 : U32}"], "\n")

def shadowed() -> String:
  String.join([
    "def a(k: U32) -> U32:",
    "  k = 1",
    "  k",
    "",
    "def k(n: U32) -> U32:",
    "  n",
    "",
    "def b(k: U32) -> U32:",
    "  k = 2",
    "  k",
    "",
    "def c(t: T) -> U32:",
    "  match t:",
    "    case K{k}:",
    "      k"], "\n")

def holes() -> String:
  "def f() -> U32:\n  ?TODO\n"

def spaced() -> String:
  "def f() -> U32:  \n\t1\n# " ++ String.repeat("x", 120n) ++ "\ns = \"" ++ String.repeat("y", 200n) ++ "\"\n#|" ++ String.repeat("z", 200n) ++ "\n"

def picked() -> String:
  String.join([
    "def go(xs: List<&2, U32>) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      Bool.pick(U32, U32.is_eq(h, 0), go(t), (h + go(t) : U32))",
    "",
    "def ok(xs: List<&2, U32>) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      +more = ok(t)",
    "      Bool.pick(U32, U32.is_eq(h, 0), more, (h + more : U32))",
    "",
    "def nested(xs: List<&2, U32>) -> U32:",
    "  match xs:",
    "    case Con{h, t}:",
    "      Bool.pick(U32, True{}, nested(t), Bool.pick(U32, False{}, 1, nested(t)))",
    "    case Nil{}:",
    "      0"], "\n")

# a project p under law: m.bend is imported by its laws and half named, o.bend
# is reached by no law, io.bend touches IO, the test is a test; q is another
# project with no laws at all
def lawful() -> List<&2, File.File>:
  [File.File{"./p/LAWS.bend", "import ./m.bend as M\n\n# LAW: f is the identity\nlaw f_id:\n  for a: U32\n  {M.f(a) == a : U32}\n"},
   File.File{"./p/m.bend", "def f(a: U32) -> U32:\n  a\n\ndef g(a: U32) -> U32:\n  a\n\ndef g.go(a: U32) -> U32:\n  a\n\ntype T is Data:\n  K{}\n\ndef main() -> U32:\n  0\n"},
   File.File{"./p/o.bend", "type O is Data:\n  K{}\n\ndef h(a: U32) -> U32:\n  a\n"},
   File.File{"./p/io.bend", "def say() -> IO(Unit):\n  IO.print(\"x\")\n\ndef k(a: U32) -> U32:\n  a\n"},
   File.File{"./p/tests/t.bend", "def z(a: U32) -> U32:\n  a\n"},
   File.File{"./q/n.bend", "def y(a: U32) -> U32:\n  a\n"}]

# a bolt.bend: a group set, a rule set apart, a typo
def config() -> String:
  String.join([
    "import Base",
    "",
    "# comments and width are errors",
    "def style() -> String:",
    "  \"error\"",
    "",
    "# but width is advice",
    "def space() -> String:",
    "  \"warn\"",
    "",
    "# a slip is silent",
    "def unused() -> String:",
    "  \"off\"",
    "",
    "# a typo",
    "def laws() -> String:",
    "  \"wran\""], "\n")

# graded findings as lines
def shown(gs: List<&2, F.Graded>) -> List<&2, String>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{g, rest}:
      F.show_graded(g) <> shown(rest)

# the level word of a rule under the config
def at(cfg: Config.Config, +rule: String) -> String:
  Config.show(Config.level(cfg, Rules.group(rule), rule))

# the levels of every rule, `rule=level`
def levels(+cfg: Config.Config, rules: List<&2, String>) -> String:
  match rules:
    case Nil{}:
      ""
    case Con{+r, rest}:
      r ++ "=" ++ at(cfg, r) ++ " " ++ levels(cfg, rest)

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str(~Report.new(), "doc: undotted defs, types and laws, not helpers or main",
      lines(Doc.check("a.bend", undocumented())),
      "a.bend:7:1: doc: def dec has no comment above it; a.bend:13:1: doc: type T has no comment above it; a.bend:16:1: doc: law l has no comment above it")
    Check.eq_str(~Report.new(), "doc: a proof file is exempt", lines(Doc.check("x/PROOF.bend", undocumented())), "")
    Check.eq_str(~Report.new(), "doc: a test is exempt", lines(Doc.check("x/tests/a.bend", undocumented())), "")
    Check.eq_str(~Report.new(), "unused: lets, lambdas and parameters; not erased, _, patterns, foreign or for",
      lines(Unused.check("a.bend", unused())),
      "a.bend:1:7: unused: parameter x is never used; a.bend:3:3: unused: local b is never used; a.bend:4:3: unused: local g is never used; a.bend:5:3: unused: local h is never used; a.bend:5:7: unused: local w is never used")
    Check.eq_str(~Report.new(), "shadow: a let or a pattern named like a def above",
      lines(Shadow.check("a.bend", shadowed())),
      "a.bend:9:3: shadow: k is a def above; imported, this binder would read as it; a.bend:14:12: shadow: k is a def above; imported, this binder would read as it")
    Check.eq_str(~Report.new(), "hole: a ?TODO", lines(Hole.check("a.bend", holes())), "a.bend:2:3: hole: a ?TODO is left here")
    Check.eq_str(~Report.new(), "hole: LAWS.bend is exempt", lines(Hole.check("LAWS.bend", holes())), "")
    Check.eq_str(~Report.new(), "space: trailing, tab, width; a string is two wide; #| lines are data",
      lines(Space.check("a.bend", spaced())),
      "a.bend:1:17: space: trailing whitespace; a.bend:2:1: space: a tab; indent with spaces; a.bend:3:121: space: over 120 characters wide")
    Check.eq_str(~Report.new(), "pick: a def in both branches, at any depth; not when bound above",
      lines(Pick.check("a.bend", picked())),
      "a.bend:6:7: pick: go recurses in both branches; Bool.pick runs both; a.bend:19:7: pick: nested recurses in both branches; Bool.pick runs both")
    Check.eq_str(~Report.new(), "law: pure defs under a LAWS.bend that no law names; types by module",
      lines(Law.check(lawful())),
      "./p/m.bend:4:1: law: def g is named by no law; ./p/o.bend:1:1: law: type O: no law reaches this module; ./p/o.bend:4:1: law: def h is named by no law")
    Check.eq_str(~Report.new(), "law: a project without laws is not under it", lines(Law.check([File.File{"./q/n.bend", "def y() -> U32:\n  1\n"}])), "")
    Check.eq_str(~Report.new(), "config: defaults are correctness at error, the rest at warn",
      levels(Config.none(), ["shadow", "hole", "pick", "unused", "doc", "space", "law"]),
      "shadow=error hole=error pick=error unused=warning doc=warning space=warning law=warning ")
    Check.eq_str(~Report.new(), "config: a group sets its rules, a rule set apart wins, a typo is an error",
      levels(Config.parse(config()), ["doc", "space", "unused", "law", "shadow"]),
      "doc=error space=warning unused=off law=error shadow=error ")
    Check.eq_str(~Report.new(), "config: the bolt.bend candidates, nearest first, up to the top",
      String.join(Config.candidates(64n, Config.dir_of("a/b/c.bend")), " "), "a/b/bolt.bend a/bolt.bend bolt.bend")
    Check.eq_str(~Report.new(), "config: an absolute path stops at /",
      String.join(Config.candidates(64n, Config.dir_of("/w/x.bend")), " "), "/w/bolt.bend /bolt.bend")
    Check.eq_str(~Report.new(), "config: the nearest file that exists is the config",
      at(Config.nearest([None{}, Some{config()}, Some{"def style() -> String:\n  \"off\"\n"}]), "doc"), "error")
    Check.eq_str(~Report.new(), "graded: findings at their levels, the off ones dropped",
      String.join(shown(Rules.graded(Config.parse(config()),
        List.append(&2, F.Finding, Doc.check("a.bend", undocumented()), Unused.check("a.bend", unused())))), "; "),
      "a.bend:7:1: error: doc: def dec has no comment above it; a.bend:13:1: error: doc: type T has no comment above it; a.bend:16:1: error: doc: law l has no comment above it")
    Check.eq_str(~Report.new(), "all rules on a clean file", lines(Rules.all("a.bend", "# one\ndef one() -> U32:\n  1\n")), "")

#|ok doc: undotted defs, types and laws, not helpers or main
#|ok doc: a proof file is exempt
#|ok doc: a test is exempt
#|ok unused: lets, lambdas and parameters; not erased, _, patterns, foreign or for
#|ok shadow: a let or a pattern named like a def above
#|ok hole: a ?TODO
#|ok hole: LAWS.bend is exempt
#|ok space: trailing, tab, width; a string is two wide; #| lines are data
#|ok pick: a def in both branches, at any depth; not when bound above
#|ok law: pure defs under a LAWS.bend that no law names; types by module
#|ok law: a project without laws is not under it
#|ok config: defaults are correctness at error, the rest at warn
#|ok config: a group sets its rules, a rule set apart wins, a typo is an error
#|ok config: the bolt.bend candidates, nearest first, up to the top
#|ok config: an absolute path stops at /
#|ok config: the nearest file that exists is the config
#|ok graded: findings at their levels, the off ones dropped
#|ok all rules on a clean file
