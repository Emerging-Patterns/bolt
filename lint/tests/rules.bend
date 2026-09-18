# lint/rules: each rule on a small source, and the whole set on a clean one
import Base
import ../rules.bend as Rules
import ../rules/doc.bend as Doc
import ../rules/unused.bend as Unused
import ../rules/shadow.bend as Shadow
import ../rules/hole.bend as Hole
import ../rules/space.bend as Space
import ../finding.bend as F
import ../../wire/check/kit.bend as Check
import ../../wire/check/print.bend as Report

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
    Check.eq_str(~Report.new(), "all rules on a clean file", lines(Rules.all("a.bend", "# one\ndef one() -> U32:\n  1\n")), "")

#|ok doc: undotted defs, types and laws, not helpers or main
#|ok doc: a proof file is exempt
#|ok doc: a test is exempt
#|ok unused: lets, lambdas and parameters; not erased, _, patterns, foreign or for
#|ok shadow: a let or a pattern named like a def above
#|ok hole: a ?TODO
#|ok hole: LAWS.bend is exempt
#|ok space: trailing, tab, width; a string is two wide; #| lines are data
#|ok all rules on a clean file
