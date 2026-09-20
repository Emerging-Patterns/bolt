# bolt/rules, the project set: unsafe, foreign, fuel and closed, each on a
# source that fires, one that is quiet, and one its exemption covers
import Base
import ../src.bend as Src
import ../rules/laws/unsafe.bend as Unsafe
import ../rules/correctness/foreign.bend as Foreign
import ../rules/suspicious/fuel.bend as Fuel
import ../rules/laws/closed.bend as Closed
import ../rules/imports.bend as Imports
import ../rules/digest.bend as Digest
import ../finding.bend as F
import ../../core/check/kit.bend as Check
import ../../core/check/print.bend as Report

def lines(fs: List<&2, F.Finding>) -> String:
  String.join(F.show_all(fs), "; ")

# a proof p whose laws import m.bend, which imports ../lib/u.bend and its
# @unsafe spin (two-line form in w.bend, which only m.bend reaches too); o.bend
# has an @unsafe def no law reaches; q.bend is imported but never read
def reached() -> List<&2, Src.Src>:
  [Src.of("./p/PROOF.bend", "import ./LAWS.bend as Laws\n\n# the proof\ndef f_id(a):\n  {==}\n"),
   Src.of("./p/LAWS.bend", "import ./m.bend as M\nimport ./q.bend as Q\n\n# LAW: f\nlaw f_id:\n  for a: U32\n  {M.f(a) == a : U32}\n"),
   Src.of("./p/m.bend", "import ../lib/u.bend as U\nimport ./w.bend as W\n\n# f\ndef f(a: U32) -> U32:\n  U.spin(a)\n"),
   Src.of("./lib/u.bend", "# spins\n@unsafe def spin(a: U32) -> U32:\n  spin(a)\n"),
   Src.of("./p/w.bend", "# walks\n@unsafe\ndef walk(a: U32) -> U32:\n  walk(a)\n"),
   Src.of("./p/o.bend", "# loose\n@unsafe def loose(a: U32) -> U32:\n  loose(a)\n")]

# the same project with its laws off the unsafe code
def unreached() -> List<&2, Src.Src>:
  [Src.of("./p/LAWS.bend", "import ./n.bend as N\n\n# LAW: g\nlaw g_id:\n  for a: U32\n  {N.g(a) == a : U32}\n"),
   Src.of("./p/n.bend", "# g\ndef g(a: U32) -> U32:\n  a\n"),
   Src.of("./p/o.bend", "# loose\n@unsafe def loose(a: U32) -> U32:\n  loose(a)\n")]

# an @unsafe def in a module no law file imports, in a project with no laws
def lawless() -> List<&2, Src.Src>:
  [Src.of("./r/main.bend", "import ./u.bend as U\n\n# main\ndef main() -> U32:\n  U.spin(1)\n"),
   Src.of("./r/u.bend", "# spins\n@unsafe def spin(a: U32) -> U32:\n  spin(a)\n")]

def foreigns() -> String:
  String.join([
    "# only C",
    "def a.b(x: U32) -> IO(U32):",
    "  import \"./b.c\"",
    "",
    "# only JS",
    "def a.c(x: U32) -> IO(U32):",
    "  import \"./c.js\"",
    "",
    "# both",
    "def a.d(x: U32) -> IO(U32):",
    "  import \"./d.c\"",
    "  import \"./d.js\"",
    "",
    "# not foreign",
    "def e(x: U32) -> U32:",
    "  x"], "\n")

def native() -> String:
  "# lanes: native\n# a native test\n\n# only C\ndef a.b(x: U32) -> IO(U32):\n  import \"./b.c\"\n\n# only JS\ndef a.c(x: U32) -> IO(U32):\n  import \"./c.js\"\n"

def fuels() -> String:
  String.join([
    "# fuel first",
    "def walk(fuel: Nat, xs: List<&2, U32>) -> U32:",
    "  match fuel:",
    "    case 0n:",
    "      0",
    "    case 1n+f:",
    "      walk(f, xs)",
    "",
    "# budget after a template",
    "def spend(~A: Type, x: A, budget: Nat) -> A:",
    "  x",
    "",
    "# fuel_max, with a fixed fuel from its own step",
    "def go(fuel_max: Nat) -> U32:",
    "  go(3n)",
    "",
    "# callers",
    "def main() -> U32:",
    "  +a = walk(1000n, [])",
    "  +b = spend(~U32, 1, 10n)",
    "  +c = walk(Nat.mul(2n, 3n), [])",
    "  +d = spend(~U32, 1n, U32.to_nat(5))",
    "  +e = M.walk(4n, [])",
    "  +g = other(7n)",
    "  a"], "\n")

def laws() -> String:
  String.join([
    "import ./m.bend as M",
    "",
    "# LAW: closed",
    "law sanity:",
    "  {U32.add(2, 3) == 5 : U32}",
    "",
    "# LAW: one line",
    "law short: {M.f(0) == 0 : U32}",
    "",
    "# LAW: for all",
    "law f_id:",
    "  for a: U32",
    "  {M.f(a) == a : U32}",
    "",
    "# LAW: a witness",
    "law has:",
    "  exs b: U32",
    "  {M.f(b) == 0 : U32}"], "\n")

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str(~Report.new(), "imports: a closure over relative imports, .. included, unread ones dropped",
      String.join(Imports.closure(reached(), "./p/PROOF.bend"), " "),
      "p/PROOF.bend p/LAWS.bend p/m.bend lib/u.bend p/w.bend")
    Check.eq_str(~Report.new(), "unsafe: an @unsafe def a law file reaches, both forms, once",
      lines(Unsafe.check(Digest.all(reached()))),
      "./lib/u.bend:2:1: unsafe: @unsafe def spin is reached from ./p/PROOF.bend: the checker only warns there and exits 0; recurse on a shrinking argument or fuel; ./p/w.bend:2:1: unsafe: @unsafe def walk is reached from ./p/PROOF.bend: the checker only warns there and exits 0; recurse on a shrinking argument or fuel")
    Check.eq_str(~Report.new(), "unsafe: quiet when no law file reaches it", lines(Unsafe.check(Digest.all(unreached()))), "")
    Check.eq_str(~Report.new(), "unsafe: a project without law files is exempt", lines(Unsafe.check(Digest.all(lawless()))), "")
    Check.eq_str(~Report.new(), "foreign: a .c body without .js, and the reverse",
      lines(Foreign.check(Src.of("a.bend", foreigns()))),
      "a.bend:2:1: foreign: foreign def a.b has a .c body but no .js body: the JS lane cannot run it; a.bend:6:1: foreign: foreign def a.c has a .js body but no .c body: a native build cannot run it")
    Check.eq_str(~Report.new(), "foreign: quiet on both bodies and on a plain def",
      lines(Foreign.check(Src.of("a.bend", "# both\ndef a.d(x: U32) -> IO(U32):\n  import \"./d.c\"\n  import \"./d.js\"\n"))), "")
    Check.eq_str(~Report.new(), "foreign: a # lanes: native file needs no .js",
      lines(Foreign.check(Src.of("a.bend", native()))),
      "a.bend:9:1: foreign: foreign def a.c has a .js body but no .c body: a native build cannot run it")
    Check.eq_str(~Report.new(), "fuel: a Nat literal in a fuel parameter of a def of the file",
      lines(Fuel.check(Src.of("a.bend", fuels()))),
      "a.bend:19:13: fuel: a fixed fuel of 1000n: input past it is cut short silently; derive the fuel from the input's size; a.bend:20:23: fuel: a fixed fuel of 10n: input past it is cut short silently; derive the fuel from the input's size")
    Check.eq_str(~Report.new(), "fuel: quiet on a derived fuel",
      lines(Fuel.check(Src.of("a.bend", "# fuel\ndef walk(fuel: Nat) -> U32:\n  0\n\n# n\ndef main() -> U32:\n  walk(Nat.add(2n, 1n))\n"))), "")
    Check.eq_str(~Report.new(), "fuel: a def's own call is exempt",
      lines(Fuel.check(Src.of("a.bend", "# gas\ndef spin(gas: Nat) -> U32:\n  spin(2n)\n"))), "")
    Check.eq_str(~Report.new(), "closed: a law with no for or exs, in a LAWS.bend",
      lines(Closed.check(Src.of("p/LAWS.bend", laws()))),
      "p/LAWS.bend:4:1: closed: law sanity has no for: it is one computed case, not a claim about every input; p/LAWS.bend:8:1: closed: law short has no for: it is one computed case, not a claim about every input")
    Check.eq_str(~Report.new(), "closed: quiet on laws with for",
      lines(Closed.check(Src.of("p/LAWS.bend", "# LAW: f\nlaw f_id:\n  for a: U32\n  {M.f(a) == a : U32}\n"))), "")
    Check.eq_str(~Report.new(), "closed: a law outside a LAWS.bend is exempt", lines(Closed.check(Src.of("p/a.bend", laws()))), "")

#|ok imports: a closure over relative imports, .. included, unread ones dropped
#|ok unsafe: an @unsafe def a law file reaches, both forms, once
#|ok unsafe: quiet when no law file reaches it
#|ok unsafe: a project without law files is exempt
#|ok foreign: a .c body without .js, and the reverse
#|ok foreign: quiet on both bodies and on a plain def
#|ok foreign: a # lanes: native file needs no .js
#|ok fuel: a Nat literal in a fuel parameter of a def of the file
#|ok fuel: quiet on a derived fuel
#|ok fuel: a def's own call is exempt
#|ok closed: a law with no for or exs, in a LAWS.bend
#|ok closed: quiet on laws with for
#|ok closed: a law outside a LAWS.bend is exempt
