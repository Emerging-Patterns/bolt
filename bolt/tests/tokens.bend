# bolt/tokens: the put, escape, nat, strings, twice and arms rules, each on a
# small source that fires, one that stays quiet, and its exemption
import Base
import ../src.bend as Src
import ../rules/correctness/put.bend as Put
import ../rules/correctness/escape.bend as Escape
import ../rules/suspicious/nat.bend as NatLit
import ../rules/correctness/strings.bend as Strings
import ../rules/correctness/twice.bend as Twice
import ../rules/correctness/arms.bend as Arms
import ../finding.bend as F
import ../../core/check/kit.bend as Check
import ../../core/check/print.bend as Report

def lines(fs: List<&2, F.Finding>) -> String:
  String.join(F.show_all(fs), "; ")

def put_src() -> String:
  String.join([
    "def f(m: Map<U32>, k: String) -> Map<U32>:",
    "  Map.put(U32, U32, m, k, 1)",
    "",
    "# Map.put( in a comment",
    "def g(m: Map<U32>, k: String) -> Map<U32>:",
    "  Map.set(U32, U32, Map.put.bit(m), \"Map.put(\", 1)"], "\n")

def put_own() -> String:
  String.join([
    "def Map.put(a, V, m, key, x):",
    "  Map.put(a, V, m, key, x)"], "\n")

def escape_src() -> String:
  String.join([
    "def main() -> IO(Unit):",
    "  IO.print(\"a\\033[1m\" ++ \"\\\\033\" ++ \"\\u{1B}\" ++ \"a\\0b\" ++ \"\\\"\\012\")",
    "",
    "# \"\\033\" in a comment",
    "def c() -> Char:",
    "  '\\07'",
    "",
    "def d() -> String:",
    "  \"\\09\""], "\n")

def nat_src() -> String:
  String.join([
    "def f() -> Nat:",
    "  g(999n, 1000n, 100000, 4294967295n, 12n)",
    "",
    "# 2000n in a comment",
    "def h() -> String:",
    "  \"5000n\""], "\n")

def strings_src() -> String:
  String.join([
    "def kind(v: String) -> U32:",
    "  match v:",
    "    case \"response.created\":",
    "      1",
    "    case \"response.output_item.added\":",
    "      2",
    "    case \"response.reasoning_summary_text.delta\":",
    "      3",
    "    case _:",
    "      0",
    "",
    "def verb(v: String) -> U32:",
    "  match v:",
    "    case \"get\":",
    "      1",
    "    case \"post\":",
    "      2",
    "    case \"put\":",
    "      3",
    "    case \"delete\":",
    "      4",
    "    case \"patch\":",
    "      5",
    "    case \"head\":",
    "      6",
    "    case \"options\":",
    "      7",
    "    case \"connect\":",
    "      8",
    "    case \"trace\":",
    "      9",
    "    case _:",
    "      0",
    "",
    "def code(n: U32) -> U32:",
    "  match n:",
    "    case 1000000001:",
    "      1",
    "    case 1000000002:",
    "      2",
    "    case 1000000003:",
    "      3",
    "    case 1000000004:",
    "      4",
    "    case 1000000005:",
    "      5",
    "    case 1000000006:",
    "      6",
    "    case 1000000007:",
    "      7",
    "    case _:",
    "      0",
    "",
    "def two(a: String, b: String) -> U32:",
    "  match a:",
    "    case \"response.created.first\":",
    "      match b:",
    "        case \"response.created.second\":",
    "          1",
    "        case _:",
    "          2",
    "    case \"response.created.third\":",
    "      3",
    "    case _:",
    "      0"], "\n")

def twice_src() -> String:
  String.join([
    "def search(bytes: List<&2, U32>, offset: Nat) -> Maybe<&2, Nat>:",
    "  match bytes:",
    "    case 10 <> 10 <> _:",
    "      Some{offset}",
    "    case 10 <> 11 <> 10 <> _:",
    "      Some{offset}",
    "    case _ <> 13 <> 13 <> _:",
    "      Some{offset}",
    "    case _ <> tail:",
    "      search(tail, offset)",
    "    case Nil{}:",
    "      None{}",
    "",
    "def chars(cs: List<&2, Char>) -> Bool:",
    "  match cs:",
    "    case Con{'a', Con{'a', t}}:",
    "      True{}",
    "    case Con{c, t}:",
    "      chars(t)",
    "    case Nil{}:",
    "      False{}",
    "",
    "def once(bytes: List<&2, U32>) -> Bool:",
    "  match bytes:",
    "    case 10 <> 10 <> _:",
    "      True{}",
    "    case other:",
    "      False{}"], "\n")

def arms_src() -> String:
  String.join([
    "def bad(x: Nat) -> Nat:",
    "  match x:",
    "    case 0n:",
    "      0n",
    "    case 1n+p:",
    "      1n",
    "    case 2n+p:",
    "      2n",
    "    case 3n:",
    "      3n",
    "",
    "def good(x: Nat) -> Nat:",
    "  match x:",
    "    case 0n:",
    "      0n",
    "    case 1n:",
    "      1n",
    "    case 3n+p:",
    "      2n",
    "    case 2n+q:",
    "      3n",
    "",
    "def succ(x: Nat) -> Nat:",
    "  match x:",
    "    case Zero{}:",
    "      0n",
    "    case Succ{p}:",
    "      1n",
    "    case 5n:",
    "      5n",
    "",
    "def two(x: Nat, y: Nat) -> Nat:",
    "  match x y:",
    "    case 1n+p m:",
    "      1n",
    "    case 2n+p m:",
    "      2n",
    "    case 0n m:",
    "      0n"], "\n")

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str(~Report.new(), "put: a Map.put( call; not Map.set, Map.put.bit, a string or a comment",
      lines(Put.check(Src.of("a.bend", put_src()))),
      "a.bend:2:3: put: Map.put never compares keys; a new key overwrites another entry: use Map.set")
    Check.eq_str(~Report.new(), "put: a file that defines Map.put is exempt", lines(Put.check(Src.of("a.bend", put_own()))), "")
    Check.eq_str(~Report.new(), "escape: \\0 then digits in a string or char; not \\\\0, \\0 alone, \\u{..} or a comment",
      lines(Escape.check(Src.of("a.bend", escape_src()))),
      String.join([
        "a.bend:2:14: escape: \\033 is NUL then \"33\", not octal: write \\u{1B}",
        "a.bend:2:62: escape: \\012 is NUL then \"12\", not octal: write \\u{A}",
        "a.bend:6:4: escape: \\07 is NUL then \"7\", not octal: write \\u{7}",
        "a.bend:9:4: escape: \\0 then digits is NUL and the digits, not octal: write \\u{..}"], "; "))
    Check.eq_str(~Report.new(), "nat: a Nat literal of 1000 or more; not 999n, a U32, a string or a comment",
      lines(NatLit.check(Src.of("a.bend", nat_src()))),
      String.join([
        "a.bend:2:11: nat: 1000n is 1000 unary cells; use U32 (or U32.to_nat at run time) for big counts",
        "a.bend:2:26: nat: 4294967295n is 4294967295 unary cells; use U32 (or U32.to_nat at run time) for big counts"],
        "; "))
    Check.eq_str(~Report.new(), "strings: a match over long string literals; not short ones, numbers, and a nested match apart",
      lines(Strings.check(Src.of("a.bend", strings_src()))),
      "a.bend:2:3: strings: a match over 3 string literals (79 characters) blows up compile time and memory; map the string to a sum type once (a lookup table)")
    Check.eq_str(~Report.new(), "twice: a list pattern opening with the same literal twice, in a recursive def only",
      lines(Twice.check(Src.of("a.bend", twice_src()))),
      String.join([
        "a.bend:3:16: twice: the same literal twice in one list pattern hangs the checker; match one element per step",
        "a.bend:16:23: twice: the same literal twice in one list pattern hangs the checker; match one element per step"],
        "; "))
    Check.eq_str(~Report.new(), "arms: a Nat arm under a wider n+p arm; not narrower first, and multi-scrutinee skipped",
      lines(Arms.check(Src.of("a.bend", arms_src()))),
      String.join([
        "a.bend:7:10: arms: unreachable: case 1n+p above already matches every 2n+..",
        "a.bend:9:10: arms: unreachable: case 1n+p above already matches 3n",
        "a.bend:29:10: arms: unreachable: case Succ{p} above already matches 5n"], "; "))

#|ok put: a Map.put( call; not Map.set, Map.put.bit, a string or a comment
#|ok put: a file that defines Map.put is exempt
#|ok escape: \0 then digits in a string or char; not \\0, \0 alone, \u{..} or a comment
#|ok nat: a Nat literal of 1000 or more; not 999n, a U32, a string or a comment
#|ok strings: a match over long string literals; not short ones, numbers, and a nested match apart
#|ok twice: a list pattern opening with the same literal twice, in a recursive def only
#|ok arms: a Nat arm under a wider n+p arm; not narrower first, and multi-scrutinee skipped
