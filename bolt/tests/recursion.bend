# bolt/rules, the recursion set: pick (one branch), strict, tail, concat and
# index, each on a small source that fires, one that does not, and its
# exemptions
import Base
import ../src.bend as Src
import ../rules/correctness/pick.bend as Pick
import ../rules/suspicious/strict.bend as Strict
import ../rules/pedantic/tail.bend as Tail
import ../rules/suspicious/concat.bend as Concat
import ../rules/suspicious/index.bend as Index
import ../finding.bend as F
import ../../core/check/kit.bend as Check
import ../../core/check/print.bend as Report

def lines(fs: List<&2, F.Finding>) -> String:
  String.join(F.show_all(fs), "; ")

def picked() -> String:
  String.join([
    "def get(xs: List<&2, U32>, +i: U32) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      Bool.pick(U32, U32.is_eq(h, i), h, get(t, i))",
    "",
    "def nested(xs: List<&2, U32>) -> U32:",
    "  match xs:",
    "    case Con{h, t}:",
    "      Bool.pick(U32, True{}, 1, Bool.pick(U32, False{}, 2, nested(t)))",
    "    case Nil{}:",
    "      0",
    "",
    "def ok(xs: List<&2, U32>, +i: U32) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      +more = ok(t, i)",
    "      Bool.pick(U32, U32.is_eq(h, i), h, more)",
    "",
    "def two(xs: List<&2, U32>) -> U32:",
    "  match xs:",
    "    case Con{h, t}:",
    "      Bool.pick(U32, True{}, two(t), Bool.pick(U32, False{}, 1, two(t)))",
    "    case Nil{}:",
    "      0"], "\n")

def stricted() -> String:
  String.join([
    "def digits(s: List<&2, U32>) -> Bool:",
    "  match s:",
    "    case Nil{}:",
    "      True{}",
    "    case Con{h, t}:",
    "      U32.is_lt(h, 10) && digits(t)",
    "",
    "def has0(xs: List<&2, U32>) -> Bool:",
    "  match xs:",
    "    case Nil{}:",
    "      False{}",
    "    case Con{h, t}:",
    "      Bool.or(U32.is_eq(h, 0), has0(t))",
    "",
    "def all0(xs: List<&2, U32>) -> Bool:",
    "  match xs:",
    "    case Nil{}:",
    "      True{}",
    "    case Con{h, t}:",
    "      all0(t) || U32.is_eq(h, 0)",
    "",
    "def ok(xs: List<&2, U32>) -> Bool:",
    "  match xs:",
    "    case Nil{}:",
    "      True{}",
    "    case Con{h, t}:",
    "      +rest = ok(t)",
    "      U32.is_lt(h, 10) && rest",
    "",
    "def cond(xs: List<&2, U32>, +a: Bool) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      Bool.pick(U32, a && U32.is_eq(h, 0), (h + cond(t, a) : U32), cond(t, a))"], "\n")

def tailed() -> String:
  String.join([
    "def len(xs: List<&2, U32>) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      (1 + len(t) : U32)",
    "",
    "def sum(xs: List<&2, U32>, acc: U32) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      acc",
    "    case Con{h, t}:",
    "      sum(t, (acc + h : U32))",
    "",
    "def up(s: String) -> String:",
    "  match s:",
    "    case SNil{}:",
    "      SNil{}",
    "    case SCon{c, t}:",
    "      +rest = up(t)",
    "      SCon{Char.to_upper(c), rest}",
    "",
    "def size(n: Tree, +k: String) -> U32:",
    "  match n:",
    "    case Leaf{}:",
    "      1",
    "    case Node{l, r}:",
    "      (size(l, k) + size(r, k) : U32)",
    "",
    "def keep(xs: List<&2, U32>) -> List<&2, U32>:",
    "  match xs:",
    "    case Nil{}:",
    "      []",
    "    case Con{h, t}:",
    "      Bool.pick(List<&2, U32>, U32.is_eq(h, 0), keep(t), h <> keep(t))",
    "",
    "def count(-A: Data, xs: List<&2, A>) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      (1 + count(A, t) : U32)"], "\n")

def concatted() -> String:
  String.join([
    "def show(xs: List<&2, U32>, acc: String) -> String:",
    "  match xs:",
    "    case Nil{}:",
    "      acc ++ \".\"",
    "    case Con{h, t}:",
    "      show(t, acc ++ U32.show(h) ++ \",\")",
    "",
    "def grow(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:",
    "  match xs:",
    "    case Nil{}:",
    "      acc",
    "    case Con{h, t}:",
    "      grow(t, List.append(&2, U32, acc, [h]))",
    "",
    "def pre(xs: List<&2, U32>, acc: String) -> String:",
    "  match xs:",
    "    case Nil{}:",
    "      acc",
    "    case Con{h, t}:",
    "      pre(t, U32.show(h) ++ acc)",
    "",
    "def back(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:",
    "  match xs:",
    "    case Nil{}:",
    "      acc",
    "    case Con{h, t}:",
    "      back(t, List.append(&2, U32, [h], acc))"], "\n")

def indexed() -> String:
  String.join([
    "def total(i: Nat, +xs: List<&2, U32>) -> U32:",
    "  match i:",
    "    case 0n:",
    "      0",
    "    case 1n+p:",
    "      (Maybe.or(List.get(&2, U32, xs, p), 0) + total(p, xs) : U32)",
    "",
    "def scan(i: Nat, +s: String) -> U32:",
    "  match i:",
    "    case 0n:",
    "      0",
    "    case 1n+p:",
    "      +c = String.get(s, p)",
    "      scan(p, s)",
    "",
    "def third(xs: List<&2, U32>) -> Maybe<&2, U32>:",
    "  List.get(&2, U32, xs, 2n)",
    "",
    "def heads(xss: List<&2, List<&2, U32>>) -> List<&2, Maybe<&2, U32>>:",
    "  match xss:",
    "    case Nil{}:",
    "      []",
    "    case Con{h, t}:",
    "      List.get(&2, U32, h, 0n) <> heads(t)"], "\n")

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str(~Report.new(), "pick: one branch recurses; nested under a reported pick is quiet; bound above is not",
      lines(Pick.check(Src.of("a.bend", picked()))),
      "a.bend:6:7: pick: get recurses in one branch; Bool.pick runs it whatever the condition (no early exit); a.bend:11:7: pick: nested recurses in one branch; Bool.pick runs it whatever the condition (no early exit); a.bend:26:7: pick: two recurses in both branches; Bool.pick runs both")
    Check.eq_str(~Report.new(), "strict: a self-call under &&, || and Bool.or; not bound above, not in another argument",
      lines(Strict.check(Src.of("a.bend", stricted()))),
      "a.bend:6:27: strict: digits recurses inside Bool.and/or; both sides always run (no short-circuit); a.bend:13:32: strict: has0 recurses inside Bool.and/or; both sides always run (no short-circuit); a.bend:20:7: strict: all0 recurses inside Bool.and/or; both sides always run (no short-circuit)")
    Check.eq_str(~Report.new(), "strict: a proof file is exempt", lines(Strict.check(Src.of("x/PROOF.bend", stricted()))), "")
    Check.eq_str(~Report.new(), "tail: non-tail self-calls over a list or string; not tail calls, trees, or pick arguments",
      lines(Tail.check(Src.of("a.bend", tailed()))),
      "a.bend:6:12: tail: len is not a tail call here; on a long list/string the JS lane overflows its stack; carry an accumulator; a.bend:20:15: tail: up is not a tail call here; on a long list/string the JS lane overflows its stack; carry an accumulator; a.bend:42:12: tail: count is not a tail call here; on a long list/string the JS lane overflows its stack; carry an accumulator")
    Check.eq_str(~Report.new(), "tail: a law file is exempt", lines(Tail.check(Src.of("x/LAWS.bend", tailed()))), "")
    Check.eq_str(~Report.new(), "concat: ++ and List.append onto the carried parameter; not a prepend, not outside the self-call",
      lines(Concat.check(Src.of("a.bend", concatted()))),
      "a.bend:6:15: concat: acc grows by appending each step: quadratic; prepend and reverse once, or build with <>; a.bend:13:36: concat: acc grows by appending each step: quadratic; prepend and reverse once, or build with <>")
    Check.eq_str(~Report.new(), "index: List.get and String.get in a recursive def; not outside one, not at a literal index",
      lines(Index.check(Src.of("a.bend", indexed()))),
      "a.bend:6:17: index: List.get inside a recursive def walks the list each step: quadratic; walk the list itself; a.bend:13:12: index: String.get inside a recursive def walks the list each step: quadratic; walk the list itself")

#|ok pick: one branch recurses; nested under a reported pick is quiet; bound above is not
#|ok strict: a self-call under &&, || and Bool.or; not bound above, not in another argument
#|ok strict: a proof file is exempt
#|ok tail: non-tail self-calls over a list or string; not tail calls, trees, or pick arguments
#|ok tail: a law file is exempt
#|ok concat: ++ and List.append onto the carried parameter; not a prepend, not outside the self-call
#|ok index: List.get and String.get in a recursive def; not outside one, not at a literal index
