# core: the laws. The human states them; PROOF.bend must prove them.
import Base
import ./monoid/service.bend as M
import ./monoid/sum.bend as Sum
import ./monoid/xor.bend as Xor
import ./leaf/service.bend as Leaf
import ./leaf/one.bend as One
import ./leaf/index.bend as Index
import ./par/fold.bend as Fold
import ./clock/service.bend as Clock
import ./clock/fake.bend as FakeClock
import ./clock/real.bend as RealClock
import ./log/service.bend as Log
import ./log/real.bend as RealLog
import ./log/quiet.bend as QuietLog
import ./check/service.bend as Rep
import ./check/kit.bend as Kit
import ./check/print.bend as Print
import ./check/quiet.bend as Quiet

# LAW: sum's unit is a right identity
law sum_unit_right:
  for a: U32
  {M.join(Sum.new(), a, M.unit(Sum.new())) == a : U32}

# LAW: xor's unit is a right identity
law xor_unit_right:
  for a: U32
  {M.join(Xor.new(), a, M.unit(Xor.new())) == a : U32}

# LAW: xor's join is associative
law xor_assoc:
  for a: U32
  for b: U32
  for c: U32
  {M.join(Xor.new(), M.join(Xor.new(), a, b), c)
    == M.join(Xor.new(), a, M.join(Xor.new(), b, c)) : U32}

# LAW: the one leaf is 1 at every index
law one_at:
  for i: U32
  {One.at(i) == 1 : U32}

# LAW: the index leaf is its index
law index_at:
  for i: U32
  {Index.at(i) == i : U32}

# LAW: the one leaf, as a service, is One.at
law one_leaf:
  for i: U32
  {Leaf.at(One.new(), i) == One.at(i) : U32}

# LAW: the index leaf, as a service, is Index.at
law index_leaf:
  for i: U32
  {Leaf.at(Index.new(), i) == Index.at(i) : U32}

# LAW: a fold over no levels is the leaf at i
law fold_leaf:
  for i: U32
  {Fold.fold(~Sum.new(), ~One.new(), 0n, i) == Leaf.at(One.new(), i) : U32}

# LAW: a fold over one level more joins the folds of its two halves
law fold_split:
  for p: Nat
  for i: U32
  {Fold.fold(~Sum.new(), ~One.new(), 1n+p, i)
    == M.join(Sum.new(), Fold.fold(~Sum.new(), ~One.new(), p, (i * 2 : U32)),
      Fold.fold(~Sum.new(), ~One.new(), p, (i * 2 + 1 : U32))) : U32}

# LAW: the fake clock is 42
law fake_clock_now:
  {FakeClock.now(Unit{}) == IO.pure(Nat, 42n) : IO(Nat)}

# LAW: the clock service reads the fake clock
law fake_clock_via_service:
  {Clock.now(FakeClock.new()) == IO.pure(Nat, 42n) : IO(Nat)}

# LAW: the real clock is IO.now
law real_clock_now:
  {RealClock.now(Unit{}) == IO.now() : IO(Nat)}

# LAW: the real clock service is RealClock.now
law real_clock_new:
  {RealClock.new() == Clock.Clock{RealClock.now} : Clock.Clock}

# LAW: the real log prints the line
law real_log_say:
  {Log.say(RealLog.new(), "hello") == IO.print("hello") : IO(Unit)}

# LAW: the quiet log is pure
law quiet_log_say:
  {Log.say(QuietLog.new(), "unheard") == IO.pure(Unit, Unit{}) : IO(Unit)}

# LAW: the quiet log's own say is pure
law quiet_log_own:
  {QuietLog.say("unheard") == IO.pure(Unit, Unit{}) : IO(Unit)}

# LAW: equal numbers print ok
law eq_u32_pass:
  {Kit.eq_u32(~Print.new(), "equal numbers pass", 7, 7) == Print.pass("equal numbers pass") : IO(Unit)}

# LAW: unequal numbers print FAIL
law eq_u32_fail:
  {Kit.eq_u32(~Print.new(), "unequal numbers fail", 1, 2) == Print.fail("unequal numbers fail") : IO(Unit)}

# LAW: equal strings print ok
law eq_str_pass:
  {Kit.eq_str(~Print.new(), "equal strings pass", "a" ++ "b", "ab") == Print.pass("equal strings pass") : IO(Unit)}

# LAW: unequal strings print FAIL
law eq_str_fail:
  {Kit.eq_str(~Print.new(), "unequal strings fail", "a", "b") == Print.fail("unequal strings fail") : IO(Unit)}

# LAW: the quiet reporter says nothing
law eq_u32_quiet:
  {Kit.eq_u32(~Quiet.new(), "the quiet reporter says nothing", 1, 2)
    == IO.pure(Unit, Unit{}) : IO(Unit)}

# LAW: a pass is ok name
law print_pass:
  {Print.pass("n") == IO.print("ok n") : IO(Unit)}

# LAW: a fail is FAIL name
law print_fail:
  {Print.fail("n") == IO.print("FAIL n") : IO(Unit)}

# LAW: report of True is pass
law report_pass:
  {Rep.report(True{}, Print.new(), "n") == Print.pass("n") : IO(Unit)}

# LAW: report of False is fail
law report_fail:
  {Rep.report(False{}, Print.new(), "n") == Print.fail("n") : IO(Unit)}

# LAW: the quiet reporter's say is pure
law quiet_say:
  {Quiet.say("n") == IO.pure(Unit, Unit{}) : IO(Unit)}
