# proofs of laws/LastLineSummary.bend
import Base
import ../src/lint/plan.bend as Plan
import ../laws/LastLineSummary.bend as Laws
import ../laws/LinesInOrder.bend as L1
import ../laws/defs/GradedFindingCounts.bend as D1
import ./lemmas/PlannerOutputOrder.bend as M1

# the last of a list with one more at its end is that one
law lint.last.go:
  for xs: List<&2, String>
  for -hd: String
  for +ss: String
  {List.last.go(&2, String, List.append(&2, String, xs, [ss]), hd) == ss : String}

def lint.last.go(xs, _hd, ss):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +tl}:
      lint.last.go(tl, x, ss)

# so the last line of lines then one more is that one
law lint.last:
  for xs: List<&2, String>
  for +ss: String
  {List.last(&2, String, List.append(&2, String, xs, [ss])) == Some{ss} : Maybe<&2, String>}

def lint.last(xs, ss):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +tl}:
      Equal.cong(String, Maybe<&2, String>, yy => Some{yy},
        List.last.go(&2, String, List.append(&2, String, tl, [ss]), x), ss, lint.last.go(tl, x, ss))

def Laws.last_line_summary(world):
  e = Equal.sym(List<&2, String>, Plan.lines.of(Plan.plan(world)), L1.out_lines(world), L1.lines_in_order(world))
  %e : {List.last(&2, String, _) == Some{D1.summary_of(D1.run_graded(world))} : Maybe<&2, String>}
  lint.last(L1.shown_all(D1.run_graded(world)), D1.summary_of(D1.run_graded(world)))
