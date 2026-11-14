# A run whose texts are past a budget (Plan.budget(), 16,000,000 characters
# over every text the World holds) parses its sources a batch at a time. The
# sources are taken in file-list order and a batch closes before the source
# that would take it past the budget, so a batch holds at most the budget, or
# one source that is past it alone, and no batch is empty. Each batch is
# parsed, each of its sources is read down to what the run keeps of it (the
# marks of its noqa comments, its per-file findings and its digest), and the
# parse is dropped before the next batch is parsed. Every file's role is read first, from the
# imports in its text. A run under the budget parses every source first, as
# every run did.
#
# What is proved: batching loses no source and keeps their order, and the
# graded findings of a batched run are exactly those of a run that parses
# every source first, so every law on a run's findings, lines and exit status
# holds either way. What no law can say: that a batched run holds one batch's
# tokens, trees and bindings at a time. That is the reason for it: parsed, a
# source is some two hundred times its text, and a tree of 36 MB peaked at
# 6.9 GB parsed whole and at 3.8 GB in batches. Internal behavior of
# src/lint/plan.bend, not interface.
#
# also rests on: laws/OffRulesAreNotRun.bend
import Base
import ../src/finding.bend as F
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan

# LAW: the batches, one after another, are the sources: none lost, none
# twice, in order, whatever the budget and whatever the first batch already
# holds
law batches_keep_sources:
  for gs: List<&2, Plan.Got>
  for +used: U32
  for +max: U32
  {List.concat(&2, Plan.Got, Plan.batches(gs, used, max)) == gs : List<&2, Plan.Got>}

# LAW: two sources whose texts together are the budget share a batch
law batch_holds_the_budget:
  for +p: String
  for +q: String
  {Plan.batches([Plan.Got{p, Some{"abc"}}, Plan.Got{q, Some{"de"}}], 0, 5)
    == [[Plan.Got{p, Some{"abc"}}, Plan.Got{q, Some{"de"}}]] : List<&2, List<&2, Plan.Got>>}

# LAW: one character past it, and the second source opens the next batch
law batch_closes_past_the_budget:
  for +p: String
  for +q: String
  {Plan.batches([Plan.Got{p, Some{"abc"}}, Plan.Got{q, Some{"de"}}], 0, 4)
    == [[Plan.Got{p, Some{"abc"}}], [Plan.Got{q, Some{"de"}}]] : List<&2, List<&2, Plan.Got>>}

# LAW: a source past the budget alone is a batch alone, with no empty batch
# before it
law batch_of_one_large_source:
  for +p: String
  for +q: String
  {Plan.batches([Plan.Got{p, Some{"abc"}}, Plan.Got{q, Some{"de"}}], 0, 1)
    == [[Plan.Got{p, Some{"abc"}}], [Plan.Got{q, Some{"de"}}]] : List<&2, List<&2, Plan.Got>>}

# LAW: a source that could not be read takes no room in a batch
law batch_unread_takes_no_room:
  for +p: String
  for +q: String
  for +r: String
  {Plan.batches([Plan.Got{p, Some{"abc"}}, Plan.Got{q, None{}}, Plan.Got{r, Some{"de"}}], 0, 5)
    == [[Plan.Got{p, Some{"abc"}}, Plan.Got{q, None{}}, Plan.Got{r, Some{"de"}}]]
    : List<&2, List<&2, Plan.Got>>}

# LAW: what is set against the budget is every character of every text the
# World read, a listing and a file that could not be read counting for none
law size_counts_texts:
  for +ps: List<&2, String>
  for +cwd: String
  for +p: String
  for +q: String
  for +d: String
  for +ns: List<&2, String>
  {W.size(W.World{ps, cwd, [W.Reply{W.Contents{p}, W.Read{"abc"}}, W.Reply{W.Entries{d}, W.Listed{ns}},
      W.Reply{W.Contents{q}, W.Unread{}}, W.Reply{W.Contents{d}, W.Directory{}},
      W.Reply{W.Contents{q}, W.Read{"de"}}]}) == 5 : U32}

# LAW: the budget is 16,000,000 characters, and a World that holds exactly
# that fits it
law budget_is_sixteen_million:
  for +world: W.World
  {Plan.fits(world) == U32.is_le(W.size(world), 16000000) : Bool}

# LAW: a run that parses its sources a batch at a time grades exactly what a
# run that parses every source first grades
law final_lean:
  for +world: W.World
  {Plan.final.lean(world) == Plan.final.live(world) : List<&2, F.Graded>}

# LAW: so the run bolt makes, batched past the budget and not under it,
# grades the same findings either way
law final_run:
  for +world: W.World
  {Plan.final.run(world) == Plan.final.live(world) : List<&2, F.Graded>}
