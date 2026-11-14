# What the planner asks the World, path by path. Each directory the walk
# reads is asked for its entries and each path the plan reads is asked for
# its text, one question a path, in the order the paths come, so no path the
# plan reads goes unasked. A bolt.bend is configuration and never a source: a
# file is one exactly when its path is `bolt.bend` or ends in `/bolt.bend`,
# and the sources of a run are its files less those, in order.
import Base
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan

# LAW: every directory is asked for its entries, in order
law entries_asked_in_order:
  for d: String
  for rest: List<&2, String>
  {Plan.asks.entries(d <> rest) == W.Entries{d} <> Plan.asks.entries(rest) : List<&2, W.Ask>}

# LAW: every path is asked for its text, in order
law texts_asked_in_order:
  for p: String
  for rest: List<&2, String>
  {Plan.asks.texts(p <> rest) == W.Contents{p} <> Plan.asks.texts(rest) : List<&2, W.Ask>}

# LAW: a path is a bolt.bend exactly when it is `bolt.bend` or ends in
# `/bolt.bend`
law config_by_name:
  for +p: String
  {Plan.is_config(p) == Bool.or(String.eq(p, "bolt.bend"), String.ends_with(p, "/bolt.bend")) : Bool}

# LAW: a bolt.bend is not a source
law sources_drop_config:
  for +p: String
  for rest: List<&2, String>
  for e: {Plan.is_config(p) == True{} : Bool}
  {Plan.sources(p <> rest) == Plan.sources(rest) : List<&2, String>}

# LAW: any other file is a source, in order
law sources_keep_files:
  for +p: String
  for rest: List<&2, String>
  for e: {Plan.is_config(p) == False{} : Bool}
  {Plan.sources(p <> rest) == p <> Plan.sources(rest) : List<&2, String>}

# LAW: the bolt.bend candidates are asked for directory by directory, in the
# order of the directories: a directory's own chain before the next one's
law conf_cands_in_directory_order:
  for d: String
  for rest: List<&2, String>
  for +world: W.World
  {Plan.conf.cands(d <> rest, world)
    == List.append(&2, String, Plan.conf.chain(world, d), Plan.conf.cands(rest, world)) : List<&2, String>}
