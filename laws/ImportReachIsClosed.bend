# What a file reaches by relative imports through the run, the walk the
# coverage rule takes over the laws' graph (laws/LawNamesEveryItem.bend),
# holds the file, is shut under imports, and is the least list that is: the
# walk's fuel never cuts it short, and it reaches only files a chain of
# relative imports leads to.
import Base
import ../src/rules/digest.bend as Digest
import ../src/rules/imports.bend as Imports
import ./defs/Unsafe.bend as D1

# LAW: over every list of digests, what the file at from reaches holds it
law unsafe_from:
  for +ds: List<&2, Digest.Digest>
  for +from: String
  {Imports.has(D1.unsafe.closure(ds, from), from) == True{} : Bool}

# LAW: over every list of digests, what a file reaches is shut: every file in
# the run that one of its files imports is in it. So the walk's fuel never
# cuts it short
law unsafe_shut:
  for +ds: List<&2, Digest.Digest>
  for +from: String
  {D1.unsafe.shut(ds, D1.unsafe.closure(ds, from), D1.unsafe.closure(ds, from)) == True{} : Bool}

# LAW: and it is the least such list: every list that holds from and is shut
# holds each file it reaches, so it reaches only files a chain of relative
# imports through the run leads to
law unsafe_least:
  for +ds: List<&2, Digest.Digest>
  for +from: String
  for +ss: List<&2, String>
  for +pp: String
  for hf: {Imports.has(ss, from) == True{} : Bool}
  for hs: {D1.unsafe.shut(ds, ss, ss) == True{} : Bool}
  for hp: {Imports.has(D1.unsafe.closure(ds, from), pp) == True{} : Bool}
  {Imports.has(ss, pp) == True{} : Bool}
