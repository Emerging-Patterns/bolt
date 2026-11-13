# What a path's name says of a file. A file's name is its path's last
# segment; it is a LAWS.bend or a PROOF.bend by that name alone, wherever it
# sits. A file is a test when some directory on its path is named exactly
# `tests`: a segment `tests` that is not the last one, so a file named
# `tests` is not a test and `src/tests/x.bend` is. `doc`, `coverage` and the
# roles all read these, so a path they misread is a file linted as the wrong
# kind.
import Base
import ../src/paths.bend as Paths

# LAW: reading the segments, the last one read is kept
law base_reads_on:
  for s: String
  for rest: List<&2, String>
  for last: String
  {Paths.base.go(s <> rest, last) == Paths.base.go(rest, s) : String}

# LAW: with no segment left, the last one read is the name
law base_ends:
  for last: String
  {Paths.base.go(Nil{}, last) == last : String}

# LAW: a path's name is the last of its segments at its slashes, and empty
# for a path that ends in a slash
law base_is_last_segment:
  for path: String
  {Paths.base(path) == Paths.base.go(String.split(path, '/'), "") : String}

# LAW: segments are under a `tests` directory when the first is `tests` and
# another follows it, or when the rest are
law tested_finds_a_directory:
  for +s: String
  for +rest: List<&2, String>
  {Paths.tested(s <> rest)
    == Bool.or(Bool.and(String.eq(s, "tests"), Bool.not(List.is_empty(&2, String, rest))), Paths.tested(rest))
    : Bool}

# LAW: a lone segment is under no directory, whatever its name
law tested_needs_a_file_below:
  for +s: String
  {Paths.tested(s <> Nil{}) == False{} : Bool}

# LAW: a file is a test exactly when its path's segments are under a `tests`
# directory
law is_test_reads_segments:
  for path: String
  {Paths.is_test(path) == Paths.tested(String.split(path, '/')) : Bool}

# LAW: a file is a LAWS.bend exactly when its name is `LAWS.bend`
law is_laws_by_name:
  for path: String
  {Paths.is_laws(path) == String.eq(Paths.base(path), "LAWS.bend") : Bool}

# LAW: a file is a PROOF.bend exactly when its name is `PROOF.bend`
law is_proof_by_name:
  for path: String
  {Paths.is_proof(path) == String.eq(Paths.base(path), "PROOF.bend") : Bool}

# LAW: a law file by name is a LAWS.bend or a PROOF.bend
law is_law_file_either:
  for +path: String
  {Paths.is_law_file(path) == Bool.or(Paths.is_laws(path), Paths.is_proof(path)) : Bool}
