# src/paths: what a path names, read by its segments, never by a suffix or a
# substring. A law file is one whose last segment is exactly LAWS.bend or
# PROOF.bend, so OUTLAWS.bend is not one; a test is one with a directory
# segment exactly `tests`, so contests/ is not one. Pure.
import Base
import ./lazy/lazy.bend as Lazy

# the last of the segments, or the one before when there are none
def base.go(segs: List<&2, String>, last: String) -> String:
  match segs:
    case Nil{}:
      last
    case Con{s, rest}:
      base.go(rest, s)

# a path's last segment
def base(path: String) -> String:
  base.go(String.split(path, '/'), "")

# is some segment but the last exactly `tests`?
def tested(segs: List<&2, String>) -> Bool:
  match segs:
    case Nil{}:
      False{}
    case Con{+s, +rest}:
      Lazy.or_else(Bool.and(String.eq(s, "tests"), Bool.not(List.is_empty(&2, String, rest))), _u => tested(rest))

# is the file under a `tests` directory?
def is_test(path: String) -> Bool:
  tested(String.split(path, '/'))

# is it a LAWS.bend?
def is_laws(path: String) -> Bool:
  String.eq(base(path), "LAWS.bend")

# is it a PROOF.bend?
def is_proof(path: String) -> Bool:
  String.eq(base(path), "PROOF.bend")

# is it a LAWS.bend or a PROOF.bend?
def is_law_file(+path: String) -> Bool:
  Bool.or(is_laws(path), is_proof(path))
