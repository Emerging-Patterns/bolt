# A relative import names a file, and two spellings of one file must compare
# equal: every rule that follows imports (the roles, `coverage`, the closures)
# keys a file by its normalized path. A path is normalized segment by
# segment: `.` and an empty segment (a doubled or leading slash) are dropped,
# `..` drops the segment before it and is itself dropped at the top, and any
# other segment is kept, in order. A file's directory is its normalized path
# without the last segment, with a slash after it (`` at the top). An import
# is resolved against the directory of the file that holds it, and only an
# import whose path starts with `.` is one of a file's targets: the others
# name packages, of which nothing is known.
import Base
import ../src/rules/imports.bend as Imports
import ../src/syntax/outline.bend as Outline

# is the item an import? Law vocabulary: bolt never calls it
def paths.is_import(kk: Outline.ItemKind) -> Bool:
  match kk:
    case Outline.IImport{}:
      True{}
    case other:
      False{}

# LAW: `..` drops the segment before it, and is dropped itself
law put_pops:
  for +h: String
  for +t: List<&2, String>
  {Imports.norm.put("..", h <> t) == t : List<&2, String>}

# LAW: `..` with no segment before it is dropped, so a path never climbs
# above where it starts
law put_stays_at_top:
  for acc: List<&2, String>
  for e: {List.is_empty(&2, String, acc) == True{} : Bool}
  {Imports.norm.put("..", acc) == Nil{} : List<&2, String>}

# LAW: `.` changes nothing
law put_skips_dot:
  for acc: List<&2, String>
  {Imports.norm.put(".", acc) == acc : List<&2, String>}

# LAW: an empty segment (a doubled, leading or trailing slash) changes nothing
law put_skips_empty:
  for acc: List<&2, String>
  {Imports.norm.put("", acc) == acc : List<&2, String>}

# LAW: any other segment is kept, in front of those before it (the path is
# held last segment first while it is read)
law put_keeps:
  for +ss: String
  for acc: List<&2, String>
  for e1: {String.eq(ss, "..") == False{} : Bool}
  for e2: {String.eq(ss, ".") == False{} : Bool}
  for e3: {String.is_empty(ss) == False{} : Bool}
  {Imports.norm.put(ss, acc) == ss <> acc : List<&2, String>}

# LAW: the segments are read left to right, each put onto those before it
law go_reads_in_order:
  for +s: String
  for rest: List<&2, String>
  for acc: List<&2, String>
  {Imports.norm.go(s <> rest, acc) == Imports.norm.go(rest, Imports.norm.put(s, acc)) : List<&2, String>}

# LAW: with no segment left, what was kept is the path, first segment first
law go_ends_in_order:
  for acc: List<&2, String>
  {Imports.norm.go(Nil{}, acc) == List.reverse(&2, String, acc) : List<&2, String>}

# LAW: a path is normalized by splitting it at its slashes, reading the
# segments from nothing kept, and joining what is kept with slashes
law norm_reads_segments:
  for path: String
  {Imports.norm(path) == String.join(Imports.norm.go(String.split(path, '/'), Nil{}), "/") : String}

# LAW: all but the last of two or more segments keeps the first and goes on
law init_keeps_first:
  for h: String
  for m: String
  for t: List<&2, String>
  {Imports.init(h <> m <> t) == h <> Imports.init(m <> t) : List<&2, String>}

# LAW: all but the last of one segment is none
law init_drops_last:
  for h: String
  {Imports.init(h <> Nil{}) == Nil{} : List<&2, String>}

# LAW: a path's directory is its normalized path's segments but the last,
# joined with slashes and ended by one, and `` when there are none
law dir_is_all_but_last:
  for path: String
  {Imports.dir_of(path)
    == Bool.pick(String,
      List.is_empty(&2, String, Imports.init(String.split(Imports.norm(path), '/'))), "",
      String.join(Imports.init(String.split(Imports.norm(path), '/')), "/") ++ "/") : String}

# LAW: an import is resolved by normalizing its path put after the directory
# of the file that holds it
law resolve_from_directory:
  for +from: String
  for rel: String
  {Imports.resolve(from, rel) == Imports.norm(Imports.dir_of(from) ++ rel) : String}

# LAW: an import whose path starts with `.` is a target of its file, resolved
# against it, in the order the imports come
law targets_take_relative:
  for name: String
  for line: U32
  for sig: String
  for doc: String
  for +path: String
  for rest: List<&2, Outline.Item>
  for +from: String
  for e: {String.starts_with(path, ".") == True{} : Bool}
  {Imports.targets(Outline.Item{Outline.IImport{}, name, line, sig, doc, path} <> rest, from)
    == Imports.resolve(from, path) <> Imports.targets(rest, from) : List<&2, String>}

# LAW: an import whose path does not start with `.` names a package and is
# no target
law targets_skip_packages:
  for name: String
  for line: U32
  for sig: String
  for doc: String
  for +path: String
  for rest: List<&2, Outline.Item>
  for +from: String
  for e: {String.starts_with(path, ".") == False{} : Bool}
  {Imports.targets(Outline.Item{Outline.IImport{}, name, line, sig, doc, path} <> rest, from)
    == Imports.targets(rest, from) : List<&2, String>}

# LAW: an item that is not an import is no target
law targets_skip_other_items:
  for kk: Outline.ItemKind
  for name: String
  for line: U32
  for sig: String
  for doc: String
  for path: String
  for rest: List<&2, Outline.Item>
  for +from: String
  for e: {paths.is_import(kk) == False{} : Bool}
  {Imports.targets(Outline.Item{kk, name, line, sig, doc, path} <> rest, from)
    == Imports.targets(rest, from) : List<&2, String>}
