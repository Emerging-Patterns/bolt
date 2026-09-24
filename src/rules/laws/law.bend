# rule coverage (project-wide; its module is law.bend, since `law` is a Bend
# keyword and no bolt.bend could name it): in a project that states laws (a
# LAWS.bend among the files the linter read), every def and type of every
# file is reached from a quantified law in a LAWS.bend. A def is reached when
# such a law names it (its binders or its statement use it, through an import
# alias or in the law's own file), or when a reached def calls it: a use on
# the def's lines, in its file or behind a relative import, across the files
# of the run. A def no law reaches has no stated property, not even through
# its callers: it is the coverage gap. A closed law, a law's own name, and a
# law outside a LAWS.bend name nothing. A type is reached when such a law or
# a reached def names it or one of its constructors (`M.Sq{..}` reaches a
# `type Shape` with `Sq{..}`); a use of another def of its module does not
# reach it, and a type reaches nothing. Out of scope: helper defs (dotted
# names; a dotted type is graded, and a helper still carries the reach to
# what it calls), tests, and the law files themselves -- decided by the name
# and the file's path, never by what the file's text mentions. IO is no
# exemption: a law can quantify over an IO value or state an IO equality, so
# a def returning `IO(..)` is graded like any other, and so is every pure def
# beside it. `main` is a def: a law that names it covers it. The rule reads
# each file's digest (src/rules/digest.bend), never the parsed source: its
# phases use the list three times, and a `+` reuse copies it. The reach is
# one walk over one graph, the walk the unsafe rule takes over imports
# (src/rules/imports.bend): its nodes are the defs, types and constructors
# of the run by key (name, a space, path), and one more node, the empty key,
# that leads to what the laws name.
import Base
import ../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../syntax/outline.bend as Outline
import ../digest.bend as Digest
import ../imports.bend as Imports

# what the laws name
# ------------------

# a file's uses onto the others', when the file is a LAWS.bend
def named.put(laws: Bool, ms: List<&2, Digest.Mention>, more: List<&2, Digest.Mention>) -> List<&2, Digest.Mention>:
  match laws:
    case True{}:
      List.append(&2, Digest.Mention, ms, more)
    case False{}:
      more

# what the laws of every LAWS.bend name (Digest.of records uses for no
# other file; a digest list handed in from elsewhere is read the same way)
def named(ds: List<&2, Digest.Digest>) -> List<&2, Digest.Mention>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      named.put(is_laws, says, named(rest))

# the graph
# ---------

# an item's key: its name, a space, its file's path. A name has no space, so
# no two items share one, and no item has the empty key
def key(+pp: String, name: String) -> String:
  name ++ " " ++ pp

# the keys of what the mentions name
def keys(ms: List<&2, Digest.Mention>) -> List<&2, String>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{Digest.Mention{p, n}, rest}:
      key(p, n) <> keys(rest)

# a type's constructors, each a node that leads nowhere, onto the others
def ctor_nodes(cs: List<&2, String>, +pp: String, more: List<&2, Imports.Edge>) -> List<&2, Imports.Edge>:
  match cs:
    case Nil{}:
      more
    case Con{c, rest}:
      Imports.Edge{key(pp, c), []} <> ctor_nodes(rest, pp, more)

# the items of a file as nodes onto the others: a def leads to what it
# calls, a type and its constructors to nothing
def nodes(ts: List<&2, Digest.Top>, +pp: String, more: List<&2, Imports.Edge>) -> List<&2, Imports.Edge>:
  match ts:
    case Nil{}:
      more
    case Con{Digest.Top{Outline.IDef{}, name, line, cs, calls}, rest}:
      Imports.Edge{key(pp, name), keys(calls)} <> nodes(rest, pp, more)
    case Con{Digest.Top{Outline.IType{}, name, line, cs, calls}, rest}:
      Imports.Edge{key(pp, name), []} <> ctor_nodes(cs, pp, nodes(rest, pp, more))
    case Con{other, rest}:
      nodes(rest, pp, more)

# the items of every file as nodes
def graph.items(ds: List<&2, Digest.Digest>) -> List<&2, Imports.Edge>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      nodes(tops, norm, graph.items(rest))

# the graph: the empty key first, leading to what the laws name, then the
# items
def graph(+ds: List<&2, Digest.Digest>) -> List<&2, Imports.Edge>:
  Imports.Edge{"", keys(named(ds))} <> graph.items(ds)

# a type's constructors: is one of them reached?
def any_item(ns: List<&2, String>, +cl: List<&2, String>, +pp: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{name, rest}:
      Lazy.or_else(Imports.has(cl, key(pp, name)), _u => any_item(rest, cl, pp))

# what is in scope
# ----------------

# the directories that state laws
def law_dirs(ds: List<&2, Digest.Digest>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      +more = law_dirs(rest)
      Bool.pick(List<&2, String>, is_laws, dir <> more, more)

# a def, or a type, that no law reaches
def gaps(ts: List<&2, Digest.Top>, +cl: List<&2, String>, +pp: String, +path: String) -> List<&2, F.Finding>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{Digest.Top{Outline.IDef{}, +name, +line, cs, calls}, rest}:
      +more = gaps(rest, cl, pp, path)
      Bool.pick(List<&2, F.Finding>,
        Lazy.or_else(String.contains(name, "."), _u => Imports.has(cl, key(pp, name))), more,
        F.Finding{path, line, 0, 0, "coverage", "No quantified law reaches def " ++ name ++ "."} <> more)
    case Con{Digest.Top{Outline.IType{}, +name, +line, cs, calls}, rest}:
      +more = gaps(rest, cl, pp, path)
      Bool.pick(List<&2, F.Finding>, Lazy.or_else(Imports.has(cl, key(pp, name)), _u => any_item(cs, cl, pp)), more,
        F.Finding{path, line, 0, 0, "coverage", "No quantified law reaches type " ++ name ++ " or any of its constructors."}
          <> more)
    case Con{other, rest}:
      gaps(rest, cl, pp, path)

# every file not exempt, against what the laws reach
def check.go(ds: List<&2, Digest.Digest>, +cl: List<&2, String>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, +norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      +more = check.go(rest, cl)
      Lazy.stop(List<&2, F.Finding>, exempt, more,
        _u => List.append(&2, F.Finding, gaps(tops, cl, norm, path), more))

# what the laws reach: the walk from the empty key over the graph, built once
def reached(+es: List<&2, Imports.Edge>) -> List<&2, String>:
  Imports.closure.go(es, Imports.paths(es), List.length(&2, Imports.Edge, es), "")

# a project states no laws: nothing of it is under law, and the graph is
# never built (a project with no LAWS.bend pays nothing)
def check.first(+ds: List<&2, Digest.Digest>, dirs: List<&2, String>) -> List<&2, F.Finding>:
  match dirs:
    case Nil{}:
      Nil{}
    case Con{d, rest}:
      check.go(ds, reached(graph(ds)))

# the rule, over every file the linter read
def check(+ds: List<&2, Digest.Digest>) -> List<&2, F.Finding>:
  check.first(ds, law_dirs(ds))
