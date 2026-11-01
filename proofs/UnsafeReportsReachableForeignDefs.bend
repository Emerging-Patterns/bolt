# proofs of laws/UnsafeReportsReachableForeignDefs.bend
import Base
import ../src/finding.bend as F
import ../src/rules/laws/unsafe.bend as Unsafe
import ../src/rules/imports.bend as Imports
import ../src/rules/digest.bend as Digest
import ../laws/UnsafeReportsReachableForeignDefs.bend as Laws
import ../laws/defs/Unsafe.bend as D1
import ./lemmas/ImportClosure.bend as M1

# unsafe (laws/UnsafeReportsReachableForeignDefs.bend)

# the rule's search of the law files' closures is unsafe.origin
law unsafe.reacher:
  for ls: List<&2, Digest.Digest>
  for +all: List<&2, Digest.Digest>
  for +pp: String
  {Unsafe.reacher(Unsafe.reaches(ls, Digest.edges(all), Imports.paths(Digest.edges(all)),
    List.length(&2, Digest.Digest, all)), pp) == Laws.unsafe.origin(ls, all, pp) : Maybe<&2, String>}

def unsafe.reacher(ls, all, pp):
  match ls:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      match is_law_file:
        case True{}:
          %unsafe.reacher(rest, all, pp) :
            {Unsafe.reacher(Unsafe.Reach{path, D1.unsafe.closure(all, norm)}
              <> Unsafe.reaches(rest, Digest.edges(all), Imports.paths(Digest.edges(all)),
                List.length(&2, Digest.Digest, all)), pp)
              == Bool.pick(Maybe<&2, String>, Imports.has(D1.unsafe.closure(all, norm), pp), Some{path}, _)
              : Maybe<&2, String>}
          {==}
        case False{}:
          unsafe.reacher(rest, all, pp)

# the rule's report is unsafe.each
law unsafe.report:
  for us: List<&2, Digest.Unsafe>
  for +origin: String
  for +via: String
  for +path: String
  {Unsafe.report(us, origin, via, path) == Laws.unsafe.each(us, origin, via, path) : List<&2, F.Finding>}

def unsafe.report(us, origin, via, path):
  match us:
    case Nil{}:
      {==}
    case Con{Digest.Unsafe{+n, +l, +c, fo}, rest}:
      match fo:
        case True{}:
          Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
            t => F.Finding{path, l, c, 3, "unsafe", Unsafe.say(True{}, n, origin, via)} <> t,
            Unsafe.report(rest, origin, via, path), Laws.unsafe.each(rest, origin, via, path),
            unsafe.report(rest, origin, via, path))
        case False{}:
          Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>,
            t => F.Finding{path, l, c, 7, "unsafe", Unsafe.say(False{}, n, origin, via)} <> t,
            Unsafe.report(rest, origin, via, path), Laws.unsafe.each(rest, origin, via, path),
            unsafe.report(rest, origin, via, path))

# the rule's found is unsafe.at
law unsafe.found:
  for mm: Maybe<&2, String>
  for us: List<&2, Digest.Unsafe>
  for +path: String
  for +norm: String
  for +all: List<&2, Digest.Digest>
  {Unsafe.found(mm, us, path, norm, Digest.edges(all), Imports.paths(Digest.edges(all)),
    List.length(&2, Digest.Digest, all)) == Laws.unsafe.at(mm, us, path, norm, all) : List<&2, F.Finding>}

def unsafe.found(mm, us, path, norm, all):
  match mm:
    case None{}:
      {==}
    case Some{+origin}:
      match us:
        case Nil{}:
          {==}
        case Con{u, rest}:
          unsafe.report(u <> rest, origin, Laws.unsafe.via(all, Imports.norm(origin), norm), path)

# the rule's walk over fs, against the law files of all, as its check runs it
def unsafe.run(fs: List<&2, Digest.Digest>, +all: List<&2, Digest.Digest>) -> List<&2, F.Finding>:
  Unsafe.check.go(fs, Unsafe.reaches(all, Digest.edges(all), Imports.paths(Digest.edges(all)),
    List.length(&2, Digest.Digest, all)), Digest.edges(all), Imports.paths(Digest.edges(all)),
    List.length(&2, Digest.Digest, all))

# the rule's walk over the files is unsafe.files
law unsafe.go:
  for fs: List<&2, Digest.Digest>
  for +all: List<&2, Digest.Digest>
  {unsafe.run(fs, all) == Laws.unsafe.files(fs, all) : List<&2, F.Finding>}

def unsafe.go(fs, all):
  match fs:
    case Nil{}:
      {==}
    case Con{Digest.Digest{+path, +norm, dir, is_laws, is_law_file, exempt, tops, says, deps, +unsafes, laws}, rest}:
      %unsafe.go(rest, all) :
        {unsafe.run(Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}
          <> rest, all)
          == List.append(&2, F.Finding, Laws.unsafe.at(Laws.unsafe.origin(all, all, norm), unsafes, path, norm, all), _)
          : List<&2, F.Finding>}
      %unsafe.found(Laws.unsafe.origin(all, all, norm), unsafes, path, norm, all) :
        {unsafe.run(Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}
          <> rest, all)
          == List.append(&2, F.Finding, _, unsafe.run(rest, all)) : List<&2, F.Finding>}
      %unsafe.reacher(all, all, norm) :
        {unsafe.run(Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}
          <> rest, all)
          == List.append(&2, F.Finding, Unsafe.found(_, unsafes, path, norm, Digest.edges(all),
            Imports.paths(Digest.edges(all)), List.length(&2, Digest.Digest, all)), unsafe.run(rest, all))
          : List<&2, F.Finding>}
      {==}

def Laws.unsafe_reports(ds):
  unsafe.go(ds, ds)
