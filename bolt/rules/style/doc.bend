# rule doc: every top-level def, type and law has a comment block right above
# it. Helpers (dotted names like `show.go`) ride on their parent's doc, `main`
# needs none, PROOF.bend fills laws that LAWS.bend already documents, and a
# test (under tests/) is documented by its header and its check names.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/outline.bend as Outline
import ../../../lazy/lazy.bend as Lazy
import ../../paths.bend as Paths

# does an item of this kind need a comment?
def needs(kk: Outline.ItemKind) -> Bool:
  match kk:
    case Outline.IDef{}:
      True{}
    case Outline.IType{}:
      True{}
    case Outline.ILaw{}:
      True{}
    case other:
      False{}

# `main`, and helpers named `x.go`
def exempt(+name: String) -> Bool:
  Bool.or(String.eq(name, "main"), String.contains(name, "."))

# an item's kind, for the message
def what(kk: Outline.ItemKind) -> String:
  match kk:
    case Outline.IType{}:
      "Type"
    case Outline.ILaw{}:
      "Law"
    case other:
      "Def"

def check.go(items: List<&2, Outline.Item>, +path: String) -> List<&2, F.Finding>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Outline.Item{+k, +name, +line, sig, +doc, p}, rest}:
      +more = check.go(rest, path)
      Bool.pick(List<&2, F.Finding>,
        Bool.and(Bool.and(needs(k), Bool.not(exempt(name))), String.is_empty(doc)),
        F.Finding{path, line, 0, 0, "doc", what(k) ++ " " ++ name ++ " has no comment above it."} <> more, more)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = ss
  Lazy.stop(List<&2, F.Finding>, Bool.or(Paths.is_proof(path), Paths.is_test(path)),
    [], _u => check.go(items, path))
