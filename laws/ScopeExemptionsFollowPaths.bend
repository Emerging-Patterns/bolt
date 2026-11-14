# Path exemptions are decided by the path alone, never by content: two files
# at one path are exempt from `law` alike whatever each holds, and on a path a
# per-file rule's header exempts (a LAWS.bend, a PROOF.bend, a file under a
# `tests` directory, and for `closed` any file but a LAWS.bend) that rule's
# findings are the same for every source. What a rule reads from content to
# skip a def, a line or a file (a def that is a proof, returning one or
# written with no type, a file that defines `Map.put`, `# lanes: native`,
# `main` and dotted names) is that rule's behavior, not a path exemption.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/correctness/hole.bend as Hole
import ../src/rules/style/reach.bend as Reach
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/rules/digest.bend as Digest
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/style/doc.bend as Doc
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/pedantic/tail.bend as Tail
import ../src/rules/suspicious/concat.bend as Concat
import ../src/rules/suspicious/eager.bend as Eager
import ../src/rules/pedantic/rewalk.bend as Rewalk
import ../src/rules/pedantic/strict.bend as Strict
import ../src/rules/pedantic/index.bend as Index
import ../src/rules/suspicious/thunk.bend as Thunk
import ../src/rules/laws/closed.bend as Closed

# Scope: a path exemption is decided by the path alone. The `law` rule lets
# off a file by its digest's `exempt` flag, and a per-file rule's header
# exempts a LAWS.bend, a PROOF.bend or a file under `tests` by src/paths.bend.
# Neither reads the text: two files at one path, whatever each holds, are
# exempt alike, and an exempt file's findings from the rule that exempts it
# are the same for both. What a rule reads from content to skip a def, a line
# or a file (a def returning a proof, a file defining `Map.put`, `#|` lines,
# `# lanes: native`, `main` and dotted names) is that rule's own behavior,
# not a path exemption.

# whether the coverage rule lets a digest's file off
def scope.exempt(d: Digest.Digest) -> Bool:
  match d:
    case Digest.Digest{_path, _norm, _dir, _is_laws, _is_law_file, exempt, _tops, _says, _deps, _laws, _links}:
      exempt

# LAW: two files at the same path are exempt from `law` alike, whatever the
# text, tokens, tree, binding structure and outline of each
law scope_digest_exempt:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +text2: String
  for +toks2: List<&2, Lex.Tok>
  for +tree2: Tree.Node
  for +bound2: Bind.Bound
  for +items2: List<&2, Outline.Item>
  {scope.exempt(Digest.of(Src.Src{path, text, toks, tree, bound, items}))
    == scope.exempt(Digest.of(Src.Src{path, text2, toks2, tree2, bound2, items2})) : Bool}

# LAW: hole's findings on a LAWS.bend are the same for any two sources at
# that path
law scope_hole:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +text2: String
  for +toks2: List<&2, Lex.Tok>
  for +tree2: Tree.Node
  for +bound2: Bind.Bound
  for +items2: List<&2, Outline.Item>
  for +e: {Paths.is_laws(path) == True{} : Bool}
  {Hole.check(Src.Src{path, text, toks, tree, bound, items})
    == Hole.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: doc's findings on a PROOF.bend or a file under `tests` are the same
# for any two sources at that path
law scope_doc:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +text2: String
  for +toks2: List<&2, Lex.Tok>
  for +tree2: Tree.Node
  for +bound2: Bind.Bound
  for +items2: List<&2, Outline.Item>
  for +e: {Bool.or(Paths.is_proof(path), Paths.is_test(path)) == True{} : Bool}
  {Doc.check(Src.Src{path, text, toks, tree, bound, items})
    == Doc.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}

# LAW: reach's findings on a PROOF.bend are the same for any two sources at
# that path
law scope_reach:
  for +max: U32
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +text2: String
  for +toks2: List<&2, Lex.Tok>
  for +tree2: Tree.Node
  for +bound2: Bind.Bound
  for +items2: List<&2, Outline.Item>
  for +e: {Paths.is_proof(path) == True{} : Bool}
  {Reach.check(Src.Src{path, text, toks, tree, bound, items}, max)
    == Reach.check(Src.Src{path, text2, toks2, tree2, bound2, items2}, max) : List<&2, F.Finding>}

# the findings of each rule a LAWS.bend or a PROOF.bend exempts, rule by rule
def scope.law_file(+s: Src.Src) -> List<&2, List<&2, F.Finding>>:
  [Pick.check(s), Tail.check(s), Concat.check(s), Eager.check(s), Rewalk.check(s), Strict.check(s),
    Index.check(s), Thunk.check(s)]

# LAW: on a LAWS.bend or a PROOF.bend, the findings of each rule its header
# exempts there (pick, tail, concat, eager, rewalk, strict, index, thunk)
# are the same for any two sources at that path
law scope_law_file:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +text2: String
  for +toks2: List<&2, Lex.Tok>
  for +tree2: Tree.Node
  for +bound2: Bind.Bound
  for +items2: List<&2, Outline.Item>
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {scope.law_file(Src.Src{path, text, toks, tree, bound, items})
    == scope.law_file(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, List<&2, F.Finding>>}

# LAW: closed's findings on a file that is not a LAWS.bend are the same for
# any two sources at that path
law scope_closed:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +text2: String
  for +toks2: List<&2, Lex.Tok>
  for +tree2: Tree.Node
  for +bound2: Bind.Bound
  for +items2: List<&2, Outline.Item>
  for +e: {Paths.is_laws(path) == False{} : Bool}
  {Closed.check(Src.Src{path, text, toks, tree, bound, items})
    == Closed.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}
