# `spare` reports exactly one finding, on the import's line, for each spare
# import that is idle, of each file of the run that is neither a law file
# nor a proof file, and none for anything else.
#
# A file's spare imports are read once, with the file (src/rules/links.bend):
# its imports of files by relative paths, each under an alias of its own,
# whose alias the file never names, when the file does name the alias of
# another import. A file names an alias when a dotted name among its tokens,
# outside every import line, starts with the alias and a dot. A spare import
# is idle when its target was read in the run and neither the target nor a
# file it reaches by relative imports loads; a file loads when it states a
# law, holds a def that is a proof, or holds a foreign def. So an import
# made for what importing does (a file's own proofs, an entry kept for the
# foreign defs it reaches) is never reported, and deleting a reported one
# changes nothing `bend` checks or links.
#
# Proved in part. That an import of a file that itself loads is never
# reported is a law here (spare_keeps_loader). That one of a file which only
# reaches a loader is never reported rests on what the walk reaches
# (laws/ImportReachIsClosed.bend: it holds the file, is shut under the
# imports the run read, and is the least such list); no law here joins the
# two. Not proved: that no comment or string changes a finding (the reading
# takes dotted names only, and laws/CodeRulesIgnoreCommentsAndStrings.bend
# does not list this rule).
#
# also rests on: laws/ImportReachIsClosed.bend
import Base
import ../src/finding.bend as F
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/calls.bend as Calls
import ../src/rules/digest.bend as Digest
import ../src/rules/imports.bend as Imports
import ../src/rules/links.bend as Links
import ../src/rules/suspicious/unused.bend as Unused
import ../src/rules/suspicious/spare.bend as Spare
import ./defs/Unsafe.bend as D1

# how many of a file's spare imports are idle, added to a count
def idle_spares(ss: List<&2, Links.Spare>, +all: List<&2, Digest.Digest>, +ls: List<&2, String>, after: Nat) -> Nat:
  match ss:
    case Nil{}:
      after
    case Con{Links.Spare{_alias, target, _line}, rest}:
      +m = idle_spares(rest, all, ls, after)
      Bool.pick(Nat, Spare.idle(all, ls, target), 1n+m, m)

# how many imports the rule reports over the files: none in a law file or a
# proof file
def spare_count(ds: List<&2, Digest.Digest>, +all: List<&2, Digest.Digest>, +ls: List<&2, String>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{
      Digest.Digest{_path, _norm, _dir, _is_laws, is_law_file, _exempt, _tops, _says, _deps, _laws,
        Links.Links{_loads, spare}}, rest}:
      +m = spare_count(rest, all, ls)
      Bool.pick(Nat, is_law_file, m, idle_spares(spare, all, ls, m))

# LAW: over the files of a run, the rule reports one finding for each idle
# spare import of each file that is neither a law file nor a proof file, and
# none for anything else
law spare_counts:
  for ds: List<&2, Digest.Digest>
  for +all: List<&2, Digest.Digest>
  for +ls: List<&2, String>
  {List.length(&2, F.Finding, Spare.check.go(ds, all, ls)) == spare_count(ds, all, ls) : Nat}

# LAW: the rule judges every file's imports against all the files of the
# run and those of them that load
law spare_reads_whole_run:
  for +ds: List<&2, Digest.Digest>
  {Spare.check(ds) == Spare.check.go(ds, ds, Spare.loaders(ds)) : List<&2, F.Finding>}

# LAW: the finding sits at the start of the import's line, over the word
# `import`, and names the alias
law spare_cites_import:
  for alias: String
  for line: U32
  for path: String
  {Spare.cite(alias, line, path)
    == F.Finding{path, line, 0, 6, "spare", "Import " ++ alias ++ " is never named in this file; delete the import."}
    : F.Finding}

# LAW: a law file's or a proof file's own imports are never reported
law spare_skips_law_files:
  for path: String
  for norm: String
  for dir: String
  for is_laws: Bool
  for exempt: Bool
  for tops: List<&2, Digest.Top>
  for says: List<&2, Digest.Mention>
  for deps: List<&2, String>
  for laws: List<&2, Digest.Law>
  for links: Links.Links
  for rest: List<&2, Digest.Digest>
  for +all: List<&2, Digest.Digest>
  for +ls: List<&2, String>
  {Spare.check.go(Digest.Digest{path, norm, dir, is_laws, True{}, exempt, tops, says, deps, laws, links} <> rest, all,
      ls)
    == Spare.check.go(rest, all, ls) : List<&2, F.Finding>}

# LAW: a target was read exactly when a file of the run has its path
law read_finds_file_of_run:
  for +all: List<&2, Digest.Digest>
  for +target: String
  {Spare.read(all, target) == D1.unsafe.read(all, target) : Bool}

# LAW: an import whose target the run did not read is not idle: nothing is
# known of the file
law idle_needs_target_read:
  for +all: List<&2, Digest.Digest>
  for ls: List<&2, String>
  for +target: String
  for e: {Spare.read(all, target) == False{} : Bool}
  {Spare.idle(all, ls, target) == False{} : Bool}

# LAW: nor is one whose target, or a file it reaches, loads
law idle_skips_loading_import:
  for +all: List<&2, Digest.Digest>
  for ls: List<&2, String>
  for +target: String
  for e: {Spare.reaches(all, ls, target) == True{} : Bool}
  {Spare.idle(all, ls, target) == False{} : Bool}

# LAW: one whose target was read and reaches no file that loads is idle
law idle_holds:
  for +all: List<&2, Digest.Digest>
  for ls: List<&2, String>
  for +target: String
  for e: {Spare.read(all, target) == True{} : Bool}
  for o: {Spare.reaches(all, ls, target) == False{} : Bool}
  {Spare.idle(all, ls, target) == True{} : Bool}

# LAW: an import of a file that itself loads is never idle, whatever else
# the run holds: what a file reaches holds the file
law spare_keeps_loader:
  for +all: List<&2, Digest.Digest>
  for +ls: List<&2, String>
  for +target: String
  for e: {Imports.has(ls, target) == True{} : Bool}
  {Spare.idle(all, ls, target) == False{} : Bool}

# LAW: a file that loads is among the loaders, under its normalized path
law loaders_take_loading_file:
  for path: String
  for norm: String
  for dir: String
  for is_laws: Bool
  for is_law_file: Bool
  for exempt: Bool
  for tops: List<&2, Digest.Top>
  for says: List<&2, Digest.Mention>
  for deps: List<&2, String>
  for laws: List<&2, Digest.Law>
  for spare: List<&2, Links.Spare>
  for rest: List<&2, Digest.Digest>
  {Spare.loaders(
      Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws, Links.Links{True{}, spare}}
        <> rest)
    == norm <> Spare.loaders(rest) : List<&2, String>}

# LAW: and a file that does not load is not
law loaders_pass_other_file:
  for path: String
  for norm: String
  for dir: String
  for is_laws: Bool
  for is_law_file: Bool
  for exempt: Bool
  for tops: List<&2, Digest.Top>
  for says: List<&2, Digest.Mention>
  for deps: List<&2, String>
  for laws: List<&2, Digest.Law>
  for spare: List<&2, Links.Spare>
  for rest: List<&2, Digest.Digest>
  {Spare.loaders(
      Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws, Links.Links{False{}, spare}}
        <> rest)
    == Spare.loaders(rest) : List<&2, String>}

# LAW: a file's links are whether its tree loads and the spare imports of
# its outline and tokens
law links_read_file:
  for items: List<&2, Outline.Item>
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for from: String
  {Links.of(items, toks, tree, from) == Links.Links{Links.loads(tree), Links.spare(items, toks, from)} : Links.Links}

# LAW: a file that states a law loads
law loads_sees_law:
  for kids: Tree.Node
  for body: Tree.Node
  for rest: Tree.Node
  {Links.loads(Tree.NCons{Tree.Stmt{Tree.SLaw{}, kids, body}, rest}) == True{} : Bool}

# LAW: a file that holds a def that is a proof loads
law loads_sees_proof:
  for +kids: Tree.Node
  for +body: Tree.Node
  for rest: Tree.Node
  for e: {Calls.proof(Calls.header(kids, body)) == True{} : Bool}
  {Links.loads(Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest}) == True{} : Bool}

# LAW: a file that holds a foreign def loads
law loads_sees_foreign_def:
  for +kids: Tree.Node
  for +body: Tree.Node
  for rest: Tree.Node
  for e: {Unused.foreign.opens(Calls.under(kids, body)) == True{} : Bool}
  {Links.loads(Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest}) == True{} : Bool}

# LAW: a def that is neither is passed over
law loads_passes_plain_def:
  for +kids: Tree.Node
  for +body: Tree.Node
  for rest: Tree.Node
  for e: {Calls.proof(Calls.header(kids, body)) == False{} : Bool}
  for o: {Unused.foreign.opens(Calls.under(kids, body)) == False{} : Bool}
  {Links.loads(Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest}) == Links.loads(rest) : Bool}

# LAW: and so is a type, an import or any other statement
law loads_passes_type:
  for kids: Tree.Node
  for body: Tree.Node
  for rest: Tree.Node
  {Links.loads(Tree.NCons{Tree.Stmt{Tree.SType{}, kids, body}, rest}) == Links.loads(rest) : Bool}

# LAW: a file that names none of its imports has no spare import
law spare_needs_named_import:
  for +items: List<&2, Outline.Item>
  for +toks: List<&2, Lex.Tok>
  for from: String
  for e: {Links.uses(items, toks) == False{} : Bool}
  {Links.spare(items, toks, from) == Nil{} : List<&2, Links.Spare>}

# LAW: one that names an import has those it never names
law spare_lists_unnamed:
  for +items: List<&2, Outline.Item>
  for +toks: List<&2, Lex.Tok>
  for from: String
  for e: {Links.uses(items, toks) == True{} : Bool}
  {Links.spare(items, toks, from) == Links.spares(items, toks, from) : List<&2, Links.Spare>}

# LAW: an import of a file by a relative path, under an alias the tokens
# never name, is one of them, with the file it names resolved against the
# importer
law spares_take_unnamed_import:
  for +name: String
  for line: U32
  for sig: String
  for doc: String
  for +path: String
  for rest: List<&2, Outline.Item>
  for +toks: List<&2, Lex.Tok>
  for +from: String
  for e: {Links.local(name, path) == True{} : Bool}
  for o: {Links.names(toks, name) == False{} : Bool}
  {Links.spares(Outline.Item{Outline.IImport{}, name, line, sig, doc, path} <> rest, toks, from)
    == Links.Spare{name, Imports.resolve(from, path), line} <> Links.spares(rest, toks, from)
    : List<&2, Links.Spare>}

# LAW: an import whose alias the tokens name is none
law spares_pass_named_import:
  for +name: String
  for line: U32
  for sig: String
  for doc: String
  for +path: String
  for rest: List<&2, Outline.Item>
  for +toks: List<&2, Lex.Tok>
  for +from: String
  for e: {Links.local(name, path) == True{} : Bool}
  for o: {Links.names(toks, name) == True{} : Bool}
  {Links.spares(Outline.Item{Outline.IImport{}, name, line, sig, doc, path} <> rest, toks, from)
    == Links.spares(rest, toks, from) : List<&2, Links.Spare>}

# LAW: nor is one that is not local: one with no alias of its own, or of a
# path that is not relative
law spares_pass_other_import:
  for +name: String
  for line: U32
  for sig: String
  for doc: String
  for +path: String
  for rest: List<&2, Outline.Item>
  for +toks: List<&2, Lex.Tok>
  for +from: String
  for e: {Links.local(name, path) == False{} : Bool}
  {Links.spares(Outline.Item{Outline.IImport{}, name, line, sig, doc, path} <> rest, toks, from)
    == Links.spares(rest, toks, from) : List<&2, Links.Spare>}

# LAW: an import named by its own path (`import Base`) is not local
law local_needs_alias:
  for +path: String
  {Links.local(path, path) == False{} : Bool}

# LAW: nor is one whose path does not start with a dot (a hub package)
law local_needs_relative_path:
  for name: String
  for +path: String
  for e: {String.starts_with(path, ".") == False{} : Bool}
  {Links.local(name, path) == False{} : Bool}

# LAW: a file names an alias when a dotted name outside an import line
# starts with the alias and a dot, whatever follows it
law names_sees_dotted_name:
  for +t: String
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  for +prefix: String
  for e: {String.starts_with(t, prefix) == True{} : Bool}
  {Links.names.go(Lex.Tok{Lex.TDotted{}, t, l, c} <> rest, prefix, False{}, False{}) == True{} : Bool}

# LAW: a dotted name that starts another way is passed over
law names_passes_other_dotted_name:
  for +t: String
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  for +prefix: String
  for e: {String.starts_with(t, prefix) == False{} : Bool}
  {Links.names.go(Lex.Tok{Lex.TDotted{}, t, l, c} <> rest, prefix, False{}, False{})
    == Links.names.go(rest, prefix, False{}, False{}) : Bool}

# LAW: on an import line a dotted name is no naming: an import's own path
# (`./O.bend`) does not name the alias O
law names_skips_import_line:
  for +t: String
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  for +prefix: String
  {Links.names.go(Lex.Tok{Lex.TDotted{}, t, l, c} <> rest, prefix, True{}, False{})
    == Links.names.go(rest, prefix, True{}, False{}) : Bool}

# LAW: the keyword `import` opens an import line
law names_import_opens_line:
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  for +prefix: String
  for skip: Bool
  {Links.names.go(Lex.Tok{Lex.TKey{}, "import", l, c} <> rest, prefix, skip, False{})
    == Links.names.go(rest, prefix, True{}, False{}) : Bool}

# LAW: and the line's end closes it
law names_newline_ends_line:
  for +t: String
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  for +prefix: String
  {Links.names.go(Lex.Tok{Lex.TNewline{}, t, l, c} <> rest, prefix, True{}, False{})
    == Links.names.go(rest, prefix, False{}, False{}) : Bool}

# LAW: a comment names nothing, whatever it says
law names_passes_comment:
  for +t: String
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  for +prefix: String
  {Links.names.go(Lex.Tok{Lex.TComment{}, t, l, c} <> rest, prefix, False{}, False{})
    == Links.names.go(rest, prefix, False{}, False{}) : Bool}

# LAW: nor does a string
law names_passes_string:
  for +t: String
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  for +prefix: String
  {Links.names.go(Lex.Tok{Lex.TStr{}, t, l, c} <> rest, prefix, False{}, False{})
    == Links.names.go(rest, prefix, False{}, False{}) : Bool}

# LAW: where the tokens end with no such name met, the file does not name
# the alias
law names_ends_unnamed:
  for prefix: String
  for skip: Bool
  {Links.names.go(Nil{}, prefix, skip, False{}) == False{} : Bool}

# LAW: the alias is looked for with its dot, from the file's first token,
# outside an import line
law names_looks_for_alias_and_dot:
  for toks: List<&2, Lex.Tok>
  for alias: String
  {Links.names(toks, alias) == Links.names.go(toks, alias ++ ".", False{}, False{}) : Bool}

# LAW: a file names an import when it names the first import's alias
law uses_sees_named_import:
  for +name: String
  for line: U32
  for sig: String
  for doc: String
  for path: String
  for rest: List<&2, Outline.Item>
  for +toks: List<&2, Lex.Tok>
  for e: {String.eq(name, path) == False{} : Bool}
  for o: {Links.names(toks, name) == True{} : Bool}
  {Links.uses(Outline.Item{Outline.IImport{}, name, line, sig, doc, path} <> rest, toks) == True{} : Bool}

# LAW: an import with no alias of its own names nothing: the search goes on
law uses_passes_unaliased_import:
  for +name: String
  for line: U32
  for sig: String
  for doc: String
  for rest: List<&2, Outline.Item>
  for +toks: List<&2, Lex.Tok>
  {Links.uses(Outline.Item{Outline.IImport{}, name, line, sig, doc, name} <> rest, toks) == Links.uses(rest, toks)
    : Bool}

# LAW: and so does one whose alias the tokens never name
law uses_passes_unnamed_import:
  for +name: String
  for line: U32
  for sig: String
  for doc: String
  for path: String
  for rest: List<&2, Outline.Item>
  for +toks: List<&2, Lex.Tok>
  for o: {Links.names(toks, name) == False{} : Bool}
  {Links.uses(Outline.Item{Outline.IImport{}, name, line, sig, doc, path} <> rest, toks) == Links.uses(rest, toks)
    : Bool}
