# proofs of laws/SpareReportsUnnamedImports.bend
import Base
import ../src/finding.bend as F
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/calls.bend as Calls
import ../src/rules/digest.bend as Digest
import ../src/rules/imports.bend as Imports
import ../src/rules/links.bend as Links
import ../src/rules/suspicious/unused.bend as Unused
import ../src/rules/suspicious/spare.bend as Spare
import ../laws/SpareReportsUnnamedImports.bend as Laws
import ../laws/ImportReachIsClosed.bend as L1
import ../laws/defs/Unsafe.bend as D1
import ./lemmas/ImportClosure.bend as M1
import ./lemmas/RoleProofPicked.bend as M2
import ./lemmas/PublishComparisons.bend as M3

# spare (laws/SpareReportsUnnamedImports.bend). The count goes import by import and file by
# file. That a loader's import is kept comes from the closure holding its
# start (laws/ImportReachIsClosed.bend) and from a path two lists hold
# making `any` True. The rest are the tests the reading is made of, each
# read off one hypothesis.

# anything and False is False
law spare.and_f:
  for x: Bool
  {Bool.and(x, False{}) == False{} : Bool}

def spare.and_f(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# anything or True is True
law spare.or_t:
  for x: Bool
  {Bool.or(x, True{}) == True{} : Bool}

def spare.or_t(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# a test and then False is False
law spare.then_f:
  for x: Bool
  {Lazy.and_then(x, _u => False{}) == False{} : Bool}

def spare.then_f(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# a test or else True is True
law spare.else_t:
  for x: Bool
  {Lazy.or_else(x, _u => True{}) == True{} : Bool}

def spare.else_t(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# a finding is added exactly when the import is idle
law spare.found:
  for hit: Bool
  for -alias: String
  for -line: U32
  for -path: String
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Spare.found(hit, alias, line, path, more)) == Bool.pick(Nat, hit, 1n+m, m) : Nat}

def spare.found(hit, _alias, _line, _path, more, m, ih):
  match hit:
    case True{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
    case False{}:
      ih

# a file's spare imports add what the law counts of them
law spare.file:
  for ss: List<&2, Links.Spare>
  for +path: String
  for +all: List<&2, Digest.Digest>
  for +ls: List<&2, String>
  for -more: List<&2, F.Finding>
  for -after: Nat
  for ih: {List.length(&2, F.Finding, more) == after : Nat}
  {List.length(&2, F.Finding, Spare.file(ss, path, all, ls, more)) == Laws.idle_spares(ss, all, ls, after) : Nat}

def spare.file(ss, path, all, ls, more, after, ih):
  match ss:
    case Nil{}:
      ih
    case Con{Links.Spare{alias, +target, line}, +rest}:
      spare.found(Spare.idle(all, ls, target), alias, line, path, Spare.file(rest, path, all, ls, more),
        Laws.idle_spares(rest, all, ls, after), spare.file(rest, path, all, ls, more, after, ih))

# a file adds its imports' findings unless it is a law or proof file
law spare.step:
  for x: Bool
  for -hits: List<&2, F.Finding>
  for -n: Nat
  for -more: List<&2, F.Finding>
  for -m: Nat
  for e: {List.length(&2, F.Finding, hits) == n : Nat}
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, x, more, _u => hits)) == Bool.pick(Nat, x, m, n) : Nat}

def spare.step(x, _hits, _n, _more, _m, e, ih):
  match x:
    case True{}:
      ih
    case False{}:
      e

def Laws.spare_counts(ds, all, ls):
  match ds:
    case Nil{}:
      {==}
    case Con{
      Digest.Digest{+path, _norm, _dir, _is_laws, is_law_file, _exempt, _tops, _says, _deps, _laws,
        Links.Links{_loads, +spare}}, +rest}:
      spare.step(is_law_file, Spare.file(spare, path, all, ls, Spare.check.go(rest, all, ls)),
        Laws.idle_spares(spare, all, ls, Laws.spare_count(rest, all, ls)), Spare.check.go(rest, all, ls),
        Laws.spare_count(rest, all, ls),
        spare.file(spare, path, all, ls, Spare.check.go(rest, all, ls), Laws.spare_count(rest, all, ls),
          Laws.spare_counts(rest, all, ls)), Laws.spare_counts(rest, all, ls))

def Laws.spare_reads_whole_run(_ds):
  {==}

def Laws.spare_cites_import(_alias, _line, _path):
  {==}

def Laws.spare_skips_law_files(
  _path,
  _norm,
  _dir,
  _is_laws,
  _exempt,
  _tops,
  _says,
  _deps,
  _laws,
  links,
  _rest,
  _all,
  _ls
):
  match links:
    case Links.Links{_loads, _spare}:
      {==}

def Laws.read_finds_file_of_run(all, target):
  Equal.trans(Bool, Spare.read(all, target), Imports.has(Imports.paths(Digest.edges(all)), target),
    D1.unsafe.read(all, target), M1.imp.seek(Imports.paths(Digest.edges(all)), target),
    M1.unsafe.read_paths(all, target))

def Laws.idle_needs_target_read(all, ls, target, e):
  s = Equal.sym(Bool, Spare.read(all, target), False{}, e)
  %s : {Lazy.and_then(_, _u => Bool.not(Spare.reaches(all, ls, target))) == False{} : Bool}
  {==}

def Laws.idle_skips_loading_import(all, ls, target, e):
  s = Equal.sym(Bool, Spare.reaches(all, ls, target), True{}, e)
  %s : {Lazy.and_then(Spare.read(all, target), _u => Bool.not(_)) == False{} : Bool}
  spare.then_f(Spare.read(all, target))

def Laws.idle_holds(all, ls, target, e, o):
  s = Equal.sym(Bool, Spare.read(all, target), True{}, e)
  %s : {Lazy.and_then(_, _u => Bool.not(Spare.reaches(all, ls, target))) == True{} : Bool}
  r = Equal.sym(Bool, Spare.reaches(all, ls, target), False{}, o)
  %r : {Bool.not(_) == True{} : Bool}
  {==}

# a path the loaders hold, met at the head of a list or further on, makes
# `any` True: b is the head's test, carried
law spare.any_has.at:
  for b: Bool
  for +h: String
  for +t: List<&2, String>
  for +ls: List<&2, String>
  for +x: String
  for eb: {String.eq(h, x) == b : Bool}
  for hl: {Imports.has(ls, x) == True{} : Bool}
  for hx: {Bool.or(b, Imports.has(t, x)) == True{} : Bool}
  for ih: {Imports.has(t, x) == True{} : Bool} -> {Spare.any(t, ls) == True{} : Bool}
  {Lazy.or_else(Imports.seek(ls, h), _u => Spare.any(t, ls)) == True{} : Bool}

def spare.any_has.at(b, h, t, ls, x, eb, hl, hx, ih):
  match b:
    case True{}:
      %Equal.sym(String, h, x, M2.unsafe.seq(h, x, eb)) :
        {Lazy.or_else(Imports.seek(ls, _), _u => Spare.any(t, ls)) == True{} : Bool}
      s = Equal.sym(Bool, Imports.seek(ls, x), Imports.has(ls, x), M1.imp.seek(ls, x))
      %s : {Lazy.or_else(_, _u => Spare.any(t, ls)) == True{} : Bool}
      r = Equal.sym(Bool, Imports.has(ls, x), True{}, hl)
      %r : {Lazy.or_else(_, _u => Spare.any(t, ls)) == True{} : Bool}
      {==}
    case False{}:
      s = Equal.sym(Bool, Spare.any(t, ls), True{}, ih(hx))
      %s : {Lazy.or_else(Imports.seek(ls, h), _u => _) == True{} : Bool}
      spare.else_t(Imports.seek(ls, h))

# a path that a list and the loaders both hold makes `any` True
law spare.any_has:
  for xs: List<&2, String>
  for +ls: List<&2, String>
  for +x: String
  for +hl: {Imports.has(ls, x) == True{} : Bool}
  for hx: {Imports.has(xs, x) == True{} : Bool}
  {Spare.any(xs, ls) == True{} : Bool}

def spare.any_has(xs, ls, x, hl, hx):
  match xs:
    case Nil{}:
      Empty.absurd({Spare.any(Nil{}, ls) == True{} : Bool}, M2.unsafe.false_true(hx))
    case Con{+h, +t}:
      spare.any_has.at(String.eq(h, x), h, t, ls, x, {==}, hl,
        Equal.trans(Bool, Bool.or(String.eq(h, x), Imports.has(t, x)), Imports.has(h <> t, x), True{},
          Equal.sym(Bool, Imports.has(h <> t, x), Bool.or(String.eq(h, x), Imports.has(t, x)),
            M1.unsafe.has_con(h, t, x)), hx), z => spare.any_has(t, ls, x, hl, z))

def Laws.spare_keeps_loader(all, ls, target, e):
  Laws.idle_skips_loading_import(all, ls, target,
    spare.any_has(Spare.closure(all, target), ls, target, e, L1.unsafe_from(all, target)))

def Laws.loaders_take_loading_file(
  _path,
  _norm,
  _dir,
  _is_laws,
  _is_law_file,
  _exempt,
  _tops,
  _says,
  _deps,
  _laws,
  _spare,
  _rest
):
  {==}

def Laws.loaders_pass_other_file(
  _path,
  _norm,
  _dir,
  _is_laws,
  _is_law_file,
  _exempt,
  _tops,
  _says,
  _deps,
  _laws,
  _spare,
  _rest
):
  {==}

def Laws.links_read_file(_items, _toks, _tree, _from):
  {==}

def Laws.loads_sees_law(_kids, _body, _rest):
  {==}

def Laws.loads_sees_proof(kids, body, rest, e):
  s = Equal.sym(Bool, Calls.proof(Calls.header(kids, body)), True{}, e)
  %s : {Lazy.or_else(Bool.or(_, Unused.foreign.opens(Calls.under(kids, body))), _u => Links.loads(rest)) == True{}
    : Bool}
  {==}

def Laws.loads_sees_foreign_def(kids, body, rest, e):
  s = Equal.sym(Bool, Unused.foreign.opens(Calls.under(kids, body)), True{}, e)
  %s : {Lazy.or_else(Bool.or(Calls.proof(Calls.header(kids, body)), _), _u => Links.loads(rest)) == True{} : Bool}
  a = Equal.sym(Bool, Bool.or(Calls.proof(Calls.header(kids, body)), True{}), True{},
    spare.or_t(Calls.proof(Calls.header(kids, body))))
  %a : {Lazy.or_else(_, _u => Links.loads(rest)) == True{} : Bool}
  {==}

def Laws.loads_passes_plain_def(kids, body, rest, e, o):
  s = Equal.sym(Bool, Calls.proof(Calls.header(kids, body)), False{}, e)
  %s : {Lazy.or_else(Bool.or(_, Unused.foreign.opens(Calls.under(kids, body))), _u => Links.loads(rest))
    == Links.loads(rest) : Bool}
  r = Equal.sym(Bool, Unused.foreign.opens(Calls.under(kids, body)), False{}, o)
  %r : {Lazy.or_else(_, _u => Links.loads(rest)) == Links.loads(rest) : Bool}
  {==}

def Laws.loads_passes_type(_kids, _body, _rest):
  {==}

def Laws.spare_needs_named_import(items, toks, from, e):
  s = Equal.sym(Bool, Links.uses(items, toks), False{}, e)
  %s : {Lazy.stop(List<&2, Links.Spare>, Bool.not(_), [], _u => Links.spares(items, toks, from)) == Nil{}
    : List<&2, Links.Spare>}
  {==}

def Laws.spare_lists_unnamed(items, toks, from, e):
  s = Equal.sym(Bool, Links.uses(items, toks), True{}, e)
  %s : {Lazy.stop(List<&2, Links.Spare>, Bool.not(_), [], _u => Links.spares(items, toks, from))
    == Links.spares(items, toks, from) : List<&2, Links.Spare>}
  {==}

def Laws.spares_take_unnamed_import(name, line, _sig, _doc, path, rest, toks, from, e, o):
  s = Equal.sym(Bool, Links.local(name, path), True{}, e)
  %s : {Bool.pick(List<&2, Links.Spare>, Lazy.and_then(_, _u => Bool.not(Links.names(toks, name))),
      Links.Spare{name, Imports.resolve(from, path), line} <> Links.spares(rest, toks, from),
      Links.spares(rest, toks, from))
    == Links.Spare{name, Imports.resolve(from, path), line} <> Links.spares(rest, toks, from)
    : List<&2, Links.Spare>}
  r = Equal.sym(Bool, Links.names(toks, name), False{}, o)
  %r : {Bool.pick(List<&2, Links.Spare>, Bool.not(_),
      Links.Spare{name, Imports.resolve(from, path), line} <> Links.spares(rest, toks, from),
      Links.spares(rest, toks, from))
    == Links.Spare{name, Imports.resolve(from, path), line} <> Links.spares(rest, toks, from)
    : List<&2, Links.Spare>}
  {==}

def Laws.spares_pass_named_import(name, line, _sig, _doc, path, rest, toks, from, e, o):
  s = Equal.sym(Bool, Links.local(name, path), True{}, e)
  %s : {Bool.pick(List<&2, Links.Spare>, Lazy.and_then(_, _u => Bool.not(Links.names(toks, name))),
      Links.Spare{name, Imports.resolve(from, path), line} <> Links.spares(rest, toks, from),
      Links.spares(rest, toks, from))
    == Links.spares(rest, toks, from) : List<&2, Links.Spare>}
  r = Equal.sym(Bool, Links.names(toks, name), True{}, o)
  %r : {Bool.pick(List<&2, Links.Spare>, Bool.not(_),
      Links.Spare{name, Imports.resolve(from, path), line} <> Links.spares(rest, toks, from),
      Links.spares(rest, toks, from))
    == Links.spares(rest, toks, from) : List<&2, Links.Spare>}
  {==}

def Laws.spares_pass_other_import(name, line, _sig, _doc, path, rest, toks, from, e):
  s = Equal.sym(Bool, Links.local(name, path), False{}, e)
  %s : {Bool.pick(List<&2, Links.Spare>, Lazy.and_then(_, _u => Bool.not(Links.names(toks, name))),
      Links.Spare{name, Imports.resolve(from, path), line} <> Links.spares(rest, toks, from),
      Links.spares(rest, toks, from))
    == Links.spares(rest, toks, from) : List<&2, Links.Spare>}
  {==}

def Laws.local_needs_alias(path):
  s = Equal.sym(Bool, String.eq(path, path), True{}, M3.pub.seq_refl(path))
  %s : {Bool.and(Bool.not(_), String.starts_with(path, ".")) == False{} : Bool}
  {==}

def Laws.local_needs_relative_path(name, path, e):
  s = Equal.sym(Bool, String.starts_with(path, "."), False{}, e)
  %s : {Bool.and(Bool.not(String.eq(name, path)), _) == False{} : Bool}
  spare.and_f(Bool.not(String.eq(name, path)))

# once a name was found, the answer is True whatever follows
law spare.hit:
  for toks: List<&2, Lex.Tok>
  for prefix: String
  for skip: Bool
  {Links.names.go(toks, prefix, skip, True{}) == True{} : Bool}

def spare.hit(toks, _prefix, _skip):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{_k, _t, _l, _c}, _rest}:
      {==}

def Laws.names_sees_dotted_name(t, _l, _c, rest, prefix, e):
  s = Equal.sym(Bool, String.starts_with(t, prefix), True{}, e)
  %s : {Links.names.go(rest, prefix, False{}, _) == True{} : Bool}
  spare.hit(rest, prefix, False{})

def Laws.names_passes_other_dotted_name(t, _l, _c, rest, prefix, e):
  s = Equal.sym(Bool, String.starts_with(t, prefix), False{}, e)
  %s : {Links.names.go(rest, prefix, False{}, _) == Links.names.go(rest, prefix, False{}, False{}) : Bool}
  {==}

def Laws.names_skips_import_line(_t, _l, _c, _rest, _prefix):
  {==}

def Laws.names_import_opens_line(_l, _c, _rest, _prefix, skip):
  match skip:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.names_newline_ends_line(_t, _l, _c, _rest, _prefix):
  {==}

def Laws.names_passes_comment(_t, _l, _c, _rest, _prefix):
  {==}

def Laws.names_passes_string(_t, _l, _c, _rest, _prefix):
  {==}

def Laws.names_ends_unnamed(_prefix, _skip):
  {==}

def Laws.names_looks_for_alias_and_dot(_toks, _alias):
  {==}

def Laws.uses_sees_named_import(name, _line, _sig, _doc, path, rest, toks, e, o):
  s = Equal.sym(Bool, String.eq(name, path), False{}, e)
  %s : {Lazy.or_else(Lazy.and_then(Bool.not(_), _u => Links.names(toks, name)), _v => Links.uses(rest, toks))
    == True{} : Bool}
  r = Equal.sym(Bool, Links.names(toks, name), True{}, o)
  %r : {Lazy.or_else(_, _v => Links.uses(rest, toks)) == True{} : Bool}
  {==}

def Laws.uses_passes_unaliased_import(name, _line, _sig, _doc, rest, toks):
  s = Equal.sym(Bool, String.eq(name, name), True{}, M3.pub.seq_refl(name))
  %s : {Lazy.or_else(Lazy.and_then(Bool.not(_), _u => Links.names(toks, name)), _v => Links.uses(rest, toks))
    == Links.uses(rest, toks) : Bool}
  {==}

def Laws.uses_passes_unnamed_import(name, _line, _sig, _doc, path, rest, toks, o):
  r = Equal.sym(Bool, Links.names(toks, name), False{}, o)
  %r : {Lazy.or_else(Lazy.and_then(Bool.not(String.eq(name, path)), _u => _), _v => Links.uses(rest, toks))
    == Links.uses(rest, toks) : Bool}
  a = Equal.sym(Bool, Lazy.and_then(Bool.not(String.eq(name, path)), _u => False{}), False{},
    spare.then_f(Bool.not(String.eq(name, path))))
  %a : {Lazy.or_else(_, _v => Links.uses(rest, toks)) == Links.uses(rest, toks) : Bool}
  {==}
