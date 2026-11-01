# proofs of laws/LawNamesEveryItem.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/calls.bend as Calls
import ../src/rules/laws/closed.bend as Closed
import ../src/rules/laws/law.bend as Coverage
import ../src/rules/imports.bend as Imports
import ../src/rules/digest.bend as Digest
import ../laws/LawNamesEveryItem.bend as Laws
import ../laws/UnsafeReportsReachableForeignDefs.bend as L1
import ./lemmas/ImportClosure.bend as M1

# coverage (laws/LawNamesEveryItem.bend)

# an early-exit or is Bool.or
law coverage.or_else:
  for c: Bool
  for -x: Bool
  {Lazy.or_else(c, _u => x) == Bool.or(c, x) : Bool}

def coverage.or_else(c, _x):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# coverage's reading of a file (laws/LawNamesEveryItem.bend)

# the digest's constructors of a type are coverage.ctors_of
law coverage.d_ctors:
  for items: List<&2, Outline.Item>
  {Digest.ctors(items) == Laws.coverage.ctors_of(items) : List<&2, String>}

def coverage.d_ctors(items):
  match items:
    case Nil{}:
      {==}
    case Con{Outline.Item{kk, +name, +line, sig, doc, path}, +rest}:
      match kk:
        case Outline.ICtor{}:
          Equal.cong(List<&2, String>, List<&2, String>, xs => name <> xs, Digest.ctors(rest),
            Laws.coverage.ctors_of(rest), coverage.d_ctors(rest))
        case Outline.IImport{}:
          {==}
        case Outline.IDef{}:
          {==}
        case Outline.ILaw{}:
          {==}
        case Outline.IType{}:
          {==}
        case Outline.ILocal{}:
          {==}

# the digest's alias lookup is coverage.alias
law coverage.d_alias:
  for items: List<&2, Outline.Item>
  for +name: String
  for +from: String
  {Digest.alias_path(Digest.aliases(items, from), name) == Laws.coverage.alias(items, name, from) : Maybe<&2, String>}

def coverage.d_alias(items, name, from):
  match items:
    case Nil{}:
      {==}
    case Con{Outline.Item{kk, +nm, line, sig, doc, +path}, +rest}:
      match kk:
        case Outline.IImport{}:
          Equal.cong(Maybe<&2, String>, Maybe<&2, String>,
            mm => Bool.pick(Maybe<&2, String>, String.eq(nm, name), Some{Imports.resolve(from, path)}, mm),
            Digest.alias_path(Digest.aliases(rest, from), name), Laws.coverage.alias(rest, name, from),
            coverage.d_alias(rest, name, from))
        case Outline.IDef{}:
          coverage.d_alias(rest, name, from)
        case Outline.ILaw{}:
          coverage.d_alias(rest, name, from)
        case Outline.IType{}:
          coverage.d_alias(rest, name, from)
        case Outline.ICtor{}:
          coverage.d_alias(rest, name, from)
        case Outline.ILocal{}:
          coverage.d_alias(rest, name, from)

# an item behind an alias, onto the others, is coverage.behind onto them
law coverage.d_aliased:
  for mm: Maybe<&2, String>
  for -name: String
  for -more: List<&2, Digest.Mention>
  {Digest.aliased(mm, name, more) == List.append(&2, Digest.Mention, Laws.coverage.behind(mm, name), more)
    : List<&2, Digest.Mention>}

def coverage.d_aliased(mm, _name, _more):
  match mm:
    case None{}:
      {==}
    case Some{_pp}:
      {==}

# what the digest makes of a use's target is coverage.target, onto the others
law coverage.d_target:
  for tt: Bind.Target
  for +items: List<&2, Outline.Item>
  for +file: String
  for +more: List<&2, Digest.Mention>
  {Digest.target(tt, Digest.aliases(items, file), file, more)
    == List.append(&2, Digest.Mention, Laws.coverage.target(tt, items, file), more) : List<&2, Digest.Mention>}

def coverage.d_target(tt, items, file, more):
  match tt:
    case Bind.TLocal{_l, _c}:
      {==}
    case Bind.TItem{_n}:
      {==}
    case Bind.TQual{+al, +name}:
      %Equal.sym(Maybe<&2, String>, Digest.alias_path(Digest.aliases(items, file), al),
          Laws.coverage.alias(items, al, file), coverage.d_alias(items, al, file)) :
        {Digest.aliased(_, name, more)
          == List.append(&2, Digest.Mention, Laws.coverage.behind(Laws.coverage.alias(items, al, file), name), more)
          : List<&2, Digest.Mention>}
      coverage.d_aliased(Laws.coverage.alias(items, al, file), name, more)
    case Bind.TFree{}:
      {==}

# a law's span, when the law binds, then the rest: the line is in one of them
# exactly when it is in the span of a binding law or in the rest
law coverage.d_span:
  for bb: Bool
  for +from: U32
  for +upto: U32
  for +rest: List<&2, Digest.Span>
  for +ln: U32
  {Digest.within(Bool.pick(List<&2, Digest.Span>, bb, Digest.Span{from, upto} <> rest, rest), ln)
    == Bool.or(Bool.and(bb, Bool.and(U32.is_le(from, ln), U32.is_le(ln, upto))), Digest.within(rest, ln)) : Bool}

def coverage.d_span(bb, from, upto, rest, ln):
  match bb:
    case True{}:
      coverage.or_else(Bool.and(U32.is_le(from, ln), U32.is_le(ln, upto)), Digest.within(rest, ln))
    case False{}:
      {==}

# the digest's test of a line against the spans is coverage.in_law
law coverage.d_within:
  for root: Tree.Node
  for +ln: U32
  {Digest.within(Digest.spans(root), ln) == Laws.coverage.in_law(root, ln) : Bool}

def coverage.d_within(root, ln):
  match root:
    case Tree.NCons{hd, +rest}:
      match hd:
        case Tree.Stmt{kk, +kids, +body}:
          match kk:
            case Tree.SLaw{}:
              +last = Tree.line.of(List.head(&2, Lex.Tok, Tree.leaves.go(body, [])))
              Equal.trans(Bool,
                Digest.within(Bool.pick(List<&2, Digest.Span>, Closed.binds(body),
                  Digest.Span{Tree.line(kids), last} <> Digest.spans(rest), Digest.spans(rest)), ln),
                Bool.or(Bool.and(Closed.binds(body), Bool.and(U32.is_le(Tree.line(kids), ln), U32.is_le(ln, last))),
                  Digest.within(Digest.spans(rest), ln)),
                Bool.or(Bool.and(Closed.binds(body), Bool.and(U32.is_le(Tree.line(kids), ln), U32.is_le(ln, last))),
                  Laws.coverage.in_law(rest, ln)),
                coverage.d_span(Closed.binds(body), Tree.line(kids), last, Digest.spans(rest), ln),
                Equal.cong(Bool, Bool,
                  b => Bool.or(Bool.and(Closed.binds(body),
                    Bool.and(U32.is_le(Tree.line(kids), ln), U32.is_le(ln, last))), b),
                  Digest.within(Digest.spans(rest), ln), Laws.coverage.in_law(rest, ln), coverage.d_within(rest, ln)))
            case Tree.SDef{}:
              coverage.d_within(rest, ln)
            case Tree.SType{}:
              coverage.d_within(rest, ln)
            case Tree.SImport{}:
              coverage.d_within(rest, ln)
            case Tree.SCase{}:
              coverage.d_within(rest, ln)
            case Tree.SFor{}:
              coverage.d_within(rest, ln)
            case Tree.SLet{}:
              coverage.d_within(rest, ln)
            case Tree.STerm{}:
              coverage.d_within(rest, ln)
        case Tree.Leaf{_tok}:
          coverage.d_within(rest, ln)
        case Tree.Group{_open, _kids, _close}:
          coverage.d_within(rest, ln)
        case Tree.NNil{}:
          coverage.d_within(rest, ln)
        case Tree.NCons{_h, _t}:
          coverage.d_within(rest, ln)
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_open, _kids, _close}:
      {==}
    case Tree.Stmt{_kk, _kids, _body}:
      {==}
    case Tree.NNil{}:
      {==}

# stopping on a negated test is picking on the test
law coverage.d_stop:
  for bb: Bool
  for -x: List<&2, Digest.Mention>
  for -y: List<&2, Digest.Mention>
  {Lazy.stop(List<&2, Digest.Mention>, Bool.not(bb), y, _u => x) == Bool.pick(List<&2, Digest.Mention>, bb, x, y)
    : List<&2, Digest.Mention>}

def coverage.d_stop(bb, _x, _y):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# the digest's mentions of the uses are coverage.said
law coverage.d_mentions:
  for us: List<&2, Bind.Use>
  for +root: Tree.Node
  for +items: List<&2, Outline.Item>
  for +file: String
  {Digest.mentions(us, Digest.spans(root), Digest.aliases(items, file), file)
    == Laws.coverage.said(us, root, items, file) : List<&2, Digest.Mention>}

def coverage.d_mentions(us, root, items, file):
  match us:
    case Nil{}:
      {==}
    case Con{Bind.Use{+nn, +ln, +cc, +tt}, +rest}:
      +mm = Digest.mentions(rest, Digest.spans(root), Digest.aliases(items, file), file)
      %coverage.d_mentions(rest, root, items, file) :
        {Digest.mentions(Bind.Use{nn, ln, cc, tt} <> rest, Digest.spans(root), Digest.aliases(items, file), file)
          == Bool.pick(List<&2, Digest.Mention>, Laws.coverage.in_law(root, ln),
            List.append(&2, Digest.Mention, Laws.coverage.target(tt, items, file), _), _) : List<&2, Digest.Mention>}
      %coverage.d_target(tt, items, file, mm) :
        {Digest.mentions(Bind.Use{nn, ln, cc, tt} <> rest, Digest.spans(root), Digest.aliases(items, file), file)
          == Bool.pick(List<&2, Digest.Mention>, Laws.coverage.in_law(root, ln), _, mm) : List<&2, Digest.Mention>}
      %coverage.d_within(root, ln) :
        {Digest.mentions(Bind.Use{nn, ln, cc, tt} <> rest, Digest.spans(root), Digest.aliases(items, file), file)
          == Bool.pick(List<&2, Digest.Mention>, _, Digest.target(tt, Digest.aliases(items, file), file, mm), mm)
          : List<&2, Digest.Mention>}
      coverage.d_stop(Digest.within(Digest.spans(root), ln), Digest.target(tt, Digest.aliases(items, file), file, mm),
        mm)

# what a file's laws name, in the digest, is coverage.said when it is a
# LAWS.bend, else nothing
law coverage.d_stated:
  for bb: Bool
  for +tree: Tree.Node
  for bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +file: String
  {Digest.stated(bb, tree, bound, Digest.aliases(items, file), file)
    == Bool.pick(List<&2, Digest.Mention>, bb, Laws.coverage.said(Laws.coverage.uses(bound), tree, items, file), [])
    : List<&2, Digest.Mention>}

def coverage.d_stated(bb, tree, bound, items, file):
  match bb:
    case True{}:
      match bound:
        case Bind.Bound{_bs, us, _scs}:
          coverage.d_mentions(us, tree, items, file)
    case False{}:
      {==}

# coverage by reach (laws/LawNamesEveryItem.bend). The rule builds its graph as edges; the
# laws' graph is digests, whose edges are the rule's. So the walk the rule
# takes is unsafe.closure of the laws' graph, and the unsafe laws give the
# rest.

# the rule's search of a type's constructors is reach.any
law reach.any_eq:
  for ns: List<&2, String>
  for +cl: List<&2, String>
  for +pp: String
  {Coverage.any_item(ns, cl, pp) == Laws.reach.any(ns, cl, pp) : Bool}

def reach.any_eq(ns, cl, pp):
  match ns:
    case Nil{}:
      {==}
    case Con{+name, +rest}:
      %reach.any_eq(rest, cl, pp) :
        {Coverage.any_item(name <> rest, cl, pp)
          == Bool.or(Imports.has(cl, Laws.reach.key(pp, name)), _) : Bool}
      coverage.or_else(Imports.has(cl, Coverage.key(pp, name)), Coverage.any_item(rest, cl, pp))

# the rule's gaps of a file are reach.gaps
law reach.gaps_eq:
  for ts: List<&2, Digest.Top>
  for +cl: List<&2, String>
  for +pp: String
  for +path: String
  {Coverage.gaps(ts, cl, pp, path) == Laws.reach.gaps(ts, cl, pp, path) : List<&2, F.Finding>}

def reach.gaps_eq(ts, cl, pp, path):
  match ts:
    case Nil{}:
      {==}
    case Con{Digest.Top{kk, +name, +line, +cs, calls}, +rest}:
      match kk:
        case Outline.IDef{}:
          %reach.gaps_eq(rest, cl, pp, path) :
            {Coverage.gaps(Digest.Top{Outline.IDef{}, name, line, cs, calls} <> rest, cl, pp, path)
              == Bool.pick(List<&2, F.Finding>,
                Bool.or(String.contains(name, "."), Imports.has(cl, Laws.reach.key(pp, name))), _,
                F.Finding{path, line, 0, 0, "coverage", "No quantified law reaches def " ++ name ++ "."} <> _)
              : List<&2, F.Finding>}
          Equal.cong(Bool, List<&2, F.Finding>,
            bb => Bool.pick(List<&2, F.Finding>, bb, Coverage.gaps(rest, cl, pp, path),
              F.Finding{path, line, 0, 0, "coverage", "No quantified law reaches def " ++ name ++ "."}
                <> Coverage.gaps(rest, cl, pp, path)),
            Lazy.or_else(String.contains(name, "."), _u => Imports.has(cl, Coverage.key(pp, name))),
            Bool.or(String.contains(name, "."), Imports.has(cl, Coverage.key(pp, name))),
            coverage.or_else(String.contains(name, "."), Imports.has(cl, Coverage.key(pp, name))))
        case Outline.IType{}:
          %reach.any_eq(cs, cl, pp) :
            {Coverage.gaps(Digest.Top{Outline.IType{}, name, line, cs, calls} <> rest, cl, pp, path)
              == Bool.pick(List<&2, F.Finding>, Bool.or(Imports.has(cl, Laws.reach.key(pp, name)), _),
                Laws.reach.gaps(rest, cl, pp, path),
                F.Finding{path, line, 0, 0, "coverage",
                    "No quantified law reaches type " ++ name ++ " or any of its constructors."}
                  <> Laws.reach.gaps(rest, cl, pp, path)) : List<&2, F.Finding>}
          %reach.gaps_eq(rest, cl, pp, path) :
            {Coverage.gaps(Digest.Top{Outline.IType{}, name, line, cs, calls} <> rest, cl, pp, path)
              == Bool.pick(List<&2, F.Finding>,
                Bool.or(Imports.has(cl, Laws.reach.key(pp, name)), Coverage.any_item(cs, cl, pp)), _,
                F.Finding{path, line, 0, 0, "coverage",
                    "No quantified law reaches type " ++ name ++ " or any of its constructors."}
                  <> _) : List<&2, F.Finding>}
          Equal.cong(Bool, List<&2, F.Finding>,
            bb => Bool.pick(List<&2, F.Finding>, bb, Coverage.gaps(rest, cl, pp, path),
              F.Finding{path, line, 0, 0, "coverage",
                  "No quantified law reaches type " ++ name ++ " or any of its constructors."}
                <> Coverage.gaps(rest, cl, pp, path)),
            Lazy.or_else(Imports.has(cl, Coverage.key(pp, name)), _u => Coverage.any_item(cs, cl, pp)),
            Bool.or(Imports.has(cl, Coverage.key(pp, name)), Coverage.any_item(cs, cl, pp)),
            coverage.or_else(Imports.has(cl, Coverage.key(pp, name)), Coverage.any_item(cs, cl, pp)))
        case Outline.IImport{}:
          reach.gaps_eq(rest, cl, pp, path)
        case Outline.ILaw{}:
          reach.gaps_eq(rest, cl, pp, path)
        case Outline.ICtor{}:
          reach.gaps_eq(rest, cl, pp, path)
        case Outline.ILocal{}:
          reach.gaps_eq(rest, cl, pp, path)

# the rule's walk over the files is reach.files
law reach.files_eq:
  for fs: List<&2, Digest.Digest>
  for +cl: List<&2, String>
  {Coverage.check.go(fs, cl) == Laws.reach.files(fs, cl) : List<&2, F.Finding>}

def reach.files_eq(fs, cl):
  match fs:
    case Nil{}:
      {==}
    case Con{Digest.Digest{+path, +norm, dir, is_laws, is_law_file, exempt, +tops, says, deps, unsafes, laws}, +rest}:
      match exempt:
        case True{}:
          reach.files_eq(rest, cl)
        case False{}:
          %reach.files_eq(rest, cl) :
            {Coverage.check.go(Digest.Digest{path, norm, dir, is_laws, is_law_file, False{}, tops, says, deps, unsafes,
              laws} <> rest, cl)
              == List.append(&2, F.Finding, Laws.reach.gaps(tops, cl, norm, path), _) : List<&2, F.Finding>}
          %reach.gaps_eq(tops, cl, norm, path) :
            {Coverage.check.go(Digest.Digest{path, norm, dir, is_laws, is_law_file, False{}, tops, says, deps, unsafes,
              laws} <> rest, cl)
              == List.append(&2, F.Finding, _, Coverage.check.go(rest, cl)) : List<&2, F.Finding>}
          {==}

# the rule builds its graph exactly when some digest is a LAWS.bend
law reach.first:
  for +fs: List<&2, Digest.Digest>
  for ds: List<&2, Digest.Digest>
  {Coverage.check.first(fs, Coverage.law_dirs(ds))
    == Bool.pick(List<&2, F.Finding>, Laws.coverage.lawful(ds),
      Coverage.check.go(fs, Coverage.reached(Coverage.graph(fs))), []) : List<&2, F.Finding>}

def reach.first(fs, ds):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, +rest}:
      match is_laws:
        case True{}:
          {==}
        case False{}:
          reach.first(fs, rest)

# the rule's keys are reach.keys
law reach.keys_eq:
  for ms: List<&2, Digest.Mention>
  {Laws.reach.keys(ms) == Coverage.keys(ms) : List<&2, String>}

def reach.keys_eq(ms):
  match ms:
    case Nil{}:
      {==}
    case Con{Digest.Mention{+pp, +name}, +rest}:
      Equal.cong(List<&2, String>, List<&2, String>, xs => Laws.reach.key(pp, name) <> xs, Laws.reach.keys(rest),
        Coverage.keys(rest), reach.keys_eq(rest))

# what the rule gathers of the laws is reach.named
law reach.named_eq:
  for ds: List<&2, Digest.Digest>
  {Laws.reach.named(ds) == Coverage.named(ds) : List<&2, Digest.Mention>}

def reach.named_eq(ds):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, +says, deps, unsafes, laws}, +rest}:
      match is_laws:
        case True{}:
          Equal.cong(List<&2, Digest.Mention>, List<&2, Digest.Mention>,
            xs => List.append(&2, Digest.Mention, says, xs), Laws.reach.named(rest), Coverage.named(rest),
            reach.named_eq(rest))
        case False{}:
          reach.named_eq(rest)

# a type's constructors as nodes have the rule's edges
law reach.ctors_eq:
  for cs: List<&2, String>
  for +pp: String
  for more: List<&2, Digest.Digest>
  {Digest.edges(Laws.reach.ctors(cs, pp, more)) == Coverage.ctor_nodes(cs, pp, Digest.edges(more))
    : List<&2, Imports.Edge>}

def reach.ctors_eq(cs, pp, more):
  match cs:
    case Nil{}:
      {==}
    case Con{+name, +rest}:
      Equal.cong(List<&2, Imports.Edge>, List<&2, Imports.Edge>, xs => Imports.Edge{Laws.reach.key(pp, name), []} <> xs,
        Digest.edges(Laws.reach.ctors(rest, pp, more)), Coverage.ctor_nodes(rest, pp, Digest.edges(more)),
        reach.ctors_eq(rest, pp, more))

# a file's items as nodes have the rule's edges
law reach.nodes_eq:
  for ts: List<&2, Digest.Top>
  for +pp: String
  for +more: List<&2, Digest.Digest>
  {Digest.edges(Laws.reach.nodes(ts, pp, more)) == Coverage.nodes(ts, pp, Digest.edges(more)) : List<&2, Imports.Edge>}

def reach.nodes_eq(ts, pp, more):
  match ts:
    case Nil{}:
      {==}
    case Con{Digest.Top{kk, +name, line, +cs, +calls}, +rest}:
      match kk:
        case Outline.IDef{}:
          %reach.nodes_eq(rest, pp, more) :
            {Digest.edges(Laws.reach.nodes(Digest.Top{Outline.IDef{}, name, line, cs, calls} <> rest, pp, more))
              == Imports.Edge{Coverage.key(pp, name), Coverage.keys(calls)} <> _ : List<&2, Imports.Edge>}
          %reach.keys_eq(calls) :
            {Digest.edges(Laws.reach.nodes(Digest.Top{Outline.IDef{}, name, line, cs, calls} <> rest, pp, more))
              == Imports.Edge{Coverage.key(pp, name), _} <> Digest.edges(Laws.reach.nodes(rest, pp, more))
              : List<&2, Imports.Edge>}
          {==}
        case Outline.IType{}:
          %reach.nodes_eq(rest, pp, more) :
            {Digest.edges(Laws.reach.nodes(Digest.Top{Outline.IType{}, name, line, cs, calls} <> rest, pp, more))
              == Imports.Edge{Coverage.key(pp, name), []} <> Coverage.ctor_nodes(cs, pp, _) : List<&2, Imports.Edge>}
          Equal.cong(List<&2, Imports.Edge>, List<&2, Imports.Edge>,
            xs => Imports.Edge{Laws.reach.key(pp, name), []} <> xs,
            Digest.edges(Laws.reach.ctors(cs, pp, Laws.reach.nodes(rest, pp, more))),
            Coverage.ctor_nodes(cs, pp, Digest.edges(Laws.reach.nodes(rest, pp, more))),
            reach.ctors_eq(cs, pp, Laws.reach.nodes(rest, pp, more)))
        case Outline.IImport{}:
          reach.nodes_eq(rest, pp, more)
        case Outline.ILaw{}:
          reach.nodes_eq(rest, pp, more)
        case Outline.ICtor{}:
          reach.nodes_eq(rest, pp, more)
        case Outline.ILocal{}:
          reach.nodes_eq(rest, pp, more)

# every file's items as nodes have the rule's edges
law reach.items_eq:
  for ds: List<&2, Digest.Digest>
  {Digest.edges(Laws.reach.items(ds)) == Coverage.graph.items(ds) : List<&2, Imports.Edge>}

def reach.items_eq(ds):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, +norm, dir, is_laws, is_law_file, exempt, +tops, says, deps, unsafes, laws}, +rest}:
      Equal.trans(List<&2, Imports.Edge>, Digest.edges(Laws.reach.nodes(tops, norm, Laws.reach.items(rest))),
        Coverage.nodes(tops, norm, Digest.edges(Laws.reach.items(rest))),
        Coverage.nodes(tops, norm, Coverage.graph.items(rest)),
        reach.nodes_eq(tops, norm, Laws.reach.items(rest)),
        Equal.cong(List<&2, Imports.Edge>, List<&2, Imports.Edge>, xs => Coverage.nodes(tops, norm, xs),
          Digest.edges(Laws.reach.items(rest)), Coverage.graph.items(rest), reach.items_eq(rest)))

# the laws' graph has the rule's edges
law reach.graph_eq:
  for +ds: List<&2, Digest.Digest>
  {Digest.edges(Laws.reach.graph(ds)) == Coverage.graph(ds) : List<&2, Imports.Edge>}

def reach.graph_eq(ds):
  %reach.items_eq(ds) :
    {Digest.edges(Laws.reach.graph(ds)) == Imports.Edge{"", Coverage.keys(Coverage.named(ds))} <> _
      : List<&2, Imports.Edge>}
  %reach.keys_eq(Coverage.named(ds)) :
    {Digest.edges(Laws.reach.graph(ds))
      == Imports.Edge{"", _} <> Digest.edges(Laws.reach.items(ds)) : List<&2, Imports.Edge>}
  %reach.named_eq(ds) :
    {Digest.edges(Laws.reach.graph(ds))
      == Imports.Edge{"", Laws.reach.keys(_)} <> Digest.edges(Laws.reach.items(ds)) : List<&2, Imports.Edge>}
  {==}

# as many edges as digests
law reach.len_edges:
  for ds: List<&2, Digest.Digest>
  {List.length(&2, Imports.Edge, Digest.edges(ds)) == List.length(&2, Digest.Digest, ds) : Nat}

def reach.len_edges(ds):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, +rest}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Imports.Edge, Digest.edges(rest)),
        List.length(&2, Digest.Digest, rest), reach.len_edges(rest))

# the rule's walk is the closure of the laws' graph
law reach.closure_eq:
  for +ds: List<&2, Digest.Digest>
  {Coverage.reached(Coverage.graph(ds)) == Laws.reach.closure(ds) : List<&2, String>}

def reach.closure_eq(ds):
  +gg = Laws.reach.graph(ds)
  %reach.graph_eq(ds) : {Coverage.reached(_) == Laws.reach.closure(ds) : List<&2, String>}
  %reach.len_edges(gg) :
    {Coverage.reached(Digest.edges(gg))
      == Imports.closure.go(Digest.edges(gg), Imports.paths(Digest.edges(gg)), _, "") : List<&2, String>}
  {==}

def Laws.coverage_reach(ds):
  %reach.closure_eq(ds) :
    {Coverage.check(ds)
      == Bool.pick(List<&2, F.Finding>, Laws.coverage.lawful(ds), Laws.reach.files(ds, _), []) : List<&2, F.Finding>}
  %reach.files_eq(ds, Coverage.reached(Coverage.graph(ds))) :
    {Coverage.check(ds) == Bool.pick(List<&2, F.Finding>, Laws.coverage.lawful(ds), _, []) : List<&2, F.Finding>}
  reach.first(ds, ds)

def Laws.reach_from(ds):
  L1.unsafe_from(Laws.reach.graph(ds), "")

def Laws.reach_shut(ds):
  L1.unsafe_shut(Laws.reach.graph(ds), "")

def Laws.reach_least(ds, ss, kk, hf, hs, hk):
  L1.unsafe_least(Laws.reach.graph(ds), "", ss, kk, hf, hs, hk)

# stopping on a test is picking on it
law reach.stop_pick:
  for bb: Bool
  for -x: List<&2, Bind.Use>
  for -y: List<&2, Bind.Use>
  {Lazy.stop(List<&2, Bind.Use>, bb, x, _u => y) == Bool.pick(List<&2, Bind.Use>, bb, x, y) : List<&2, Bind.Use>}

def reach.stop_pick(bb, _x, _y):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# the digest's uses before a line are reach.before
law reach.before_eq:
  for us: List<&2, Bind.Use>
  for +at: U32
  {Digest.before(us, at) == Laws.reach.before(us, at) : List<&2, Bind.Use>}

def reach.before_eq(us, at):
  match us:
    case Nil{}:
      {==}
    case Con{Bind.Use{+nm, +ln, +cc, +tt}, +rest}:
      %reach.before_eq(rest, at) :
        {Digest.before(Bind.Use{nm, ln, cc, tt} <> rest, at)
          == Bool.pick(List<&2, Bind.Use>, U32.is_le(at, ln), [], Bind.Use{nm, ln, cc, tt} <> _) : List<&2, Bind.Use>}
      reach.stop_pick(U32.is_le(at, ln), [], Bind.Use{nm, ln, cc, tt} <> Digest.before(rest, at))

# the digest's uses from a line on are reach.after
law reach.after_eq:
  for us: List<&2, Bind.Use>
  for +at: U32
  {Digest.after(us, at) == Laws.reach.after(us, at) : List<&2, Bind.Use>}

def reach.after_eq(us, at):
  match us:
    case Nil{}:
      {==}
    case Con{Bind.Use{+nm, +ln, +cc, +tt}, +rest}:
      %reach.after_eq(rest, at) :
        {Digest.after(Bind.Use{nm, ln, cc, tt} <> rest, at)
          == Bool.pick(List<&2, Bind.Use>, U32.is_le(at, ln), Bind.Use{nm, ln, cc, tt} <> rest, _) : List<&2, Bind.Use>}
      reach.stop_pick(U32.is_le(at, ln), Bind.Use{nm, ln, cc, tt} <> rest, Digest.after(rest, at))

# the digest's next item line is reach.next
law reach.next_eq:
  for items: List<&2, Outline.Item>
  {Digest.next_line(items) == Laws.reach.next(items) : Maybe<&2, U32>}

def reach.next_eq(items):
  match items:
    case Nil{}:
      {==}
    case Con{Outline.Item{kk, name, line, sig, doc, path}, +rest}:
      match kk:
        case Outline.ICtor{}:
          reach.next_eq(rest)
        case Outline.IImport{}:
          {==}
        case Outline.IDef{}:
          {==}
        case Outline.ILaw{}:
          {==}
        case Outline.IType{}:
          {==}
        case Outline.ILocal{}:
          {==}

# the uses an item takes, in the digest, are reach.upto
law reach.upto_m:
  for us: List<&2, Bind.Use>
  for mm: Maybe<&2, U32>
  {Digest.upto(us, mm) == Laws.reach.upto(us, mm) : List<&2, Bind.Use>}

def reach.upto_m(us, mm):
  match mm:
    case None{}:
      {==}
    case Some{at}:
      reach.before_eq(us, at)

# the uses an item leaves, in the digest, are reach.past
law reach.past_m:
  for us: List<&2, Bind.Use>
  for mm: Maybe<&2, U32>
  {Digest.past(us, mm) == Laws.reach.past(us, mm) : List<&2, Bind.Use>}

def reach.past_m(us, mm):
  match mm:
    case None{}:
      {==}
    case Some{at}:
      reach.after_eq(us, at)

# the uses an item takes, in the digest, are reach.upto of the next line
law reach.upto_eq:
  for +us: List<&2, Bind.Use>
  for +rest: List<&2, Outline.Item>
  {Digest.upto(us, Digest.next_line(rest)) == Laws.reach.upto(us, Laws.reach.next(rest)) : List<&2, Bind.Use>}

def reach.upto_eq(us, rest):
  %reach.next_eq(rest) : {Digest.upto(us, Digest.next_line(rest)) == Laws.reach.upto(us, _) : List<&2, Bind.Use>}
  reach.upto_m(us, Digest.next_line(rest))

# the uses an item leaves, in the digest, are reach.past of the next line
law reach.past_eq:
  for +us: List<&2, Bind.Use>
  for +rest: List<&2, Outline.Item>
  {Digest.past(us, Digest.next_line(rest)) == Laws.reach.past(us, Laws.reach.next(rest)) : List<&2, Bind.Use>}

def reach.past_eq(us, rest):
  %reach.next_eq(rest) : {Digest.past(us, Digest.next_line(rest)) == Laws.reach.past(us, _) : List<&2, Bind.Use>}
  reach.past_m(us, Digest.next_line(rest))

# what the digest makes of the uses is reach.calls
law reach.calls_eq:
  for us: List<&2, Bind.Use>
  for +all: List<&2, Outline.Item>
  for +file: String
  {Digest.called(us, Digest.aliases(all, file), file) == Laws.reach.calls(us, all, file) : List<&2, Digest.Mention>}

def reach.calls_eq(us, all, file):
  match us:
    case Nil{}:
      {==}
    case Con{Bind.Use{nn, ll, cc, +tt}, +rest}:
      Equal.trans(List<&2, Digest.Mention>,
        Digest.target(tt, Digest.aliases(all, file), file, Digest.called(rest, Digest.aliases(all, file), file)),
        List.append(&2, Digest.Mention, Laws.coverage.target(tt, all, file),
          Digest.called(rest, Digest.aliases(all, file), file)),
        List.append(&2, Digest.Mention, Laws.coverage.target(tt, all, file), Laws.reach.calls(rest, all, file)),
        coverage.d_target(tt, all, file, Digest.called(rest, Digest.aliases(all, file), file)),
        Equal.cong(List<&2, Digest.Mention>, List<&2, Digest.Mention>,
          xs => List.append(&2, Digest.Mention, Laws.coverage.target(tt, all, file), xs),
          Digest.called(rest, Digest.aliases(all, file), file), Laws.reach.calls(rest, all, file),
          reach.calls_eq(rest, all, file)))

# a def's name joins the digest's proofs as it joins reach.proofs
law reach.proof_push:
  for mm: Maybe<&2, String>
  for +kids: Tree.Node
  for body: Tree.Node
  for ds: List<&2, Calls.Def>
  for ss: List<&2, String>
  for e: {Digest.proofs(ds) == ss : List<&2, String>}
  {Digest.proofs(Calls.defs.push(mm, kids, body, ds)) == Laws.reach.proof(mm, Calls.proof(kids), ss)
    : List<&2, String>}

def reach.proof_push(mm, kids, body, ds, _ss, e):
  match mm:
    case None{}:
      e
    case Some{nn}:
      %e : {Digest.proofs(Calls.Def{nn, kids, body} <> ds)
        == Bool.pick(List<&2, String>, Calls.proof(kids), nn <> _, _) : List<&2, String>}
      {==}

# the digest's proofs are reach.proofs
law reach.proofs_eq:
  for root: Tree.Node
  {Digest.proofs(Calls.defs(root)) == Laws.reach.proofs(root) : List<&2, String>}

def reach.proofs_eq(root):
  match root:
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{o, gk, cl}:
      {==}
    case Tree.Stmt{kind, sk, sb}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          reach.proofs_eq(rest)
        case Tree.Group{o, gk, cl}:
          reach.proofs_eq(rest)
        case Tree.Stmt{kind, +kids, b}:
          match kind:
            case Tree.SDef{}:
              reach.proof_push(Bind.declared(kids), kids, b, Calls.defs(rest), Laws.reach.proofs(rest),
                reach.proofs_eq(rest))
            case Tree.SType{}:
              reach.proofs_eq(rest)
            case Tree.SLaw{}:
              reach.proofs_eq(rest)
            case Tree.SImport{}:
              reach.proofs_eq(rest)
            case Tree.SCase{}:
              reach.proofs_eq(rest)
            case Tree.SFor{}:
              reach.proofs_eq(rest)
            case Tree.SLet{}:
              reach.proofs_eq(rest)
            case Tree.STerm{}:
              reach.proofs_eq(rest)
        case Tree.NNil{}:
          reach.proofs_eq(rest)
        case Tree.NCons{nh, nt}:
          reach.proofs_eq(rest)

# the digest's defs and types, with their calls, are reach.tops
law reach.tops_eq:
  for items: List<&2, Outline.Item>
  for +all: List<&2, Outline.Item>
  for +us: List<&2, Bind.Use>
  for +file: String
  for +ps: List<&2, String>
  {Digest.ranged(items, us, Digest.aliases(all, file), file, ps) == Laws.reach.tops(items, all, us, file, ps)
    : List<&2, Digest.Top>}

def reach.tops_eq(items, all, us, file, ps):
  match items:
    case Nil{}:
      {==}
    case Con{Outline.Item{kk, +name, +line, +sig, +doc, +path}, +rest}:
      match kk:
        case Outline.IDef{}:
          +as = Digest.aliases(all, file)
          +nx = Digest.next_line(rest)
          +hit = Imports.has(ps, name)
          %reach.past_eq(us, rest) :
            {Digest.ranged(Outline.Item{Outline.IDef{}, name, line, sig, doc, path} <> rest, us, as, file, ps)
              == Bool.pick(List<&2, Digest.Top>, hit, Laws.reach.tops(rest, all, _, file, ps),
                Digest.Top{Outline.IDef{}, name, line, [],
                  Laws.reach.calls(Laws.reach.upto(us, Laws.reach.next(rest)), all, file)}
                  <> Laws.reach.tops(rest, all, _, file, ps)) : List<&2, Digest.Top>}
          %reach.upto_eq(us, rest) :
            {Digest.ranged(Outline.Item{Outline.IDef{}, name, line, sig, doc, path} <> rest, us, as, file, ps)
              == Bool.pick(List<&2, Digest.Top>, hit, Laws.reach.tops(rest, all, Digest.past(us, nx), file, ps),
                Digest.Top{Outline.IDef{}, name, line, [], Laws.reach.calls(_, all, file)}
                  <> Laws.reach.tops(rest, all, Digest.past(us, nx), file, ps)) : List<&2, Digest.Top>}
          %reach.calls_eq(Digest.upto(us, nx), all, file) :
            {Digest.ranged(Outline.Item{Outline.IDef{}, name, line, sig, doc, path} <> rest, us, as, file, ps)
              == Bool.pick(List<&2, Digest.Top>, hit, Laws.reach.tops(rest, all, Digest.past(us, nx), file, ps),
                Digest.Top{Outline.IDef{}, name, line, [], _}
                  <> Laws.reach.tops(rest, all, Digest.past(us, nx), file, ps)) : List<&2, Digest.Top>}
          %reach.tops_eq(rest, all, Digest.past(us, nx), file, ps) :
            {Digest.ranged(Outline.Item{Outline.IDef{}, name, line, sig, doc, path} <> rest, us, as, file, ps)
              == Bool.pick(List<&2, Digest.Top>, hit, _,
                Digest.Top{Outline.IDef{}, name, line, [], Digest.called(Digest.upto(us, nx), as, file)} <> _)
              : List<&2, Digest.Top>}
          {==}
        case Outline.IType{}:
          +as = Digest.aliases(all, file)
          +nx = Digest.next_line(rest)
          %reach.past_eq(us, rest) :
            {Digest.ranged(Outline.Item{Outline.IType{}, name, line, sig, doc, path} <> rest, us, as, file, ps)
              == Digest.Top{Outline.IType{}, name, line, Laws.coverage.ctors_of(rest),
                Laws.reach.calls(Laws.reach.upto(us, Laws.reach.next(rest)), all, file)}
                <> Laws.reach.tops(rest, all, _, file, ps) : List<&2, Digest.Top>}
          %reach.upto_eq(us, rest) :
            {Digest.ranged(Outline.Item{Outline.IType{}, name, line, sig, doc, path} <> rest, us, as, file, ps)
              == Digest.Top{Outline.IType{}, name, line, Laws.coverage.ctors_of(rest), Laws.reach.calls(_, all, file)}
                <> Laws.reach.tops(rest, all, Digest.past(us, nx), file, ps) : List<&2, Digest.Top>}
          %reach.calls_eq(Digest.upto(us, nx), all, file) :
            {Digest.ranged(Outline.Item{Outline.IType{}, name, line, sig, doc, path} <> rest, us, as, file, ps)
              == Digest.Top{Outline.IType{}, name, line, Laws.coverage.ctors_of(rest), _}
                <> Laws.reach.tops(rest, all, Digest.past(us, nx), file, ps) : List<&2, Digest.Top>}
          %coverage.d_ctors(rest) :
            {Digest.ranged(Outline.Item{Outline.IType{}, name, line, sig, doc, path} <> rest, us, as, file, ps)
              == Digest.Top{Outline.IType{}, name, line, _, Digest.called(Digest.upto(us, nx), as, file)}
                <> Laws.reach.tops(rest, all, Digest.past(us, nx), file, ps) : List<&2, Digest.Top>}
          %reach.tops_eq(rest, all, Digest.past(us, nx), file, ps) :
            {Digest.ranged(Outline.Item{Outline.IType{}, name, line, sig, doc, path} <> rest, us, as, file, ps)
              == Digest.Top{Outline.IType{}, name, line, Digest.ctors(rest),
                Digest.called(Digest.upto(us, nx), as, file)}
                <> _ : List<&2, Digest.Top>}
          {==}
        case Outline.ICtor{}:
          reach.tops_eq(rest, all, us, file, ps)
        case Outline.IImport{}:
          %reach.past_eq(us, rest) :
            {Digest.ranged(Outline.Item{Outline.IImport{}, name, line, sig, doc, path} <> rest, us,
              Digest.aliases(all, file), file, ps) == Laws.reach.tops(rest, all, _, file, ps) : List<&2, Digest.Top>}
          reach.tops_eq(rest, all, Digest.past(us, Digest.next_line(rest)), file, ps)
        case Outline.ILaw{}:
          %reach.past_eq(us, rest) :
            {Digest.ranged(Outline.Item{Outline.ILaw{}, name, line, sig, doc, path} <> rest, us,
              Digest.aliases(all, file), file, ps) == Laws.reach.tops(rest, all, _, file, ps) : List<&2, Digest.Top>}
          reach.tops_eq(rest, all, Digest.past(us, Digest.next_line(rest)), file, ps)
        case Outline.ILocal{}:
          %reach.past_eq(us, rest) :
            {Digest.ranged(Outline.Item{Outline.ILocal{}, name, line, sig, doc, path} <> rest, us,
              Digest.aliases(all, file), file, ps) == Laws.reach.tops(rest, all, _, file, ps) : List<&2, Digest.Top>}
          reach.tops_eq(rest, all, Digest.past(us, Digest.next_line(rest)), file, ps)

# the digest's uses are coverage.uses
law reach.uses_eq:
  for bb: Bind.Bound
  {Digest.uses.of(bb) == Laws.coverage.uses(bb) : List<&2, Bind.Use>}

def reach.uses_eq(bb):
  match bb:
    case Bind.Bound{_bs, _us, _scs}:
      {==}

def Laws.reach_digest(path, text, toks, tree, bound, items):
  +pp = Imports.norm(path)
  %reach.proofs_eq(tree) :
    {Laws.coverage.view(Digest.of(Src.Src{path, text, toks, tree, bound, items}))
      == Laws.CoverageView{pp, Paths.is_laws(path), Bool.or(Paths.is_law_file(pp), Paths.is_test(pp)),
        Laws.reach.tops(items, items, Laws.coverage.uses(bound), pp, _),
        Bool.pick(List<&2, Digest.Mention>, Paths.is_laws(path),
          Laws.coverage.said(Laws.coverage.uses(bound), tree, items, pp), [])} : Laws.CoverageView}
  %reach.uses_eq(bound) :
    {Laws.coverage.view(Digest.of(Src.Src{path, text, toks, tree, bound, items}))
      == Laws.CoverageView{pp, Paths.is_laws(path), Bool.or(Paths.is_law_file(pp), Paths.is_test(pp)),
        Laws.reach.tops(items, items, _, pp, Digest.proofs(Calls.defs(tree))),
        Bool.pick(List<&2, Digest.Mention>, Paths.is_laws(path),
          Laws.coverage.said(Laws.coverage.uses(bound), tree, items, pp), [])} : Laws.CoverageView}
  %reach.tops_eq(items, items, Digest.uses.of(bound), pp, Digest.proofs(Calls.defs(tree))) :
    {Laws.coverage.view(Digest.of(Src.Src{path, text, toks, tree, bound, items}))
      == Laws.CoverageView{pp, Paths.is_laws(path), Bool.or(Paths.is_law_file(pp), Paths.is_test(pp)), _,
        Bool.pick(List<&2, Digest.Mention>, Paths.is_laws(path),
          Laws.coverage.said(Laws.coverage.uses(bound), tree, items, pp), [])} : Laws.CoverageView}
  %coverage.d_stated(Paths.is_laws(path), tree, bound, items, pp) :
    {Laws.coverage.view(Digest.of(Src.Src{path, text, toks, tree, bound, items}))
      == Laws.CoverageView{pp, Paths.is_laws(path), Bool.or(Paths.is_law_file(pp), Paths.is_test(pp)),
        Digest.ranged(items, Digest.uses.of(bound), Digest.aliases(items, pp), pp, Digest.proofs(Calls.defs(tree))), _}
        : Laws.CoverageView}
  {==}

def Laws.reach_binder(path, text):
  Laws.reach_digest(path, text, Lex.tokens(text), Tree.parse(text),
    Bind.of_tree(Tree.parse(text), String.lines(text)), Outline.of_tokens(text, Lex.tokens(text)))
