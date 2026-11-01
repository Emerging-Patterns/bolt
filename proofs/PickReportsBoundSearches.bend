# proofs of laws/PickReportsBoundSearches.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/lazy/lazy.bend as Lazy
import ../src/paths.bend as Paths
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/correctness/pick.bend as Pick
import ../laws/PickReportsBoundSearches.bend as Laws
import ./lemmas/Pick.bend as M1
import ./lemmas/LawFileExemptions.bend as M2

# A search bound above its pick (laws/PickReportsBoundSearches.bend). The
# rule's reads, cheap and empty agree with the law's reads, same and none by
# induction or one split, and its first, which carries the test, is the law's
# eager first once the carried test is false. Each step of the let's own
# tokens agrees with the law's, so a let gives one finding exactly when the
# law's at holds; the walk and the def walk then add up as thunk's do.

# equal sides give equal ors
law ps.or:
  for -a: Bool
  for -b: Bool
  for -c: Bool
  for -d: Bool
  for e1: {a == b : Bool}
  for e2: {c == d : Bool}
  {Bool.or(a, c) == Bool.or(b, d) : Bool}

def ps.or(a, b, c, d, e1, e2):
  Equal.trans(Bool, Bool.or(a, c), Bool.or(b, c), Bool.or(b, d), Equal.cong(Bool, Bool, x => Bool.or(x, c), a, b, e1),
    Equal.cong(Bool, Bool, y => Bool.or(b, y), c, d, e2))

# the rule's reads is the law's
law ps.reads:
  for nn: Tree.Node
  for +xx: String
  {Pick.search.reads(nn, xx) == Laws.search.reads(nn, xx) : Bool}

def ps.reads(nn, xx):
  match nn:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}:
          {==}
    case Tree.Group{o, +kids, cl}:
      ps.reads(kids, xx)
    case Tree.Stmt{sk, +kids, +body}:
      ps.or(Pick.search.reads(kids, xx), Laws.search.reads(kids, xx), Pick.search.reads(body, xx),
        Laws.search.reads(body, xx), ps.reads(kids, xx), ps.reads(body, xx))
    case Tree.NCons{+h, +t}:
      ps.or(Pick.search.reads(h, xx), Laws.search.reads(h, xx), Pick.search.reads(t, xx), Laws.search.reads(t, xx),
        ps.reads(h, xx), ps.reads(t, xx))
    case Tree.NNil{}:
      {==}

# the rule's first, its test carried, is the law's once the test is false
law ps.first:
  for nn: Tree.Node
  for +xx: String
  for +prev: Tree.Node
  for hit: Bool
  {Pick.search.first(nn, xx, prev, hit) == Bool.pick(Tree.Node, hit, prev, Laws.search.first(nn, xx)) : Tree.Node}

def ps.first(nn, xx, _prev, hit):
  match nn:
    case Tree.NCons{+h, +t}:
      match hit:
        case True{}:
          {==}
        case False{}:
          %ps.reads(h, xx) : {Pick.search.first(t, xx, h, Pick.search.reads(h, xx))
            == Bool.pick(Tree.Node, _, h, Laws.search.first(t, xx)) : Tree.Node}
          ps.first(t, xx, h, Pick.search.reads(h, xx))
    case Tree.Leaf{x}:
      match hit:
        case True{}:
          {==}
        case False{}:
          {==}
    case Tree.Group{x, y, z}:
      match hit:
        case True{}:
          {==}
        case False{}:
          {==}
    case Tree.Stmt{x, y, z}:
      match hit:
        case True{}:
          {==}
        case False{}:
          {==}
    case Tree.NNil{}:
      match hit:
        case True{}:
          {==}
        case False{}:
          {==}

# the rule's cheap is the law's same
law ps.same:
  for nn: Tree.Node
  for +cond: String
  {Pick.search.cheap(nn, cond) == Laws.search.same(nn, cond) : Bool}

def ps.same(nn, cond):
  match nn:
    case Tree.NCons{+h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, l, c}:
              match rest:
                case Tree.NCons{+h2, +r2}:
                  match h2:
                    case Tree.Group{open, +kids, cl}:
                      match open:
                        case Lex.Tok{ko, +o, lo, co}:
                          +here = Bool.and(Bool.and(String.eq(t, "Bool.pick"), String.eq(o, "(")),
                            String.eq(Pick.search.text(Calls.arg(Calls.args(kids), 1n)), cond))
                          Equal.cong(Bool, Bool, x => Bool.or(here, x),
                            Bool.or(Pick.search.cheap(kids, cond), Pick.search.cheap(r2, cond)),
                            Bool.or(Laws.search.same(kids, cond), Laws.search.same(r2, cond)),
                            ps.or(Pick.search.cheap(kids, cond), Laws.search.same(kids, cond),
                              Pick.search.cheap(r2, cond), Laws.search.same(r2, cond), ps.same(kids, cond),
                              ps.same(r2, cond)))
                    case Tree.Leaf{x}:
                      ps.or(Pick.search.cheap(h, cond), Laws.search.same(h, cond), Pick.search.cheap(rest, cond),
                        Laws.search.same(rest, cond), ps.same(h, cond), ps.same(rest, cond))
                    case Tree.Stmt{x, y, z}:
                      ps.or(Pick.search.cheap(h, cond), Laws.search.same(h, cond), Pick.search.cheap(rest, cond),
                        Laws.search.same(rest, cond), ps.same(h, cond), ps.same(rest, cond))
                    case Tree.NNil{}:
                      ps.or(Pick.search.cheap(h, cond), Laws.search.same(h, cond), Pick.search.cheap(rest, cond),
                        Laws.search.same(rest, cond), ps.same(h, cond), ps.same(rest, cond))
                    case Tree.NCons{x, y}:
                      ps.or(Pick.search.cheap(h, cond), Laws.search.same(h, cond), Pick.search.cheap(rest, cond),
                        Laws.search.same(rest, cond), ps.same(h, cond), ps.same(rest, cond))
                case Tree.Leaf{x}:
                  ps.or(Pick.search.cheap(h, cond), Laws.search.same(h, cond), Pick.search.cheap(rest, cond),
                    Laws.search.same(rest, cond), ps.same(h, cond), ps.same(rest, cond))
                case Tree.Group{x, y, z}:
                  ps.or(Pick.search.cheap(h, cond), Laws.search.same(h, cond), Pick.search.cheap(rest, cond),
                    Laws.search.same(rest, cond), ps.same(h, cond), ps.same(rest, cond))
                case Tree.Stmt{x, y, z}:
                  ps.or(Pick.search.cheap(h, cond), Laws.search.same(h, cond), Pick.search.cheap(rest, cond),
                    Laws.search.same(rest, cond), ps.same(h, cond), ps.same(rest, cond))
                case Tree.NNil{}:
                  ps.or(Pick.search.cheap(h, cond), Laws.search.same(h, cond), Pick.search.cheap(rest, cond),
                    Laws.search.same(rest, cond), ps.same(h, cond), ps.same(rest, cond))
        case Tree.Group{x, y, z}:
          ps.or(Pick.search.cheap(h, cond), Laws.search.same(h, cond), Pick.search.cheap(rest, cond),
            Laws.search.same(rest, cond), ps.same(h, cond), ps.same(rest, cond))
        case Tree.Stmt{x, y, z}:
          ps.or(Pick.search.cheap(h, cond), Laws.search.same(h, cond), Pick.search.cheap(rest, cond),
            Laws.search.same(rest, cond), ps.same(h, cond), ps.same(rest, cond))
        case Tree.NNil{}:
          ps.or(Pick.search.cheap(h, cond), Laws.search.same(h, cond), Pick.search.cheap(rest, cond),
            Laws.search.same(rest, cond), ps.same(h, cond), ps.same(rest, cond))
        case Tree.NCons{x, y}:
          ps.or(Pick.search.cheap(h, cond), Laws.search.same(h, cond), Pick.search.cheap(rest, cond),
            Laws.search.same(rest, cond), ps.same(h, cond), ps.same(rest, cond))
    case Tree.Group{o, +kids, cl}:
      ps.same(kids, cond)
    case Tree.Stmt{sk, +kids, +body}:
      ps.or(Pick.search.cheap(kids, cond), Laws.search.same(kids, cond), Pick.search.cheap(body, cond),
        Laws.search.same(body, cond), ps.same(kids, cond), ps.same(body, cond))
    case Tree.Leaf{x}:
      {==}
    case Tree.NNil{}:
      {==}

# the rule's empty is the law's none
law ps.none:
  for nn: Tree.Node
  {Pick.search.empty(nn) == Laws.search.none(nn) : Bool}

def ps.none(nn):
  match nn:
    case Tree.NNil{}:
      {==}
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{x, y, z}:
      {==}
    case Tree.Stmt{x, y, z}:
      {==}
    case Tree.NCons{x, y}:
      {==}

# the rule's verdict on a pick's parts is the law's
law ps.verdict:
  for +t: String
  for +o: String
  for +after: Tree.Node
  for +kids: Tree.Node
  for +xx: String
  for +args: Tree.Node
  {Bool.and(Bool.and(Bool.and(Bool.and(String.eq(t, "Bool.pick"), String.eq(o, "(")), Pick.search.empty(after)),
      Bool.and(Bool.not(Bool.or(Pick.search.reads(Calls.arg(Calls.args(kids), 1n), xx),
        Pick.search.reads(Calls.arg(Calls.args(kids), 2n), xx))), Pick.search.reads(Calls.arg(Calls.args(kids), 3n),
        xx))), Bool.not(Pick.search.cheap(args, Pick.search.text(Calls.arg(Calls.args(kids), 1n)))))
    == Bool.and(Bool.and(Bool.and(Bool.and(String.eq(t, "Bool.pick"), String.eq(o, "(")), Laws.search.none(after)),
      Laws.search.only(Calls.args(kids), xx)),
      Bool.not(Laws.search.same(args, Pick.search.text(Calls.arg(Calls.args(kids), 1n))))) : Bool}

def ps.verdict(t, o, after, kids, xx, args):
  +a1 = Calls.arg(Calls.args(kids), 1n)
  +a2 = Calls.arg(Calls.args(kids), 2n)
  +a3 = Calls.arg(Calls.args(kids), 3n)
  +tc = Pick.search.text(a1)
  +so = Bool.and(String.eq(t, "Bool.pick"), String.eq(o, "("))
  %ps.none(after) : {Bool.and(Bool.and(Bool.and(so, Pick.search.empty(after)),
      Bool.and(Bool.not(Bool.or(Pick.search.reads(a1, xx), Pick.search.reads(a2, xx))), Pick.search.reads(a3, xx))),
      Bool.not(Pick.search.cheap(args, tc)))
    == Bool.and(Bool.and(Bool.and(so, _),
      Bool.and(Bool.not(Bool.or(Laws.search.reads(a1, xx), Laws.search.reads(a2, xx))), Laws.search.reads(a3, xx))),
      Bool.not(Laws.search.same(args, tc))) : Bool}
  %ps.reads(a1, xx) : {Bool.and(Bool.and(Bool.and(so, Pick.search.empty(after)),
      Bool.and(Bool.not(Bool.or(Pick.search.reads(a1, xx), Pick.search.reads(a2, xx))), Pick.search.reads(a3, xx))),
      Bool.not(Pick.search.cheap(args, tc)))
    == Bool.and(Bool.and(Bool.and(so, Pick.search.empty(after)),
      Bool.and(Bool.not(Bool.or(_, Laws.search.reads(a2, xx))), Laws.search.reads(a3, xx))),
      Bool.not(Laws.search.same(args, tc))) : Bool}
  %ps.reads(a2, xx) : {Bool.and(Bool.and(Bool.and(so, Pick.search.empty(after)),
      Bool.and(Bool.not(Bool.or(Pick.search.reads(a1, xx), Pick.search.reads(a2, xx))), Pick.search.reads(a3, xx))),
      Bool.not(Pick.search.cheap(args, tc)))
    == Bool.and(Bool.and(Bool.and(so, Pick.search.empty(after)),
      Bool.and(Bool.not(Bool.or(Pick.search.reads(a1, xx), _)), Laws.search.reads(a3, xx))),
      Bool.not(Laws.search.same(args, tc))) : Bool}
  %ps.reads(a3, xx) : {Bool.and(Bool.and(Bool.and(so, Pick.search.empty(after)),
      Bool.and(Bool.not(Bool.or(Pick.search.reads(a1, xx), Pick.search.reads(a2, xx))), Pick.search.reads(a3, xx))),
      Bool.not(Pick.search.cheap(args, tc)))
    == Bool.and(Bool.and(Bool.and(so, Pick.search.empty(after)),
      Bool.and(Bool.not(Bool.or(Pick.search.reads(a1, xx), Pick.search.reads(a2, xx))), _)),
      Bool.not(Laws.search.same(args, tc))) : Bool}
  %ps.same(args, tc) : {Bool.and(Bool.and(Bool.and(so, Pick.search.empty(after)),
      Bool.and(Bool.not(Bool.or(Pick.search.reads(a1, xx), Pick.search.reads(a2, xx))), Pick.search.reads(a3, xx))),
      Bool.not(Pick.search.cheap(args, tc)))
    == Bool.and(Bool.and(Bool.and(so, Pick.search.empty(after)),
      Bool.and(Bool.not(Bool.or(Pick.search.reads(a1, xx), Pick.search.reads(a2, xx))), Pick.search.reads(a3, xx))),
      Bool.not(_)) : Bool}
  {==}

# a finding when b, none otherwise, counts what a Bool equal to b says
law ps.one:
  for b: Bool
  for -c: Bool
  for e: {b == c : Bool}
  for -x: F.Finding
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, b, [x], [])) == Bool.pick(Nat, c, 1n, 0n) : Nat}

def ps.one(b, c, e, x):
  Equal.trans(Nat, List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, b, [x], [])), Bool.pick(Nat, b, 1n, 0n),
    Bool.pick(Nat, c, 1n, 0n), M1.thunk.one(b, x), Equal.cong(Bool, Nat, y => Bool.pick(Nat, y, 1n, 0n), b, c, e))

# the rule's judge of a statement counts what the law's pick says
law ps.judge:
  for ss: Tree.Node
  for +xx: String
  for +args: Tree.Node
  for +ll: U32
  for +cc: U32
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Pick.search.judge(ss, xx, args, ll, cc, name, path))
    == Bool.pick(Nat, Laws.search.pick(ss, xx, args), 1n, 0n) : Nat}

def ps.judge(ss, xx, args, ll, cc, name, path):
  match ss:
    case Tree.Stmt{sk, kk, body}:
      match kk:
        case Tree.NCons{h, rest}:
          match h:
            case Tree.Leaf{tok}:
              match tok:
                case Lex.Tok{kt, +t, lt, ct}:
                  match rest:
                    case Tree.NCons{h2, +after}:
                      match h2:
                        case Tree.Group{open, +kids, cl}:
                          match open:
                            case Lex.Tok{ko, +o, lo, co}:
                              +as = Calls.args(kids)
                              +no = Calls.arg(as, 3n)
                              ps.one(
                                Bool.and(Bool.and(Bool.and(Bool.and(String.eq(t, "Bool.pick"), String.eq(o, "(")),
                                  Pick.search.empty(after)), Bool.and(Bool.not(Bool.or(Pick.search.reads(Calls.arg(as,
                                  1n), xx), Pick.search.reads(Calls.arg(as, 2n), xx))), Pick.search.reads(no, xx))),
                                  Bool.not(Pick.search.cheap(args, Pick.search.text(Calls.arg(as, 1n))))),
                                Laws.search.pick(ss, xx, args), ps.verdict(t, o, after, kids, xx, args),
                                Pick.search.cite(ll, cc, name, path, Pick.search.lone(no, xx)))
                        case Tree.Leaf{x}: {==}
                        case Tree.Stmt{x, y, z}: {==}
                        case Tree.NNil{}: {==}
                        case Tree.NCons{x, y}: {==}
                    case Tree.Leaf{x}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
            case Tree.Group{x, y, z}: {==}
            case Tree.Stmt{x, y, z}: {==}
            case Tree.NNil{}: {==}
            case Tree.NCons{x, y}: {==}
        case Tree.Leaf{x}: {==}
        case Tree.Group{x, y, z}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# a stop on the negation of b before a walk that counts what j says counts
# what b and j say
law ps.stop:
  for b: Bool
  for -j: Bool
  for -more: List<&2, F.Finding>
  for ih: {List.length(&2, F.Finding, more) == Bool.pick(Nat, j, 1n, 0n) : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(b), [], _u => more))
    == Bool.pick(Nat, Bool.and(b, j), 1n, 0n) : Nat}

def ps.stop(b, _j, _more, ih):
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# past the bound name: the rule's finding counts what the law's call says
law ps.eq:
  for kx: Lex.TokKind
  for +xx: String
  for r1: Tree.Node
  for +rest: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Pick.search.eq(kx, xx, r1, rest, name, path))
    == Bool.pick(Nat, Laws.search.call(kx, xx, r1, rest, name), 1n, 0n) : Nat}

def ps.eq(kx, xx, r1, rest, name, path):
  match r1:
    case Tree.NCons{h1, r2}:
      match h1:
        case Tree.Leaf{tok1}:
          match tok1:
            case Lex.Tok{ke, +e, le, ce}:
              match r2:
                case Tree.NCons{h2, r3}:
                  match h2:
                    case Tree.Leaf{tok2}:
                      match tok2:
                        case Lex.Tok{kn, +n, +l, +c}:
                          match r3:
                            case Tree.NCons{h3, +after}:
                              match h3:
                                case Tree.Group{open, +args, cl}:
                                  match open:
                                    case Lex.Tok{ko, +o, lo, co}:
                                      +so = Bool.and(Bool.and(String.eq(n, name), String.eq(o, "(")),
                                        Pick.search.empty(after))
                                      +ke2 = Bool.and(Lex.is_name(kx), String.eq(e, "="))
                                      +ok = Bool.and(ke2, so)
                                      +fs = Pick.search.judge(Pick.search.first(rest, xx, Tree.NNil{}, False{}), xx,
                                        args, l, c, name, path)
                                      %ps.none(after) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
                                          Bool.not(ok), [], _u => fs))
                                        == Bool.pick(Nat, Bool.and(Bool.and(ke2, Bool.and(Bool.and(String.eq(n, name),
                                          String.eq(o, "(")), _)), Laws.search.pick(Laws.search.first(rest, xx), xx,
                                          args)), 1n, 0n) : Nat}
                                      %ps.first(rest, xx, Tree.NNil{}, False{}) : {List.length(&2, F.Finding,
                                          Lazy.stop(List<&2, F.Finding>, Bool.not(ok), [], _u => fs))
                                        == Bool.pick(Nat, Bool.and(ok, Laws.search.pick(_, xx, args)), 1n, 0n) : Nat}
                                      ps.stop(ok, Laws.search.pick(Pick.search.first(rest, xx, Tree.NNil{}, False{}),
                                        xx, args), fs,
                                        ps.judge(Pick.search.first(rest, xx, Tree.NNil{}, False{}), xx, args, l, c,
                                          name, path))
                                case Tree.Leaf{x}: {==}
                                case Tree.Stmt{x, y, z}: {==}
                                case Tree.NNil{}: {==}
                                case Tree.NCons{x, y}: {==}
                            case Tree.Leaf{x}: {==}
                            case Tree.Group{x, y, z}: {==}
                            case Tree.Stmt{x, y, z}: {==}
                            case Tree.NNil{}: {==}
                    case Tree.Group{x, y, z}: {==}
                    case Tree.Stmt{x, y, z}: {==}
                    case Tree.NNil{}: {==}
                    case Tree.NCons{x, y}: {==}
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NNil{}: {==}
        case Tree.Group{x, y, z}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a let's own tokens past any `+`: the rule's finding counts what the law's
# bound says
law ps.bound:
  for nn: Tree.Node
  for +rest: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Pick.search.bound(nn, rest, name, path))
    == Bool.pick(Nat, Laws.search.bound(nn, rest, name), 1n, 0n) : Nat}

def ps.bound(nn, rest, name, path):
  match nn:
    case Tree.NCons{h, r1}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{kx, +x, lx, cx}:
              ps.eq(kx, x, r1, rest, name, path)
        case Tree.Group{x, y, z}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a let's own tokens: the rule's finding counts what the law's bound says
# past its plus
law ps.lead:
  for kids: Tree.Node
  for +rest: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Pick.search.lead(kids, rest, name, path))
    == Bool.pick(Nat, Laws.search.bound(Laws.search.plus(kids), rest, name), 1n, 0n) : Nat}

def ps.lead(kids, rest, name, path):
  match kids:
    case Tree.NCons{h, +more}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, l, c}:
              ps.bound(Bool.pick(Tree.Node, String.eq(t, "+"), more, Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, more}),
                rest, name, path)
        case Tree.Group{x, y, z}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a statement: the rule's finding counts what the law's at says
law ps.stmt:
  for kind: Tree.StmtKind
  for kids: Tree.Node
  for +rest: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Pick.search.stmt(kind, kids, rest, name, path))
    == Bool.pick(Nat, Laws.search.at(kind, kids, rest, name), 1n, 0n) : Nat}

def ps.stmt(kind, kids, rest, name, path):
  match kind:
    case Tree.SLet{}:
      ps.lead(kids, rest, name, path)
    case Tree.SDef{}: {==}
    case Tree.SType{}: {==}
    case Tree.SLaw{}: {==}
    case Tree.SImport{}: {==}
    case Tree.SCase{}: {==}
    case Tree.SFor{}: {==}
    case Tree.STerm{}: {==}

def Laws.pick_search_walk_counts(nn, name, path):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{+kind, +kids, +body}:
          M1.table.three(Pick.search.stmt(kind, kids, rest, name, path), Pick.search.walk(body, name, path),
            Pick.search.walk(rest, name, path), Bool.pick(Nat, Laws.search.at(kind, kids, rest, name), 1n, 0n),
            Laws.search.count(body, name), Laws.search.count(rest, name), ps.stmt(kind, kids, rest, name, path),
            Laws.pick_search_walk_counts(body, name, path), Laws.pick_search_walk_counts(rest, name, path))
        case Tree.Leaf{x}:
          Laws.pick_search_walk_counts(rest, name, path)
        case Tree.Group{x, y, z}:
          Laws.pick_search_walk_counts(rest, name, path)
        case Tree.NNil{}:
          Laws.pick_search_walk_counts(rest, name, path)
        case Tree.NCons{x, y}:
          Laws.pick_search_walk_counts(rest, name, path)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{x, y, z}:
      {==}
    case Tree.Stmt{x, y, z}:
      {==}
    case Tree.NNil{}:
      {==}

# one def's findings: none when it is exempt, else its walk
law ps.defstop:
  for b: Bool
  for +body: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, b, [], _u => Pick.search.walk(body, name, path)))
    == Bool.pick(Nat, b, 0n, Laws.search.count(body, name)) : Nat}

def ps.defstop(b, body, name, path):
  match b:
    case True{}:
      {==}
    case False{}:
      Laws.pick_search_walk_counts(body, name, path)

# the def walk: the findings gathered so far, then each def's
law ps.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Pick.search.go(ds, path, acc)) == M1.pick.sum(acc, Laws.search.defs(ds, path)) : Nat}

def ps.go(ds, path, acc):
  match ds:
    case Nil{}:
      M1.pick.rev(acc, Nil{})
    case Con{d, +rest}:
      match d:
        case Calls.Def{+name, +sig, +body}:
          +b = Calls.exempt(path, sig)
          +x = Lazy.stop(List<&2, F.Finding>, b, [], _u => Pick.search.walk(body, name, path))
          +cb = Bool.pick(Nat, b, 0n, Laws.search.count(body, name))
          Equal.trans(Nat, List.length(&2, F.Finding, Pick.search.go(rest, path, x <> acc)),
            M1.pick.sum(acc, Nat.add(List.length(&2, F.Finding, x), Laws.search.defs(rest, path))),
            M1.pick.sum(acc, Nat.add(cb, Laws.search.defs(rest, path))),
            ps.go(rest, path, x <> acc),
            Equal.cong(Nat, Nat, n => M1.pick.sum(acc, Nat.add(n, Laws.search.defs(rest, path))),
              List.length(&2, F.Finding, x), cb, ps.defstop(b, body, name, path)))

def Laws.pick_search_counts(path, _text, _toks, tree, _bound, _items):
  ps.go(Calls.defs(tree), path, Nil{})

# the def walk gathers nothing in a law file
law ps.exempt:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +n: Nat
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {Pick.search.go(ds, path, M2.ex.rep(n)) == Nil{} : List<&2, F.Finding>}

def ps.exempt(ds, path, n, e):
  match ds:
    case Nil{}:
      M2.ex.flat(n, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      M2.ex.push(Calls.exempt(path, sig), M2.ex.calls(path, sig, e), _u => Pick.search.walk(body, name, path), n,
        v => Pick.search.go(rest, path, v), ps.exempt(rest, path, 1n+n, e))

def Laws.pick_search_exempt(path, _text, _toks, tree, _bound, _items, e):
  ps.exempt(Calls.defs(tree), path, 0n, e)
