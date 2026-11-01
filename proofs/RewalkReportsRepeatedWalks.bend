# proofs of laws/RewalkReportsRepeatedWalks.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/pedantic/rewalk.bend as Rewalk
import ../laws/RewalkReportsRepeatedWalks.bend as Laws
import ./lemmas/Pick.bend as M1

# the rule's names are the law's
law rewalk.names_eq:
  for nn: Tree.Node
  for +acc: List<&2, String>
  {Rewalk.names(nn, acc) == Laws.rewalk.names(nn, acc) : List<&2, String>}

def rewalk.names_eq(nn, acc):
  match nn:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}:
          match k:
            case Lex.TName{}:
              {==}
            case Lex.TUpper{}:
              {==}
            case Lex.TDotted{}:
              {==}
            case Lex.TWild{}:
              {==}
            case Lex.TKey{}:
              {==}
            case Lex.TNum{}:
              {==}
            case Lex.TStr{}:
              {==}
            case Lex.TChar{}:
              {==}
            case Lex.TComment{}:
              {==}
            case Lex.TSpace{}:
              {==}
            case Lex.TNewline{}:
              {==}
            case Lex.TOp{}:
              {==}
            case Lex.TColon{}:
              {==}
            case Lex.TEq{}:
              {==}
            case Lex.TBind{}:
              {==}
            case Lex.TArrow{}:
              {==}
            case Lex.TLam{}:
              {==}
            case Lex.TAll{}:
              {==}
            case Lex.TAmp{}:
              {==}
            case Lex.TOpen{}:
              {==}
            case Lex.TClose{}:
              {==}
            case Lex.TComma{}:
              {==}
    case Tree.Group{open, kids, close}:
      rewalk.names_eq(kids, acc)
    case Tree.Stmt{kind, +kids, body}:
      %rewalk.names_eq(kids, acc) : {Rewalk.names(body, Rewalk.names(kids, acc)) == Laws.rewalk.names(body, _)
        : List<&2, String>}
      rewalk.names_eq(body, Rewalk.names(kids, acc))
    case Tree.NCons{+h, rest}:
      %rewalk.names_eq(h, acc) : {Rewalk.names(rest, Rewalk.names(h, acc)) == Laws.rewalk.names(rest, _)
        : List<&2, String>}
      rewalk.names_eq(rest, Rewalk.names(h, acc))
    case Tree.NNil{}:
      {==}

# the rule's let names are the law's
law rewalk.lhs_eq:
  for nn: Tree.Node
  for +acc: List<&2, String>
  {Rewalk.lhs_names(nn, acc) == Laws.rewalk.lhs(nn, acc) : List<&2, String>}

def rewalk.lhs_eq(nn, acc):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}:
                  rewalk.lhs_eq(rest, t <> acc)
                case Lex.TUpper{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TDotted{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TWild{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TKey{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TNum{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TStr{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TChar{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TComment{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TSpace{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TNewline{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TOp{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TColon{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TEq{}:
                  {==}
                case Lex.TBind{}:
                  {==}
                case Lex.TArrow{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TLam{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TAll{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TAmp{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TOpen{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TClose{}:
                  rewalk.lhs_eq(rest, acc)
                case Lex.TComma{}:
                  rewalk.lhs_eq(rest, acc)
        case Tree.Group{open, +kids, close}:
          %rewalk.names_eq(kids, acc) : {Rewalk.lhs_names(rest, Rewalk.names(kids, acc))
            == Laws.rewalk.lhs(rest, _) : List<&2, String>}
          rewalk.lhs_eq(rest, Rewalk.names(kids, acc))
        case Tree.Stmt{kind, kids, body}:
          rewalk.lhs_eq(rest, acc)
        case Tree.NNil{}:
          rewalk.lhs_eq(rest, acc)
        case Tree.NCons{x, y}:
          rewalk.lhs_eq(rest, acc)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# the rule's lets of a piece are the law's
law rewalk.binds_eq:
  for nn: Tree.Node
  for +acc: List<&2, Rewalk.Bind>
  {Rewalk.binds(nn, acc) == Laws.rewalk.binds(nn, acc) : List<&2, Rewalk.Bind>}

def rewalk.binds_eq(nn, acc):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SDef{}:
              %rewalk.binds_eq(body, acc) : {Rewalk.binds(rest, Rewalk.binds(body, acc)) == Laws.rewalk.binds(rest,
                _) : List<&2, Rewalk.Bind>}
              rewalk.binds_eq(rest, Rewalk.binds(body, acc))
            case Tree.SType{}:
              %rewalk.binds_eq(body, acc) : {Rewalk.binds(rest, Rewalk.binds(body, acc)) == Laws.rewalk.binds(rest,
                _) : List<&2, Rewalk.Bind>}
              rewalk.binds_eq(rest, Rewalk.binds(body, acc))
            case Tree.SLaw{}:
              %rewalk.binds_eq(body, acc) : {Rewalk.binds(rest, Rewalk.binds(body, acc)) == Laws.rewalk.binds(rest,
                _) : List<&2, Rewalk.Bind>}
              rewalk.binds_eq(rest, Rewalk.binds(body, acc))
            case Tree.SImport{}:
              %rewalk.binds_eq(body, acc) : {Rewalk.binds(rest, Rewalk.binds(body, acc)) == Laws.rewalk.binds(rest,
                _) : List<&2, Rewalk.Bind>}
              rewalk.binds_eq(rest, Rewalk.binds(body, acc))
            case Tree.SCase{}:
              rewalk.binds_eq(rest, acc)
            case Tree.SFor{}:
              %rewalk.binds_eq(body, acc) : {Rewalk.binds(rest, Rewalk.binds(body, acc)) == Laws.rewalk.binds(rest,
                _) : List<&2, Rewalk.Bind>}
              rewalk.binds_eq(rest, Rewalk.binds(body, acc))
            case Tree.SLet{}:
              +pp = Rewalk.last_pos(Tree.leaves.go(body, Tree.leaves.go(kids, [])))
              %rewalk.lhs_eq(kids, []) : {Rewalk.binds(rest, Rewalk.binds(body, Rewalk.bind_at(Rewalk.lhs_names(kids,
                []), pp, acc))) == Laws.rewalk.binds(rest, Laws.rewalk.binds(body, Rewalk.bind_at(_, pp,
                  acc))) : List<&2, Rewalk.Bind>}
              +x = Rewalk.bind_at(Rewalk.lhs_names(kids, []), pp, acc)
              %rewalk.binds_eq(body, x) : {Rewalk.binds(rest, Rewalk.binds(body, x)) == Laws.rewalk.binds(rest,
                _) : List<&2, Rewalk.Bind>}
              rewalk.binds_eq(rest, Rewalk.binds(body, x))
            case Tree.STerm{}:
              %rewalk.binds_eq(body, acc) : {Rewalk.binds(rest, Rewalk.binds(body, acc)) == Laws.rewalk.binds(rest,
                _) : List<&2, Rewalk.Bind>}
              rewalk.binds_eq(rest, Rewalk.binds(body, acc))
        case Tree.Leaf{tok}:
          rewalk.binds_eq(rest, acc)
        case Tree.Group{open, kids, close}:
          rewalk.binds_eq(rest, acc)
        case Tree.NNil{}:
          rewalk.binds_eq(rest, acc)
        case Tree.NCons{x, y}:
          rewalk.binds_eq(rest, acc)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# the rule's let count is the law's
law rewalk.lets_eq:
  for bs: List<&2, Rewalk.Bind>
  for +name: String
  for +line: U32
  for +col: U32
  {Rewalk.count(bs, name, line, col) == Laws.rewalk.lets(bs, name, line, col) : U32}

def rewalk.lets_eq(bs, name, line, col):
  match bs:
    case Nil{}:
      {==}
    case Con{b, rest}:
      match b:
        case Rewalk.Bind{+nm, +l, +c}:
          Equal.cong(U32, U32, m => Bool.pick(U32, Bool.and(String.eq(nm, name), Rewalk.before(l, c, line, col)),
            (m + 1 : U32), m), Rewalk.count(rest, name, line, col), Laws.rewalk.lets(rest, name, line, col),
            rewalk.lets_eq(rest, name, line, col))

# the rule's stamp is the law's
law rewalk.stamp_eq:
  for ns: List<&2, String>
  for +bs: List<&2, Rewalk.Bind>
  for +line: U32
  for +col: U32
  {Rewalk.stamp(ns, bs, line, col) == Laws.rewalk.stamp(ns, bs, line, col) : String}

def rewalk.stamp_eq(ns, bs, line, col):
  match ns:
    case Nil{}:
      {==}
    case Con{+nm, rest}:
      %rewalk.lets_eq(bs, nm, line, col) : {Rewalk.stamp(nm <> rest, bs, line, col)
        == "|" ++ nm ++ "=" ++ U32.show(_) ++ Laws.rewalk.stamp(rest, bs, line, col) : String}
      %rewalk.stamp_eq(rest, bs, line, col) : {Rewalk.stamp(nm <> rest, bs, line, col)
        == "|" ++ nm ++ "=" ++ U32.show(Rewalk.count(bs, nm, line, col)) ++ _ : String}
      {==}

# two lists joined, each equal to its counterpart
law rewalk.cat2:
  for -A: Data
  for -a1: List<&2, A>
  for -a2: List<&2, A>
  for -b1: List<&2, A>
  for -b2: List<&2, A>
  for ea: {a1 == a2 : List<&2, A>}
  for eb: {b1 == b2 : List<&2, A>}
  {List.concat(&2, A, [a1, b1]) == List.concat(&2, A, [a2, b2]) : List<&2, A>}

def rewalk.cat2(A, a1, _a2, b1, b2, ea, eb):
  %ea : {List.concat(&2, A, [a1, b1]) == List.concat(&2, A, [_, b2]) : List<&2, A>}
  %eb : {List.concat(&2, A, [a1, b1]) == List.concat(&2, A, [a1, _]) : List<&2, A>}
  {==}

# three lists joined, each equal to its counterpart
law rewalk.cat3:
  for -A: Data
  for -a1: List<&2, A>
  for -a2: List<&2, A>
  for -b1: List<&2, A>
  for -b2: List<&2, A>
  for -c1: List<&2, A>
  for -c2: List<&2, A>
  for ea: {a1 == a2 : List<&2, A>}
  for eb: {b1 == b2 : List<&2, A>}
  for ec: {c1 == c2 : List<&2, A>}
  {List.concat(&2, A, [a1, b1, c1]) == List.concat(&2, A, [a2, b2, c2]) : List<&2, A>}

def rewalk.cat3(A, a1, _a2, b1, b2, c1, c2, ea, eb, ec):
  %ea : {List.concat(&2, A, [a1, b1, c1]) == List.concat(&2, A, [_, b2, c2]) : List<&2, A>}
  %eb : {List.concat(&2, A, [a1, b1, c1]) == List.concat(&2, A, [a1, _, c2]) : List<&2, A>}
  %ec : {List.concat(&2, A, [a1, b1, c1]) == List.concat(&2, A, [a1, b1, _]) : List<&2, A>}
  {==}

# a call's argument key, to the rule and to the law
law rewalk.args_eq:
  for +kids: Tree.Node
  for +bs: List<&2, Rewalk.Bind>
  for +l: U32
  for +c: U32
  {Tree.show(kids) ++ Rewalk.stamp(Rewalk.names(kids, []), bs, l, c)
    == Tree.show(kids) ++ Laws.rewalk.stamp(Laws.rewalk.names(kids, []), bs, l, c) : String}

def rewalk.args_eq(kids, bs, l, c):
  %rewalk.names_eq(kids, []) : {Tree.show(kids) ++ Rewalk.stamp(Rewalk.names(kids, []), bs, l, c)
    == Tree.show(kids) ++ Laws.rewalk.stamp(_, bs, l, c) : String}
  %rewalk.stamp_eq(Rewalk.names(kids, []), bs, l, c) : {Tree.show(kids) ++ Rewalk.stamp(Rewalk.names(kids, []), bs, l,
    c) == Tree.show(kids) ++ _ : String}
  {==}

# the rule's sites are the law's
law rewalk.gather_eq:
  for nn: Tree.Node
  for +self: String
  for +lp: List<&2, String>
  for +bs: List<&2, Rewalk.Bind>
  {Rewalk.gather(nn, self, lp, bs) == Laws.rewalk.gather(nn, self, lp, bs) : List<&2, Rewalk.Site>}

# a call's own site, to the rule and to the law
law rewalk.here_eq:
  for +o: String
  for +r2: Tree.Node
  for +t: String
  for +kids: Tree.Node
  for +bs: List<&2, Rewalk.Bind>
  for +l: U32
  for +c: U32
  for +self: String
  for +lp: List<&2, String>
  {Rewalk.open_site(String.eq(o, "("), Rewalk.indexed(r2), t, Tree.show(kids) ++ Rewalk.stamp(Rewalk.names(kids, []),
    bs, l, c), l, c, U32.from_nat(String.length(t)), self, lp)
    == Rewalk.open_site(String.eq(o, "("), Rewalk.indexed(r2), t, Tree.show(kids)
      ++ Laws.rewalk.stamp(Laws.rewalk.names(kids, []), bs, l, c), l, c, U32.from_nat(String.length(t)), self, lp)
    : List<&2, Rewalk.Site>}

def rewalk.here_eq(o, r2, t, kids, bs, l, c, self, lp):
  Equal.cong(String, List<&2, Rewalk.Site>, a => Rewalk.open_site(String.eq(o, "("), Rewalk.indexed(r2), t, a, l, c,
    U32.from_nat(String.length(t)), self, lp), Tree.show(kids) ++ Rewalk.stamp(Rewalk.names(kids, []), bs, l, c),
    Tree.show(kids) ++ Laws.rewalk.stamp(Laws.rewalk.names(kids, []), bs, l, c), rewalk.args_eq(kids, bs, l, c))

# a statement's sites: its own tokens, its body, then what follows
law rewalk.gather_stmt:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +lp: List<&2, String>
  for +bs: List<&2, Rewalk.Bind>
  for ek: {Rewalk.gather(kids, self, lp, bs) == Laws.rewalk.gather(kids, self, lp, bs) : List<&2, Rewalk.Site>}
  for eb: {Rewalk.gather(body, self, lp, bs) == Laws.rewalk.gather(body, self, lp, bs) : List<&2, Rewalk.Site>}
  for er: {Rewalk.gather(rest, self, lp, bs) == Laws.rewalk.gather(rest, self, lp, bs) : List<&2, Rewalk.Site>}
  {List.concat(&2, Rewalk.Site, [Rewalk.gather(kids, self, lp, bs), Rewalk.gather(body, self, lp, bs),
    Rewalk.gather(rest, self, lp, bs)]) == List.concat(&2, Rewalk.Site, [Laws.rewalk.gather(kids, self, lp, bs),
    Laws.rewalk.gather(body, self, lp, bs), Laws.rewalk.gather(rest, self, lp, bs)]) : List<&2, Rewalk.Site>}

def rewalk.gather_stmt(kids, body, rest, self, lp, bs, ek, eb, er):
  rewalk.cat3(Rewalk.Site, Rewalk.gather(kids, self, lp, bs), Laws.rewalk.gather(kids, self, lp, bs),
    Rewalk.gather(body, self, lp, bs), Laws.rewalk.gather(body, self, lp, bs), Rewalk.gather(rest, self, lp, bs),
    Laws.rewalk.gather(rest, self, lp, bs), ek, eb, er)

def rewalk.gather_eq(nn, self, lp, bs):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{open, +kids, close}:
                      match open:
                        case Lex.Tok{ok, +o, ol, oc}:
                          rewalk.cat3(Rewalk.Site,
                            Rewalk.open_site(String.eq(o, "("), Rewalk.indexed(r2), t, Tree.show(kids)
                              ++ Rewalk.stamp(Rewalk.names(kids, []), bs, l, c), l, c, U32.from_nat(String.length(t)),
                              self, lp),
                            Rewalk.open_site(String.eq(o, "("), Rewalk.indexed(r2), t, Tree.show(kids)
                              ++ Laws.rewalk.stamp(Laws.rewalk.names(kids, []), bs, l, c), l, c,
                              U32.from_nat(String.length(t)), self, lp),
                            Rewalk.gather(kids, self, lp, bs), Laws.rewalk.gather(kids, self, lp, bs),
                            Rewalk.gather(r2, self, lp, bs), Laws.rewalk.gather(r2, self, lp, bs),
                            rewalk.here_eq(o, r2, t, kids, bs, l, c, self, lp),
                            rewalk.gather_eq(kids, self, lp, bs), rewalk.gather_eq(r2, self, lp, bs))
                    case Tree.Leaf{x}:
                      rewalk.gather_eq(rest, self, lp, bs)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.gather_eq(rest, self, lp, bs)
                    case Tree.NNil{}:
                      rewalk.gather_eq(rest, self, lp, bs)
                    case Tree.NCons{x, y}:
                      rewalk.gather_eq(rest, self, lp, bs)
                case Tree.Leaf{x}:
                  rewalk.gather_eq(rest, self, lp, bs)
                case Tree.Group{open, kids, close}:
                  rewalk.gather_eq(rest, self, lp, bs)
                case Tree.Stmt{kind, kids, body}:
                  rewalk.gather_eq(rest, self, lp, bs)
                case Tree.NNil{}:
                  rewalk.gather_eq(rest, self, lp, bs)
        case Tree.Group{open, +kids, close}:
          rewalk.cat2(Rewalk.Site, Rewalk.gather(kids, self, lp, bs), Laws.rewalk.gather(kids, self, lp, bs),
            Rewalk.gather(rest, self, lp, bs), Laws.rewalk.gather(rest, self, lp, bs),
            rewalk.gather_eq(kids, self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SDef{}:
              rewalk.gather_stmt(kids, body, rest, self, lp, bs, rewalk.gather_eq(kids, self, lp, bs),
                rewalk.gather_eq(body, self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
            case Tree.SType{}:
              rewalk.gather_stmt(kids, body, rest, self, lp, bs, rewalk.gather_eq(kids, self, lp, bs),
                rewalk.gather_eq(body, self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
            case Tree.SLaw{}:
              rewalk.gather_stmt(kids, body, rest, self, lp, bs, rewalk.gather_eq(kids, self, lp, bs),
                rewalk.gather_eq(body, self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
            case Tree.SImport{}:
              rewalk.gather_stmt(kids, body, rest, self, lp, bs, rewalk.gather_eq(kids, self, lp, bs),
                rewalk.gather_eq(body, self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
            case Tree.SCase{}:
              rewalk.cat2(Rewalk.Site, Rewalk.gather(kids, self, lp, bs), Laws.rewalk.gather(kids, self, lp, bs),
                Rewalk.gather(rest, self, lp, bs), Laws.rewalk.gather(rest, self, lp, bs), rewalk.gather_eq(kids,
                  self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
            case Tree.SFor{}:
              rewalk.gather_stmt(kids, body, rest, self, lp, bs, rewalk.gather_eq(kids, self, lp, bs),
                rewalk.gather_eq(body, self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
            case Tree.SLet{}:
              rewalk.gather_stmt(kids, body, rest, self, lp, bs, rewalk.gather_eq(kids, self, lp, bs),
                rewalk.gather_eq(body, self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
            case Tree.STerm{}:
              rewalk.gather_stmt(kids, body, rest, self, lp, bs, rewalk.gather_eq(kids, self, lp, bs),
                rewalk.gather_eq(body, self, lp, bs), rewalk.gather_eq(rest, self, lp, bs))
        case Tree.NNil{}:
          rewalk.gather_eq(rest, self, lp, bs)
        case Tree.NCons{x, y}:
          rewalk.gather_eq(rest, self, lp, bs)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# two steps, each the rule's and the law's alike, from equal starts
law rewalk.then:
  for -A: Type
  for -f1: A -> A
  for -g1: A -> A
  for -f2: A -> A
  for -g2: A -> A
  for -x: A
  for -y: A
  for e0: {x == y : A}
  for e1: {f1(x) == g1(x) : A}
  for e2: {f2(f1(x)) == g2(f1(x)) : A}
  {f2(f1(x)) == g2(g1(y)) : A}

def rewalk.then(A, f1, g1, f2, g2, x, _y, e0, e1, e2):
  %e0 : {f2(f1(x)) == g2(g1(_)) : A}
  %e1 : {f2(f1(x)) == g2(_) : A}
  e2

# the rule's retag is the law's
law rewalk.retag_eq:
  for sites: List<&2, Rewalk.Site>
  for +note: Rewalk.Note
  {Rewalk.retag(sites, note) == Laws.rewalk.retag(sites, note) : List<&2, Rewalk.Site>}

def rewalk.retag_eq(sites, note):
  match sites:
    case Nil{}:
      {==}
    case Con{s, rest}:
      match s:
        case Rewalk.Site{+name, +args, +line, +col, +len, how}:
          +hd = Rewalk.retag_one(Bool.and(U32.is_eq(line, Rewalk.note_line(note)), U32.is_eq(col,
            Rewalk.note_col(note))), how, Rewalk.note_how_of(note), name, args, line, col, len)
          Equal.cong(List<&2, Rewalk.Site>, List<&2, Rewalk.Site>, tl => hd <> tl, Rewalk.retag(rest, note),
            Laws.rewalk.retag(rest, note), rewalk.retag_eq(rest, note))

# a let's note retags alike
law rewalk.relet_eq:
  for mm: Maybe<&2, Rewalk.Note>
  for sites: List<&2, Rewalk.Site>
  {Rewalk.retag_may(mm, sites) == Laws.rewalk.relet(mm, sites) : List<&2, Rewalk.Site>}

def rewalk.relet_eq(mm, sites):
  match mm:
    case None{}:
      {==}
    case Some{note}:
      rewalk.retag_eq(sites, note)

# the rule's apply is the law's
law rewalk.apply_eq:
  for nn: Tree.Node
  for +sites: List<&2, Rewalk.Site>
  {Rewalk.apply(nn, sites) == Laws.rewalk.apply(nn, sites) : List<&2, Rewalk.Site>}

# a statement retags its own call, then its body's, then what follows
law rewalk.apply_stmt:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +sites: List<&2, Rewalk.Site>
  for eb: {Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites))
    == Laws.rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites)) : List<&2, Rewalk.Site>}
  for er: {Rewalk.apply(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites)))
    == Laws.rewalk.apply(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites)))
    : List<&2, Rewalk.Site>}
  {Rewalk.apply(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites)))
    == Laws.rewalk.apply(rest, Laws.rewalk.apply(body, Laws.rewalk.relet(Rewalk.note_st(kids), sites)))
    : List<&2, Rewalk.Site>}

def rewalk.apply_stmt(kids, body, rest, sites, eb, er):
  rewalk.then(List<&2, Rewalk.Site>, ss => Rewalk.apply(body, ss), ss => Laws.rewalk.apply(body, ss),
    ss => Rewalk.apply(rest, ss), ss => Laws.rewalk.apply(rest, ss), Rewalk.retag_may(Rewalk.note_st(kids), sites),
    Laws.rewalk.relet(Rewalk.note_st(kids), sites), rewalk.relet_eq(Rewalk.note_st(kids), sites), eb, er)

def rewalk.apply_eq(nn, sites):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SDef{}:
              rewalk.apply_stmt(kids, body, rest, sites, rewalk.apply_eq(body, Rewalk.retag_may(Rewalk.note_st(kids),
                sites)), rewalk.apply_eq(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites))))
            case Tree.SType{}:
              rewalk.apply_stmt(kids, body, rest, sites, rewalk.apply_eq(body, Rewalk.retag_may(Rewalk.note_st(kids),
                sites)), rewalk.apply_eq(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites))))
            case Tree.SLaw{}:
              rewalk.apply_stmt(kids, body, rest, sites, rewalk.apply_eq(body, Rewalk.retag_may(Rewalk.note_st(kids),
                sites)), rewalk.apply_eq(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites))))
            case Tree.SImport{}:
              rewalk.apply_stmt(kids, body, rest, sites, rewalk.apply_eq(body, Rewalk.retag_may(Rewalk.note_st(kids),
                sites)), rewalk.apply_eq(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites))))
            case Tree.SCase{}:
              rewalk.apply_eq(rest, sites)
            case Tree.SFor{}:
              rewalk.apply_stmt(kids, body, rest, sites, rewalk.apply_eq(body, Rewalk.retag_may(Rewalk.note_st(kids),
                sites)), rewalk.apply_eq(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites))))
            case Tree.SLet{}:
              rewalk.apply_stmt(kids, body, rest, sites, rewalk.apply_eq(body, Rewalk.retag_may(Rewalk.note_st(kids),
                sites)), rewalk.apply_eq(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites))))
            case Tree.STerm{}:
              rewalk.apply_stmt(kids, body, rest, sites, rewalk.apply_eq(body, Rewalk.retag_may(Rewalk.note_st(kids),
                sites)), rewalk.apply_eq(rest, Rewalk.apply(body, Rewalk.retag_may(Rewalk.note_st(kids), sites))))
        case Tree.Group{open, +kids, close}:
          rewalk.then(List<&2, Rewalk.Site>, ss => Rewalk.apply(kids, ss), ss => Laws.rewalk.apply(kids, ss),
            ss => Rewalk.apply(rest, ss), ss => Laws.rewalk.apply(rest, ss), sites, sites, {==},
            rewalk.apply_eq(kids, sites), rewalk.apply_eq(rest, Rewalk.apply(kids, sites)))
        case Tree.Leaf{tok}:
          rewalk.apply_eq(rest, sites)
        case Tree.NNil{}:
          rewalk.apply_eq(rest, sites)
        case Tree.NCons{x, y}:
          rewalk.apply_eq(rest, sites)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# an accessor's mark, taken lazily by the rule and outright by the law
law rewalk.mark_here:
  for b: Bool
  for +t: String
  for +kids: Tree.Node
  {Lazy.stop(List<&2, Rewalk.Pos>, Bool.not(b), [], _u => Rewalk.mark_slot(Rewalk.slot_of(t), Calls.args(kids)))
    == Bool.pick(List<&2, Rewalk.Pos>, b, Rewalk.mark_slot(Rewalk.slot_of(t), Calls.args(kids)), [])
    : List<&2, Rewalk.Pos>}

def rewalk.mark_here(b, _t, _kids):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the rule's marks are the law's
law rewalk.marks_eq:
  for nn: Tree.Node
  {Rewalk.mark(nn) == Laws.rewalk.marks(nn) : List<&2, Rewalk.Pos>}

# a statement's marks: its own tokens, its body, then what follows
law rewalk.marks_stmt:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for ek: {Rewalk.mark(kids) == Laws.rewalk.marks(kids) : List<&2, Rewalk.Pos>}
  for eb: {Rewalk.mark(body) == Laws.rewalk.marks(body) : List<&2, Rewalk.Pos>}
  for er: {Rewalk.mark(rest) == Laws.rewalk.marks(rest) : List<&2, Rewalk.Pos>}
  {List.concat(&2, Rewalk.Pos, [Rewalk.mark(kids), Rewalk.mark(body), Rewalk.mark(rest)])
    == List.concat(&2, Rewalk.Pos, [Laws.rewalk.marks(kids), Laws.rewalk.marks(body), Laws.rewalk.marks(rest)])
    : List<&2, Rewalk.Pos>}

def rewalk.marks_stmt(kids, body, rest, ek, eb, er):
  rewalk.cat3(Rewalk.Pos, Rewalk.mark(kids), Laws.rewalk.marks(kids), Rewalk.mark(body), Laws.rewalk.marks(body),
    Rewalk.mark(rest), Laws.rewalk.marks(rest), ek, eb, er)

# two chains' marks, joined
law rewalk.marks_two:
  for +kids: Tree.Node
  for +rest: Tree.Node
  for ek: {Rewalk.mark(kids) == Laws.rewalk.marks(kids) : List<&2, Rewalk.Pos>}
  for er: {Rewalk.mark(rest) == Laws.rewalk.marks(rest) : List<&2, Rewalk.Pos>}
  {List.concat(&2, Rewalk.Pos, [Rewalk.mark(kids), Rewalk.mark(rest)])
    == List.concat(&2, Rewalk.Pos, [Laws.rewalk.marks(kids), Laws.rewalk.marks(rest)]) : List<&2, Rewalk.Pos>}

def rewalk.marks_two(kids, rest, ek, er):
  rewalk.cat2(Rewalk.Pos, Rewalk.mark(kids), Laws.rewalk.marks(kids), Rewalk.mark(rest), Laws.rewalk.marks(rest), ek,
    er)

def rewalk.marks_eq(nn):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, l, c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{open, +kids, close}:
                      match open:
                        case Lex.Tok{ok, +o, ol, oc}:
                          rewalk.cat3(Rewalk.Pos,
                            Lazy.stop(List<&2, Rewalk.Pos>, Bool.not(String.eq(o, "(")), [],
                              _u => Rewalk.mark_slot(Rewalk.slot_of(t), Calls.args(kids))),
                            Bool.pick(List<&2, Rewalk.Pos>, String.eq(o, "("),
                              Rewalk.mark_slot(Rewalk.slot_of(t), Calls.args(kids)), []),
                            Rewalk.mark(kids), Laws.rewalk.marks(kids), Rewalk.mark(r2), Laws.rewalk.marks(r2),
                            rewalk.mark_here(String.eq(o, "("), t, kids), rewalk.marks_eq(kids), rewalk.marks_eq(r2))
                    case Tree.Leaf{x}:
                      rewalk.marks_eq(rest)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.marks_eq(rest)
                    case Tree.NNil{}:
                      rewalk.marks_eq(rest)
                    case Tree.NCons{x, y}:
                      rewalk.marks_eq(rest)
                case Tree.Leaf{x}:
                  rewalk.marks_eq(rest)
                case Tree.Group{open, kids, close}:
                  rewalk.marks_eq(rest)
                case Tree.Stmt{kind, kids, body}:
                  rewalk.marks_eq(rest)
                case Tree.NNil{}:
                  rewalk.marks_eq(rest)
        case Tree.Group{open, +kids, close}:
          rewalk.marks_two(kids, rest, rewalk.marks_eq(kids), rewalk.marks_eq(rest))
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SDef{}:
              rewalk.marks_stmt(kids, body, rest, rewalk.marks_eq(kids), rewalk.marks_eq(body), rewalk.marks_eq(rest))
            case Tree.SType{}:
              rewalk.marks_stmt(kids, body, rest, rewalk.marks_eq(kids), rewalk.marks_eq(body), rewalk.marks_eq(rest))
            case Tree.SLaw{}:
              rewalk.marks_stmt(kids, body, rest, rewalk.marks_eq(kids), rewalk.marks_eq(body), rewalk.marks_eq(rest))
            case Tree.SImport{}:
              rewalk.marks_stmt(kids, body, rest, rewalk.marks_eq(kids), rewalk.marks_eq(body), rewalk.marks_eq(rest))
            case Tree.SCase{}:
              rewalk.marks_two(kids, rest, rewalk.marks_eq(kids), rewalk.marks_eq(rest))
            case Tree.SFor{}:
              rewalk.marks_stmt(kids, body, rest, rewalk.marks_eq(kids), rewalk.marks_eq(body), rewalk.marks_eq(rest))
            case Tree.SLet{}:
              rewalk.marks_stmt(kids, body, rest, rewalk.marks_eq(kids), rewalk.marks_eq(body), rewalk.marks_eq(rest))
            case Tree.STerm{}:
              rewalk.marks_stmt(kids, body, rest, rewalk.marks_eq(kids), rewalk.marks_eq(body), rewalk.marks_eq(rest))
        case Tree.NNil{}:
          rewalk.marks_eq(rest)
        case Tree.NCons{x, y}:
          rewalk.marks_eq(rest)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# the rule's pinned is the law's
law rewalk.pinned_eq:
  for +line: U32
  for +col: U32
  for ps: List<&2, Rewalk.Pos>
  {Rewalk.pinned(line, col, ps) == Laws.rewalk.pinned(line, col, ps) : Bool}

def rewalk.pinned_eq(line, col, ps):
  match ps:
    case Nil{}:
      {==}
    case Con{p, rest}:
      match p:
        case Rewalk.Pos{+l, +c}:
          Equal.cong(Bool, Bool, m => Bool.or(Bool.and(U32.is_eq(l, line), U32.is_eq(c, col)), m),
            Rewalk.pinned(line, col, rest), Laws.rewalk.pinned(line, col, rest), rewalk.pinned_eq(line, col, rest))

# the rule's pin is the law's
law rewalk.pin_eq:
  for +ps: List<&2, Rewalk.Pos>
  for sites: List<&2, Rewalk.Site>
  {Rewalk.pin(ps, sites) == Laws.rewalk.pin(ps, sites) : List<&2, Rewalk.Site>}

def rewalk.pin_eq(ps, sites):
  match sites:
    case Nil{}:
      {==}
    case Con{s, rest}:
      match s:
        case Rewalk.Site{+name, +args, +line, +col, +len, +how}:
          %rewalk.pinned_eq(line, col, ps) : {Rewalk.pin(ps, Rewalk.Site{name, args, line, col, len, how} <> rest)
            == Rewalk.pin_how(_, how, name, args, line, col, len) <> Laws.rewalk.pin(ps, rest)
            : List<&2, Rewalk.Site>}
          %rewalk.pin_eq(ps, rest) : {Rewalk.pin(ps, Rewalk.Site{name, args, line, col, len, how} <> rest)
            == Rewalk.pin_how(Rewalk.pinned(line, col, ps), how, name, args, line, col, len) <> _
            : List<&2, Rewalk.Site>}
          {==}

# two joined reads, each the rule's and the law's alike
law rewalk.either2:
  for -a1: Rewalk.Hit
  for -a2: Rewalk.Hit
  for -b1: Rewalk.Hit
  for -b2: Rewalk.Hit
  for ea: {a1 == a2 : Rewalk.Hit}
  for eb: {b1 == b2 : Rewalk.Hit}
  {Rewalk.either(a1, b1) == Rewalk.either(a2, b2) : Rewalk.Hit}

def rewalk.either2(a1, _a2, b1, b2, ea, eb):
  %ea : {Rewalk.either(a1, b1) == Rewalk.either(_, b2) : Rewalk.Hit}
  %eb : {Rewalk.either(a1, b1) == Rewalk.either(a1, _) : Rewalk.Hit}
  {==}

# the rule's reads are the law's
law rewalk.reads_eq:
  for nn: Tree.Node
  for +name: String
  for +hot: Bool
  for +left: Nat
  for +live: Bool
  for +skip: Bool
  {Rewalk.hits(nn, name, hot, left, live, skip) == Laws.rewalk.reads(nn, name, hot, left, live, skip) : Rewalk.Hit}

# a mention of a name, then the rest of the chain
law rewalk.reads_name:
  for +t: String
  for +rest: Tree.Node
  for +name: String
  for +hot: Bool
  for +left: Nat
  for +live: Bool
  for +skip: Bool
  for ih: {Rewalk.hits(rest, name, hot, left, live, skip) == Laws.rewalk.reads(rest, name, hot, left, live, skip)
    : Rewalk.Hit}
  {Rewalk.either(Rewalk.hit_keep(skip, Rewalk.name_hit(String.eq(t, name), hot)),
    Rewalk.hits(rest, name, hot, left, live, skip))
    == Rewalk.either(Rewalk.hit_keep(skip, Rewalk.name_hit(String.eq(t, name), hot)),
      Laws.rewalk.reads(rest, name, hot, left, live, skip)) : Rewalk.Hit}

def rewalk.reads_name(t, rest, name, hot, left, live, skip, ih):
  +h = Rewalk.hit_keep(skip, Rewalk.name_hit(String.eq(t, name), hot))
  rewalk.either2(h, h, Rewalk.hits(rest, name, hot, left, live, skip),
    Laws.rewalk.reads(rest, name, hot, left, live, skip), {==}, ih)

# a callee or an indexed name, its group, then the rest of the chain
law rewalk.reads_call:
  for +o: String
  for +t: String
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +name: String
  for +hot: Bool
  for +left: Nat
  for +live: Bool
  for +skip: Bool
  for ik: {Rewalk.hits(kids, name, Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot),
    Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t),
    Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t), skip)
    == Laws.rewalk.reads(kids, name, Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot),
    Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t),
    Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t), skip) : Rewalk.Hit}
  for ir: {Rewalk.hits(r2, name, hot, left, live, skip) == Laws.rewalk.reads(r2, name, hot, left, live, skip)
    : Rewalk.Hit}
  {Rewalk.either(Rewalk.hit_keep(skip, Rewalk.here_hit(String.eq(o, "["), String.eq(o, "("), t, name, hot)),
    Rewalk.either(Rewalk.hits(kids, name, Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot),
      Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t),
      Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t), skip),
      Rewalk.hits(r2, name, hot, left, live, skip)))
    == Rewalk.either(Rewalk.hit_keep(skip, Rewalk.here_hit(String.eq(o, "["), String.eq(o, "("), t, name, hot)),
      Rewalk.either(Laws.rewalk.reads(kids, name, Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot),
        Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t),
        Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t), skip),
        Laws.rewalk.reads(r2, name, hot, left, live, skip))) : Rewalk.Hit}

def rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, ik, ir):
  +h = Rewalk.hit_keep(skip, Rewalk.here_hit(String.eq(o, "["), String.eq(o, "("), t, name, hot))
  +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
  +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
  +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
  rewalk.either2(h, h, Rewalk.either(Rewalk.hits(kids, name, hk, lk, vk, skip), Rewalk.hits(r2, name, hot, left, live,
    skip)), Rewalk.either(Laws.rewalk.reads(kids, name, hk, lk, vk, skip), Laws.rewalk.reads(r2, name, hot, left, live,
    skip)), {==}, rewalk.either2(Rewalk.hits(kids, name, hk, lk, vk, skip), Laws.rewalk.reads(kids, name, hk, lk, vk,
    skip), Rewalk.hits(r2, name, hot, left, live, skip), Laws.rewalk.reads(r2, name, hot, left, live, skip), ik, ir))

# a bare group, then the rest of the chain
law rewalk.reads_group:
  for +kids: Tree.Node
  for +rest: Tree.Node
  for +name: String
  for +hot: Bool
  for +left: Nat
  for +live: Bool
  for +skip: Bool
  for ik: {Rewalk.hits(kids, name, hot, 0n, False{}, skip) == Laws.rewalk.reads(kids, name, hot, 0n, False{}, skip)
    : Rewalk.Hit}
  for ir: {Rewalk.hits(rest, name, hot, left, live, skip) == Laws.rewalk.reads(rest, name, hot, left, live, skip)
    : Rewalk.Hit}
  {Rewalk.either(Rewalk.hits(kids, name, hot, 0n, False{}, skip), Rewalk.hits(rest, name, hot, left, live, skip))
    == Rewalk.either(Laws.rewalk.reads(kids, name, hot, 0n, False{}, skip),
      Laws.rewalk.reads(rest, name, hot, left, live, skip)) : Rewalk.Hit}

def rewalk.reads_group(kids, rest, name, hot, left, live, skip, ik, ir):
  rewalk.either2(Rewalk.hits(kids, name, hot, 0n, False{}, skip), Laws.rewalk.reads(kids, name, hot, 0n, False{}, skip),
    Rewalk.hits(rest, name, hot, left, live, skip), Laws.rewalk.reads(rest, name, hot, left, live, skip), ik, ir)

# a statement: its own tokens (the left of a let skipped), its body, then the
# rest of the chain
law rewalk.reads_stmt:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +name: String
  for +hot: Bool
  for +left: Nat
  for +live: Bool
  for +skip: Bool
  for ik: {Rewalk.hits(kids, name, False{}, 0n, False{}, Rewalk.has_eq(kids))
    == Laws.rewalk.reads(kids, name, False{}, 0n, False{}, Rewalk.has_eq(kids)) : Rewalk.Hit}
  for ib: {Rewalk.hits(body, name, False{}, 0n, False{}, False{})
    == Laws.rewalk.reads(body, name, False{}, 0n, False{}, False{}) : Rewalk.Hit}
  for ir: {Rewalk.hits(rest, name, hot, left, live, skip) == Laws.rewalk.reads(rest, name, hot, left, live, skip)
    : Rewalk.Hit}
  {Rewalk.either(Rewalk.hits(kids, name, False{}, 0n, False{}, Rewalk.has_eq(kids)),
    Rewalk.either(Rewalk.hits(body, name, False{}, 0n, False{}, False{}), Rewalk.hits(rest, name, hot, left, live,
      skip)))
    == Rewalk.either(Laws.rewalk.reads(kids, name, False{}, 0n, False{}, Rewalk.has_eq(kids)),
      Rewalk.either(Laws.rewalk.reads(body, name, False{}, 0n, False{}, False{}),
        Laws.rewalk.reads(rest, name, hot, left, live, skip))) : Rewalk.Hit}

def rewalk.reads_stmt(kids, body, rest, name, hot, left, live, skip, ik, ib, ir):
  +k1 = Rewalk.hits(kids, name, False{}, 0n, False{}, Rewalk.has_eq(kids))
  +k2 = Laws.rewalk.reads(kids, name, False{}, 0n, False{}, Rewalk.has_eq(kids))
  +b1 = Rewalk.hits(body, name, False{}, 0n, False{}, False{})
  +b2 = Laws.rewalk.reads(body, name, False{}, 0n, False{}, False{})
  +r1 = Rewalk.hits(rest, name, hot, left, live, skip)
  +r2 = Laws.rewalk.reads(rest, name, hot, left, live, skip)
  rewalk.either2(k1, k2, Rewalk.either(b1, r1), Rewalk.either(b2, r2), ik, rewalk.either2(b1, b2, r1, r2, ib, ir))

def rewalk.reads_eq(nn, name, hot, left, live, skip):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, l, c}:
              match k:
                case Lex.TName{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_name(t, rest, name, hot, left, live, skip, rewalk.reads_eq(rest, name, hot,
                            left, live, skip))
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_name(t, rest, name, hot, left, live, skip, rewalk.reads_eq(rest, name, hot,
                            left, live, skip))
                        case Tree.NNil{}:
                          rewalk.reads_name(t, rest, name, hot, left, live, skip, rewalk.reads_eq(rest, name, hot,
                            left, live, skip))
                        case Tree.NCons{x, y}:
                          rewalk.reads_name(t, rest, name, hot, left, live, skip, rewalk.reads_eq(rest, name, hot,
                            left, live, skip))
                    case Tree.Leaf{x}:
                      rewalk.reads_name(t, rest, name, hot, left, live, skip, rewalk.reads_eq(rest, name, hot, left,
                        live, skip))
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_name(t, rest, name, hot, left, live, skip, rewalk.reads_eq(rest, name, hot, left,
                        live, skip))
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_name(t, rest, name, hot, left, live, skip, rewalk.reads_eq(rest, name, hot, left,
                        live, skip))
                    case Tree.NNil{}:
                      rewalk.reads_name(t, rest, name, hot, left, live, skip, rewalk.reads_eq(rest, name, hot, left,
                        live, skip))
                case Lex.TUpper{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TDotted{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TWild{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TKey{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TNum{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TStr{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TChar{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TComment{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TSpace{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TNewline{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TOp{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TColon{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TEq{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              rewalk.reads_eq(rest, name, hot, left, live, False{})
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, False{})
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, False{})
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, False{})
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, False{})
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, False{})
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, False{})
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, False{})
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, False{})
                case Lex.TBind{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TArrow{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TLam{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TAll{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TAmp{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TOpen{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TClose{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              +hk = Rewalk.pick_hot(skip, String.eq(o, "["), String.eq(o, "("), hot)
                              +lk = Rewalk.pick_left(skip, String.eq(o, "["), String.eq(o, "("), t)
                              +vk = Rewalk.pick_live(skip, String.eq(o, "["), String.eq(o, "("), t)
                              rewalk.reads_call(o, t, kids, r2, name, hot, left, live, skip, rewalk.reads_eq(kids,
                                name, hk, lk, vk, skip),
                                rewalk.reads_eq(r2, name, hot, left, live, skip))
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, hot, left, live, skip)
                case Lex.TComma{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left,
                                live), live, skip)
                        case Tree.Leaf{x}:
                          rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left, live),
                            live, skip)
                        case Tree.Stmt{kind, kids, body}:
                          rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left, live),
                            live, skip)
                        case Tree.NNil{}:
                          rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left, live),
                            live, skip)
                        case Tree.NCons{x, y}:
                          rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left, live),
                            live, skip)
                    case Tree.Leaf{x}:
                      rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left, live),
                        live, skip)
                    case Tree.Group{open, kids, close}:
                      rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left, live),
                        live, skip)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left, live),
                        live, skip)
                    case Tree.NNil{}:
                      rewalk.reads_eq(rest, name, Rewalk.step_hot(hot, left, live), Rewalk.step_left(left, live),
                        live, skip)
        case Tree.Group{open, +kids, close}:
          rewalk.reads_group(kids, rest, name, hot, left, live, skip, rewalk.reads_eq(kids, name, hot, 0n, False{},
            skip),
            rewalk.reads_eq(rest, name, hot, left, live, skip))
        case Tree.Stmt{kind, +kids, +body}:
          rewalk.reads_stmt(kids, body, rest, name, hot, left, live, skip,
            rewalk.reads_eq(kids, name, False{}, 0n, False{}, Rewalk.has_eq(kids)),
            rewalk.reads_eq(body, name, False{}, 0n, False{}, False{}), rewalk.reads_eq(rest, name, hot, left, live,
              skip))
        case Tree.NNil{}:
          rewalk.reads_eq(rest, name, hot, left, live, skip)
        case Tree.NCons{x, y}:
          rewalk.reads_eq(rest, name, hot, left, live, skip)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# the rule's narrow is the law's single
law rewalk.single_eq:
  for hh: Rewalk.How
  for +piece: Tree.Node
  {Rewalk.narrow(hh, piece) == Laws.rewalk.single(hh, piece) : Bool}

def rewalk.single_eq(hh, piece):
  match hh:
    case Rewalk.HWide{}:
      {==}
    case Rewalk.HSlot{}:
      {==}
    case Rewalk.HField{}:
      {==}
    case Rewalk.HLet{+binder}:
      Equal.cong(Rewalk.Hit, Bool, x => Rewalk.narrow_let(x), Rewalk.hits(piece, binder, False{}, 0n, False{}, False{}),
        Laws.rewalk.reads(piece, binder, False{}, 0n, False{}, False{}),
        rewalk.reads_eq(piece, binder, False{}, 0n, False{}, False{}))

# the rule's other_go over the rated sites is the law's whole
law rewalk.whole_eq:
  for sites: List<&2, Rewalk.Site>
  for +name: String
  for +args: String
  for +line: U32
  for +col: U32
  for +piece: Tree.Node
  {Rewalk.other_go(Rewalk.rate(sites, piece), name, args, line, col)
    == Laws.rewalk.whole(sites, name, args, line, col, piece) : Bool}

def rewalk.whole_eq(sites, name, args, line, col, piece):
  match sites:
    case Nil{}:
      {==}
    case Con{s, +rest}:
      match s:
        case Rewalk.Site{+nm, +as, +l, +c, len, +how}:
          +tw = Laws.rewalk.twin(nm, as, l, c, name, args, line, col)
          +lhs = Rewalk.other_go(Rewalk.rate(Rewalk.Site{nm, as, l, c, len, how} <> rest, piece), name, args, line, col)
          %rewalk.single_eq(how, piece) : {lhs == Bool.or(Bool.and(tw, Bool.not(_)),
            Laws.rewalk.whole(rest, name, args, line, col, piece)) : Bool}
          %rewalk.whole_eq(rest, name, args, line, col, piece) : {lhs
            == Bool.or(Bool.and(tw, Bool.not(Rewalk.narrow(how, piece))), _) : Bool}
          {==}

# the rule's earlier over the rated sites is the law's prior
law rewalk.prior_eq:
  for seen: List<&2, Rewalk.Site>
  for +name: String
  for +args: String
  for +line: U32
  for +col: U32
  for +piece: Tree.Node
  {Rewalk.earlier(Rewalk.rate(seen, piece), name, args, line, col)
    == Laws.rewalk.prior(seen, name, args, line, col, piece) : Bool}

def rewalk.prior_eq(seen, name, args, line, col, piece):
  match seen:
    case Nil{}:
      {==}
    case Con{s, +rest}:
      match s:
        case Rewalk.Site{+nm, +as, +l, +c, len, +how}:
          +tw = Laws.rewalk.twin(nm, as, l, c, name, args, line, col)
          +lhs = Rewalk.earlier(Rewalk.rate(Rewalk.Site{nm, as, l, c, len, how} <> rest, piece), name, args, line, col)
          %rewalk.single_eq(how, piece) : {lhs == Bool.or(Bool.and(tw, _),
            Laws.rewalk.prior(rest, name, args, line, col, piece)) : Bool}
          %rewalk.prior_eq(rest, name, args, line, col, piece) : {lhs
            == Bool.or(Bool.and(tw, Rewalk.narrow(how, piece)), _) : Bool}
          {==}

# a narrow site with no narrow twin before it: one finding
law rewalk.nar_len:
  for n: Bool
  for p: Bool
  for +name: String
  for +line: U32
  for +col: U32
  for +len: U32
  for +path: String
  {List.length(&2, F.Finding, Rewalk.report_nar(n, p, name, line, col, len, path))
    == Bool.pick(Nat, Bool.and(n, Bool.not(p)), 1n, 0n) : Nat}

def rewalk.nar_len(n, p, _name, _line, _col, _len, _path):
  match n p:
    case False{} p:
      {==}
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}

# a site with a whole twin, read narrow, and no narrow twin before it: one
# finding
law rewalk.dup_len:
  for d: Bool
  for +nar: Bool
  for +name: String
  for +args: String
  for +line: U32
  for +col: U32
  for +len: U32
  for +path: String
  for +seen: List<&2, Rewalk.Rated>
  {List.length(&2, F.Finding, Rewalk.report_dup(d, nar, name, args, line, col, len, path, seen))
    == Bool.pick(Nat, Bool.and(d, Bool.and(nar, Bool.not(Rewalk.earlier(seen, name, args, line, col)))), 1n, 0n)
    : Nat}

def rewalk.dup_len(d, nar, name, args, line, col, len, path, seen):
  match d:
    case False{}:
      {==}
    case True{}:
      rewalk.nar_len(nar, Rewalk.earlier(seen, name, args, line, col), name, line, col, len, path)

# one site, rated: one finding when the law flags it, none otherwise
law rewalk.one_len:
  for s: Rewalk.Site
  for +all: List<&2, Rewalk.Site>
  for +body: Tree.Node
  for +path: String
  for +seen: List<&2, Rewalk.Site>
  {List.length(&2, F.Finding, Rewalk.report_one(Rewalk.rate_one(s, body), Rewalk.rate(all, body), path,
    Rewalk.rate(seen, body))) == Bool.pick(Nat, Laws.rewalk.flag(s, all, body, seen), 1n, 0n) : Nat}

def rewalk.one_len(s, all, body, path, seen):
  match s:
    case Rewalk.Site{+name, +args, +line, +col, +len, +how}:
      +lhs = List.length(&2, F.Finding, Rewalk.report_one(Rewalk.rate_one(Rewalk.Site{name, args, line, col, len, how},
        body), Rewalk.rate(all, body), path, Rewalk.rate(seen, body)))
      %rewalk.whole_eq(all, name, args, line, col, body) : {lhs == Bool.pick(Nat, Bool.and(_,
        Bool.and(Laws.rewalk.single(how, body), Bool.not(Laws.rewalk.prior(seen, name, args, line, col, body)))), 1n,
          0n)
        : Nat}
      %rewalk.single_eq(how, body) : {lhs == Bool.pick(Nat, Bool.and(Rewalk.other_go(Rewalk.rate(all, body), name,
        args, line, col), Bool.and(_, Bool.not(Laws.rewalk.prior(seen, name, args, line, col, body)))), 1n, 0n) : Nat}
      %rewalk.prior_eq(seen, name, args, line, col, body) : {lhs == Bool.pick(Nat, Bool.and(Rewalk.other_go(
        Rewalk.rate(all, body), name, args, line, col), Bool.and(Rewalk.narrow(how, body), Bool.not(_))), 1n, 0n)
        : Nat}
      rewalk.dup_len(Rewalk.other_go(Rewalk.rate(all, body), name, args, line, col), Rewalk.narrow(how, body), name,
        args, line, col, len, path, Rewalk.rate(seen, body))

# a flag's one or none, onto the rest's count
law rewalk.add_pick:
  for f: Bool
  for m: Nat
  {Nat.add(Bool.pick(Nat, f, 1n, 0n), m) == Bool.pick(Nat, f, 1n+m, m) : Nat}

def rewalk.add_pick(f, _m):
  match f:
    case True{}:
      {==}
    case False{}:
      {==}

# the rule's report over the rated sites counts what the law counts
law rewalk.report_len:
  for sites: List<&2, Rewalk.Site>
  for +all: List<&2, Rewalk.Site>
  for +body: Tree.Node
  for +path: String
  for +seen: List<&2, Rewalk.Site>
  {List.length(&2, F.Finding, Rewalk.report(Rewalk.rate(sites, body), Rewalk.rate(all, body), path,
    Rewalk.rate(seen, body))) == Laws.rewalk.count(sites, all, body, seen) : Nat}

def rewalk.report_len(sites, all, body, path, seen):
  match sites:
    case Nil{}:
      {==}
    case Con{+s, +rest}:
      +one = Rewalk.report_one(Rewalk.rate_one(s, body), Rewalk.rate(all, body), path, Rewalk.rate(seen, body))
      +tl = Rewalk.report(Rewalk.rate(rest, body), Rewalk.rate(all, body), path, Rewalk.rate(s <> seen, body))
      +f = Laws.rewalk.flag(s, all, body, seen)
      +m = Laws.rewalk.count(rest, all, body, s <> seen)
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, one, tl)),
        Nat.add(List.length(&2, F.Finding, one), List.length(&2, F.Finding, tl)), Bool.pick(Nat, f, 1n+m, m),
        M1.esc.app(one, tl),
        Equal.trans(Nat, Nat.add(List.length(&2, F.Finding, one), List.length(&2, F.Finding, tl)),
          Nat.add(Bool.pick(Nat, f, 1n, 0n), m), Bool.pick(Nat, f, 1n+m, m),
          M1.esc.add(List.length(&2, F.Finding, one), Bool.pick(Nat, f, 1n, 0n), List.length(&2, F.Finding, tl), m,
            rewalk.one_len(s, all, body, path, seen), rewalk.report_len(rest, all, body, path, s <> seen)),
          rewalk.add_pick(f, m)))

# the rule's sites of a piece are the law's
law rewalk.sites_eq:
  for +nn: Tree.Node
  for +self: String
  for +lp: List<&2, String>
  {Rewalk.pin(Rewalk.mark(nn), Rewalk.apply(nn, Rewalk.gather(nn, self, lp, Rewalk.binds(nn, []))))
    == Laws.rewalk.sites(nn, self, lp) : List<&2, Rewalk.Site>}

def rewalk.sites_eq(nn, self, lp):
  +lhs = Rewalk.pin(Rewalk.mark(nn), Rewalk.apply(nn, Rewalk.gather(nn, self, lp, Rewalk.binds(nn, []))))
  %rewalk.binds_eq(nn, []) : {lhs == Laws.rewalk.pin(Laws.rewalk.marks(nn), Laws.rewalk.apply(nn,
    Laws.rewalk.gather(nn, self, lp, _))) : List<&2, Rewalk.Site>}
  %rewalk.gather_eq(nn, self, lp, Rewalk.binds(nn, [])) : {lhs == Laws.rewalk.pin(Laws.rewalk.marks(nn),
    Laws.rewalk.apply(nn, _)) : List<&2, Rewalk.Site>}
  %rewalk.apply_eq(nn, Rewalk.gather(nn, self, lp, Rewalk.binds(nn, []))) : {lhs
    == Laws.rewalk.pin(Laws.rewalk.marks(nn), _) : List<&2, Rewalk.Site>}
  %rewalk.marks_eq(nn) : {lhs == Laws.rewalk.pin(_, Rewalk.apply(nn, Rewalk.gather(nn, self, lp, Rewalk.binds(nn,
    [])))) : List<&2, Rewalk.Site>}
  rewalk.pin_eq(Rewalk.mark(nn), Rewalk.apply(nn, Rewalk.gather(nn, self, lp, Rewalk.binds(nn, []))))

def Laws.rewalk_local_counts(nn, self, lp, path):
  +ss = Rewalk.pin(Rewalk.mark(nn), Rewalk.apply(nn, Rewalk.gather(nn, self, lp, Rewalk.binds(nn, []))))
  %rewalk.sites_eq(nn, self, lp) : {List.length(&2, F.Finding, Rewalk.report(Rewalk.rate(ss, nn), Rewalk.rate(ss, nn),
    path, [])) == Laws.rewalk.count(_, _, nn, []) : Nat}
  rewalk.report_len(ss, ss, nn, path, [])

# two finding lists joined: the counts added
law rewalk.two_len:
  for a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for -ma: Nat
  for -mb: Nat
  for ea: {List.length(&2, F.Finding, a) == ma : Nat}
  for eb: {List.length(&2, F.Finding, b) == mb : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b])) == Nat.add(ma, mb) : Nat}

def rewalk.two_len(a, b, ma, mb, ea, eb):
  M1.pick.join(a, List.append(&2, F.Finding, b, Nil{}), ma, mb, ea, M1.pick.last(b, mb, eb))

# three finding lists joined: the counts added
law rewalk.three_len:
  for a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for +c: List<&2, F.Finding>
  for -ma: Nat
  for -mb: Nat
  for -mc: Nat
  for ea: {List.length(&2, F.Finding, a) == ma : Nat}
  for eb: {List.length(&2, F.Finding, b) == mb : Nat}
  for ec: {List.length(&2, F.Finding, c) == mc : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])) == Nat.add(ma, Nat.add(mb, mc)) : Nat}

def rewalk.three_len(a, b, c, ma, mb, mc, ea, eb, ec):
  M1.pick.join(a, List.append(&2, F.Finding, b, List.append(&2, F.Finding, c, Nil{})), ma, Nat.add(mb, mc), ea,
    M1.pick.join(b, List.append(&2, F.Finding, c, Nil{}), mb, mc, eb, M1.pick.last(c, mc, ec)))

# a statement's case-arm findings: its own tokens, its body, then what follows
law rewalk.visit_stmt:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +lp: List<&2, String>
  for +path: String
  for ek: {List.length(&2, F.Finding, Rewalk.visit(kids, self, lp, path)) == Laws.rewalk.arms(kids, self, lp) : Nat}
  for eb: {List.length(&2, F.Finding, Rewalk.visit(body, self, lp, path)) == Laws.rewalk.arms(body, self, lp) : Nat}
  for er: {List.length(&2, F.Finding, Rewalk.visit(rest, self, lp, path)) == Laws.rewalk.arms(rest, self, lp) : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [Rewalk.visit(kids, self, lp, path),
    Rewalk.visit(body, self, lp, path), Rewalk.visit(rest, self, lp, path)]))
    == Nat.add(Laws.rewalk.arms(kids, self, lp), Nat.add(Laws.rewalk.arms(body, self, lp),
      Laws.rewalk.arms(rest, self, lp))) : Nat}

def rewalk.visit_stmt(kids, body, rest, self, lp, path, ek, eb, er):
  rewalk.three_len(Rewalk.visit(kids, self, lp, path), Rewalk.visit(body, self, lp, path), Rewalk.visit(rest, self, lp,
    path), Laws.rewalk.arms(kids, self, lp), Laws.rewalk.arms(body, self, lp), Laws.rewalk.arms(rest, self, lp), ek,
    eb, er)

# a case arm: its own piece, the arms in it, then what follows
law rewalk.visit_case:
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +lp: List<&2, String>
  for +path: String
  for eb: {List.length(&2, F.Finding, Rewalk.visit(body, self, lp, path)) == Laws.rewalk.arms(body, self, lp) : Nat}
  for er: {List.length(&2, F.Finding, Rewalk.visit(rest, self, lp, path)) == Laws.rewalk.arms(rest, self, lp) : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [Rewalk.local(body, self, lp, path),
    Rewalk.visit(body, self, lp, path), Rewalk.visit(rest, self, lp, path)]))
    == Nat.add(Laws.rewalk.piece(body, self, lp), Nat.add(Laws.rewalk.arms(body, self, lp),
      Laws.rewalk.arms(rest, self, lp))) : Nat}

def rewalk.visit_case(body, rest, self, lp, path, eb, er):
  rewalk.three_len(Rewalk.local(body, self, lp, path), Rewalk.visit(body, self, lp, path), Rewalk.visit(rest, self, lp,
    path), Laws.rewalk.piece(body, self, lp), Laws.rewalk.arms(body, self, lp), Laws.rewalk.arms(rest, self, lp),
    Laws.rewalk_local_counts(body, self, lp, path), eb, er)

def Laws.rewalk_visit_counts(nn, self, lp, path):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SDef{}:
              rewalk.visit_stmt(kids, body, rest, self, lp, path, Laws.rewalk_visit_counts(kids, self, lp, path),
                Laws.rewalk_visit_counts(body, self, lp, path), Laws.rewalk_visit_counts(rest, self, lp, path))
            case Tree.SType{}:
              rewalk.visit_stmt(kids, body, rest, self, lp, path, Laws.rewalk_visit_counts(kids, self, lp, path),
                Laws.rewalk_visit_counts(body, self, lp, path), Laws.rewalk_visit_counts(rest, self, lp, path))
            case Tree.SLaw{}:
              rewalk.visit_stmt(kids, body, rest, self, lp, path, Laws.rewalk_visit_counts(kids, self, lp, path),
                Laws.rewalk_visit_counts(body, self, lp, path), Laws.rewalk_visit_counts(rest, self, lp, path))
            case Tree.SImport{}:
              rewalk.visit_stmt(kids, body, rest, self, lp, path, Laws.rewalk_visit_counts(kids, self, lp, path),
                Laws.rewalk_visit_counts(body, self, lp, path), Laws.rewalk_visit_counts(rest, self, lp, path))
            case Tree.SCase{}:
              rewalk.visit_case(body, rest, self, lp, path, Laws.rewalk_visit_counts(body, self, lp, path),
                Laws.rewalk_visit_counts(rest, self, lp, path))
            case Tree.SFor{}:
              rewalk.visit_stmt(kids, body, rest, self, lp, path, Laws.rewalk_visit_counts(kids, self, lp, path),
                Laws.rewalk_visit_counts(body, self, lp, path), Laws.rewalk_visit_counts(rest, self, lp, path))
            case Tree.SLet{}:
              rewalk.visit_stmt(kids, body, rest, self, lp, path, Laws.rewalk_visit_counts(kids, self, lp, path),
                Laws.rewalk_visit_counts(body, self, lp, path), Laws.rewalk_visit_counts(rest, self, lp, path))
            case Tree.STerm{}:
              rewalk.visit_stmt(kids, body, rest, self, lp, path, Laws.rewalk_visit_counts(kids, self, lp, path),
                Laws.rewalk_visit_counts(body, self, lp, path), Laws.rewalk_visit_counts(rest, self, lp, path))
        case Tree.Group{open, +kids, close}:
          rewalk.two_len(Rewalk.visit(kids, self, lp, path), Rewalk.visit(rest, self, lp, path),
            Laws.rewalk.arms(kids, self, lp), Laws.rewalk.arms(rest, self, lp),
            Laws.rewalk_visit_counts(kids, self, lp, path), Laws.rewalk_visit_counts(rest, self, lp, path))
        case Tree.Leaf{tok}:
          Laws.rewalk_visit_counts(rest, self, lp, path)
        case Tree.NNil{}:
          Laws.rewalk_visit_counts(rest, self, lp, path)
        case Tree.NCons{x, y}:
          Laws.rewalk_visit_counts(rest, self, lp, path)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# the rule's called names are the law's
law rewalk.called_eq:
  for nn: Tree.Node
  {Rewalk.called(nn) == Laws.rewalk.called(nn) : List<&2, String>}

# a callee, then what its group and the rest call
law rewalk.called_call:
  for +o: String
  for +t: String
  for +kids: Tree.Node
  for +r2: Tree.Node
  for ek: {Rewalk.called(kids) == Laws.rewalk.called(kids) : List<&2, String>}
  for er: {Rewalk.called(r2) == Laws.rewalk.called(r2) : List<&2, String>}
  {Bool.pick(List<&2, String>, String.eq(o, "("), t <> List.concat(&2, String, [Rewalk.called(kids),
    Rewalk.called(r2)]), List.concat(&2, String, [Rewalk.called(kids), Rewalk.called(r2)]))
    == Bool.pick(List<&2, String>, String.eq(o, "("), t <> List.concat(&2, String, [Laws.rewalk.called(kids),
      Laws.rewalk.called(r2)]), List.concat(&2, String, [Laws.rewalk.called(kids), Laws.rewalk.called(r2)]))
    : List<&2, String>}

def rewalk.called_call(o, t, kids, r2, ek, er):
  Equal.cong(List<&2, String>, List<&2, String>, m => Bool.pick(List<&2, String>, String.eq(o, "("), t <> m, m),
    List.concat(&2, String, [Rewalk.called(kids), Rewalk.called(r2)]),
    List.concat(&2, String, [Laws.rewalk.called(kids), Laws.rewalk.called(r2)]),
    rewalk.cat2(String, Rewalk.called(kids), Laws.rewalk.called(kids), Rewalk.called(r2), Laws.rewalk.called(r2), ek,
      er))

def rewalk.called_eq(nn):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, l, c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{open, +kids, close}:
                      match open:
                        case Lex.Tok{ok, +o, ol, oc}:
                          rewalk.called_call(o, t, kids, r2, rewalk.called_eq(kids), rewalk.called_eq(r2))
                    case Tree.Leaf{x}:
                      rewalk.called_eq(rest)
                    case Tree.Stmt{kind, kids, body}:
                      rewalk.called_eq(rest)
                    case Tree.NNil{}:
                      rewalk.called_eq(rest)
                    case Tree.NCons{x, y}:
                      rewalk.called_eq(rest)
                case Tree.Leaf{x}:
                  rewalk.called_eq(rest)
                case Tree.Group{open, kids, close}:
                  rewalk.called_eq(rest)
                case Tree.Stmt{kind, kids, body}:
                  rewalk.called_eq(rest)
                case Tree.NNil{}:
                  rewalk.called_eq(rest)
        case Tree.Group{open, +kids, close}:
          rewalk.cat2(String, Rewalk.called(kids), Laws.rewalk.called(kids), Rewalk.called(rest),
            Laws.rewalk.called(rest), rewalk.called_eq(kids), rewalk.called_eq(rest))
        case Tree.Stmt{kind, +kids, +body}:
          rewalk.cat3(String, Rewalk.called(kids), Laws.rewalk.called(kids), Rewalk.called(body),
            Laws.rewalk.called(body), Rewalk.called(rest), Laws.rewalk.called(rest), rewalk.called_eq(kids),
            rewalk.called_eq(body), rewalk.called_eq(rest))
        case Tree.NNil{}:
          rewalk.called_eq(rest)
        case Tree.NCons{x, y}:
          rewalk.called_eq(rest)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# a lazy or is the plain or
law rewalk.or_else:
  for b: Bool
  for t: List<&2, String>
  for +set: List<&2, String>
  for ih: {Rewalk.any_of(t, set) == Laws.rewalk.any(t, set) : Bool}
  {Lazy.or_else(b, _u => Rewalk.any_of(t, set)) == Bool.or(b, Laws.rewalk.any(t, set)) : Bool}

def rewalk.or_else(b, _t, _set, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# the rule's any_of is the law's any
law rewalk.any_eq:
  for cs: List<&2, String>
  for +set: List<&2, String>
  {Rewalk.any_of(cs, set) == Laws.rewalk.any(cs, set) : Bool}

def rewalk.any_eq(cs, set):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      rewalk.or_else(List.contains(~String, ~String.eq, set, c), t, set, rewalk.any_eq(t, set))

# the rule's looping defs are the law's
law rewalk.loops_eq:
  for ds: List<&2, Calls.Def>
  for +acc: List<&2, String>
  {Rewalk.loops.go(ds, acc) == Laws.rewalk.loops(ds, acc) : List<&2, String>}

def rewalk.loops_eq(ds, acc):
  match ds:
    case Nil{}:
      {==}
    case Con{d, +rest}:
      match d:
        case Calls.Def{+name, sig, +body}:
          +lhs = Rewalk.loops.go(Calls.Def{name, sig, body} <> rest, acc)
          %rewalk.called_eq(body) : {lhs == Laws.rewalk.loops(rest, Bool.pick(List<&2, String>,
            Bool.or(List.contains(~String, ~String.eq, _, name), Laws.rewalk.any(_, acc)), name <> acc, acc))
            : List<&2, String>}
          %rewalk.any_eq(Rewalk.called(body), acc) : {lhs == Laws.rewalk.loops(rest, Bool.pick(List<&2, String>,
            Bool.or(List.contains(~String, ~String.eq, Rewalk.called(body), name), _), name <> acc, acc))
            : List<&2, String>}
          rewalk.loops_eq(rest, Bool.pick(List<&2, String>, Bool.or(List.contains(~String, ~String.eq,
            Rewalk.called(body), name), Rewalk.any_of(Rewalk.called(body), acc)), name <> acc, acc))

# one def's findings, exempt or its piece and its arms
law rewalk.stop:
  for b: Bool
  for +body: Tree.Node
  for +name: String
  for +lp: List<&2, String>
  for +path: String
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, b, [], _u => List.concat(&2, F.Finding,
    [Rewalk.local(body, name, lp, path), Rewalk.visit(body, name, lp, path)])))
    == Bool.pick(Nat, b, 0n, Nat.add(Laws.rewalk.piece(body, name, lp), Laws.rewalk.arms(body, name, lp))) : Nat}

def rewalk.stop(b, body, name, lp, path):
  match b:
    case True{}:
      {==}
    case False{}:
      rewalk.two_len(Rewalk.local(body, name, lp, path), Rewalk.visit(body, name, lp, path),
        Laws.rewalk.piece(body, name, lp), Laws.rewalk.arms(body, name, lp),
        Laws.rewalk_local_counts(body, name, lp, path), Laws.rewalk_visit_counts(body, name, lp, path))

# rewalk's def walk: the findings gathered so far, then each def's
law rewalk.go:
  for ds: List<&2, Calls.Def>
  for +lp: List<&2, String>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Rewalk.check.go(ds, lp, path, acc)) == M1.pick.sum(acc, Laws.rewalk.total(ds, lp, path))
    : Nat}

def rewalk.go(ds, lp, path, acc):
  match ds:
    case Nil{}:
      M1.pick.rev(acc, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +x = Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [], _u => List.concat(&2, F.Finding,
        [Rewalk.local(body, name, lp, path), Rewalk.visit(body, name, lp, path)]))
      +n = Bool.pick(Nat, Calls.exempt(path, sig), 0n, Nat.add(Laws.rewalk.piece(body, name, lp),
        Laws.rewalk.arms(body, name, lp)))
      Equal.trans(Nat, List.length(&2, F.Finding, Rewalk.check.go(rest, lp, path, x <> acc)),
        M1.pick.sum(acc, Nat.add(List.length(&2, F.Finding, x), Laws.rewalk.total(rest, lp, path))),
        M1.pick.sum(acc, Nat.add(n, Laws.rewalk.total(rest, lp, path))),
        rewalk.go(rest, lp, path, x <> acc),
        Equal.cong(Nat, Nat, m => M1.pick.sum(acc, Nat.add(m, Laws.rewalk.total(rest, lp, path))),
          List.length(&2, F.Finding, x), n, rewalk.stop(Calls.exempt(path, sig), body, name, lp, path)))

def Laws.rewalk_counts(path, _text, _toks, tree, _bound, _items):
  +ds = Calls.defs(tree)
  %rewalk.loops_eq(ds, []) : {List.length(&2, F.Finding, Rewalk.check.go(ds, Rewalk.loops.go(ds, []), path, []))
    == Laws.rewalk.total(ds, _, path) : Nat}
  rewalk.go(ds, Rewalk.loops.go(ds, []), path, [])
