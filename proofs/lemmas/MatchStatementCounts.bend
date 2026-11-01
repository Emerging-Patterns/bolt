# statement walks and gathered-list counts for the match and index rules
import Base
import ../../src/syntax/lex.bend as Lex
import ../../src/finding.bend as F
import ../../src/rules/tokens.bend as T
import ../../src/lazy/lazy.bend as Lazy
import ../../src/syntax/tree.bend as Tree
import ../../src/rules/correctness/pick.bend as Pick
import ../../laws/defs/MatchArmRules.bend as D1
import ./Pick.bend as M1

# The match rules, chars and strings: a statement's walk joins three lists,
# its own finding, its body's and the rest's, so the count is their sum.

# appending nothing keeps the length
law chars.nil:
  for xs: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.append(&2, F.Finding, xs, [])) == List.length(&2, F.Finding, xs) : Nat}

def chars.nil(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, List.append(&2, F.Finding, t, [])),
        List.length(&2, F.Finding, t), chars.nil(t))

# three lists joined count as the sum of their counts
law chars.three:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for +c: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c]))
    == Nat.add(List.length(&2, F.Finding, a), Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c)))
    : Nat}

def chars.three(a, b, c):
  +bc = List.append(&2, F.Finding, b, List.append(&2, F.Finding, c, []))
  Equal.trans(Nat,
    List.length(&2, F.Finding, List.append(&2, F.Finding, a, bc)),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, bc)),
    Nat.add(List.length(&2, F.Finding, a), Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c))),
    M1.esc.app(a, bc),
    M1.esc.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, a), List.length(&2, F.Finding, bc),
      Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c)), {==},
      Equal.trans(Nat,
        List.length(&2, F.Finding, bc),
        Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, List.append(&2, F.Finding, c, []))),
        Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c)),
        M1.esc.app(b, List.append(&2, F.Finding, c, [])),
        M1.esc.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, b),
          List.length(&2, F.Finding, List.append(&2, F.Finding, c, [])), List.length(&2, F.Finding, c), {==},
          chars.nil(c)))))

# a statement that is not a match adds nothing; a match adds what its report does
law chars.gate:
  for b: Bool
  for -more: List<&2, F.Finding>
  for -g: Bool
  for ih: {List.length(&2, F.Finding, more) == Bool.pick(Nat, g, 1n, 0n) : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(b), [], _u => more))
    == Bool.pick(Nat, Bool.and(b, g), 1n, 0n) : Nat}

def chars.gate(b, _more, _g, ih):
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# the rule's keyword test is the law's
law chars.key:
  for kids: Tree.Node
  {T.keyword(kids, "match") == D1.chars.is_match(kids) : Bool}

def chars.key(kids):
  match kids:
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{o, gk, cl}:
      {==}
    case Tree.Stmt{kind, sk, sb}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{h, rest}:
      match h:
        case Tree.Leaf{Lex.Tok{kind, t, l, c}}:
          match kind:
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
        case Tree.Group{o, gk, cl}:
          {==}
        case Tree.Stmt{kind, sk, sb}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{nh, nt}:
          {==}

# a statement onto the rest: its finding, its body's and the rest's
law chars.sum:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for +c: List<&2, F.Finding>
  for -x: Nat
  for -y: Nat
  for -z: Nat
  for e1: {List.length(&2, F.Finding, a) == x : Nat}
  for e2: {List.length(&2, F.Finding, b) == y : Nat}
  for e3: {List.length(&2, F.Finding, c) == z : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])) == Nat.add(x, Nat.add(y, z)) : Nat}

def chars.sum(a, b, c, x, y, z, e1, e2, e3):
  Equal.trans(Nat,
    List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])),
    Nat.add(List.length(&2, F.Finding, a), Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c))),
    Nat.add(x, Nat.add(y, z)),
    chars.three(a, b, c),
    M1.esc.add(List.length(&2, F.Finding, a), x,
      Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c)), Nat.add(y, z), e1,
      M1.esc.add(List.length(&2, F.Finding, b), y, List.length(&2, F.Finding, c), z, e2, e3)))

# two lists joined count as the sum of their counts
law index.two:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for -x: Nat
  for -y: Nat
  for e1: {List.length(&2, F.Finding, a) == x : Nat}
  for e2: {List.length(&2, F.Finding, b) == y : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b])) == Nat.add(x, y) : Nat}

def index.two(a, b, x, y, e1, e2):
  Equal.trans(Nat,
    List.length(&2, F.Finding, List.append(&2, F.Finding, a, List.append(&2, F.Finding, b, []))),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, List.append(&2, F.Finding, b, []))),
    Nat.add(x, y),
    M1.esc.app(a, List.append(&2, F.Finding, b, [])),
    M1.esc.add(List.length(&2, F.Finding, a), x, List.length(&2, F.Finding, List.append(&2, F.Finding, b, [])), y, e1,
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, b, [])), List.length(&2, F.Finding, b), y,
        chars.nil(b), e2)))

# the counts of gathered finding lists, the last gathered first
def index.sum(acc: List<&2, List<&2, F.Finding>>) -> Nat:
  match acc:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(index.sum(t), List.length(&2, F.Finding, h))

# adding is associative
law index.assoc:
  for a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def index.assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), index.assoc(p, b, c))

# reversing gathered lists onto others and joining them counts them all
law index.flat:
  for xs: List<&2, List<&2, F.Finding>>
  for +ys: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, List.reverse.go(&2, List<&2, F.Finding>, xs, ys)))
    == Nat.add(index.sum(xs), List.length(&2, F.Finding, List.concat(&2, F.Finding, ys))) : Nat}

def index.flat(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +cs = List.concat(&2, F.Finding, ys)
      Equal.trans(Nat,
        List.length(&2, F.Finding, List.concat(&2, F.Finding, List.reverse.go(&2, List<&2, F.Finding>, t, h <> ys))),
        Nat.add(index.sum(t), List.length(&2, F.Finding, List.append(&2, F.Finding, h, cs))),
        Nat.add(Nat.add(index.sum(t), List.length(&2, F.Finding, h)), List.length(&2, F.Finding, cs)),
        index.flat(t, h <> ys),
        Equal.trans(Nat,
          Nat.add(index.sum(t), List.length(&2, F.Finding, List.append(&2, F.Finding, h, cs))),
          Nat.add(index.sum(t), Nat.add(List.length(&2, F.Finding, h), List.length(&2, F.Finding, cs))),
          Nat.add(Nat.add(index.sum(t), List.length(&2, F.Finding, h)), List.length(&2, F.Finding, cs)),
          Equal.cong(Nat, Nat, z => Nat.add(index.sum(t), z),
            List.length(&2, F.Finding, List.append(&2, F.Finding, h, cs)),
            Nat.add(List.length(&2, F.Finding, h), List.length(&2, F.Finding, cs)), M1.esc.app(h, cs)),
          Equal.sym(Nat,
            Nat.add(Nat.add(index.sum(t), List.length(&2, F.Finding, h)), List.length(&2, F.Finding, cs)),
            Nat.add(index.sum(t), Nat.add(List.length(&2, F.Finding, h), List.length(&2, F.Finding, cs))),
            index.assoc(index.sum(t), List.length(&2, F.Finding, h), List.length(&2, F.Finding, cs)))))
