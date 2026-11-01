# proofs of laws/CharsReportManyCharArms.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/syntax/tree.bend as Tree
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/correctness/chars.bend as Chars
import ../laws/CharsReportManyCharArms.bend as Laws
import ../laws/defs/MatchArmRules.bend as D1
import ./lemmas/MatchStatementCounts.bend as M1
import ./lemmas/Pick.bend as M2

# the rule's literal test on the pattern is the law's on the case
law chars.lit:
  for kids: Tree.Node
  {Chars.literal(T.pattern(kids)) == Laws.chars.opens(kids) : U32}

def chars.lit(kids):
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
      match rest:
        case Tree.Leaf{tok}:
          {==}
        case Tree.Group{o, gk, cl}:
          {==}
        case Tree.Stmt{kind, sk, sb}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{h2, r2}:
          match h2:
            case Tree.Leaf{Lex.Tok{kind, +t, l, c}}:
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

# a case statement onto a body the law holds for, at the rule's count
law chars.step:
  for +rest: Tree.Node
  for +nn: U32
  for +kids: Tree.Node
  for ih: {Chars.tally(rest, (nn + Chars.literal(T.pattern(kids)) : U32))
    == Laws.chars.arms(rest, (nn + Chars.literal(T.pattern(kids)) : U32)) : U32}
  {Chars.tally(rest, (nn + Chars.literal(T.pattern(kids)) : U32))
    == Laws.chars.arms(rest, (nn + Laws.chars.opens(kids) : U32)) : U32}

def chars.step(rest, nn, kids, ih):
  Equal.trans(U32,
    Chars.tally(rest, (nn + Chars.literal(T.pattern(kids)) : U32)),
    Laws.chars.arms(rest, (nn + Chars.literal(T.pattern(kids)) : U32)),
    Laws.chars.arms(rest, (nn + Laws.chars.opens(kids) : U32)),
    ih,
    Equal.cong(U32, U32, z => Laws.chars.arms(rest, (nn + z : U32)),
      Chars.literal(T.pattern(kids)), Laws.chars.opens(kids), chars.lit(kids)))

# chars' tally counts the arms the law counts
law chars.tally:
  for body: Tree.Node
  for +nn: U32
  {Chars.tally(body, nn) == Laws.chars.arms(body, nn) : U32}

def chars.tally(body, nn):
  match body:
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
          chars.tally(rest, nn)
        case Tree.Group{o, gk, cl}:
          chars.tally(rest, nn)
        case Tree.Stmt{kind, +kids, b}:
          match kind:
            case Tree.SDef{}:
              chars.tally(rest, nn)
            case Tree.SType{}:
              chars.tally(rest, nn)
            case Tree.SLaw{}:
              chars.tally(rest, nn)
            case Tree.SImport{}:
              chars.tally(rest, nn)
            case Tree.SCase{}:
              chars.step(rest, nn, kids, chars.tally(rest, (nn + Chars.literal(T.pattern(kids)) : U32)))
            case Tree.SFor{}:
              chars.tally(rest, nn)
            case Tree.SLet{}:
              chars.tally(rest, nn)
            case Tree.STerm{}:
              chars.tally(rest, nn)
        case Tree.NNil{}:
          chars.tally(rest, nn)
        case Tree.NCons{nh, nt}:
          chars.tally(rest, nn)

# a statement's own finding: one when it is a match over more than eight
# char arms
law chars.stmt:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Chars.on_stmt(kids, body, path))
    == Bool.pick(Nat, Bool.and(D1.chars.is_match(kids), U32.is_gt(Laws.chars.arms(body, 0), 8)), 1n, 0n) : Nat}

def chars.stmt(kids, body, path):
  +n = Chars.tally(body, 0)
  Equal.trans(Nat,
    List.length(&2, F.Finding, Chars.on_stmt(kids, body, path)),
    Bool.pick(Nat, Bool.and(T.keyword(kids, "match"), U32.is_gt(n, 8)), 1n, 0n),
    Bool.pick(Nat, Bool.and(D1.chars.is_match(kids), U32.is_gt(Laws.chars.arms(body, 0), 8)), 1n, 0n),
    M1.chars.gate(T.keyword(kids, "match"), Chars.report(n, path, Tree.line(kids), Tree.col(kids)), U32.is_gt(n, 8),
      M2.chars.one(U32.is_gt(n, 8), F.Finding{path, Tree.line(kids), Tree.col(kids), 5, "chars",
        "This match has " ++ U32.show(n) ++ " character-literal cases, over the limit of 8, which blows up compile time"
        ++ " and memory; compare Char.to_u32(c) instead."})),
    Equal.trans(Nat,
      Bool.pick(Nat, Bool.and(T.keyword(kids, "match"), U32.is_gt(n, 8)), 1n, 0n),
      Bool.pick(Nat, Bool.and(D1.chars.is_match(kids), U32.is_gt(n, 8)), 1n, 0n),
      Bool.pick(Nat, Bool.and(D1.chars.is_match(kids), U32.is_gt(Laws.chars.arms(body, 0), 8)), 1n, 0n),
      Equal.cong(Bool, Nat, z => Bool.pick(Nat, Bool.and(z, U32.is_gt(n, 8)), 1n, 0n),
        T.keyword(kids, "match"), D1.chars.is_match(kids), M1.chars.key(kids)),
      Equal.cong(U32, Nat, z => Bool.pick(Nat, Bool.and(D1.chars.is_match(kids), U32.is_gt(z, 8)), 1n, 0n),
        n, Laws.chars.arms(body, 0), chars.tally(body, 0))))

# chars' walk counts the matches the law counts
law chars.walk:
  for nn: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Chars.walk(nn, path)) == Laws.chars.count(nn) : Nat}

def chars.walk(nn, path):
  match nn:
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
          chars.walk(rest, path)
        case Tree.Group{o, gk, cl}:
          chars.walk(rest, path)
        case Tree.Stmt{kind, +kids, +body}:
          M1.chars.sum(Chars.on_stmt(kids, body, path), Chars.walk(body, path), Chars.walk(rest, path),
            Bool.pick(Nat, Bool.and(D1.chars.is_match(kids), U32.is_gt(Laws.chars.arms(body, 0), 8)), 1n, 0n),
            Laws.chars.count(body), Laws.chars.count(rest),
            chars.stmt(kids, body, path), chars.walk(body, path), chars.walk(rest, path))
        case Tree.NNil{}:
          chars.walk(rest, path)
        case Tree.NCons{nh, nt}:
          chars.walk(rest, path)

def Laws.chars_counts(path, _text, _toks, tree, _bound, _items):
  chars.walk(tree, path)
