# proofs of laws/StringsReportLongLiteralArms.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/syntax/tree.bend as Tree
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/perf/strings.bend as Strings
import ../laws/StringsReportLongLiteralArms.bend as Laws
import ../laws/defs/MatchArmRules.bend as D1
import ./lemmas/MatchStatementCounts.bend as M1
import ./lemmas/Pick.bend as M2

# the chars of a closed string arm, else zero, to the rule and to the law
law strings.pick:
  for b: Bool
  for -x: U32
  {Strings.size(Bool.pick(Maybe<&2, U32>, b, Some{x}, None{})) == Bool.pick(U32, b, x, 0) : U32}

def strings.pick(b, _x):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the rule's string arm test on the pattern is the law's on the case
law strings.lit:
  for kids: Tree.Node
  {Strings.size(Strings.literal(T.pattern(kids))) == Laws.strings.size(kids) : U32}

def strings.lit(kids):
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
                  strings.pick(Strings.terminated(t), (U32.from_nat(String.length(t)) - 2 : U32))
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

# a body with no case left: the report reads the chars so far
law strings.base:
  for +nn: U32
  for +ch: U32
  for +path: String
  for +l: U32
  for +c: U32
  {List.length(&2, F.Finding, Strings.report(Strings.Tally{nn, ch}, path, l, c))
    == Bool.pick(Nat, U32.is_gt(ch, 64), 1n, 0n) : Nat}

def strings.base(n, ch, path, l, c):
  M2.chars.one(U32.is_gt(ch, 64), F.Finding{path, l, c, 5, "strings",
    "This match has " ++ U32.show(n) ++ " string-literal cases totalling " ++ U32.show(ch)
    ++ " characters, over the limit of 64, which blows up compile time and memory;"
    ++ " map the string to a sum type once and match on that."})

# a case statement onto a body the law holds for, at the rule's count
law strings.step:
  for +rest: Tree.Node
  for +nn: U32
  for +ch: U32
  for +kids: Tree.Node
  for +path: String
  for +l: U32
  for +c: U32
  for ih: {List.length(&2, F.Finding, Strings.report(Strings.tally(rest,
      (nn + Strings.one(Strings.literal(T.pattern(kids))) : U32),
      (ch + Strings.size(Strings.literal(T.pattern(kids))) : U32)), path, l, c))
    == Bool.pick(Nat, U32.is_gt(Laws.strings.total(rest, (ch + Strings.size(Strings.literal(T.pattern(kids))) : U32)),
      64), 1n, 0n) : Nat}
  {List.length(&2, F.Finding, Strings.report(Strings.tally(rest,
      (nn + Strings.one(Strings.literal(T.pattern(kids))) : U32),
      (ch + Strings.size(Strings.literal(T.pattern(kids))) : U32)), path, l, c))
    == Bool.pick(Nat, U32.is_gt(Laws.strings.total(rest, (ch + Laws.strings.size(kids) : U32)), 64), 1n, 0n) : Nat}

def strings.step(rest, nn, ch, kids, path, l, c, ih):
  Equal.trans(Nat,
    List.length(&2, F.Finding, Strings.report(Strings.tally(rest,
      (nn + Strings.one(Strings.literal(T.pattern(kids))) : U32),
      (ch + Strings.size(Strings.literal(T.pattern(kids))) : U32)), path, l, c)),
    Bool.pick(Nat, U32.is_gt(Laws.strings.total(rest, (ch + Strings.size(Strings.literal(T.pattern(kids))) : U32)),
      64), 1n, 0n),
    Bool.pick(Nat, U32.is_gt(Laws.strings.total(rest, (ch + Laws.strings.size(kids) : U32)), 64), 1n, 0n),
    ih,
    Equal.cong(U32, Nat, z => Bool.pick(Nat, U32.is_gt(Laws.strings.total(rest, (ch + z : U32)), 64), 1n, 0n),
      Strings.size(Strings.literal(T.pattern(kids))), Laws.strings.size(kids), strings.lit(kids)))

# strings' tally reports when the chars the law totals are over 64
law strings.tally:
  for body: Tree.Node
  for +nn: U32
  for +ch: U32
  for +path: String
  for +l: U32
  for +c: U32
  {List.length(&2, F.Finding, Strings.report(Strings.tally(body, nn, ch), path, l, c))
    == Bool.pick(Nat, U32.is_gt(Laws.strings.total(body, ch), 64), 1n, 0n) : Nat}

def strings.tally(body, n, ch, path, l, c):
  match body:
    case Tree.Leaf{tok}:
      strings.base(n, ch, path, l, c)
    case Tree.Group{o, gk, cl}:
      strings.base(n, ch, path, l, c)
    case Tree.Stmt{kind, sk, sb}:
      strings.base(n, ch, path, l, c)
    case Tree.NNil{}:
      strings.base(n, ch, path, l, c)
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          strings.tally(rest, n, ch, path, l, c)
        case Tree.Group{o, gk, cl}:
          strings.tally(rest, n, ch, path, l, c)
        case Tree.Stmt{kind, +kids, b}:
          match kind:
            case Tree.SDef{}:
              strings.tally(rest, n, ch, path, l, c)
            case Tree.SType{}:
              strings.tally(rest, n, ch, path, l, c)
            case Tree.SLaw{}:
              strings.tally(rest, n, ch, path, l, c)
            case Tree.SImport{}:
              strings.tally(rest, n, ch, path, l, c)
            case Tree.SCase{}:
              strings.step(rest, n, ch, kids, path, l, c,
                strings.tally(rest, (n + Strings.one(Strings.literal(T.pattern(kids))) : U32),
                  (ch + Strings.size(Strings.literal(T.pattern(kids))) : U32), path, l, c))
            case Tree.SFor{}:
              strings.tally(rest, n, ch, path, l, c)
            case Tree.SLet{}:
              strings.tally(rest, n, ch, path, l, c)
            case Tree.STerm{}:
              strings.tally(rest, n, ch, path, l, c)
        case Tree.NNil{}:
          strings.tally(rest, n, ch, path, l, c)
        case Tree.NCons{nh, nt}:
          strings.tally(rest, n, ch, path, l, c)

# a statement's own finding: one when it is a match whose closed string arms
# total over 64 chars
law strings.stmt:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Strings.on_stmt(kids, body, path))
    == Bool.pick(Nat, Bool.and(D1.chars.is_match(kids), U32.is_gt(Laws.strings.total(body, 0), 64)), 1n, 0n) : Nat}

def strings.stmt(kids, body, path):
  Equal.trans(Nat,
    List.length(&2, F.Finding, Strings.on_stmt(kids, body, path)),
    Bool.pick(Nat, Bool.and(T.keyword(kids, "match"), U32.is_gt(Laws.strings.total(body, 0), 64)), 1n, 0n),
    Bool.pick(Nat, Bool.and(D1.chars.is_match(kids), U32.is_gt(Laws.strings.total(body, 0), 64)), 1n, 0n),
    M1.chars.gate(T.keyword(kids, "match"),
      Strings.report(Strings.tally(body, 0, 0), path, Tree.line(kids), Tree.col(kids)),
      U32.is_gt(Laws.strings.total(body, 0), 64),
      strings.tally(body, 0, 0, path, Tree.line(kids), Tree.col(kids))),
    Equal.cong(Bool, Nat, z => Bool.pick(Nat, Bool.and(z, U32.is_gt(Laws.strings.total(body, 0), 64)), 1n, 0n),
      T.keyword(kids, "match"), D1.chars.is_match(kids), M1.chars.key(kids)))

# strings' walk counts the matches the law counts
law strings.walk:
  for n: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Strings.walk(n, path)) == Laws.strings.count(n) : Nat}

def strings.walk(nn, path):
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
          strings.walk(rest, path)
        case Tree.Group{o, gk, cl}:
          strings.walk(rest, path)
        case Tree.Stmt{kind, +kids, +body}:
          M1.chars.sum(Strings.on_stmt(kids, body, path), Strings.walk(body, path), Strings.walk(rest, path),
            Bool.pick(Nat, Bool.and(D1.chars.is_match(kids), U32.is_gt(Laws.strings.total(body, 0), 64)), 1n, 0n),
            Laws.strings.count(body), Laws.strings.count(rest),
            strings.stmt(kids, body, path), strings.walk(body, path), strings.walk(rest, path))
        case Tree.NNil{}:
          strings.walk(rest, path)
        case Tree.NCons{nh, nt}:
          strings.walk(rest, path)

def Laws.strings_counts(path, _text, _toks, tree, _bound, _items):
  strings.walk(tree, path)
