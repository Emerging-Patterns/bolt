# `prefix` reports exactly, outside a LAWS.bend or a PROOF.bend, one finding
# (on the first) for each run among the significant tokens (spaces,
# newlines and comments dropped) of a dotted name `String.eq`, `(`,
# `String.take`, `(`, an argument, k, `)`, `,`, a string literal and `)`,
# or of a dotted name `String.eq`, `(`, a string literal, `,`,
# `String.take`, `(`, an argument, k, `)` and `)`, where k's text is the
# literal's length (laws/defs/PrefixLength.bend) in decimal and then `n`;
# and nothing else. The argument is every token up to the first comma not
# inside a bracket the argument opened, that comma included: any
# expression, a call such as `String.drop(m, 4n)` as well as a name, and a
# closing bracket the argument did not open ends the run first. So a take
# whose length is not the literal's is not reported, and since a comment is
# dropped and a string literal is one token, the shape written inside a
# comment or a string is not reported either.
#
# also rests on: laws/PrefixExempt.bend, laws/InertPrefix.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/prefix.bend as Prefix
import ../src/rules/tokens.bend as T
import ./defs/PrefixLength.bend as D1

# where the scan of a take's argument goes after a comma at the depth
def prefix_comma(dd: Nat) -> Prefix.Skip:
  match dd:
    case 0n:
      Prefix.SComma{}
    case 1n+p:
      Prefix.SGo{1n+p}

# where the scan goes after a closing bracket at the depth
def prefix_close(dd: Nat) -> Prefix.Skip:
  match dd:
    case 0n:
      Prefix.SClose{}
    case 1n+p:
      Prefix.SGo{p}

# where the scan goes after a token of the kind at the depth: an opening
# bracket one deeper, a closing one back out, a comma per prefix_comma
def prefix_step(kk: Lex.TokKind, dd: Nat) -> Prefix.Skip:
  match kk:
    case Lex.TComma{}:
      prefix_comma(dd)
    case Lex.TOpen{}:
      Prefix.SGo{1n+dd}
    case Lex.TClose{}:
      prefix_close(dd)
    case other:
      Prefix.SGo{dd}

# the tokens after the argument's comma, none when the take closes first
def prefix_skip(toks: List<&2, Lex.Tok>, sk: Prefix.Skip) -> Maybe<&2, List<&2, Lex.Tok>>:
  match toks:
    case Nil{}:
      None{}
    case Con{Lex.Tok{+k, t, l, c}, rest}:
      match sk:
        case Prefix.SComma{}:
          Some{Lex.Tok{k, t, l, c} <> rest}
        case Prefix.SClose{}:
          None{}
        case Prefix.SGo{dd}:
          prefix_skip(rest, prefix_step(k, dd))

# True for a dotted name
def prefix_dotted(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TDotted{}:
      True{}
    case other:
      False{}

# True when the tokens after the argument are k, `)`, `,`, a string literal
# and `)`, k its length
def prefix_tail_a(mr: Maybe<&2, List<&2, Lex.Tok>>) -> Bool:
  match mr:
    case None{}:
      False{}
    case Some{r}:
      match r:
        case Nil{}:
          False{}
        case Con{Lex.Tok{k6, +a6, l6, c6}, r6}:
          match r6:
            case Nil{}:
              False{}
            case Con{Lex.Tok{k7, +a7, l7, c7}, r7}:
              match r7:
                case Nil{}:
                  False{}
                case Con{Lex.Tok{k8, +a8, l8, c8}, r8}:
                  match r8:
                    case Nil{}:
                      False{}
                    case Con{Lex.Tok{+k9, +a9, l9, c9}, r9}:
                      match r9:
                        case Nil{}:
                          False{}
                        case Con{Lex.Tok{k10, +a10, l10, c10}, r10}:
                          Bool.and(String.eq(a7, ")"), Bool.and(String.eq(a8, ","), Bool.and(Lex.is_str(k9),
                            Bool.and(String.eq(a10, ")"), D1.prefix_fits(a6, a9)))))

# True when the tokens after the argument are k, `)` and `)`, k the
# literal's length
def prefix_tail_b(mr: Maybe<&2, List<&2, Lex.Tok>>, +lit: String) -> Bool:
  match mr:
    case None{}:
      False{}
    case Some{r}:
      match r:
        case Nil{}:
          False{}
        case Con{Lex.Tok{k8, +a8, l8, c8}, r8}:
          match r8:
            case Nil{}:
              False{}
            case Con{Lex.Tok{k9, +a9, l9, c9}, r9}:
              match r9:
                case Nil{}:
                  False{}
                case Con{Lex.Tok{k10, +a10, l10, c10}, r10}:
                  Bool.and(String.eq(a9, ")"), Bool.and(String.eq(a10, ")"), D1.prefix_fits(a8, lit)))

# True when a dotted `String.eq` of text tt, then these, open
# `String.eq(String.take(s, k), "..")`
def prefix_a(+k0: Lex.TokKind, +tt: String, toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Nil{}:
      False{}
    case Con{Lex.Tok{k1, +a1, l1, c1}, r1}:
      match r1:
        case Nil{}:
          False{}
        case Con{Lex.Tok{k2, +a2, l2, c2}, r2}:
          match r2:
            case Nil{}:
              False{}
            case Con{Lex.Tok{k3, +a3, l3, c3}, r3}:
              Bool.and(Bool.and(prefix_dotted(k0), Bool.and(String.eq(tt, "String.eq"), Bool.and(String.eq(a1, "("),
                  Bool.and(String.eq(a3, "("), String.eq(a2, "String.take"))))),
                prefix_tail_a(prefix_skip(r3, Prefix.SGo{0n})))

# True when a dotted `String.eq` of text tt, then these, open
# `String.eq("..", String.take(s, k))`
def prefix_b(+k0: Lex.TokKind, +tt: String, toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Nil{}:
      False{}
    case Con{Lex.Tok{k1, +a1, l1, c1}, r1}:
      match r1:
        case Nil{}:
          False{}
        case Con{Lex.Tok{+k2, +a2, l2, c2}, r2}:
          match r2:
            case Nil{}:
              False{}
            case Con{Lex.Tok{k3, +a3, l3, c3}, r3}:
              match r3:
                case Nil{}:
                  False{}
                case Con{Lex.Tok{k4, +a4, l4, c4}, r4}:
                  match r4:
                    case Nil{}:
                      False{}
                    case Con{Lex.Tok{k5, +a5, l5, c5}, r5}:
                      Bool.and(Bool.and(prefix_dotted(k0), Bool.and(String.eq(tt, "String.eq"),
                        Bool.and(String.eq(a1, "("), Bool.and(Lex.is_str(k2), Bool.and(String.eq(a3, ","),
                          Bool.and(String.eq(a4, "String.take"), String.eq(a5, "("))))))),
                        prefix_tail_b(prefix_skip(r5, Prefix.SGo{0n}), a2))

# True when a token of kind k0 and text tt, then these, make either shape
def prefix_at(+k0: Lex.TokKind, +tt: String, +toks: List<&2, Lex.Tok>) -> Bool:
  Bool.or(prefix_a(k0, tt, toks), prefix_b(k0, tt, toks))

# how many tokens start a run of either shape
def prefix_count(toks: List<&2, Lex.Tok>) -> Nat:
  match toks:
    case Nil{}:
      0n
    case Con{Lex.Tok{+k, +t, l, c}, +rest}:
      +m = prefix_count(rest)
      Bool.pick(Nat, prefix_at(k, t, rest), 1n+m, m)

# LAW: prefix reports, outside a LAWS.bend or a PROOF.bend, one finding for
# each run of significant tokens of either shape whose take is the
# literal's length, its argument any expression, and none for any other token
law prefix_counts:
  for +path: String
  for text: String
  for +toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Prefix.check(Src.Src{path, text, toks, tree, bound, items}))
    == Bool.pick(Nat, Paths.is_law_file(path), 0n, prefix_count(T.sig(toks))) : Nat}
