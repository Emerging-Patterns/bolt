# `concat` also reports an append passed on through a continuation: an
# argument of a call of a function-typed parameter (`rest: File -> .. -> T`,
# called `rest(file, List.append(&2, U32, acc, xs))`) that appends onto a
# parameter of the def, read the way a self-call's is (in place, inside any
# number of parentheses, or a lone name through its nearest let). A `+`
# parameter the body reads more than once is not reported: it builds a value
# it also uses elsewhere (`path ++ "/" ++ name`), not an accumulator. Law
# files, proof files and defs that are proofs are exempt, as for the
# self-call half.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/role.bend as Role
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/concat.bend as Concat
import ../src/rules/calls.bend as Calls

# concat's continuation half (laws/ConcatReportsContinuationAppend.bend).
# A continuation call is a leaf whose text is one of the def's
# function-typed parameters (Concat.conts) followed by a `(` group; its
# arguments are the group's kids split at top-level commas (Calls.args). An
# argument counts when the name it appends onto (Concat.seen) is one the
# def may report (Concat.accs, filtered by Concat.keep).

# True when the argument appends onto a reportable name
def cont.is(mm: Maybe<&2, Lex.Tok>, +accs: List<&2, String>) -> Bool:
  match mm:
    case None{}:
      False{}
    case Some{Lex.Tok{k, +t, l, c}}:
      List.contains(~String, ~String.eq, accs, t)

# how many arguments append onto a reportable name
def cont.args(as: List<&2, Tree.Node>, +accs: List<&2, String>, +lets: List<&2, Concat.Let>) -> Nat:
  match as:
    case Nil{}:
      0n
    case Con{+a, rest}:
      +m = cont.args(rest, accs, lets)
      Bool.pick(Nat, cont.is(Concat.seen(a, lets), accs), 1n+m, m)

# how many arguments of continuation calls under the node append onto a
# reportable name: a call's own arguments, then what its group and what
# follows it hold; a statement's let is in scope for what follows it
def cont.count(
  nn: Tree.Node,
  +conts: List<&2, String>,
  +accs: List<&2, String>,
  +lets: List<&2, Concat.Let>
) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +here = Bool.pick(Nat, Bool.and(String.eq(o, "("), List.contains(~String, ~String.eq, conts, t)),
        cont.args(Calls.args(kids), accs, lets), 0n)
      Nat.add(here, Nat.add(cont.count(kids, conts, accs, lets), cont.count(rest, conts, accs, lets)))
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      Nat.add(cont.count(kids, conts, accs, lets), cont.count(rest, conts, accs, lets))
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      Nat.add(cont.count(kids, conts, accs, lets),
        Nat.add(cont.count(body, conts, accs, lets),
          cont.count(rest, conts, accs, Concat.after(kind, kids, lets))))
    case Tree.NCons{h, rest}:
      cont.count(rest, conts, accs, lets)
    case other:
      0n

# the count over a file's defs, none in a def that is exempt, each def
# starting with no lets
def cont.file(ds: List<&2, Calls.Def>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{name, +sig, +body}, rest}:
      Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n,
        cont.count(body, Concat.conts(sig), Concat.accs(sig, body), [])), cont.file(rest, path))

# LAW: concat reports one finding for each argument of a continuation call
# that appends onto a reportable parameter, in every def its header does not
# exempt, and none for anything else
law concat_cont_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Concat.cont(Src.Src{path, text, toks, tree, bound, items}))
    == cont.file(Calls.defs(tree), path) : Nat}

# LAW: a parameter that is not `+` may always be reported, however often the
# body reads it (each match arm may read it once)
law concat_keep_plain:
  for n: Nat
  {Concat.keep(False{}, n) == True{} : Bool}

# LAW: a parameter read once may be reported, `+` or not
law concat_keep_once:
  for b: Bool
  {Concat.keep(b, 1n) == True{} : Bool}

# LAW: a `+` parameter read twice or more is never reported
law concat_keep_reused:
  for n: Nat
  {Concat.keep(True{}, 1n+1n+n) == False{} : Bool}

# LAW: a parameter written `+name: ..` is a `+` one
law concat_plus:
  for l: U32
  for c: U32
  for rest: Tree.Node
  {Concat.plus(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, "+", l, c}}, rest}) == True{} : Bool}

# LAW: a parameter whose chain holds a `->` is a continuation
law concat_conts:
  for +p: Tree.Node
  for ps: List<&2, Tree.Node>
  for +acc: List<&2, String>
  for e: {Calls.has_arrow(p) == True{} : Bool}
  {Concat.conts.go(p <> ps, acc) == Concat.conts.go(ps, Calls.param_name(p) <> acc) : List<&2, String>}

# LAW: a parameter whose chain holds no `->` is not
law concat_not_cont:
  for +p: Tree.Node
  for ps: List<&2, Tree.Node>
  for +acc: List<&2, String>
  for e: {Calls.has_arrow(p) == False{} : Bool}
  {Concat.conts.go(p <> ps, acc) == Concat.conts.go(ps, acc) : List<&2, String>}

# LAW: the continuation half reports nothing in a LAWS.bend or a PROOF.bend
law concat_cont_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_law_file(path) == True{} : Bool}
  {Concat.cont(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}

# LAW: the continuation half, told a file's role by its name, finds what it
# finds
law role_concat_cont:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {Role.skip(Role.of_path(path), _u => Concat.cont(Src.Src{path, text, toks, tree, bound, items}))
    == Concat.cont(Src.Src{path, text, toks, tree, bound, items}) : List<&2, F.Finding>}
