# `scan` reports exactly, outside a LAWS.bend or a PROOF.bend, in a def that
# calls itself and is not a proof, outside a lambda's body (the rest of a
# chain after `=>`), a case pattern, and a case arm that does not call the
# def: each call, a plain or dotted name token then a `(` group, of a callee
# other than the def, one of whose walked arguments is exactly the lone name
# of a parameter that every self-call passes back as that same lone name in
# its own position (carried). A callee walks argument 2 of `List.contains`,
# `List.find`, `List.filter` and `List.length`, 3 of `List.any` and
# `List.all`, and 4 of `List.foldl` and `List.foldr` (the Base list searches);
# a def of the file walks, when it calls itself, its first live parameter that
# some self-call does not pass back unchanged, unless that parameter's type is
# `Nat` or `String`, and each parameter its body passes, anywhere, as the lone
# name of an argument a call of a Base search or of a def listed before it
# walks. One finding per call.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/hoist.bend as Hoist
import ../src/rules/suspicious/scan.bend as Scan
import ../src/rules/calls.bend as Calls

# scan (laws/ScanReportsCarriedArgumentWalks.bend). Outside a law file the rule walks each def of the
# file that calls itself (Calls.calls) and is not a proof, its body hot, as
# hoist does: a `=>` token makes the rest of its chain cold, a case's pattern
# is cold, and a case arm's body stays hot only when it calls the def. In a
# hot region it reports each call, a plain or dotted name token then a `(`
# group, of a callee other than the def, when one of the arguments the
# callee walks (Scan.slots, over the file's walks, Scan.walks) is exactly the
# lone name of a carried parameter (Hoist.carried).

# a callee is a plain or a dotted name
def scan.callee(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TName{}:
      True{}
    case Lex.TDotted{}:
      True{}
    case other:
      False{}

# is the token a plain name the list holds?
def scan.named(tok: Lex.Tok, +carried: List<&2, String>) -> Bool:
  match tok:
    case Lex.Tok{Lex.TName{}, +t, l, c}:
      List.contains(~String, ~String.eq, carried, t)
    case other:
      False{}

# is the argument exactly the lone name of a carried parameter?
def scan.lone(nn: Tree.Node, +carried: List<&2, String>) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{tok}, Tree.NNil{}}:
      scan.named(tok, carried)
    case other:
      False{}

# does some walked argument hold a carried parameter's lone name?
def scan.held(ss: List<&2, Nat>, +as: List<&2, Tree.Node>, +carried: List<&2, String>) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case Con{at, rest}:
      Bool.or(scan.lone(Calls.arg(as, at), carried), scan.held(rest, as, carried))

# does a call site report: a named callee, hot, a `(` group, not the def,
# and a walked argument carried
def scan.call(
  kk: Lex.TokKind,
  +hot: Bool,
  +open: Bool,
  +tt: String,
  kids: Tree.Node,
  +self: String,
  +ws: List<&2, Scan.Walk>,
  +carried: List<&2, String>
) -> Bool:
  Bool.and(scan.callee(kk), Bool.and(hot, Bool.and(open, Bool.and(Bool.not(String.eq(tt, self)),
    scan.held(Scan.slots(tt, ws), Calls.args(kids), carried)))))

# how many calls scan reports under the node, entered hot or cold
def scan.count(
  nn: Tree.Node,
  +self: String,
  +ws: List<&2, Scan.Walk>,
  +carried: List<&2, String>,
  +hot: Bool
) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +heat = Hoist.warm(hot, k)
      Nat.add(Bool.pick(Nat, scan.call(k, heat, String.eq(o, "("), t, kids, self, ws, carried), 1n, 0n),
        Nat.add(scan.count(kids, self, ws, carried, heat), scan.count(rest, self, ws, carried, heat)))
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, rest}:
      scan.count(rest, self, ws, carried, Hoist.warm(hot, k))
    case Tree.NCons{Tree.Group{o, kids, cl}, rest}:
      Nat.add(scan.count(kids, self, ws, carried, hot), scan.count(rest, self, ws, carried, hot))
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, +body}, rest}:
      Nat.add(scan.count(kids, self, ws, carried, False{}),
        Nat.add(scan.count(body, self, ws, carried, Bool.and(hot, Calls.calls(body, self))),
          scan.count(rest, self, ws, carried, hot)))
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      Nat.add(scan.count(kids, self, ws, carried, hot),
        Nat.add(scan.count(body, self, ws, carried, hot), scan.count(rest, self, ws, carried, hot)))
    case Tree.NCons{h, rest}:
      scan.count(rest, self, ws, carried, hot)
    case other:
      0n

# how many scan reports over the defs: those in each def that calls itself
# and is not a proof, walked hot, with its carried parameters
def scan.total(ds: List<&2, Calls.Def>, +ws: List<&2, Scan.Walk>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig))),
        scan.count(body, name, ws, Hoist.carried(sig, body, name), True{}), 0n), scan.total(rest, ws, path))

# LAW: outside a law file, scan reports one finding for each call the walk
# above counts, in each def that calls itself and is not a proof, with the
# file's walks; none for anything else
law scan_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_law_file(path) == False{} : Bool}
  {List.length(&2, F.Finding, Scan.check(Src.Src{path, text, toks, tree, bound, items}))
    == scan.total(Calls.defs(tree), Scan.walks(Calls.defs(tree)), path) : Nat}

# LAW: a walk whose def carries no parameter reports nothing, whatever the
# tree, the file's walks and the heat
law scan_quiet:
  for nn: Tree.Node
  for +self: String
  for +ws: List<&2, Scan.Walk>
  for +lead: String
  for +path: String
  for +hot: Bool
  {Scan.walk(nn, self, ws, [], lead, path, hot) == Nil{} : List<&2, F.Finding>}

# the list arguments of the Base list searches: 2, 3 or 4, counted from 0
def scan.base(+tt: String) -> List<&2, Nat>:
  Bool.pick(List<&2, Nat>, List.contains(~String, ~String.eq, ["List.contains", "List.find", "List.filter",
    "List.length"], tt), [2n],
    Bool.pick(List<&2, Nat>, List.contains(~String, ~String.eq, ["List.any", "List.all"], tt), [3n],
      Bool.pick(List<&2, Nat>, List.contains(~String, ~String.eq, ["List.foldl", "List.foldr"], tt), [4n], [])))

# the arguments the file's walks record for a name, in order
def scan.file(ws: List<&2, Scan.Walk>, +tt: String) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{Scan.Walk{+nm, at}, rest}:
      +more = scan.file(rest, tt)
      Bool.pick(List<&2, Nat>, String.eq(nm, tt), at <> more, more)

# LAW: a callee walks the Base search's list argument, then each argument a
# walk of the file of that name records
law scan_slots:
  for +tt: String
  for ws: List<&2, Scan.Walk>
  {Scan.slots(tt, ws) == List.append(&2, Nat, scan.base(tt), scan.file(ws, tt)) : List<&2, Nat>}
