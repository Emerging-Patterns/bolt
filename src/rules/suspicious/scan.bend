# rule scan: a def that calls itself and, on the same step, hands a
# parameter it carries unchanged to a walk. Every step walks that list again:
# O(|A| * |B|), A what the def walks and B what it carries. Index it once
# outside the loop, or merge two sorted walks. A parameter is carried when
# every self-call passes it back as that same lone name in its own position
# (hoist's notion). A call is a name token (plain or dotted), then a `(`
# group, and what it walks is some of its arguments, counted from 0. A Base
# list search walks its list: argument 2 of `List.contains`, `List.find`,
# `List.filter` and `List.length`, 3 of `List.any` and `List.all`, 4 of
# `List.foldl` and `List.foldr`; a Base walk that rebuilds the list
# (`List.map`, `List.append`, ...) makes output, not a search, and is left
# alone. A def of this file walks, when it calls itself, its first live
# parameter that some self-call does not pass back unchanged (the one it
# shrinks), unless that parameter is a `Nat` or a `String` (a count, such as
# fuel, or a text); and each parameter its body, anywhere, passes as the lone
# name of an argument a call walks, of a Base search or of a def listed
# before it. A def of another module is not seen. A call reports when it is
# not a self-call and an argument it walks is exactly the lone name of a
# carried parameter: anything else there (a literal table, an expression, a
# name the step binds) is left alone. The step is what hoist reads as hot:
# the def's body, a case arm's body only when it calls the def, never a case
# pattern, and never the rest of a chain after `=>` (a lambda's body, a
# `Lazy` thunk, runs when it is called). Laws and proofs do not run (a def
# with no type at all fills a law: it is a proof), and a law file is skipped
# whole. One finding per call, on its callee.
import Base
import ../../src.bend as Src
import ../../paths.bend as Paths
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree
import ../calls.bend as Calls
import ../../lazy/lazy.bend as Lazy
import ./hoist.bend as Hoist

# a def of this file, and one argument it walks
type Walk is Data:
  Walk{name: String, at: Nat}

# the answer as a list: none or one
def opt(mm: Maybe<&2, Nat>) -> List<&2, Nat>:
  match mm:
    case None{}:
      Nil{}
    case Some{at}:
      [at]

# the list argument of a Base list search
def base_at(+tt: String) -> List<&2, Nat>:
  +two = List.contains(~String, ~String.eq, ["List.contains", "List.find", "List.filter", "List.length"], tt)
  +three = List.contains(~String, ~String.eq, ["List.any", "List.all"], tt)
  +four = List.contains(~String, ~String.eq, ["List.foldl", "List.foldr"], tt)
  Bool.pick(List<&2, Nat>, two, [2n], Bool.pick(List<&2, Nat>, three, [3n], Bool.pick(List<&2, Nat>, four, [4n], [])))

# the arguments the defs of this file named tt walk
def file_at(ws: List<&2, Walk>, +tt: String) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{Walk{+nm, +at}, rest}:
      +more = file_at(rest, tt)
      Bool.pick(List<&2, Nat>, String.eq(nm, tt), at <> more, more)

# the arguments a callee walks: a Base walk's list, and those the defs of this file record
def slots(+tt: String, +ws: List<&2, Walk>) -> List<&2, Nat>:
  List.append(&2, Nat, base_at(tt), file_at(ws, tt))

# a leaf that is a plain name: its text
def name_tok(tok: Lex.Tok) -> Maybe<&2, String>:
  match tok:
    case Lex.Tok{Lex.TName{}, t, l, c}:
      Some{t}
    case other:
      None{}

# the argument, when it is exactly one plain name
def name_of(nn: Tree.Node) -> Maybe<&2, String>:
  match nn:
    case Tree.NCons{Tree.Leaf{tok}, Tree.NNil{}}:
      name_tok(tok)
    case other:
      None{}

# the name, when the list holds it
def keep_in(mm: Maybe<&2, String>, +names: List<&2, String>) -> Maybe<&2, String>:
  match mm:
    case None{}:
      None{}
    case Some{+nm}:
      Bool.pick(Maybe<&2, String>, List.contains(~String, ~String.eq, names, nm), Some{nm}, None{})

# the first of two answers that has one
def first(aa: Maybe<&2, String>, bb: Maybe<&2, String>) -> Maybe<&2, String>:
  match aa:
    case None{}:
      bb
    case Some{nm}:
      Some{nm}

# the first walked argument that is the lone name of one of the names
def found(ss: List<&2, Nat>, +as: List<&2, Tree.Node>, +names: List<&2, String>) -> Maybe<&2, String>:
  match ss:
    case Nil{}:
      None{}
    case Con{at, rest}:
      +more = found(rest, as, names)
      first(keep_in(name_of(Calls.arg(as, at)), names), more)

# where a name sits among the parameter names
def index_of(ps: List<&2, String>, +nm: String, +ii: Nat) -> Maybe<&2, Nat>:
  match ps:
    case Nil{}:
      None{}
    case Con{+p, rest}:
      Lazy.stop(Maybe<&2, Nat>, String.eq(p, nm), Some{ii}, _u => index_of(rest, nm, 1n+ii))

# where the name sits among the parameter names, when there is a name
def index_in(mm: Maybe<&2, String>, +ps: List<&2, String>) -> Maybe<&2, Nat>:
  match mm:
    case None{}:
      None{}
    case Some{+nm}:
      index_of(ps, nm, 0n)

# the parameters that sit, as lone names, at walked arguments
def params_at(ss: List<&2, Nat>, +as: List<&2, Tree.Node>, +ps: List<&2, String>) -> List<&2, Nat>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{at, rest}:
      +more = params_at(rest, as, ps)
      List.append(&2, Nat, opt(index_in(name_of(Calls.arg(as, at)), ps)), more)

# a call's walked parameters, when its callee is a name and it is a call
def pass_hit(
  kk: Lex.TokKind,
  +open: Bool,
  +tt: String,
  kids: Tree.Node,
  +ps: List<&2, String>,
  +ws: List<&2, Walk>
) -> List<&2, Nat>:
  match kk:
    case Lex.TName{}:
      Lazy.stop(List<&2, Nat>, Bool.not(open), [], _u => params_at(slots(tt, ws), Calls.args(kids), ps))
    case Lex.TDotted{}:
      Lazy.stop(List<&2, Nat>, Bool.not(open), [], _u => params_at(slots(tt, ws), Calls.args(kids), ps))
    case other:
      Nil{}

# the parameters a body passes, anywhere, as an argument some call walks
def passes(nn: Tree.Node, +ps: List<&2, String>, +ws: List<&2, Walk>) -> List<&2, Nat>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +own = pass_hit(k, String.eq(o, "("), t, kids, ps, ws)
      List.concat(&2, Nat, [own, passes(kids, ps, ws), passes(rest, ps, ws)])
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      List.concat(&2, Nat, [passes(kids, ps, ws), passes(rest, ps, ws)])
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      List.concat(&2, Nat, [passes(kids, ps, ws), passes(body, ps, ws), passes(rest, ps, ws)])
    case Tree.NCons{h, rest}:
      passes(rest, ps, ws)
    case other:
      Nil{}

# a live parameter that some self-call does not pass back unchanged
def moves(+pp: Tree.Node, +carried: List<&2, String>) -> Bool:
  Bool.and(Calls.is_live(pp), Bool.not(List.contains(~String, ~String.eq, carried, Calls.param_name(pp))))

# a count or a text: a loop down one scans no list
def scalar(+pp: Tree.Node) -> Bool:
  +hh = Calls.type_head(pp, False{})
  Bool.or(String.eq(hh, "Nat"), String.eq(hh, "String"))

# where the parameter a def shrinks sits, unless it is a count or a text
def place(+pp: Tree.Node, +ii: Nat) -> Maybe<&2, Nat>:
  Bool.pick(Maybe<&2, Nat>, scalar(pp), None{}, Some{ii})

def own.go(ps: List<&2, Tree.Node>, +carried: List<&2, String>, +ii: Nat) -> Maybe<&2, Nat>:
  match ps:
    case Nil{}:
      None{}
    case Con{+p, rest}:
      +here = moves(p, carried)
      Lazy.stop(Maybe<&2, Nat>, here, place(p, ii), _u => own.go(rest, carried, 1n+ii))

# where the parameter a def shrinks sits, when it calls itself and it is no count or text
def own(+sig: Tree.Node, +body: Tree.Node, +name: String) -> Maybe<&2, Nat>:
  Lazy.stop(Maybe<&2, Nat>, Bool.not(Calls.calls(body, name)), None{},
    _u => own.go(Calls.params(sig), Hoist.carried(sig, body, name), 0n))

# one walk of the def for each argument
def tag(ns: List<&2, Nat>, +name: String, +ws: List<&2, Walk>) -> List<&2, Walk>:
  match ns:
    case Nil{}:
      ws
    case Con{at, rest}:
      Walk{name, at} <> tag(rest, name, ws)

def walks.go(ds: List<&2, Calls.Def>, +ws: List<&2, Walk>) -> List<&2, Walk>:
  match ds:
    case Nil{}:
      ws
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      +mine = List.append(&2, Nat, opt(own(sig, body, name)), passes(body, Calls.names(sig), ws))
      walks.go(rest, tag(mine, name, ws))

# the defs of this file that walk, each with an argument it walks, in order
def walks(ds: List<&2, Calls.Def>) -> List<&2, Walk>:
  walks.go(ds, [])

# the name of the parameter a def shrinks, "" for none
def lead.go(ps: List<&2, Tree.Node>, +carried: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{+p, rest}:
      +here = moves(p, carried)
      Lazy.stop(String, here, Calls.param_name(p), _u => lead.go(rest, carried))

# a finding on the callee, naming the carried list
def cite(
  mm: Maybe<&2, String>,
  +tt: String,
  +line: U32,
  +col: U32,
  +self: String,
  +lead: String,
  +path: String
) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      Nil{}
    case Some{+pp}:
      [F.Finding{path, line, col, U32.from_nat(String.length(tt)), "scan",
        tt ++ " walks " ++ pp ++ " on every step of " ++ self ++ ", which carries it unchanged: that is O(|" ++ lead
          ++ "| * |" ++ pp ++ "|). Index it once outside the loop, or merge two sorted walks."}]

# a hot call of a walk other than the def, a walked argument carried
def on_name(
  +hot: Bool,
  +open: Bool,
  +tt: String,
  +line: U32,
  +col: U32,
  kids: Tree.Node,
  +self: String,
  +ws: List<&2, Walk>,
  +carried: List<&2, String>,
  +lead: String,
  +path: String
) -> List<&2, F.Finding>:
  Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(hot, Bool.and(open, Bool.not(String.eq(tt, self))))), [],
    _u => cite(found(slots(tt, ws), Calls.args(kids), carried), tt, line, col, self, lead, path))

# a call's finding, when its callee is a name
def call_hit(
  kk: Lex.TokKind,
  +hot: Bool,
  +open: Bool,
  +tt: String,
  +line: U32,
  +col: U32,
  kids: Tree.Node,
  +self: String,
  +ws: List<&2, Walk>,
  +carried: List<&2, String>,
  +lead: String,
  +path: String
) -> List<&2, F.Finding>:
  match kk:
    case Lex.TName{}:
      on_name(hot, open, tt, line, col, kids, self, ws, carried, lead, path)
    case Lex.TDotted{}:
      on_name(hot, open, tt, line, col, kids, self, ws, carried, lead, path)
    case other:
      Nil{}

# the walks of carried lists on a hot path
def walk(
  nn: Tree.Node,
  +self: String,
  +ws: List<&2, Walk>,
  +carried: List<&2, String>,
  +lead: String,
  +path: String,
  +hot: Bool
) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, +t, +l, +c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +heat = Hoist.warm(hot, k)
      +own = call_hit(k, heat, String.eq(o, "("), t, l, c, kids, self, ws, carried, lead, path)
      +inn = walk(kids, self, ws, carried, lead, path, heat)
      +aft = walk(rest, self, ws, carried, lead, path, heat)
      List.concat(&2, F.Finding, [own, inn, aft])
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, rest}:
      walk(rest, self, ws, carried, lead, path, Hoist.warm(hot, k))
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      List.concat(&2, F.Finding,
        [walk(kids, self, ws, carried, lead, path, hot), walk(rest, self, ws, carried, lead, path, hot)])
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, +body}, rest}:
      +arm = Bool.and(hot, Calls.calls(body, self))
      List.concat(&2, F.Finding, [walk(kids, self, ws, carried, lead, path, False{}),
        walk(body, self, ws, carried, lead, path, arm), walk(rest, self, ws, carried, lead, path, hot)])
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      List.concat(&2, F.Finding, [walk(kids, self, ws, carried, lead, path, hot),
        walk(body, self, ws, carried, lead, path, hot), walk(rest, self, ws, carried, lead, path, hot)])
    case Tree.NCons{h, rest}:
      walk(rest, self, ws, carried, lead, path, hot)
    case other:
      Nil{}

# one def's walk, its carried parameters and the one it shrinks read once
def run(+sig: Tree.Node, +body: Tree.Node, +name: String, +ws: List<&2, Walk>, +path: String) -> List<&2, F.Finding>:
  +carried = Hoist.carried(sig, body, name)
  walk(body, name, ws, carried, lead.go(Calls.params(sig), carried), path, True{})

def check.go(
  ds: List<&2, Calls.Def>,
  +ws: List<&2, Walk>,
  +path: String,
  acc: List<&2, List<&2, F.Finding>>
) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      check.go(rest, ws, path,
        Lazy.stop(List<&2, F.Finding>,
          Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))), [],
          _u => run(sig, body, name, ws, path)) <> acc)

# the findings over a file's defs, their walks read once
def check.on(+ds: List<&2, Calls.Def>, +path: String) -> List<&2, F.Finding>:
  check.go(ds, walks(ds), path, [])

# the rule; a law file is skipped whole, before its walks are read
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = ss
  Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path), [], _u => check.on(Calls.defs(tree), path))
