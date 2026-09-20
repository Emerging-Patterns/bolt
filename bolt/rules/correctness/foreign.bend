# rule foreign: a foreign def (its body only `import "./x.c"` / `import
# "./x.js"` lines) with a body for one lane and not the other. Each lane
# finds out only when it first runs: a native build (`bend -o bin`) fails
# with "no .c import", an interpreted or JS run with "a foreign def without a
# .js import". Give every foreign def both bodies, `x.c` and `x.js`. A file
# headed `# lanes: native` never runs on the JS lane, so it needs no `.js`.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../../../syntax/bind.bend as Bind

# which lanes a foreign def's bodies cover
type Lanes is Data:
  Lanes{c: Bool, js: Bool}

# the imported path of an import statement's tokens (`"./x.c"`, quoted)
def target(kids: Tree.Node) -> String:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TStr{}, t, l, c}}, rest}:
      t
    case Tree.NCons{h, rest}:
      target(rest)
    case other:
      ""

# the lanes of a body that is only imports; None when it is anything else
def lanes.go(body: Tree.Node, c: Bool, js: Bool) -> Maybe<&2, Lanes>:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SImport{}, kids, ib}, rest}:
      +t = target(kids)
      lanes.go(rest, Bool.or(c, String.ends_with(t, ".c\"")), Bool.or(js, String.ends_with(t, ".js\"")))
    case Tree.NCons{h, rest}:
      None{}
    case other:
      Some{Lanes{c, js}}

# the lanes of a def's body: None unless it is a foreign def
def lanes(body: Tree.Node) -> Maybe<&2, Lanes>:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SImport{}, kids, ib}, rest}:
      +t = target(kids)
      lanes.go(rest, String.ends_with(t, ".c\""), String.ends_with(t, ".js\""))
    case other:
      None{}

# what the lanes lack, as a message ("" for nothing)
def lack(m: Maybe<&2, Lanes>, +native: Bool, +name: String) -> String:
  match m:
    case None{}:
      ""
    case Some{Lanes{+c, +js}}:
      Bool.pick(String, Bool.and(c, Bool.and(Bool.not(js), Bool.not(native))),
        "foreign def " ++ name ++ " has a .c body but no .js body: the JS lane cannot run it",
        Bool.pick(String, Bool.and(js, Bool.not(c)),
          "foreign def " ++ name ++ " has a .js body but no .c body: a native build cannot run it", ""))

# a message as a finding, when there is one
def at(+msg: String, +line: U32, +col: U32, +path: String, +more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  Bool.pick(List<&2, F.Finding>, String.is_empty(msg), more, F.Finding{path, line, col, 0, "foreign", msg} <> more)

# a def's name, `?` when it has none
def name.of(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      "?"
    case Some{n}:
      n

def check.go(root: Tree.Node, +native: Bool, +path: String) -> List<&2, F.Finding>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, +kids, body}, rest}:
      at(lack(lanes(body), native, name.of(Bind.declared(kids))), Tree.line(kids), Tree.col(kids), path,
        check.go(rest, native, path))
    case Tree.NCons{h, rest}:
      check.go(rest, native, path)
    case other:
      Nil{}

# is the file headed `# lanes: native`?
def native_only(+text: String) -> Bool:
  Bool.or(String.starts_with(text, "# lanes: native"), String.contains(text, "\n# lanes: native"))

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = s
  check.go(tree, native_only(text), path)
