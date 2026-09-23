# rule foreign: a foreign def (its body only `import "./x.c"` / `import
# "./x.js"` lines) with a body for one lane and not the other. Each lane
# finds out only when it first runs: a native build (`bend -o bin`) fails
# with "no .c import", an interpreted or JS run with "a foreign def without a
# .js import". Give every foreign def both bodies, `x.c` and `x.js`. A file
# headed `# lanes: native` never runs on the JS lane, so it needs no `.js`.
# Headed means the exact line `# lanes: native` is one of the file's leading
# comment lines, those before its first line that does not start with `#`;
# the line anywhere later does not count.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../../../syntax/bind.bend as Bind
import ../../../lazy/lazy.bend as Lazy

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
def lanes.go(body: Tree.Node, cc: Bool, js: Bool) -> Maybe<&2, Lanes>:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SImport{}, kids, ib}, rest}:
      +t = target(kids)
      lanes.go(rest, Bool.or(cc, String.ends_with(t, ".c\"")), Bool.or(js, String.ends_with(t, ".js\"")))
    case Tree.NCons{h, rest}:
      None{}
    case other:
      Some{Lanes{cc, js}}

# the lanes of a def's body: None unless it is a foreign def
def lanes(body: Tree.Node) -> Maybe<&2, Lanes>:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SImport{}, kids, ib}, rest}:
      +t = target(kids)
      lanes.go(rest, String.ends_with(t, ".c\""), String.ends_with(t, ".js\""))
    case other:
      None{}

# what the lanes lack, as a message ("" for nothing)
def lack(mm: Maybe<&2, Lanes>, +native: Bool, +name: String) -> String:
  match mm:
    case None{}:
      ""
    case Some{Lanes{+c, +js}}:
      Bool.pick(String, Bool.and(c, Bool.and(Bool.not(js), Bool.not(native))),
        "Foreign def " ++ name ++ " has a .c body but no .js body, so it cannot run on the JS lane.",
        Bool.pick(String, Bool.and(js, Bool.not(c)),
          "Foreign def " ++ name ++ " has a .js body but no .c body, so it cannot run in a native build.", ""))

# a message as a finding, when there is one
def at(+msg: String, +line: U32, +col: U32, +path: String, +more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  Bool.pick(List<&2, F.Finding>, String.is_empty(msg), more, F.Finding{path, line, col, 0, "foreign", msg} <> more)

# a def's name, `?` when it has none
def name.of(mm: Maybe<&2, String>) -> String:
  match mm:
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

def native_only.go(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{+l, rest}:
      Lazy.stop(Bool, Bool.not(String.starts_with(l, "#")), False{},
        _u => Lazy.or_else(String.eq(l, "# lanes: native"), _v => native_only.go(rest)))

# is the file headed `# lanes: native`: that exact line among the comment
# lines before its first line that is not a comment?
def native_only(text: String) -> Bool:
  native_only.go(String.lines(text))

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.go(tree, native_only(text), path)
