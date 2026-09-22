# bolt/spec/cases: fixtures the laws name. Dotted helpers ride on the file header.
import Base
import ../src.bend as Src
import ../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree
import ../../syntax/bind.bend as Bind
import ../lsp/frame.bend as Frame
import ../lsp/docs.bend as Docs
import ../lsp/report.bend as Rep
import ../lsp/files/service.bend as Files
import ../args.bend as Args

def src.sample() -> String:
  String.join([
    "import Base",
    "",
    "# adds one",
    "def inc(n: U32) -> U32:",
    "  a = 1",
    "  (n + a : U32)",
    "",
    "def go(xs: List<&2, U32>) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      Bool.pick(U32, U32.is_eq(h, 0), go(t), (h + go(t) : U32))"], "\n")

def src.leaves(nn: Tree.Node) -> Nat:
  List.length(&2, Lex.Tok, Tree.leaves(nn))

def src.bound_counts(bb: Bind.Bound) -> String:
  Bind.Bound{binds, uses, scopes} = bb
  Nat.show(List.length(&2, Bind.Bind, binds)) ++ "/" ++ Nat.show(List.length(&2, Bind.Use, uses))
    ++ "/" ++ Nat.show(List.length(&2, Bind.Scope, scopes))

def src.fields(ss: Src.Src) -> String:
  Src.Src{path, text, toks, tree, bound, items} = ss
  path ++ " " ++ Nat.show(List.length(&2, Lex.Tok, toks)) ++ " " ++ Nat.show(src.leaves(tree))
    ++ " " ++ src.bound_counts(bound)

def src.direct(+path: String, +text: String) -> String:
  path ++ " " ++ Nat.show(List.length(&2, Lex.Tok, Lex.tokens(text))) ++ " "
    ++ Nat.show(src.leaves(Tree.parse(text))) ++ " " ++ src.bound_counts(Bind.bound(text))

def show.lines(fs: List<&2, F.Finding>) -> String:
  String.join(F.show_all(fs), "; ")

def args.split(+av: List<&2, String>) -> String:
  "[" ++ Args.command(av) ++ "] " ++ String.join(Args.files(av), " ")

def args.help_root() -> String:
  "bolt 0.9.0\n" ++ # x-release-please-version
  "A linter, checker and language server for Bend 2.\n\n" ++
  "Usage: bolt [OPTIONS] [FILES]... [COMMAND]\n\n" ++
  "Commands:\n" ++
  "  lint   Lint files\n" ++
  "  check  Check files\n" ++
  "  lsp    Serve an editor over stdio\n" ++
  "  help   Print this message or the help of the given subcommand(s)\n\n" ++
  "Options:\n" ++
  "    --version  Print the version\n\n"

def rules.undocumented() -> String:
  String.join([
    "import Base",
    "",
    "# adds one",
    "def inc(n: U32) -> U32:",
    "  (n + 1 : U32)",
    "",
    "def dec(n: U32) -> U32:",
    "  (n - 1 : U32)",
    "",
    "def dec.go(n: U32) -> U32:",
    "  n",
    "",
    "type T is Data:",
    "  K{}",
    "",
    "law l:",
    "  {1 == 1 : U32}",
    "",
    "def main() -> U32:",
    "  0"], "\n")

def rules.unused() -> String:
  String.join([
    "def f(x: U32, -A: Type, _y: U32, z: U32) -> U32:",
    "  a = 1",
    "  b = 2",
    "  g = q => q",
    "  h = w => 3",
    "  (a + z : U32)",
    "",
    "def g(t: T) -> U32:",
    "  match t:",
    "    case K{p, r}:",
    "      p",
    "",
    "def ext(path: String) -> IO(String):",
    "  import \"./x.c\"",
    "",
    "law l:",
    "  for ih : U32",
    "  {1 == 1 : U32}"], "\n")

def rules.shadowed() -> String:
  String.join([
    "def a(k: U32) -> U32:",
    "  k = 1",
    "  k",
    "",
    "def k(n: U32) -> U32:",
    "  n",
    "",
    "def b(k: U32) -> U32:",
    "  k = 2",
    "  k",
    "",
    "def c(t: T) -> U32:",
    "  match t:",
    "    case K{k}:",
    "      k"], "\n")

def rules.holes() -> String:
  "def f() -> U32:\n  ?TODO\n"

def rules.spaced() -> String:
  "def f() -> U32:  \n\t1\n# " ++ String.repeat("x", 120n) ++ "\ns = \"" ++ String.repeat("y", 200n) ++ "\"\n#|" ++ String.repeat("z", 200n) ++ "\n"

# a fitting one-liner, one over 120, one already wrapped, one whose string counts as two
def rules.headers() -> String:
  String.join([
    "def fits(ab: U32, cd: U32, ef: U32, gh: U32) -> U32:",
    "  ab",
    "def " ++ String.repeat("n", 2n) ++ "(" ++ String.repeat("p", 110n) ++ ": U32) -> U32:",
    "  1",
    "def wide(",
    "  ab: U32,",
    "  cd: List<&2, U32>",
    ") -> List<&2, U32>:",
    "  ab",
    "def lit(s: \"" ++ String.repeat("y", 200n) ++ "\") -> U32:",
    "  1"], "\n")

# jammed multi-line headers, and breaks that already put one parameter on a line
def rules.jammed() -> String:
  String.join([
    "def slurp.next(got: File & Result<&1, &1, U32 & String, String>, acc: String,",
    "  rest: File -> String -> IO(String)) -> IO(String):",
    "  acc",
    "def slurp.more(rr: Result<&1, &1, U32 & String, String>, file: File, acc: String,",
    "  rest: File -> String -> IO(String)) -> IO(String):",
    "  acc",
    "def slurp.cut(bytes: List<&2, U32>, file: File, acc: String,",
    "  rest: File -> String -> IO(String)) -> IO(String):",
    "  acc",
    "def black(",
    "  ab: Result<&1, &1, U32 & String, String>,",
    "  cd: List<&2, U32>",
    ") -> U32:",
    "  ab",
    "def shut(",
    "  ab: U32,",
    "  cd: U32) -> U32:",
    "  ab",
    "def trail(",
    "  ab: U32,",
    "  cd: U32,",
    ") -> U32:",
    "  ab",
    "def fits(ab: U32, cd: U32) -> U32:",
    "  ab",
    "def hung(ab: U32,",
    "  cd: U32) -> U32:",
    "  ab",
    "def crowd(",
    "  ab: U32, cd: U32) -> U32:",
    "  ab",
    "def longret(ab: U32) ->",
    "  U32:",
    "  ab",
    "def split(",
    "  ab: U32 &",
    "    U32) -> U32:",
    "  ab"], "\n")

# one short value parameter; type parameters, a quantity and a local are not
def rules.params() -> String:
  String.join([
    "def bad(n: U32, ok: U32) -> U32:",
    "  (n + ok : U32)",
    "",
    "def gen(~A: Type, ~T: Type, xs: List<&2, A>) -> A:",
    "  xs",
    "",
    "def qty(a, -A: Type, xs: List<&2, A>) -> A:",
    "  xs",
    "",
    "def local(ok: U32) -> U32:",
    "  x = ok",
    "  q => x"], "\n")

def rules.picked() -> String:
  String.join([
    "def go(xs: List<&2, U32>) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      Bool.pick(U32, U32.is_eq(h, 0), go(t), (h + go(t) : U32))",
    "",
    "def ok(xs: List<&2, U32>) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      +more = ok(t)",
    "      Bool.pick(U32, U32.is_eq(h, 0), more, (h + more : U32))",
    "",
    "def nested(xs: List<&2, U32>) -> U32:",
    "  match xs:",
    "    case Con{h, t}:",
    "      Bool.pick(U32, True{}, nested(t), Bool.pick(U32, False{}, 1, nested(t)))",
    "    case Nil{}:",
    "      0"], "\n")

def rules.lawful() -> List<&2, Src.Src>:
  [Src.of("./p/LAWS.bend",
     "import ./m.bend as M\nimport ./io.bend as I\n\n# LAW: f is the identity\nlaw f_id:\n  for a: U32\n  {M.f(a) == a : U32}\n\n# LAW: say prints x\nlaw say_x:\n  {I.say() == IO.print(\"x\") : IO(Unit)}\n"),
   Src.of("./p/m.bend", "def f(a: U32) -> U32:\n  a\n\ndef g(a: U32) -> U32:\n  a\n\ndef g.go(a: U32) -> U32:\n  a\n\ntype T is Data:\n  K{}\n\ndef main() -> U32:\n  0\n"),
   Src.of("./p/o.bend", "type O is Data:\n  K{}\n\ndef h(a: U32) -> U32:\n  a\n"),
   Src.of("./p/io.bend",
     "def say() -> IO(Unit):\n  IO.print(\"x\")\n\ndef shout() -> IO(Unit):\n  IO.print(\"X\")\n\ndef k(a: U32) -> U32:\n  a\n"),
   Src.of("./p/note.bend", "# pure: IO is only in this comment\ndef j(a: U32) -> U32:\n  a\n\n# and a string\ndef s() -> String:\n  \"IO\"\n"),
   Src.of("./p/tests/t.bend", "def z(a: U32) -> U32:\n  a\n"),
   Src.of("./q/n.bend", "def y(a: U32) -> U32:\n  a\n")]

def rules.config() -> String:
  String.join([
    "import Base",
    "",
    "# comments and width are errors",
    "def style() -> String:",
    "  \"error\"",
    "",
    "# but width is advice",
    "def space() -> String:",
    "  \"warn\"",
    "",
    "# a slip is silent",
    "def unused() -> String:",
    "  \"off\"",
    "",
    "# a typo",
    "def laws() -> String:",
    "  \"wran\""], "\n")

def proj.reached() -> List<&2, Src.Src>:
  [Src.of("./p/PROOF.bend", "import ./LAWS.bend as Laws\n\n# the proof\ndef f_id(a):\n  {==}\n"),
   Src.of("./p/LAWS.bend", "import ./m.bend as M\nimport ./q.bend as Q\n\n# LAW: f\nlaw f_id:\n  for a: U32\n  {M.f(a) == a : U32}\n"),
   Src.of("./p/m.bend", "import ../lib/u.bend as U\nimport ./w.bend as W\n\n# f\ndef f(a: U32) -> U32:\n  U.spin(a)\n"),
   Src.of("./lib/u.bend", "# spins\n@unsafe def spin(a: U32) -> U32:\n  spin(a)\n"),
   Src.of("./p/w.bend", "# walks\n@unsafe\ndef walk(a: U32) -> U32:\n  walk(a)\n"),
   Src.of("./p/o.bend", "# loose\n@unsafe def loose(a: U32) -> U32:\n  loose(a)\n")]

def proj.unreached() -> List<&2, Src.Src>:
  [Src.of("./p/LAWS.bend", "import ./n.bend as N\n\n# LAW: g\nlaw g_id:\n  for a: U32\n  {N.g(a) == a : U32}\n"),
   Src.of("./p/n.bend", "# g\ndef g(a: U32) -> U32:\n  a\n"),
   Src.of("./p/o.bend", "# loose\n@unsafe def loose(a: U32) -> U32:\n  loose(a)\n")]

def proj.lawless() -> List<&2, Src.Src>:
  [Src.of("./r/main.bend", "import ./u.bend as U\n\n# main\ndef main() -> U32:\n  U.spin(1)\n"),
   Src.of("./r/u.bend", "# spins\n@unsafe def spin(a: U32) -> U32:\n  spin(a)\n")]

def proj.foreigns() -> String:
  String.join([
    "# only C",
    "def a.b(x: U32) -> IO(U32):",
    "  import \"./b.c\"",
    "",
    "# only JS",
    "def a.c(x: U32) -> IO(U32):",
    "  import \"./c.js\"",
    "",
    "# both",
    "def a.d(x: U32) -> IO(U32):",
    "  import \"./d.c\"",
    "  import \"./d.js\"",
    "",
    "# not foreign",
    "def e(x: U32) -> U32:",
    "  x"], "\n")

def proj.native() -> String:
  "# lanes: native\n# a native test\n\n# only C\ndef a.b(x: U32) -> IO(U32):\n  import \"./b.c\"\n\n# only JS\ndef a.c(x: U32) -> IO(U32):\n  import \"./c.js\"\n"

def proj.fuels() -> String:
  String.join([
    "# fuel first",
    "def walk(fuel: Nat, xs: List<&2, U32>) -> U32:",
    "  match fuel:",
    "    case 0n:",
    "      0",
    "    case 1n+f:",
    "      walk(f, xs)",
    "",
    "# budget after a template",
    "def spend(~A: Type, x: A, budget: Nat) -> A:",
    "  x",
    "",
    "# fuel_max, with a fixed fuel from its own step",
    "def go(fuel_max: Nat) -> U32:",
    "  go(3n)",
    "",
    "# callers",
    "def main() -> U32:",
    "  +a = walk(1000n, [])",
    "  +b = spend(~U32, 1, 10n)",
    "  +c = walk(Nat.mul(2n, 3n), [])",
    "  +d = spend(~U32, 1n, U32.to_nat(5))",
    "  +e = M.walk(4n, [])",
    "  +g = other(7n)",
    "  a"], "\n")

def proj.laws() -> String:
  String.join([
    "import ./m.bend as M",
    "",
    "# LAW: closed",
    "law sanity:",
    "  {U32.add(2, 3) == 5 : U32}",
    "",
    "# LAW: one line",
    "law short: {M.f(0) == 0 : U32}",
    "",
    "# LAW: for all",
    "law f_id:",
    "  for a: U32",
    "  {M.f(a) == a : U32}",
    "",
    "# LAW: a witness",
    "law has:",
    "  exs b: U32",
    "  {M.f(b) == 0 : U32}"], "\n")

def tok.put_src() -> String:
  String.join([
    "def f(m: Map<U32>, k: String) -> Map<U32>:",
    "  Map.put(U32, U32, m, k, 1)",
    "",
    "# Map.put( in a comment",
    "def g(m: Map<U32>, k: String) -> Map<U32>:",
    "  Map.set(U32, U32, Map.put.bit(m), \"Map.put(\", 1)"], "\n")

def tok.put_own() -> String:
  String.join([
    "def Map.put(a, V, m, key, x):",
    "  Map.put(a, V, m, key, x)"], "\n")

def tok.escape_src() -> String:
  String.join([
    "def main() -> IO(Unit):",
    "  IO.print(\"a\\033[1m\" ++ \"\\\\033\" ++ \"\\u{1B}\" ++ \"a\\0b\" ++ \"\\\"\\012\")",
    "",
    "# \"\\033\" in a comment",
    "def c() -> Char:",
    "  '\\07'",
    "",
    "def d() -> String:",
    "  \"\\09\""], "\n")

def tok.nat_src() -> String:
  String.join([
    "def f() -> Nat:",
    "  g(999n, 1000n, 100000, 4294967295n, 12n)",
    "",
    "# 2000n in a comment",
    "def h() -> String:",
    "  \"5000n\""], "\n")

def rec.stricted() -> String:
  String.join([
    "def digits(s: List<&2, U32>) -> Bool:",
    "  match s:",
    "    case Nil{}:",
    "      True{}",
    "    case Con{h, t}:",
    "      U32.is_lt(h, 10) && digits(t)",
    "",
    "def has0(xs: List<&2, U32>) -> Bool:",
    "  match xs:",
    "    case Nil{}:",
    "      False{}",
    "    case Con{h, t}:",
    "      Bool.or(U32.is_eq(h, 0), has0(t))",
    "",
    "def all0(xs: List<&2, U32>) -> Bool:",
    "  match xs:",
    "    case Nil{}:",
    "      True{}",
    "    case Con{h, t}:",
    "      all0(t) || U32.is_eq(h, 0)",
    "",
    "def ok(xs: List<&2, U32>) -> Bool:",
    "  match xs:",
    "    case Nil{}:",
    "      True{}",
    "    case Con{h, t}:",
    "      +rest = ok(t)",
    "      U32.is_lt(h, 10) && rest",
    "",
    "def cond(xs: List<&2, U32>, +a: Bool) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      Bool.pick(U32, a && U32.is_eq(h, 0), (h + cond(t, a) : U32), cond(t, a))"], "\n")

def rec.eagered() -> String:
  String.join([
    "def cost(xs: List<&2, U32>) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      (h + cost(t) : U32)",
    "",
    "def hit(xs: List<&2, U32>, +b: U32) -> U32:",
    "  Bool.pick(U32, U32.is_eq(b, 0), 0, cost(xs))",
    "",
    "def cheap(xs: List<&2, U32>, +b: U32) -> U32:",
    "  Bool.pick(U32, String.eq(U32.show(b), \"0\"), 0, 1)",
    "",
    "def bound(xs: List<&2, U32>, +b: U32) -> U32:",
    "  +c = cost(xs)",
    "  Bool.pick(U32, U32.is_eq(b, 0), 0, c)",
    "",
    "def selfish(xs: List<&2, U32>, +b: U32) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      Bool.pick(U32, U32.is_eq(h, b), h, selfish(t, b))",
    "",
    "def flat(+b: U32) -> U32:",
    "  (b + 1 : U32)",
    "",
    "def calm(xs: List<&2, U32>, +b: U32) -> U32:",
    "  Bool.pick(U32, U32.is_eq(b, 0), 0, flat(b))",
    "",
    "def ladder(xs: List<&2, U32>, +b: U32) -> U32:",
    "  Bool.pick(U32, U32.is_eq(b, 0), 0, Bool.pick(U32, U32.is_eq(cost(xs), 0), 1, 2))"], "\n")

def rec.tailed() -> String:
  String.join([
    "def len(xs: List<&2, U32>) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      (1 + len(t) : U32)",
    "",
    "def sum(xs: List<&2, U32>, acc: U32) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      acc",
    "    case Con{h, t}:",
    "      sum(t, (acc + h : U32))",
    "",
    "def up(s: String) -> String:",
    "  match s:",
    "    case SNil{}:",
    "      SNil{}",
    "    case SCon{c, t}:",
    "      +rest = up(t)",
    "      SCon{Char.to_upper(c), rest}",
    "",
    "def size(n: Tree, +k: String) -> U32:",
    "  match n:",
    "    case Leaf{}:",
    "      1",
    "    case Node{l, r}:",
    "      (size(l, k) + size(r, k) : U32)",
    "",
    "def keep(xs: List<&2, U32>) -> List<&2, U32>:",
    "  match xs:",
    "    case Nil{}:",
    "      []",
    "    case Con{h, t}:",
    "      Bool.pick(List<&2, U32>, U32.is_eq(h, 0), keep(t), h <> keep(t))",
    "",
    "def count(-A: Data, xs: List<&2, A>) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      (1 + count(A, t) : U32)"], "\n")

def rec.concatted() -> String:
  String.join([
    "def show(xs: List<&2, U32>, acc: String) -> String:",
    "  match xs:",
    "    case Nil{}:",
    "      acc ++ \".\"",
    "    case Con{h, t}:",
    "      show(t, acc ++ U32.show(h) ++ \",\")",
    "",
    "def grow(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:",
    "  match xs:",
    "    case Nil{}:",
    "      acc",
    "    case Con{h, t}:",
    "      grow(t, List.append(&2, U32, acc, [h]))",
    "",
    "def pre(xs: List<&2, U32>, acc: String) -> String:",
    "  match xs:",
    "    case Nil{}:",
    "      acc",
    "    case Con{h, t}:",
    "      pre(t, U32.show(h) ++ acc)",
    "",
    "def back(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:",
    "  match xs:",
    "    case Nil{}:",
    "      acc",
    "    case Con{h, t}:",
    "      back(t, List.append(&2, U32, [h], acc))"], "\n")

def rec.indexed() -> String:
  String.join([
    "def total(i: Nat, +xs: List<&2, U32>) -> U32:",
    "  match i:",
    "    case 0n:",
    "      0",
    "    case 1n+p:",
    "      (Maybe.or(List.get(&2, U32, xs, p), 0) + total(p, xs) : U32)",
    "",
    "def scan(i: Nat, +s: String) -> U32:",
    "  match i:",
    "    case 0n:",
    "      0",
    "    case 1n+p:",
    "      +c = String.get(s, p)",
    "      scan(p, s)",
    "",
    "def third(xs: List<&2, U32>) -> Maybe<&2, U32>:",
    "  List.get(&2, U32, xs, 2n)",
    "",
    "def heads(xss: List<&2, List<&2, U32>>) -> List<&2, Maybe<&2, U32>>:",
    "  match xss:",
    "    case Nil{}:",
    "      []",
    "    case Con{h, t}:",
    "      List.get(&2, U32, h, 0n) <> heads(t)"], "\n")

def rec.tabled() -> String:
  String.join([
    "def go(i: Nat) -> U32:",
    "  +tab = [1, 2, 3, 4, 5, 6, 7, 8, 9]",
    "  match i:",
    "    case 0n:",
    "      0",
    "    case 1n+p:",
    "      (Maybe.or(List.get(&2, U32, tab, p), 0) + go(p) : U32)",
    "",
    "def setgo(i: Nat) -> List<&2, U32>:",
    "  +tab = List.replicate(&2, U32, 16n, 0)",
    "  match i:",
    "    case 0n:",
    "      tab",
    "    case 1n+p:",
    "      setgo(List.set(&2, U32, tab, p, 1))",
    "",
    "def grow(i: Nat, +acc: List<&2, U32>) -> List<&2, U32>:",
    "  match i:",
    "    case 0n:",
    "      acc",
    "    case 1n+p:",
    "      grow(p, List.set(&2, U32, acc, p, 1))",
    "",
    "def once(xs: List<&2, U32>) -> List<&2, U32>:",
    "  List.set(&2, U32, xs, 1n, 0)",
    "",
    "def slot(i: Nat) -> U32:",
    "  +tab = [1, 2, 3, 4, 5, 6, 7, 8, 9]",
    "  match i:",
    "    case 0n:",
    "      Maybe.or(List.get(&2, U32, tab, 0n), 0)",
    "    case 1n+p:",
    "      slot(p)",
    "",
    "def dep(i: Nat, +n: Nat) -> U32:",
    "  +tab = List.replicate(&2, U32, n, 0)",
    "  match i:",
    "    case 0n:",
    "      0",
    "    case 1n+p:",
    "      (Maybe.or(List.get(&2, U32, tab, p), 0) + dep(p, n) : U32)"], "\n")

def rec.hoisted() -> String:
  String.join([
    "def go(i: Nat) -> U32:",
    "  +t = [1, 2, 3, 4, 5, 6, 7, 8, 9]",
    "  match i:",
    "    case 0n:",
    "      0",
    "    case 1n+p:",
    "      (Maybe.or(List.get(&2, U32, t, p), 0) + go(p) : U32)",
    "",
    "def cold(i: Nat) -> U32:",
    "  match i:",
    "    case 0n:",
    "      +tab = [1, 2, 3]",
    "      Maybe.or(List.get(&2, U32, tab, 0n), 0)",
    "    case 1n+p:",
    "      cold(p)",
    "",
    "def uses(p: Nat, +n: U32) -> U32:",
    "  +w = tones(n)",
    "  match p:",
    "    case 0n:",
    "      0",
    "    case 1n+q:",
    "      (Maybe.or(List.get(&2, U32, w, q), 0) + uses(q, n) : U32)",
    "",
    "def rowed(xs: List<&2, U32>) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      +row = [h, h]",
    "      (Maybe.or(List.get(&2, U32, row, 0n), 0) + rowed(t) : U32)",
    "",
    "def tiny(i: Nat) -> U32:",
    "  +a = [0 : U32*8n]",
    "  match i:",
    "    case 0n:",
    "      0",
    "    case 1n+p:",
    "      (a[i] + tiny(p) : U32)",
    "",
    "def arr(i: Nat) -> U32:",
    "  +a = [0 : U32*16n]",
    "  match i:",
    "    case 0n:",
    "      0",
    "    case 1n+p:",
    "      (a[i] + arr(p) : U32)"], "\n")

def rec.ringed() -> String:
  String.join([
    "def step(w: List<&2, U32>, x: U32) -> U32:",
    "  step(List.append(&2, U32, List.drop(&2, U32, w, 1n), [x]), x)",
    "",
    "def text(w: String, x: String) -> String:",
    "  text(String.drop(w, 1n) ++ x, x)",
    "",
    "def grow(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:",
    "  match xs:",
    "    case Nil{}:",
    "      acc",
    "    case Con{h, t}:",
    "      grow(t, List.append(&2, U32, acc, [h]))",
    "",
    "def eat(xs: List<&2, U32>) -> List<&2, U32>:",
    "  match xs:",
    "    case Nil{}:",
    "      []",
    "    case Con{h, t}:",
    "      eat(List.append(&2, U32, List.drop(&2, U32, xs, 1n), [h]))"], "\n")

def rec.rewalked() -> String:
  String.join([
    "def walk(xs: List<&2, U32>) -> List<&2, U32>:",
    "  match xs:",
    "    case Nil{}:",
    "      []",
    "    case Con{h, t}:",
    "      h <> walk(t)",
    "",
    "def go(xs: List<&2, U32>) -> U32:",
    "  +dc = Maybe.or(List.get(&2, U32, walk(xs), 0n), 0)",
    "  +rest = walk(xs)",
    "  dc",
    "",
    "def both(xs: List<&2, U32>, ys: List<&2, U32>) -> U32:",
    "  (Maybe.or(List.get(&2, U32, walk(xs), 0n), 0) + Maybe.or(List.head(&2, U32, walk(ys)), 0) : U32)",
    "",
    "def full(xs: List<&2, U32>) -> List<&2, U32>:",
    "  List.append(&2, U32, walk(xs), walk(xs))",
    "",
    "def bound(xs: List<&2, U32>) -> U32:",
    "  +spec = walk(xs)",
    "  +dc = Maybe.or(List.get(&2, U32, spec, 0n), 0)",
    "  +rest = walk(xs)",
    "  dc",
    "",
    "def split(xs: List<&2, U32>, n: U32) -> U32:",
    "  match n:",
    "    case 0:",
    "      Maybe.or(List.get(&2, U32, walk(xs), 0n), 0)",
    "    case 1+p:",
    "      Maybe.or(List.head(&2, U32, walk(xs)), 0)"], "\n")

def rec.united() -> String:
  String.join([
    "def hot(n: U32) -> U32:",
    "  ((n * 1 : U32) + hot((n - 1 : U32)) : U32)",
    "",
    "def nest(p: Nat) -> Nat:",
    "  Nat.div(Nat.mul(p, 1n), 1n) + nest(p)",
    "",
    "def cold(x: U32) -> U32:",
    "  (x * 1 : U32)",
    "",
    "def base(n: U32) -> U32:",
    "  match n:",
    "    case 0:",
    "      (n * 1 : U32)",
    "    case 1+p:",
    "      base(p)",
    "",
    "def minus(n: U32) -> U32:",
    "  match n:",
    "    case 0:",
    "      0",
    "    case 1+p:",
    "      minus((n - 1 : U32))"], "\n")

def rec.picked() -> String:
  String.join([
    "def get(xs: List<&2, U32>, +i: U32) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      Bool.pick(U32, U32.is_eq(h, i), h, get(t, i))",
    "",
    "def nested(xs: List<&2, U32>) -> U32:",
    "  match xs:",
    "    case Con{h, t}:",
    "      Bool.pick(U32, True{}, 1, Bool.pick(U32, False{}, 2, nested(t)))",
    "    case Nil{}:",
    "      0",
    "",
    "def ok(xs: List<&2, U32>, +i: U32) -> U32:",
    "  match xs:",
    "    case Nil{}:",
    "      0",
    "    case Con{h, t}:",
    "      +more = ok(t, i)",
    "      Bool.pick(U32, U32.is_eq(h, i), h, more)",
    "",
    "def two(xs: List<&2, U32>) -> U32:",
    "  match xs:",
    "    case Con{h, t}:",
    "      Bool.pick(U32, True{}, two(t), Bool.pick(U32, False{}, 1, two(t)))",
    "    case Nil{}:",
    "      0"], "\n")

def frame.show(cc: Frame.Cut) -> String:
  match cc:
    case Frame.More{}:
      "more"
    case Frame.Ready{body, rest}:
      Frame.decode(body) ++ " +" ++ Nat.show(List.length(&2, U32, rest))

def docs.sample() -> List<&2, Docs.Doc>:
  Docs.set(Docs.set(Docs.set([], "a", "1"), "b", "2"), "a", "3")

def rep.show.go(ds: List<&2, Rep.Diag>) -> String:
  match ds:
    case Nil{}:
      ""
    case Con{Rep.Diag{line, msg}, t}:
      "[" ++ U32.show(line) ++ "|" ++ msg ++ "]" ++ rep.show.go(t)

def rep.show(text: String) -> String:
  rep.show.go(Rep.parse(text))

def fake.read(_path: String) -> IO(Maybe<&2, String>):
  IO.pure(Maybe<&2, String>, None{})

def fake.base_path(_u: Unit) -> IO(String):
  IO.pure(String, "/base.bend")

def fake.files() -> Files.Files:
  Files.Files{fake.read, fake.base_path}

def io.prints(ls: List<&2, String>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{h, t}:
      do IO<Unit>:
        IO.print(h)
        io.prints(t)

def refs.text() -> String:
  "import Base\\n\\ntype Shape is Data:\\n  Circle{r: U32}\\n\\n# the area\\ndef area(+x: U32) -> U32:\\n  match x:\\n    case Circle{r}:\\n      (x * r : U32)\\n\\ndef main() -> U32:\\n  area(Circle{2})\\n"

def refs.ask(id: String, method: String, line: String, col: String, extra: String) -> String:
  "{\"jsonrpc\":\"2.0\",\"id\":" ++ id ++ ",\"method\":\"textDocument/" ++ method ++ "\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/a.bend\"},\"position\":{\"line\":" ++ line ++ ",\"character\":" ++ col ++ "}" ++ extra ++ "}}"

def refs.inbox() -> List<&2, String>:
  ["{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/a.bend\",\"text\":\"" ++ refs.text() ++ "\"}}}",
   refs.ask("1", "references", "7", "8", ",\"context\":{\"includeDeclaration\":true}"),
   refs.ask("2", "rename", "9", "7", ",\"newName\":\"shape\""),
   refs.ask("3", "references", "12", "3", ""),
   refs.ask("4", "references", "3", "3", ""),
   refs.ask("5", "references", "0", "2", ""),
   refs.ask("6", "rename", "6", "20", ",\"newName\":\"Word\""),
   "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"textDocument/semanticTokens/full\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/a.bend\"}}}"]

def nav.math() -> String:
  "import Base\n\n# squares a number\ndef square(+x: U32) -> U32:\n  (x * x : U32)\n\ntype Shape is Data:\n  Circle{r: U32}\n"

def nav.base() -> String:
  "# shows a number\ndef U32.show(n: U32) -> String:\n  \"\"\n"

def nav.at(+path: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.eq(path, "/w/lib/math.bend"), Some{nav.math()},
    Bool.pick(Maybe<&2, String>, String.eq(path, "/base.bend"), Some{nav.base()}, None{}))

def nav.read(path: String) -> IO(Maybe<&2, String>):
  IO.pure(Maybe<&2, String>, nav.at(path))

def nav.files() -> Files.Files:
  Files.Files{nav.read, fake.base_path}

def nav.main() -> String:
  "import Base\\nimport ../lib/math.bend as M\\n\\n# doubles\\ndef twice(x: U32) -> U32:\\n  M.square(x)\\n\\ndef main() -> String:\\n  U32.show(twice(M.Circle{2}))\\n"

def nav.edited() -> String:
  "import Base\\n\\n# triples now\\ndef twice(x: U32) -> U32:\\n  x\\n\\ndef main() -> U32:\\n  twice(1)\\n"

def nav.ask(id: String, method: String, line: String, col: String) -> String:
  "{\"jsonrpc\":\"2.0\",\"id\":" ++ id ++ ",\"method\":\"textDocument/" ++ method ++ "\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/app/main.bend\"},\"position\":{\"line\":" ++ line ++ ",\"character\":" ++ col ++ "}}}"

def nav.inbox() -> List<&2, String>:
  ["{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/app/main.bend\",\"text\":\"" ++ nav.main() ++ "\"}}}",
   nav.ask("1", "hover", "5", "5"),
   nav.ask("2", "definition", "5", "5"),
   nav.ask("3", "hover", "8", "20"),
   nav.ask("4", "hover", "8", "6"),
   nav.ask("5", "definition", "8", "13"),
   nav.ask("6", "hover", "4", "12"),
   nav.ask("7", "documentSymbol", "0", "0"),
   nav.ask("9", "hover", "5", "11"),
   nav.ask("10", "definition", "5", "11"),
   "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/app/main.bend\"},\"contentChanges\":[{\"text\":\"" ++ nav.edited() ++ "\"}]}}",
   nav.ask("8", "hover", "7", "3")]

# a law file: the header is not the law's comment
def lawhover.laws() -> String:
  "# io: rationale that must stay off the law.\\nimport Base\\nimport ./file.bend as F\\n\\n# LAW: and the text of nothing is the empty string.\\nlaw text_of_none:\\n  {F.text_of(None{}) == \\\"\\\" : String}\\n"

# the def a call inside the law names
def lawhover.file() -> String:
  "# the text a read answered\\ndef text_of(m: Maybe<&2, String>) -> String:\\n  match m:\\n    case None{}:\\n      \\\"\\\"\\n    case Some{s}:\\n      s\\n"

# the proof: `def Laws.text_of_none` fills the law, and has no comment of its own
def lawhover.proof() -> String:
  "import Base\\nimport ./LAWS.bend as Laws\\n\\ndef Laws.text_of_none():\\n  {==}\\n"

# the same three files as source, for the files service
def lawhover.laws_text() -> String:
  "# io: rationale that must stay off the law.\nimport Base\nimport ./file.bend as F\n\n# LAW: and the text of nothing is the empty string.\nlaw text_of_none:\n  {F.text_of(None{}) == \"\" : String}\n"

def lawhover.file_text() -> String:
  "# the text a read answered\ndef text_of(m: Maybe<&2, String>) -> String:\n  match m:\n    case None{}:\n      \"\"\n    case Some{s}:\n      s\n"

def lawhover.proof_text() -> String:
  "import Base\nimport ./LAWS.bend as Laws\n\ndef Laws.text_of_none():\n  {==}\n"

def lawhover.at(+path: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.eq(path, "/w/io/LAWS.bend"), Some{lawhover.laws_text()},
    Bool.pick(Maybe<&2, String>, String.eq(path, "/w/io/PROOF.bend"), Some{lawhover.proof_text()},
      Bool.pick(Maybe<&2, String>, String.eq(path, "/w/io/file.bend"), Some{lawhover.file_text()}, None{})))

def lawhover.read(path: String) -> IO(Maybe<&2, String>):
  IO.pure(Maybe<&2, String>, lawhover.at(path))

def lawhover.files() -> Files.Files:
  Files.Files{lawhover.read, fake.base_path}

def lawhover.ask(id: String, method: String, uri: String, line: String, col: String) -> String:
  "{\"jsonrpc\":\"2.0\",\"id\":" ++ id ++ ",\"method\":\"textDocument/" ++ method ++ "\",\"params\":{\"textDocument\":{\"uri\":\"" ++ uri ++ "\"},\"position\":{\"line\":" ++ line ++ ",\"character\":" ++ col ++ "}}}"

def lawhover.inbox() -> List<&2, String>:
  ["{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/io/LAWS.bend\",\"text\":\"" ++ lawhover.laws() ++ "\"}}}",
   lawhover.ask("1", "hover", "file:///w/io/LAWS.bend", "5", "6"),
   lawhover.ask("2", "definition", "file:///w/io/LAWS.bend", "5", "6"),
   lawhover.ask("3", "hover", "file:///w/io/LAWS.bend", "6", "7"),
   "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/io/PROOF.bend\",\"text\":\"" ++ lawhover.proof() ++ "\"}}}",
   lawhover.ask("4", "hover", "file:///w/io/PROOF.bend", "3", "10"),
   lawhover.ask("5", "definition", "file:///w/io/PROOF.bend", "3", "10")]

def completion.math() -> String:
  "import Base\n\n# squares a number\ndef square(+x: U32) -> U32:\n  (x * x : U32)\n\ndef sqrt(x: U32) -> U32:\n  x\n\ndef cube(x: U32) -> U32:\n  x\n"

def completion.base() -> String:
  "law U32.show:\n  U32 -> String\n\ndef U32.show.go(n: U32) -> String:\n  \"\"\n\n# shows a number\ndef U32.show(n):\n  \"\"\n\ndef U32.add(a: U32, b: U32) -> U32:\n  a\n\ndef Nat.show(n: Nat) -> String:\n  \"\"\n"

def completion.at(+path: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.eq(path, "/w/lib/math.bend"), Some{completion.math()},
    Bool.pick(Maybe<&2, String>, String.eq(path, "/base.bend"), Some{completion.base()}, None{}))

def completion.read(path: String) -> IO(Maybe<&2, String>):
  IO.pure(Maybe<&2, String>, completion.at(path))

def completion.files() -> Files.Files:
  Files.Files{completion.read, fake.base_path}

def completion.main() -> String:
  "import Base\\nimport ../lib/math.bend as M\\n\\ndef mine(x: U32) -> U32:\\n  M.sq\\n  U32.s\\n  m\\n  x\\n"

def completion.ask(id: String, line: String, col: String) -> String:
  "{\"jsonrpc\":\"2.0\",\"id\":" ++ id ++ ",\"method\":\"textDocument/completion\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/app/main.bend\"},\"position\":{\"line\":" ++ line ++ ",\"character\":" ++ col ++ "}}}"

def completion.inbox() -> List<&2, String>:
  ["{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/app/main.bend\",\"text\":\"" ++ completion.main() ++ "\"}}}",
   completion.ask("1", "4", "6"),
   completion.ask("2", "5", "7"),
   completion.ask("3", "6", "3"),
   completion.ask("4", "7", "3")]

def session.inbox() -> List<&2, String>:
  ["{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{}}",
   "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}",
   "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/my%20bad.bend\",\"text\":\"x\"}}}",
   "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didSave\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/good.bend\"}}}",
   "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"workspace/symbol\",\"params\":{}}",
   "not json at all",
   "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didClose\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/my%20bad.bend\"}}}",
   "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"shutdown\"}",
   "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}",
   "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"initialize\"}"]

def lint.opened() -> String:
  "import Base\\n\\ndef f(x: U32) -> U32:\\n  y = 1\\n  x\\n"

def lint.edited() -> String:
  "import Base\\n\\n# the identity\\ndef f(x: U32) -> U32:\\n  x\\n"

def lint.inbox() -> List<&2, String>:
  ["{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/bad.bend\",\"text\":\"" ++ lint.opened() ++ "\"}}}",
   "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/bad.bend\"},\"contentChanges\":[{\"text\":\"" ++ lint.edited() ++ "\"}]}}",
   "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didSave\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/bad.bend\"}}}"]

def tok.strings_src() -> String:
  String.join([
    "def kind(v: String) -> U32:",
    "  match v:",
    "    case \"response.created\":",
    "      1",
    "    case \"response.output_item.added\":",
    "      2",
    "    case \"response.reasoning_summary_text.delta\":",
    "      3",
    "    case _:",
    "      0",
    "",
    "def verb(v: String) -> U32:",
    "  match v:",
    "    case \"get\":",
    "      1",
    "    case \"post\":",
    "      2",
    "    case \"put\":",
    "      3",
    "    case \"delete\":",
    "      4",
    "    case \"patch\":",
    "      5",
    "    case \"head\":",
    "      6",
    "    case \"options\":",
    "      7",
    "    case \"connect\":",
    "      8",
    "    case \"trace\":",
    "      9",
    "    case _:",
    "      0",
    "",
    "def code(n: U32) -> U32:",
    "  match n:",
    "    case 1000000001:",
    "      1",
    "    case 1000000002:",
    "      2",
    "    case 1000000003:",
    "      3",
    "    case 1000000004:",
    "      4",
    "    case 1000000005:",
    "      5",
    "    case 1000000006:",
    "      6",
    "    case 1000000007:",
    "      7",
    "    case _:",
    "      0",
    "",
    "def two(a: String, b: String) -> U32:",
    "  match a:",
    "    case \"response.created.first\":",
    "      match b:",
    "        case \"response.created.second\":",
    "          1",
    "        case _:",
    "          2",
    "    case \"response.created.third\":",
    "      3",
    "    case _:",
    "      0"], "\n")

def tok.chars_src() -> String:
  String.join([
    "def classify(c: Char) -> U32:",
    "  match c:",
    "    case '.':",
    "      1",
    "    case ',':",
    "      2",
    "    case ':':",
    "      3",
    "    case ';':",
    "      4",
    "    case '(':",
    "      5",
    "    case ')':",
    "      6",
    "    case '[':",
    "      7",
    "    case ']':",
    "      8",
    "    case '{':",
    "      9",
    "    case _:",
    "      0",
    "",
    "# a few is fine: 'a' 'b' 'c' in a comment",
    "def side(c: Char) -> U32:",
    "  match c:",
    "    case 'l':",
    "      1",
    "    case 'r':",
    "      2",
    "    case _:",
    "      0",
    "",
    "def word(s: String) -> U32:",
    "  match s:",
    "    case \"a\":",
    "      1",
    "    case _:",
    "      0"], "\n")

def tok.twice_src() -> String:
  String.join([
    "def search(bytes: List<&2, U32>, offset: Nat) -> Maybe<&2, Nat>:",
    "  match bytes:",
    "    case 10 <> 10 <> _:",
    "      Some{offset}",
    "    case 10 <> 11 <> 10 <> _:",
    "      Some{offset}",
    "    case _ <> 13 <> 13 <> _:",
    "      Some{offset}",
    "    case _ <> tail:",
    "      search(tail, offset)",
    "    case Nil{}:",
    "      None{}",
    "",
    "def chars(cs: List<&2, Char>) -> Bool:",
    "  match cs:",
    "    case Con{'a', Con{'a', t}}:",
    "      True{}",
    "    case Con{c, t}:",
    "      chars(t)",
    "    case Nil{}:",
    "      False{}",
    "",
    "def once(bytes: List<&2, U32>) -> Bool:",
    "  match bytes:",
    "    case 10 <> 10 <> _:",
    "      True{}",
    "    case other:",
    "      False{}"], "\n")

def tok.arms_src() -> String:
  String.join([
    "def bad(x: Nat) -> Nat:",
    "  match x:",
    "    case 0n:",
    "      0n",
    "    case 1n+p:",
    "      1n",
    "    case 2n+p:",
    "      2n",
    "    case 3n:",
    "      3n",
    "",
    "def good(x: Nat) -> Nat:",
    "  match x:",
    "    case 0n:",
    "      0n",
    "    case 1n:",
    "      1n",
    "    case 3n+p:",
    "      2n",
    "    case 2n+q:",
    "      3n",
    "",
    "def succ(x: Nat) -> Nat:",
    "  match x:",
    "    case Zero{}:",
    "      0n",
    "    case Succ{p}:",
    "      1n",
    "    case 5n:",
    "      5n",
    "",
    "def two(x: Nat, y: Nat) -> Nat:",
    "  match x y:",
    "    case 1n+p m:",
    "      1n",
    "    case 2n+p m:",
    "      2n",
    "    case 0n m:",
    "      0n"], "\n")
