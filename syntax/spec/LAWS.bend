# syntax: the laws. Closed equalities of word, lex, tree, outline and bind.
import Base
import ../word.bend as Word
import ../lex.bend as Lex
import ../tree.bend as Tree
import ../outline.bend as Outline
import ../bind.bend as Bind

# a source with a qualified name on line 1
def word_src() -> String:
  "import Base\n  Frame.decode(body) ++ Nat.show(List.length(&2, U32, rest))\n"

# a lexer fixture
def lex_src() -> String:
  "def f(+x: U32) -> List<&2, U32>: # note\n  case 1n+p:\n    M.go(x, \"a\\\"b\", 'c') ++ {==} <> 1.5\n  y = a[5] <- 42\n"

# a token kind as a short letter
def lex_kind(kk: Lex.TokKind) -> String:
  match kk:
    case Lex.TName{}:
      "n"
    case Lex.TUpper{}:
      "N"
    case Lex.TDotted{}:
      "d"
    case Lex.TWild{}:
      "w"
    case Lex.TKey{}:
      "k"
    case Lex.TColon{}:
      ":"
    case Lex.TEq{}:
      "="
    case Lex.TBind{}:
      "<"
    case Lex.TArrow{}:
      ">"
    case Lex.TLam{}:
      "l"
    case Lex.TAll{}:
      "@"
    case Lex.TAmp{}:
      "&"
    case Lex.TNum{}:
      "#"
    case Lex.TStr{}:
      "s"
    case Lex.TChar{}:
      "c"
    case Lex.TComment{}:
      "%"
    case Lex.TSpace{}:
      "_"
    case Lex.TNewline{}:
      "/"
    case Lex.TOp{}:
      "o"
    case Lex.TOpen{}:
      "("
    case Lex.TClose{}:
      ")"
    case Lex.TComma{}:
      ","

# the significant tokens of a line, as kind:text@col
def lex_show.go(toks: List<&2, Lex.Tok>, +line: U32) -> List<&2, String>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{+k, text, l, c}, t}:
      +rest = lex_show.go(t, line)
      Bool.pick(List<&2, String>, Bool.and(U32.is_eq(l, line), Lex.significant(k)),
        (lex_kind(k) ++ ":" ++ text ++ "@" ++ U32.show(c)) <> rest, rest)

# the significant tokens of one line of lex_src
def lex_show(line: U32) -> String:
  String.join(lex_show.go(Lex.tokens(lex_src()), line), " ")

# a tree fixture
def tree_src() -> String:
  String.join([
    "# doc",
    "def f(+x: List<&2, U32>, y: U32) -> U32:",
    "  match x:",
    "    case Con{h, t}:",
    "      z = (h + y : U32)  # sum",
    "      z",
    "    case Nil{}:",
    "      0",
    "",
    "type T<A> is Data:",
    "  K{a: A}"], "\n")

# a parsed source as text
def tree_show(src: String) -> String:
  Tree.show(Tree.parse(src))

# the significant tokens of a parsed source
def tree_sig(src: String) -> String:
  Lex.text(Tree.leaves(Tree.parse(src)))

# an outline fixture
def outline_src() -> String:
  String.join([
    "# a module",
    "import Base",
    "import ./math.bend as M",
    "",
    "# a shape",
    "# in two lines",
    "type Shape<-A: Type> is Data:",
    "  Circle{r: U32}",
    "  Square{s: U32}",
    "",
    "stray junk here (((",
    "# the area",
    "def area(x: Shape) -> U32:",
    "  match x:",
    "    case Circle{+r}:",
    "      (3 * r : U32)",
    "",
    "def long.header(",
    "  a: U32, b: U32",
    ") -> U32:",
    "  a",
    "",
    "# LAW: zero is neutral",
    "law add_zero:",
    "  for x: Nat",
    "  {Nat.add(x, 0n) == x : Nat}",
    "@unsafe def spin(x: U32) -> U32:",
    "  spin(x)"], "\n")

# an outline item kind as a word
def outline_kind(kk: Outline.ItemKind) -> String:
  match kk:
    case Outline.IImport{}:
      "import"
    case Outline.IDef{}:
      "def"
    case Outline.ILaw{}:
      "law"
    case Outline.IType{}:
      "type"
    case Outline.ICtor{}:
      "ctor"
    case Outline.ILocal{}:
      "local"

# every item as kind name @line <path> [doc] sig
def outline_show.go(items: List<&2, Outline.Item>) -> List<&2, String>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Outline.Item{k, name, line, sig, doc, path}, t}:
      (outline_kind(k) ++ " " ++ name ++ " @" ++ U32.show(line) ++ " <" ++ path ++ "> [" ++ doc ++ "] "
        ++ sig) <> outline_show.go(t)

# the outline of outline_src
def outline_shown() -> String:
  String.join(outline_show.go(Outline.items(outline_src())), "\n")

# a binder fixture
def bind_src() -> String:
  String.join([
    "import Base",
    "import ../lex.bend as Lex",
    "",
    "def area(+x: Shape, -A: Type, ~f: U32 -> U32) -> U32:",
    "  match x:",
    "    case Circle{+r}:",
    "      y = (3 * r : U32)",
    "      (a, K{b}) = pair(y)",
    "      g = z => (z + a : U32)",
    "      g(b)",
    "    case Square{s}:",
    "      s",
    "",
    "def main() -> IO(Unit):",
    "  do IO<Unit>:",
    "    name : String <- IO.get_env(\"USER\")",
    "    n : U32 = 3",
    "    n = Lex.step(n)",
    "    IO.print(name)",
    "",
    "law add_zero:",
    "  for x: Nat",
    "  {Nat.add(x, 0n) == x : Nat}",
    "",
    "def long.header(",
    "  first: U32, second: List<&2, U32>",
    ") -> U32:",
    "  area(first)",
    "",
    "type Monoid is Data:",
    "  Monoid{unit: U32, join: @+p:U32 -> @+q:U32 -> U32}"], "\n")

# a bind kind as a word
def bind_kind(kk: Bind.BindKind) -> String:
  match kk:
    case Bind.KItem{}:
      "item"
    case Bind.KCtor{}:
      "ctor"
    case Bind.KParam{}:
      "param"
    case Bind.KTypeParam{}:
      "typeparam"
    case Bind.KField{}:
      "field"
    case Bind.KLocal{}:
      "local"
    case Bind.KPat{}:
      "pat"
    case Bind.KFor{}:
      "for"
    case Bind.KTypeVar{}:
      "typevar"

# visible names on a line
def bind_names.go(ls: List<&2, Bind.Bind>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Bind.Bind{name, line, col, k, note}, t}:
      name <> bind_names.go(t)

# visible names on a line of bind_src, space-separated
def bind_names(line: U32) -> String:
  String.join(bind_names.go(Bind.visible(Bind.bound(bind_src()), line)), " ")

# one binder as line:col kind | note
def bind_show(bb: Bind.Bind) -> String:
  Bind.Bind{name, line, col, k, note} = bb
  U32.show(line) ++ ":" ++ U32.show(col) ++ " " ++ bind_kind(k) ++ " | " ++ note

# a target as local / item / qual / free
def bind_target(tt: Bind.Target) -> String:
  match tt:
    case Bind.TLocal{line, col}:
      "local " ++ U32.show(line) ++ ":" ++ U32.show(col)
    case Bind.TItem{name}:
      "item " ++ name
    case Bind.TQual{alias, name}:
      "qual " ++ alias ++ " " ++ name
    case Bind.TFree{}:
      "free"

# a site as bind / use / -
def bind_site(mm: Maybe<&2, Bind.Site>) -> String:
  match mm:
    case None{}:
      "-"
    case Some{Bind.SBind{b}}:
      "bind " ++ bind_show(b)
    case Some{Bind.SUse{Bind.Use{name, line, col, t}}}:
      "use " ++ name ++ " -> " ++ bind_target(t)

# the site at a position of bind_src
def bind_at(line: U32, col: U32) -> String:
  bind_site(Bind.at(Bind.bound(bind_src()), line, col))

# one position as line:col
def bind_pair(pp: Bind.Pos) -> String:
  Bind.Pos{l, c} = pp
  U32.show(l) ++ ":" ++ U32.show(c)

# positions as a list of line:col
def bind_pairs.go(ps: List<&2, Bind.Pos>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      bind_pair(p) <> bind_pairs.go(t)

# every site of the name at a position
def bind_sites(line: U32, col: U32) -> String:
  String.join(bind_pairs.go(Bind.sites(Bind.bound(bind_src()), line, col)), " ")

# every site of an item
def bind_item_sites(name: String) -> String:
  String.join(bind_pairs.go(Bind.item_sites(Bind.bound(bind_src()), name)), " ")

# LAW: inside a qualified name
law word_at_inside:
  {Word.at(word_src(), 1, 9) == "Frame.decode" : String}

# LAW: at a name's first char
law word_at_first:
  {Word.at(word_src(), 1, 2) == "Frame.decode" : String}

# LAW: right after a name
law word_at_after:
  {Word.at(word_src(), 1, 14) == "Frame.decode" : String}

# LAW: a plain name
law word_at_plain:
  {Word.at(word_src(), 1, 16) == "body" : String}

# LAW: a name deep in the line
law word_at_deep:
  {Word.at(word_src(), 1, 40) == "List.length" : String}

# LAW: on an operator there is none
law word_at_op:
  {Word.at(word_src(), 1, 23) == "" : String}

# LAW: past the end of the line
law word_at_eol:
  {Word.at(word_src(), 1, 500) == "" : String}

# LAW: past the end of the text
law word_at_eof:
  {Word.at(word_src(), 9, 0) == "" : String}

# LAW: the first line
law word_at_line0:
  {Word.at(word_src(), 0, 8) == "Base" : String}

# LAW: typed so far, mid-name
law word_before_mid:
  {Word.before(word_src(), 1, 10) == "Frame.de" : String}

# LAW: typed so far, after an alias dot
law word_before_dot:
  {Word.before(word_src(), 1, 8) == "Frame." : String}

# LAW: nothing typed after a paren
law word_before_paren:
  {Word.before(word_src(), 1, 15) == "" : String}

# LAW: a letter is a name char
law word_is_name:
  {Word.is_name('a') == True{} : Bool}

# LAW: an operator is not a name char
law word_is_name_op:
  {Word.is_name('+') == False{} : Bool}

# LAW: text of a reversed run
law word_text:
  {Word.text(['b', 'a']) == "ab" : String}

# LAW: in_line is at on one line
law word_in_line:
  {Word.in_line("Frame.decode", 2) == "Frame.decode" : String}

# LAW: finish of a scanned line
law word_finish_scan:
  {Word.finish(Word.scan(String.to_list("ab"), Word.W{0, 0, [], None{}}, 0), 0) == "ab" : String}

# LAW: step of a name char
law word_step:
  {Word.finish(Word.step('a', Word.W{0, 0, [], None{}}, 0), 0) == "a" : String}

# LAW: close of a run that holds the column
law word_close:
  {Maybe.default(&2, String, Word.close(2, 0, ['b', 'a'], None{}, 1), "") == "ab" : String}

# LAW: head of a dotted name
law word_head:
  {Word.head("Alias.rest") == "Alias" : String}

# LAW: rest of a dotted name
law word_rest:
  {Word.rest("Alias.rest") == "rest" : String}

# LAW: fst of a cut
law word_cut_fst:
  {Word.fst(Word.cut("Alias.rest")) == "Alias" : String}

# LAW: snd of a cut
law word_cut_snd:
  {Word.snd(Word.cut("Alias.rest")) == "rest" : String}

# LAW: run_of stops at a non-name
law word_run_of:
  {String.from_list(Word.run_of(String.to_list("ab+"))) == "ab" : String}

# LAW: lex is lossless
law lex_lossless:
  {Lex.text(Lex.tokens(lex_src())) == lex_src() : String}

# LAW: lex is lossless on an unclosed string
law lex_lossless_unclosed:
  {Lex.text(Lex.tokens("x = \"abc\ny = 'q\nz")) == "x = \"abc\ny = 'q\nz" : String}

# LAW: line 0 of lex_src
law lex_line_0:
  {lex_show(0) ==
    "k:def@0 n:f@4 (:(@5 o:+@6 n:x@7 :::@8 N:U32@10 ):)@13 >:->@15 N:List@18 o:<&@22 #:2@24 ,:,@25 N:U32@27 o:>@30 :::@31"
    : String}

# LAW: line 1 of lex_src
law lex_line_1:
  {lex_show(1) == "k:case@2 #:1n@7 o:+@9 n:p@10 :::@11" : String}

# LAW: line 2 of lex_src
law lex_line_2:
  {lex_show(2) ==
    "d:M.go@4 (:(@8 n:x@9 ,:,@10 s:\"a\\\"b\"@12 ,:,@18 c:'c'@20 ):)@23 o:++@25 (:{@28 o:==@29 ):}@31 o:<>@33 #:1.5@36"
    : String}

# LAW: line 3 of lex_src
law lex_line_3:
  {lex_show(3) == "n:y@2 =:=@4 n:a@6 (:[@7 #:5@8 ):]@9 <:<-@11 #:42@14" : String}

# LAW: def is a keyword
law lex_is_keyword:
  {Lex.is_keyword("def") == True{} : Bool}

# LAW: foo is not a keyword
law lex_not_keyword:
  {Lex.is_keyword("foo") == False{} : Bool}

# LAW: an open token
law lex_is_open:
  {Lex.is_open(Lex.TOpen{}) == True{} : Bool}

# LAW: a close token
law lex_is_close:
  {Lex.is_close(Lex.TClose{}) == True{} : Bool}

# LAW: a comma token
law lex_is_comma:
  {Lex.is_comma(Lex.TComma{}) == True{} : Bool}

# LAW: a name token
law lex_is_name:
  {Lex.is_name(Lex.TName{}) == True{} : Bool}

# LAW: an operator token
law lex_is_op:
  {Lex.is_op(Lex.TOp{}) == True{} : Bool}

# LAW: a newline token
law lex_is_nl:
  {Lex.is_nl(Lex.TNewline{}) == True{} : Bool}

# LAW: space is not significant
law lex_significant_space:
  {Lex.significant(Lex.TSpace{}) == False{} : Bool}

# LAW: a word's text
law lex_word:
  {Lex.word(['b', 'a']) == "ab" : String}

# LAW: refine_name of def is a keyword
law lex_refine_name:
  {Lex.refine_name("def") == Lex.TKey{} : Lex.TokKind}

# LAW: refine_op of -> is an arrow
law lex_refine_op:
  {Lex.refine_op("->") == Lex.TArrow{} : Lex.TokKind}

# LAW: refine of a name
law lex_refine:
  {Lex.refine(Lex.TName{}, "def") == Lex.TKey{} : Lex.TokKind}

# LAW: upper_first of U32
law lex_upper_first:
  {Lex.upper_first(String.to_list("U32")) == True{} : Bool}

# LAW: is_newline of CNewline
law lex_is_newline:
  {Lex.is_newline(Lex.CNewline{}) == True{} : Bool}

# LAW: statements nest by indent, groups by brackets
law tree_nested:
  {tree_show(tree_src()) ==
    "[def f (+ x : List <&2 , U32> , y : U32) -> U32 : {[match x : {[case Con {h , t} : {[z = (h + y : U32)] [z]}] [case Nil {} : {[0]}]}]}] [type T <A> is Data : {[K {a : A}]}]"
    : String}

# LAW: a call over lines is one statement
law tree_call_lines:
  {tree_show("f(a,\n  b)\nc") == "[f (a , b)] [c]" : String}

# LAW: a header over lines, then its body
law tree_header_lines:
  {tree_show("def g(\n  a: U32\n) -> U32:\n  a") == "[def g (a : U32) -> U32 : {[a]}]" : String}

# LAW: >> closes two angle groups
law tree_angles:
  {tree_show("x: List<List<U32>>") == "[x : List <List <U32>>]" : String}

# LAW: less-than is not a bracket
law tree_lt:
  {tree_show("a < b") == "[a < b]" : String}

# LAW: <> and <- are operators
law tree_ops:
  {tree_show("a <> b <- c") == "[a <> b <- c]" : String}

# LAW: the next item closes an unclosed bracket
law tree_unclosed:
  {tree_show("def f(x\ndef g() -> U32:\n  1") == "[def f (x..] [def g () -> U32 : {[1]}]" : String}

# LAW: a stray close is a leaf
law tree_stray:
  {tree_show("f(x))") == "[f (x) )]" : String}

# LAW: a mismatched close reaches its match
law tree_mismatch:
  {tree_show("f([x)\ny") == "[f ([x..)] [y]" : String}

# LAW: the end of the file closes everything
law tree_eof:
  {tree_show("f(x\n  y") == "[f (x y..]" : String}

# LAW: the leaves are the significant tokens
law tree_leaves:
  {tree_sig("def f(x):\n  g(x)  # c") == "deff(x):g(x)" : String}

# LAW: an empty source
law tree_empty:
  {tree_show("") == "" : String}

# LAW: of_tokens is parse of the tokens
law tree_of_tokens:
  {Tree.show(Tree.of_tokens(Lex.tokens("x"))) == Tree.show(Tree.parse("x")) : String}

# LAW: closer of (
law tree_closer:
  {Tree.closer("(") == ")" : String}

# LAW: all_gt of >>
law tree_all_gt:
  {Tree.all_gt(['>', '>']) == True{} : Bool}

# LAW: line of a one-token source
law tree_line:
  {Tree.line(Tree.parse("x")) == 0 : U32}

# LAW: col of a one-token source
law tree_col:
  {Tree.col(Tree.parse("x")) == 0 : U32}

# LAW: text of a one-token source
law tree_text:
  {Tree.text(Tree.parse("x")) == "x" : String}

# LAW: first of a one-token source is some
law tree_first:
  {Maybe.is_some(&2, Lex.Tok, Tree.first(Tree.parse("x"))) == True{} : Bool}

# LAW: a leaf is a leaf
law tree_is_leaf:
  {Tree.is_leaf(Tree.Leaf{Lex.Tok{Lex.TName{}, "x", 0, 0}}) == True{} : Bool}

# LAW: is_text of that leaf
law tree_is_text:
  {Tree.is_text(Tree.Leaf{Lex.Tok{Lex.TName{}, "x", 0, 0}}, "x") == True{} : Bool}

# LAW: is_name_tok of a name
law tree_is_name_tok:
  {Tree.is_name_tok(Lex.Tok{Lex.TName{}, "x", 0, 0}) == True{} : Bool}

# LAW: to_list of NNil
law tree_to_list:
  {List.is_empty(&2, Tree.Node, Tree.to_list(Tree.NNil{})) == True{} : Bool}

# LAW: of_list of none is NNil
law tree_of_list:
  {Tree.show(Tree.of_list([])) == "" : String}

# LAW: reverse of NNil is the acc
law tree_reverse:
  {Tree.show(Tree.reverse(Tree.NNil{}, Tree.NNil{})) == "" : String}

# LAW: closes_with of a close paren
law tree_closes_with:
  {Tree.closes_with(Lex.TClose{}, ")") == True{} : Bool}

# LAW: opens_angle of List<
law tree_opens_angle:
  {Tree.opens_angle(Lex.TOp{}, "<", True{}) == True{} : Bool}

# LAW: opens of a group
law tree_opens:
  {Tree.opens(Tree.parse("f(x)"), "(") == False{} : Bool}

# LAW: the outline of outline_src
law outline_items:
  {outline_shown() == String.join([
    "import Base @1 <Base> [a module] import Base",
    "import M @2 <./math.bend> [] import ./math.bend as M",
    "type Shape @6 <> [a shape\nin two lines] type Shape<-A: Type> is Data:",
    "ctor Circle @7 <> [] Circle{r: U32}",
    "ctor Square @8 <> [] Square{s: U32}",
    "def area @12 <> [the area] def area(x: Shape) -> U32:",
    "def long.header @17 <> [] def long.header(\n  a: U32, b: U32\n) -> U32:",
    "law add_zero @23 <> [LAW: zero is neutral] law add_zero:\n  for x: Nat\n  {Nat.add(x, 0n) == x : Nat}",
    "def spin @26 <> [] @unsafe def spin(x: U32) -> U32:"], "\n") : String}

# LAW: a blank line
law outline_is_blank:
  {Outline.is_blank("") == True{} : Bool}

# LAW: an import kind
law outline_is_import:
  {Outline.is_import(Outline.IImport{}) == True{} : Bool}

# LAW: a def kind
law outline_is_def:
  {Outline.is_def(Outline.IDef{}) == True{} : Bool}

# LAW: name up to a paren
law outline_name:
  {Outline.name("area(x: Shape) -> U32:") == "area" : String}

# LAW: lstrip of a padded line
law outline_lstrip:
  {Outline.lstrip("  x") == "x" : String}

# LAW: nonempty of a word
law outline_nonempty:
  {Outline.nonempty("x") == True{} : Bool}

# LAW: words of a line
law outline_words:
  {List.length(&2, String, Outline.words("def area")) == 2n : Nat}

# LAW: undoc drops a hash
law outline_undoc:
  {Outline.undoc("# hi") == "hi" : String}

# LAW: doc_text of one line
law outline_doc_text:
  {Outline.doc_text(["hi"]) == "hi" : String}

# LAW: sig_text of one line
law outline_sig_text:
  {Outline.sig_text(["def f():"]) == "def f():" : String}

# LAW: def_name of a def line
law outline_def_name:
  {Outline.def_name("def area(x: Shape) -> U32:") == "area" : String}

# LAW: starts_upper of Circle
law outline_starts_upper:
  {Outline.starts_upper("Circle{r: U32}") == True{} : Bool}

# LAW: has of a name
law outline_has:
  {Outline.has(["a"], "a") == True{} : Bool}

# LAW: find of area
law outline_find:
  {Maybe.is_some(&2, Outline.Item, Outline.find(Outline.items(outline_src()), "area"))
    == True{} : Bool}

# LAW: import_path of M
law outline_import_path:
  {Maybe.default(&2, String, Outline.import_path(Outline.items(outline_src()), "M"), "")
    == "./math.bend" : String}

# LAW: starting area
law outline_starting:
  {List.length(&2, Outline.Item, Outline.starting(Outline.items(outline_src()), "ar", ""))
    == 1n : Nat}

# LAW: aliases of M
law outline_aliases:
  {List.length(&2, Outline.Item, Outline.aliases(Outline.items(outline_src()), "M"))
    == 1n : Nat}

# LAW: add of none
law outline_add:
  {List.is_empty(&2, Outline.Item, Outline.add(None{}, [])) == True{} : Bool}

# LAW: classify of a def line
law outline_classify:
  {Outline.classify("def f():") == Outline.LDef{} : Outline.Cls}

# LAW: deep in a case
law bind_names_case:
  {bind_names(9) == "g b a y r f A x" : String}

# LAW: the next case sees none of the first
law bind_names_next:
  {bind_names(11) == "s f A x" : String}

# LAW: do-binds and typed lets
law bind_names_do:
  {bind_names(18) == "n n name" : String}

# LAW: a law's for
law bind_names_for:
  {bind_names(22) == "x" : String}

# LAW: a header over three lines
law bind_names_header:
  {bind_names(27) == "second first" : String}

# LAW: a parameter
law bind_at_param:
  {bind_at(3, 10) == "bind 3:10 param | +x: Shape" : String}

# LAW: a parameter's use
law bind_at_use:
  {bind_at(4, 8) == "use x -> local 3:10" : String}

# LAW: a template parameter's arrow type
law bind_at_tele:
  {bind_at(3, 31) == "bind 3:31 param | ~f: U32 -> U32" : String}

# LAW: a case binder
law bind_at_case:
  {bind_at(5, 17) == "bind 5:17 pat | case Circle{+r}:" : String}

# LAW: a destructured let
law bind_at_let:
  {bind_at(7, 12) == "bind 7:12 pat | (a, K{b}) = pair(y)" : String}

# LAW: a constructor in a pattern is a use
law bind_at_ctor:
  {bind_at(7, 10) == "use K -> free" : String}

# LAW: a lambda's binder
law bind_at_lam:
  {bind_at(8, 16) == "use z -> local 8:10" : String}

# LAW: a do-bind
law bind_at_do:
  {bind_at(15, 4) == "bind 15:4 local | name : String <- IO.get_env(\"USER\")" : String}

# LAW: a rebinding reads the old name
law bind_at_rebind:
  {bind_at(17, 17) == "use n -> local 16:4" : String}

# LAW: a name through an alias
law bind_at_alias:
  {bind_at(17, 8) == "use Lex.step -> qual Lex step" : String}

# LAW: a Base name is free
law bind_at_free:
  {bind_at(18, 4) == "use IO.print -> free" : String}

# LAW: an item of the file
law bind_at_item:
  {bind_at(27, 2) == "use area -> item area" : String}

# LAW: a later parameter with type arguments
law bind_at_later:
  {bind_at(25, 14) == "bind 25:14 param | second: List<&2, U32>" : String}

# LAW: a field
law bind_at_field:
  {bind_at(30, 20) == "bind 30:20 field | join: @+p: U32 -> @+q: U32 -> U32" : String}

# LAW: a type variable
law bind_at_typevar:
  {bind_at(30, 28) ==
    "bind 30:28 typevar | Monoid{unit: U32, join: @+p:U32 -> @+q:U32 -> U32}" : String}

# LAW: nothing at a keyword
law bind_at_kw:
  {bind_at(4, 2) == "-" : String}

# LAW: every site of a local
law bind_sites_local:
  {bind_sites(7, 12) == "7:12 9:8" : String}

# LAW: every site of an item
law bind_item_area:
  {bind_item_sites("area") == "3:4 27:2" : String}

# LAW: a constructor line
law bind_at_ctor_line:
  {bind_at(30, 2) ==
    "bind 30:2 ctor | Monoid{unit: U32, join: @+p:U32 -> @+q:U32 -> U32}" : String}

# LAW: head_of of a dotted name
law bind_head_of:
  {Bind.head_of(String.to_list("Lex.step")) == "Lex" : String}

# LAW: rest_of of a dotted name
law bind_rest_of:
  {Bind.rest_of(String.to_list("Lex.step")) == "step" : String}

# LAW: has of a name
law bind_has:
  {Bind.has(["a", "b"], "a") == True{} : Bool}

# LAW: spaced of ->
law bind_spaced:
  {Bind.spaced("->") == " -> " : String}

# LAW: named_sites of area
law bind_named_sites:
  {List.length(&2, Bind.Pos, Bind.named_sites(Bind.bound(bind_src()), "area")) == 1n : Nat}

# LAW: of_tree of a parse
law bind_of_tree:
  {List.length(&2, Bind.Bind, Bind.visible(Bind.of_tree(Tree.parse(bind_src()),
    String.lines(bind_src())), 3)) == 3n : Nat}
