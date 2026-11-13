# The semantic tokens the server sends follow LSP 3.17's encoding and the
# legend the server announced. A token is five numbers: its line, relative
# to the token before it; its start column, relative to that token's when
# the two share a line and absolute on a new line; its length; the index of
# its type in the legend; and its modifiers, of which bolt sends none. A
# name's type is the legend entry its binder's kind stands for (an item is a
# type when capitalized, else a function; a constructor an enumMember; a
# parameter a parameter; a let, a pattern or a `for` name a variable; a field
# a property; a type parameter or a type-level name a typeParameter), and a
# name bound nowhere in the file is read by its shape (capitalized: an
# enumMember before a `{`, else a type; dotted: a function; else a variable).
# The editor colors by the entry's name, so an index that named another
# entry would color the token as that. Proved here: the five numbers of each
# token, and the legend entry of each kind and each shape. Not stated here:
# which binder or use a token is matched to as the tokens are walked.
import Base
import ../src/syntax/bind.bend as Bind
import ../src/lsp/semantic.bend as Semantic

# the legend's entry at an index, as the editor looks a token's type up. Law
# vocabulary: bolt never calls it
def semantic.entry(ii: U32) -> Maybe<&2, String>:
  List.get(&2, String, Semantic.legend(), U32.to_nat(ii))

# the legend entry a binder's kind stands for; upper: its name is
# capitalized. Law vocabulary
def semantic.kind_name(kk: Bind.BindKind, upper: Bool) -> String:
  match kk:
    case Bind.KItem{}:
      Bool.pick(String, upper, "type", "function")
    case Bind.KCtor{}:
      "enumMember"
    case Bind.KParam{}:
      "parameter"
    case Bind.KLocal{}:
      "variable"
    case Bind.KPat{}:
      "variable"
    case Bind.KFor{}:
      "variable"
    case Bind.KField{}:
      "property"
    case Bind.KTypeParam{}:
      "typeParameter"
    case Bind.KTypeVar{}:
      "typeParameter"

# the legend entry a name bound nowhere in the file gets by its shape;
# upper: its last segment is capitalized, braced: a `{` follows it, dotted:
# it holds a dot. Law vocabulary
def semantic.shape_name(upper: Bool, braced: Bool, dotted: Bool) -> String:
  match upper:
    case True{}:
      Bool.pick(String, braced, "enumMember", "type")
    case False{}:
      Bool.pick(String, dotted, "function", "variable")

# LAW: a token on the line of the one before it is sent with a line delta,
# its column relative to that token's, its length, its type and no modifier,
# and the next token is relative to it
law token_on_the_same_line:
  for +line: U32
  for +col: U32
  for len: U32
  for typ: U32
  for +rest: List<&2, Semantic.Sem>
  for +pl: U32
  for +pc: U32
  for e: {U32.is_eq(line, pl) == True{} : Bool}
  {Semantic.encode(Semantic.Sem{line, col, len, typ} <> rest, pl, pc)
    == (line - pl : U32) <> ((col - pc : U32) <> (len <> (typ <> (0 <> Semantic.encode(rest, line, col)))))
    : List<&2, U32>}

# LAW: a token on a new line is sent with its column as it is
law token_on_a_new_line:
  for +line: U32
  for +col: U32
  for len: U32
  for typ: U32
  for +rest: List<&2, Semantic.Sem>
  for +pl: U32
  for +pc: U32
  for e: {U32.is_eq(line, pl) == False{} : Bool}
  {Semantic.encode(Semantic.Sem{line, col, len, typ} <> rest, pl, pc)
    == (line - pl : U32) <> (col <> (len <> (typ <> (0 <> Semantic.encode(rest, line, col))))) : List<&2, U32>}

# LAW: the type index of a binder's kind names the legend entry that kind
# stands for, whatever the name
law kind_names_its_legend_entry:
  for kk: Bind.BindKind
  for +name: String
  {semantic.entry(Semantic.of_kind(kk, name))
    == Some{semantic.kind_name(kk, Semantic.upper_first(String.to_list(name)))} : Maybe<&2, String>}

# LAW: the type index of a name bound nowhere in the file names the legend
# entry its shape stands for
law shape_names_its_legend_entry:
  for +name: String
  for +braced: Bool
  {semantic.entry(Semantic.by_shape(name, braced))
    == Some{semantic.shape_name(Semantic.upper_first(Semantic.last_segment(String.to_list(name), [])), braced,
      String.contains(name, "."))} : Maybe<&2, String>}
