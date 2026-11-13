# Bend has four brackets: `(..)`, `[..]`, `{..}` and `<..>`. The lexer, the
# tree, the binder and four rules each read a bracket off its text, and
# each keeps its own small table of which text is which bracket. The
# sweep of #310 found each of those tables could start answering yes to
# every text, or to the wrong one, without a proof failing. Here each is
# stated bracket by bracket:
#
# - the lexer classes `(`, `[` and `{` as openers, `)`, `]` and `}` as
#   closers, and `<` and `>` as operators (the tree, not the lexer, decides
#   when an angle bracket is one);
# - the tree closes each opener with its own closer;
# - `wrap` counts depth in round, square and curly brackets by their text,
#   and reads angle brackets elsewhere (an operator's `>`s);
# - the binder binds a telescope's names as parameters in `(..)`, as type
#   parameters in `<..>`, and as fields otherwise;
# - `arms` reads an opener among a pattern's parts except an angle bracket;
# - `table` and `rewalk` read a callee only through a round bracket: `f(..)`
#   is a call, `f[..]` and `f{..}` are not, and `rewalk` looks through one
#   pair of round brackets around a call and no other, and the call inside
#   them is read the same way.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/syntax/bind.bend as Bind
import ../src/rules/style/wrap.bend as Wrap
import ../src/rules/correctness/arms.bend as Arms
import ../src/rules/table.bend as Table
import ../src/rules/pedantic/rewalk.bend as Rewalk
import ./defs/Brackets.bend as B

# the lexer's class of a bracket's opening char
def lex.opens(bb: B.Bracket) -> Lex.Class:
  match bb:
    case B.BAngle{}:
      Lex.COp{}
    case other:
      Lex.COpen{}

# the lexer's class of a bracket's closing char
def lex.closes(bb: B.Bracket) -> Lex.Class:
  match bb:
    case B.BAngle{}:
      Lex.COp{}
    case other:
      Lex.CClose{}

# the depth wrap raises at a bracket's opening text
def wrap.raises(bb: B.Bracket) -> Wrap.Act:
  match bb:
    case B.BParen{}:
      Wrap.AParen{}
    case B.BSquare{}:
      Wrap.ABrack{}
    case B.BBrace{}:
      Wrap.ABrace{}
    case B.BAngle{}:
      Wrap.ANone{}

# the depth wrap lowers at a bracket's closing text
def wrap.lowers(bb: B.Bracket) -> Wrap.Act:
  match bb:
    case B.BParen{}:
      Wrap.AUnparen{}
    case B.BSquare{}:
      Wrap.AUnbrack{}
    case B.BBrace{}:
      Wrap.AUnbrace{}
    case B.BAngle{}:
      Wrap.ANone{}

# what a telescope's names bind as, by its bracket
def bind.tele(bb: B.Bracket) -> Bind.BindKind:
  match bb:
    case B.BParen{}:
      Bind.KParam{}
    case B.BAngle{}:
      Bind.KTypeParam{}
    case other:
      Bind.KField{}

# arms' part for a bracket's opening text
def arms.opener(bb: B.Bracket) -> Arms.Part:
  match bb:
    case B.BAngle{}:
      Arms.PBad{}
    case other:
      Arms.POpen{B.br.open(bb)}

# the callee's name when the call's bracket is round, else nothing
def callee.name(bb: B.Bracket) -> String:
  Bool.pick(String, B.br.is_paren(bb), "f", "")

# the callee when the call's bracket is round, else none
def callee.tok(bb: B.Bracket) -> Maybe<&2, Lex.Tok>:
  Bool.pick(Maybe<&2, Lex.Tok>, B.br.is_paren(bb), Some{B.br.callee()}, None{})

# LAW: the lexer classes a bracket's opening char
law lex_classes_opener:
  for bb: B.Bracket
  {Lex.classify(B.br.open_char(bb)) == lex.opens(bb) : Lex.Class}

# LAW: the lexer classes a bracket's closing char
law lex_classes_closer:
  for bb: B.Bracket
  {Lex.classify(B.br.close_char(bb)) == lex.closes(bb) : Lex.Class}

# LAW: the tree closes each opener with its own closer
law tree_closer_pairs:
  for bb: B.Bracket
  {Tree.closer(B.br.open(bb)) == B.br.close(bb) : String}

# LAW: wrap raises the depth of a bracket's own kind at its opening text
law wrap_open_raises:
  for bb: B.Bracket
  {Wrap.check.open_text(B.br.open(bb)) == wrap.raises(bb) : Wrap.Act}

# LAW: wrap lowers the depth of a bracket's own kind at its closing text
law wrap_close_lowers:
  for bb: B.Bracket
  {Wrap.check.close_text(B.br.close(bb)) == wrap.lowers(bb) : Wrap.Act}

# LAW: wrap's `(` is an opener token whose text is the round bracket's
law wrap_oparen_is_round:
  for bb: B.Bracket
  {Wrap.check.is_oparen(Lex.TOpen{}, B.br.open(bb)) == B.br.is_paren(bb) : Bool}

# LAW: wrap's `)` is a closer token whose text is the round bracket's
law wrap_cparen_is_round:
  for bb: B.Bracket
  {Wrap.check.is_cparen(Lex.TClose{}, B.br.close(bb)) == B.br.is_paren(bb) : Bool}

# LAW: a telescope's names bind as its bracket says
law bind_tele_kind_by_bracket:
  for bb: B.Bracket
  {Bind.tele_kind(B.br.open(bb)) == bind.tele(bb) : Bind.BindKind}

# LAW: arms reads every opener but an angle bracket
law arms_part_open_by_bracket:
  for bb: B.Bracket
  {Arms.part.open(B.br.open(bb)) == arms.opener(bb) : Arms.Part}

# LAW: table reads a callee's name only through a round bracket
law table_call_name_round:
  for bb: B.Bracket
  {Table.call_name(B.br.call(bb)) == callee.name(bb) : String}

# LAW: rewalk reads a callee only through a round bracket
law rewalk_as_call_round:
  for bb: B.Bracket
  {Rewalk.as_call(B.br.call(bb)) == callee.tok(bb) : Maybe<&2, Lex.Tok>}

# LAW: rewalk looks through one pair of round brackets around a call, and no other
law rewalk_as_call_wrapped_round:
  for bb: B.Bracket
  {Rewalk.as_call(B.br.wrapped(bb)) == callee.tok(bb) : Maybe<&2, Lex.Tok>}

# LAW: inside round brackets, rewalk reads a callee only through a round bracket
law rewalk_as_call_inside_round:
  for bb: B.Bracket
  {Rewalk.as_call(B.br.inside(bb)) == callee.tok(bb) : Maybe<&2, Lex.Tok>}
