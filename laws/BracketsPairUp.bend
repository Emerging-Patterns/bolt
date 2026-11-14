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
def lex.opens(b: B.Bracket) -> Lex.Class:
  match b:
    case B.BAngle{}:
      Lex.COp{}
    case other:
      Lex.COpen{}

# the lexer's class of a bracket's closing char
def lex.closes(b: B.Bracket) -> Lex.Class:
  match b:
    case B.BAngle{}:
      Lex.COp{}
    case other:
      Lex.CClose{}

# the depth wrap raises at a bracket's opening text
def wrap.raises(b: B.Bracket) -> Wrap.Act:
  match b:
    case B.BParen{}:
      Wrap.AParen{}
    case B.BSquare{}:
      Wrap.ABrack{}
    case B.BBrace{}:
      Wrap.ABrace{}
    case B.BAngle{}:
      Wrap.ANone{}

# the depth wrap lowers at a bracket's closing text
def wrap.lowers(b: B.Bracket) -> Wrap.Act:
  match b:
    case B.BParen{}:
      Wrap.AUnparen{}
    case B.BSquare{}:
      Wrap.AUnbrack{}
    case B.BBrace{}:
      Wrap.AUnbrace{}
    case B.BAngle{}:
      Wrap.ANone{}

# what a telescope's names bind as, by its bracket
def bind.tele(b: B.Bracket) -> Bind.BindKind:
  match b:
    case B.BParen{}:
      Bind.KParam{}
    case B.BAngle{}:
      Bind.KTypeParam{}
    case other:
      Bind.KField{}

# arms' part for a bracket's opening text
def arms.opener(b: B.Bracket) -> Arms.Part:
  match b:
    case B.BAngle{}:
      Arms.PBad{}
    case other:
      Arms.POpen{B.br.open(b)}

# the callee's name when the call's bracket is round, else nothing
def callee.name(b: B.Bracket) -> String:
  Bool.pick(String, B.br.is_paren(b), "f", "")

# the callee when the call's bracket is round, else none
def callee.tok(b: B.Bracket) -> Maybe<&2, Lex.Tok>:
  Bool.pick(Maybe<&2, Lex.Tok>, B.br.is_paren(b), Some{B.br.callee()}, None{})

# LAW: the lexer classes a bracket's opening char
law lex_classes_opener:
  for b: B.Bracket
  {Lex.classify(B.br.open_char(b)) == lex.opens(b) : Lex.Class}

# LAW: the lexer classes a bracket's closing char
law lex_classes_closer:
  for b: B.Bracket
  {Lex.classify(B.br.close_char(b)) == lex.closes(b) : Lex.Class}

# LAW: the tree closes each opener with its own closer
law tree_closer_pairs:
  for b: B.Bracket
  {Tree.closer(B.br.open(b)) == B.br.close(b) : String}

# LAW: wrap raises the depth of a bracket's own kind at its opening text
law wrap_open_raises:
  for b: B.Bracket
  {Wrap.check.open_text(B.br.open(b)) == wrap.raises(b) : Wrap.Act}

# LAW: wrap lowers the depth of a bracket's own kind at its closing text
law wrap_close_lowers:
  for b: B.Bracket
  {Wrap.check.close_text(B.br.close(b)) == wrap.lowers(b) : Wrap.Act}

# LAW: wrap's `(` is an opener token whose text is the round bracket's
law wrap_oparen_is_round:
  for b: B.Bracket
  {Wrap.check.is_oparen(Lex.TOpen{}, B.br.open(b)) == B.br.is_paren(b) : Bool}

# LAW: wrap's `)` is a closer token whose text is the round bracket's
law wrap_cparen_is_round:
  for b: B.Bracket
  {Wrap.check.is_cparen(Lex.TClose{}, B.br.close(b)) == B.br.is_paren(b) : Bool}

# LAW: a telescope's names bind as its bracket says
law bind_tele_kind_by_bracket:
  for b: B.Bracket
  {Bind.tele_kind(B.br.open(b)) == bind.tele(b) : Bind.BindKind}

# LAW: arms reads every opener but an angle bracket
law arms_part_open_by_bracket:
  for b: B.Bracket
  {Arms.part.open(B.br.open(b)) == arms.opener(b) : Arms.Part}

# LAW: table reads a callee's name only through a round bracket
law table_call_name_round:
  for b: B.Bracket
  {Table.call_name(B.br.call(b)) == callee.name(b) : String}

# LAW: rewalk reads a callee only through a round bracket
law rewalk_as_call_round:
  for b: B.Bracket
  {Rewalk.as_call(B.br.call(b)) == callee.tok(b) : Maybe<&2, Lex.Tok>}

# LAW: rewalk looks through one pair of round brackets around a call, and no other
law rewalk_as_call_wrapped_round:
  for b: B.Bracket
  {Rewalk.as_call(B.br.wrapped(b)) == callee.tok(b) : Maybe<&2, Lex.Tok>}

# LAW: inside round brackets, rewalk reads a callee only through a round bracket
law rewalk_as_call_inside_round:
  for b: B.Bracket
  {Rewalk.as_call(B.br.inside(b)) == callee.tok(b) : Maybe<&2, Lex.Tok>}
