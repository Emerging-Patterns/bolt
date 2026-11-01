import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/rules/suspicious/concat.bend as Concat

# LAW: a lone name is looked up in the lets, whatever they hold
law concat_via_name:
  for +t: String
  for l: U32
  for c: U32
  for +lets: List<&2, Concat.Let>
  {Concat.via(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, Tree.NNil{}}, lets) == Concat.find(lets, t)
    : Maybe<&2, Lex.Tok>}
