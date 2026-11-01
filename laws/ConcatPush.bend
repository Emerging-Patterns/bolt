import Base
import ../src/rules/suspicious/concat.bend as Concat

# LAW: a statement that binds nothing leaves the lets as they were
law concat_push:
  for lets: List<&2, Concat.Let>
  {Concat.push(None{}, lets) == lets : List<&2, Concat.Let>}
