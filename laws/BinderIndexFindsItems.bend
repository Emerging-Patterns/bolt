# The binder's index of a file's items answers as its scan of them does: a
# name is in the index of some names exactly when the scan finds it among
# them (Bind.has_item, which laws/BinderResolvesInnermostFirst.bend's proof
# shows is List.contains). So the binder asks the index, which walks to one
# leaf, where it asked the list, which it walked whole for every use no
# binder holds.
import Base
import ../src/syntax/bind.bend as Bind

# LAW: the index of any names holds a name exactly when the scan of those
# names finds it
law index_finds:
  for +its: List<&2, String>
  for +name: String
  {Bind.indexed(Bind.index(its), name) == Bind.has_item(its, name) : Bool}
