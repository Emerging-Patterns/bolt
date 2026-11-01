# A file's own role (src/role.bend's own): a LAWS.bend or a PROOF.bend
# keeps its role by name; any other package's main.bend is code whatever it
# holds; any other file that fills a law (a def that is a proof) is a proof
# file, one that states a law and fills none a law file, and one that does
# neither is code. So a guarantee kept one per file under laws/ and proofs/
# is read as laws and proofs with no LAWS.bend or PROOF.bend in the run, and
# a run over files named on the line, which takes each file's own role with
# no import walk (laws/defs/GradedFindingCounts.bend's on_run), never takes
# the code a law imports for a law.
import Base
import ../src/role.bend as Role

# LAW: a LAWS.bend or a PROOF.bend keeps its role by name
law own_named:
  for +named: Role.Role
  for entry: Bool
  for fills: Bool
  for states: Bool
  for e: {Role.is_law_file(named) == True{} : Bool}
  {Role.own.of(named, entry, fills, states) == named : Role.Role}

# LAW: any other main.bend is code, whatever it holds
law own_entry:
  for +named: Role.Role
  for fills: Bool
  for states: Bool
  for e: {Role.is_law_file(named) == False{} : Bool}
  {Role.own.of(named, True{}, fills, states) == Role.Plain{} : Role.Role}

# LAW: any other file that fills a law is a proof file
law own_fills:
  for +named: Role.Role
  for states: Bool
  for e: {Role.is_law_file(named) == False{} : Bool}
  {Role.own.of(named, False{}, True{}, states) == Role.Proof{} : Role.Role}

# LAW: any other file that states a law and fills none is a law file, and
# one that does neither is code
law own_states:
  for +named: Role.Role
  for states: Bool
  for e: {Role.is_law_file(named) == False{} : Bool}
  {Role.own.of(named, False{}, False{}, states) == Bool.pick(Role.Role, states, Role.Laws{}, Role.Plain{})
    : Role.Role}
