# proofs of laws/RoleOwn.bend
import Base
import ../src/role.bend as Role
import ../laws/RoleOwn.bend as Laws

def Laws.own_named(named, entry, fills, states, e):
  s = Equal.sym(Bool, Role.is_law_file(named), True{}, e)
  %s : {Bool.pick(Role.Role, _, named,
      Bool.pick(Role.Role, entry, Role.Plain{}, Bool.pick(Role.Role, fills, Role.Proof{},
        Bool.pick(Role.Role, states, Role.Laws{}, Role.Plain{}))))
    == named : Role.Role}
  {==}

def Laws.own_entry(named, fills, states, e):
  s = Equal.sym(Bool, Role.is_law_file(named), False{}, e)
  %s : {Bool.pick(Role.Role, _, named,
      Bool.pick(Role.Role, True{}, Role.Plain{}, Bool.pick(Role.Role, fills, Role.Proof{},
        Bool.pick(Role.Role, states, Role.Laws{}, Role.Plain{}))))
    == Role.Plain{} : Role.Role}
  {==}

def Laws.own_fills(named, states, e):
  s = Equal.sym(Bool, Role.is_law_file(named), False{}, e)
  %s : {Bool.pick(Role.Role, _, named,
      Bool.pick(Role.Role, False{}, Role.Plain{}, Bool.pick(Role.Role, True{}, Role.Proof{},
        Bool.pick(Role.Role, states, Role.Laws{}, Role.Plain{}))))
    == Role.Proof{} : Role.Role}
  {==}

def Laws.own_states(named, states, e):
  s = Equal.sym(Bool, Role.is_law_file(named), False{}, e)
  %s : {Bool.pick(Role.Role, _, named,
      Bool.pick(Role.Role, False{}, Role.Plain{}, Bool.pick(Role.Role, False{}, Role.Proof{},
        Bool.pick(Role.Role, states, Role.Laws{}, Role.Plain{}))))
    == Bool.pick(Role.Role, states, Role.Laws{}, Role.Plain{}) : Role.Role}
  {==}
