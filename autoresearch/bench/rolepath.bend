# check: do Digest.of and Digest.of.role (told the path's role) agree on the exempt flag for `LAWS.bend/`?
import Base
import ../../src/src.bend as Src
import ../../src/role.bend as Role
import ../../src/rules/digest.bend as Digest

def exempt(dd: Digest.Digest) -> Bool:
  Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws} = dd
  exempt

def show(bb: Bool) -> String:
  Bool.pick(String, bb, "exempt", "graded")

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("of:      " ++ show(exempt(Digest.of(Src.of("LAWS.bend/", "")))))
    IO.print("of.role: " ++ show(exempt(Digest.of.role(Role.of_path("LAWS.bend/"), Src.of("LAWS.bend/", "")))))
