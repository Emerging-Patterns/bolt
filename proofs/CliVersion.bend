# proofs of laws/CliVersion.bend
import Base
import ../laws/CliVersion.bend as Laws
import ../laws/CliVersionExits.bend as L1
import ./lemmas/CliVersionExit.bend as M1

def Laws.cli_version(fs, _h, m, hp, hv):
  L1.cli_version_exits("--version" <> fs, m, hp, hv)
