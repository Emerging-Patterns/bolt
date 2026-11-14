# the version form of the command line exits
import Base
import ../../src/args.bend as Args
import ../../src/version.bend as Ver
import ../../src/build_rev.bend as Rev
import shake@0.6.0.0/main.bend as Shake
import ../../laws/CliVersionExits.bend as L1

def L1.cli_version_exits(av, m, h, h_ver):
  e = Equal.sym(Result<&2, &2, Shake.ParseErr, Shake.Matched>, Args.parse(av), Done{m}, h)
  %e : {Args.out(_)
    == Args.Stop{Args.Line{}, "bolt " ++ Args.version.at(Ver.text(), Rev.text()), 0} : Args.Out}
  v = Equal.sym(Bool, Shake.on(m, "version"), True{}, h_ver)
  %v : {Args.out.run(_, m)
    == Args.Stop{Args.Line{}, "bolt " ++ Args.version.at(Ver.text(), Rev.text()), 0} : Args.Out}
  {==}
