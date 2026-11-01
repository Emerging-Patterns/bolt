# part of: laws/CliAcceptsDocumentedForms.bend,
# laws/CliVersionPrintsRelease.bend
import Base
import ../src/args.bend as Args
import ../src/version.bend as Ver
import ../src/build_rev.bend as Rev
import 0xa383b26a5a0ef35663b3615d7aedf9e3/main.bend as Shake

# LAW: every argv that parses with `--version` set prints bolt, then the
# release and the commit, and exits 0, whatever else it names
law cli_version_exits:
  for +av: List<&2, String>
  for +mm: Shake.Matched
  for h: {Args.parse(av) == Done{mm} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_ver: {Shake.on(mm, "version") == True{} : Bool}
  {Args.out(Args.parse(av))
    == Args.Stop{Args.Line{}, "bolt " ++ Args.version.at(Ver.text(), Rev.text()), 0} : Args.Out}
