import Base
import ../src/args.bend as Args
import ../src/version.bend as Ver
import ../src/build_rev.bend as Rev
import shake@0.6.0.0/main.bend as Shake
import ./defs/CliWordKinds.bend as D1

# LAW: `bolt --version` prints bolt, then the release and the commit, and
# exits 0, with or without files after it. shake's answer, the premises: the
# line parses and sets the root's `version` flag (SHAKE-TOK-1, SHAKE-GET-1)
law cli_version:
  for +fs: List<&2, String>
  for h: {D1.all_loose(fs) == True{} : Bool}
  for +m: Shake.Matched
  for hp: {Args.parse("--version" <> fs) == Done{m} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hv: {Shake.on(m, "version") == True{} : Bool}
  {Args.out(Args.parse("--version" <> fs))
    == Args.Stop{Args.Line{}, "bolt " ++ Args.version.at(Ver.text(), Rev.text()), 0} : Args.Out}
