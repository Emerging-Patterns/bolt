import Base
import ../src/args.bend as Args
import 0xa383b26a5a0ef35663b3615d7aedf9e3/main.bend as Shake

# LAW: a line that asks for `--help` prints the usage of the command path it
# asks about to stdout and exits 0, the page `bolt help` prints for that
# path. shake's answer, the premise: `help` followed by that path fails the
# parse as a request for usage of it (SHAKE-PARSE-8, SHAKE-ERR-1)
law cli_dash_help:
  for +ws: List<&2, String>
  for +ee: Shake.ParseErr
  for h: {Args.asks_help(ws) == True{} : Bool}
  for hp: {Args.parse("help" <> Args.help_path(ws)) == Fail{ee} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hh: {Shake.help_path(ee) == Some{Args.help_path(ws)} : Maybe<&2, List<&2, String>>}
  {Args.out(Args.parse(Args.line(ws))) == Args.Stop{Args.Page{}, Args.help_text(Args.help_path(ws)), 0} : Args.Out}
