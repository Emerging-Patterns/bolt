# the help form of the command line and its exit
import Base
import ../../src/args.bend as Args
import 0xa383b26a5a0ef35663b3615d7aedf9e3/main.bend as Shake
import ../../laws/CliAcceptsDocumentedForms.bend as L1

def L1.cli_help_exits(av, ee, ps, h, h_help):
  e = Equal.sym(Result<&2, &2, Shake.ParseErr, Shake.Matched>, Args.parse(av), Fail{ee}, h)
  %e : {Args.out(_) == Args.Stop{Args.Page{}, Args.help_text(ps), 0} : Args.Out}
  q = Equal.sym(Maybe<&2, List<&2, String>>, Shake.help_path(ee), Some{ps}, h_help)
  %q : {Args.out.fail.at(_, ee) == Args.Stop{Args.Page{}, Args.help_text(ps), 0} : Args.Out}
  {==}

def L1.cli_help(ps, ee, hp, hh):
  L1.cli_help_exits("help" <> ps, ee, ps, hp, hh)
