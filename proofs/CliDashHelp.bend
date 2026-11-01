# proofs of laws/CliDashHelp.bend
import Base
import ../src/args.bend as Args
import ../laws/CliAcceptsDocumentedForms.bend as L1
import ../laws/CliDashHelp.bend as Laws
import ./lemmas/CliHelpExit.bend as M1

def Laws.cli_dash_help(ws, ee, h, hp, hh):
  e = Equal.sym(Bool, Args.asks_help(ws), True{}, h)
  %e : {Args.out(Args.parse(Args.line.at(_, ws))) == Args.Stop{Args.Page{}, Args.help_text(Args.help_path(ws)), 0}
    : Args.Out}
  L1.cli_help(Args.help_path(ws), ee, hp, hh)
