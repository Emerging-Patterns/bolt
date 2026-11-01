# proofs of laws/CliReadsArgumentsAfterProgram.bend
import Base
import ../src/lazy/lazy.bend as Lazy
import ../src/args.bend as Args
import ../laws/CliReadsArgumentsAfterProgram.bend as Laws

def Laws.cli_args_program(_prog, _ws):
  {==}

def Laws.cli_line_plain(ws, h):
  e = Equal.sym(Bool, Args.asks_help(ws), False{}, h)
  %e : {Args.line.at(_, ws) == ws : List<&2, String>}
  {==}

def Laws.cli_help_flag(_ws):
  {==}

def Laws.cli_help_dashes(_ws):
  {==}

def Laws.cli_help_flag_path(_ws):
  {==}

def Laws.cli_help_cmd(cc, ws, h_cmd, h_not):
  e = Equal.sym(Bool, String.eq(cc, "--help"), False{}, h_not)
  %e : {Lazy.either(List<&2, String>, _, _u => Args.help_path(ws),
    _u => Bool.pick(List<&2, String>, Args.is_cmd(cc), [cc], [])) == [cc] : List<&2, String>}
  c = Equal.sym(Bool, Args.is_cmd(cc), True{}, h_cmd)
  %c : {Bool.pick(List<&2, String>, _, [cc], []) == [cc] : List<&2, String>}
  {==}
