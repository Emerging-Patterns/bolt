# bolt reads the arguments after the program, which IO.args names first (bend
# 2.0.32). `--help` before the line's first `--` asks for the page `bolt help`
# prints, for the subcommand named first when there is one, else the root's;
# after `--` it is a file, and a line with no such `--help` is parsed as it
# is.
#
# also rests on: laws/CliDashHelp.bend
import Base
import ../src/args.bend as Args

# The line bolt parses (laws/CliReadsArgumentsAfterProgram.bend). IO.args gives the program as invoked
# first (bend 2.0.32), and bolt reads the words after it. A compiled binary
# passes `--help` to the program (bend 2.0.29): Args.line reads it, before
# the line's first `--`, as `help` for the command path it asks about, so it
# prints the page `bolt help` prints (cli_help); any other line is parsed as
# it is.

# LAW: bolt's arguments are the words after the program IO.args names first
law cli_args_program:
  for prog: String
  for ws: List<&1, String>
  {Args.args_of(prog <> ws) == Args.widen(ws) : List<&2, String>}

# LAW: a line with no `--help` before its first `--` is parsed as it is
law cli_line_plain:
  for +ws: List<&2, String>
  for h: {Args.asks_help(ws) == False{} : Bool}
  {Args.line(ws) == ws : List<&2, String>}

# LAW: a line that opens with `--help` asks for help
law cli_help_flag:
  for ws: List<&2, String>
  {Args.asks_help("--help" <> ws) == True{} : Bool}

# LAW: after `--`, `--help` is a file: the line is parsed as it is
law cli_help_dashes:
  for +ws: List<&2, String>
  {Args.line("--" <> ws) == "--" <> ws : List<&2, String>}

# LAW: `--help` is passed over in finding the command path it asks about
law cli_help_flag_path:
  for ws: List<&2, String>
  {Args.help_path("--help" <> ws) == Args.help_path(ws) : List<&2, String>}

# LAW: a line whose first word (other than `--help`) is a subcommand asks
# about that subcommand
law cli_help_cmd:
  for +cc: String
  for ws: List<&2, String>
  for h_cmd: {Args.is_cmd(cc) == True{} : Bool}
  for h_not: {String.eq(cc, "--help") == False{} : Bool}
  {Args.help_path(cc <> ws) == [cc] : List<&2, String>}
