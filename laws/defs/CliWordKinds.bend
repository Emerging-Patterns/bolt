# loose and plain command-line words for argv parsing
import Base
import ../../src/args.bend as Args

# The command line. shake parses argv against bolt's spec, and
# what it answers for a given argv is shake's guarantee, proved in shake's
# own gate at the pinned version (v0.6.0, where no row is pending): bolt
# cites those rows, trusts only that gate and SHAKE-TRUST-2 (trusted in src/args.bend),
# and never unfolds shake's parser or re-proves its walker, reading it only
# through its interface. Args.out
# decides what the parse does, and main only does it (trusted in src/lint.bend): a Stop
# prints its text to its stream and exits with its code, and a Go runs its
# subcommand over the files, which then exits as that command decides
# (laws/OutputSummaryAndExitStatus.bend for lint).
#
# The laws come in two kinds. Those over every parse result
# (cli_error_exits, cli_help_exits, cli_version_exits, cli_runs, cli_files)
# are about bolt's code alone. Those naming an argv (cli_bare to cli_version)
# take what shake answers for it as premises, each premise citing the shake
# row that guarantees it, and prove what bolt does with that answer. An argv
# here is the list IO.args hands the program: a compiled binary's runtime has
# already taken its own flags and the first `--` out of the command line, so
# at a shell `bolt -- -- -x.bend` is what reaches shake as `-- -x.bend`
# (SHAKE-TRUST-2).

# a word bolt reads as a file after a command: neither `--` nor `help`, and
# not starting with `-` (a flag)
def plain_word(+w: String) -> Bool:
  Bool.not(Bool.or(String.eq(w, "--"), Bool.or(String.eq(w, "help"), String.starts_with(w, "-"))))

# a word bolt reads as a file with no command before it: a plain word that
# names no subcommand
def loose_word(+w: String) -> Bool:
  Bool.and(plain_word(w),
    Bool.not(Bool.or(String.eq("lint", w), Bool.or(String.eq("check", w), String.eq("lsp", w)))))

# whether every word is loose
def all_loose(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+w, rest}:
      Bool.and(loose_word(w), all_loose(rest))
