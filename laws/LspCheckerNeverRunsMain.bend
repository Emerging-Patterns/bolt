# The checker never runs `main`.
import Base
import ../src/lsp/report.bend as Rep
import ../src/lsp/checker/argv.bend as Argv

# the checker
# -----------

# The checker's runs of bend are data (checker/argv.bend): the real checker
# runs `bend` on each with the run's path and flag and nothing else, and it
# makes a run of the file it is asked about, then at most the one followup
# gives. So every run carries `--check-only`, over every path and every first
# report. That bend checks and never runs `main` under that flag is
# trusted in src/lsp/report.bend.

# LAW: the run that checks a file, whatever its path, is `bend <path>
# --check-only`
law check_only:
  for +path: String
  {Argv.run_of(path) == Argv.Run{path, "--check-only"} : Argv.Run}

# LAW: the run that follows a first report, whatever the report and the
# path, is a `--check-only` run too
law followup_check_only:
  for +ds: List<&2, Rep.Diag>
  for +path: String
  for rr: Argv.Run
  for h: {Argv.followup(ds, path) == Some{rr} : Maybe<&2, Argv.Run>}
  {Argv.flag(rr) == "--check-only" : String}
