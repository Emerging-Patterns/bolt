# checker/argv: the runs of bend the real checker makes, as data. Pure: the
# effect (bend.bend) only performs them, so LAWS.bend states over every path
# and every first report that each run carries `--check-only`, the flag that
# makes bend check the file and never run its main (BOLT-LSP-5; that bend
# honours it is BOLT-TRUST-5).
import Base
import ../../paths.bend as Paths
import ../report.bend as Rep

# a run of bend: the file it is given and the flag after it
type Run is Data:
  Run{path: String, flag: String}

# the flag of a run
def flag(rr: Run) -> String:
  Run{path, ff} = rr
  ff

# the run that checks a file: `bend <path> --check-only`
def run_of(path: String) -> Run:
  Run{path, "--check-only"}

# only the open-laws report ("N TODOs found"), and nothing else
def only_todos(ds: List<&2, Rep.Diag>) -> Bool:
  match ds:
    case Con{Rep.Diag{line, msg}, Nil{}}:
      String.contains(msg, "TODO found")
    case other:
      False{}

# the PROOF.bend beside a LAWS.bend
def proof_path(+path: String) -> String:
  String.take(path, Nat.sub(String.length(path), 9n)) ++ "PROOF.bend"

# By convention LAWS.bend states its laws as open claims and PROOF.bend, beside
# it, fills them: alone, LAWS.bend always has TODOs. They are an error only
# while PROOF.bend does not check clean, so a first report that is only the
# open laws of a LAWS.bend is followed by a run on that PROOF.bend
def followup(+ds: List<&2, Rep.Diag>, +path: String) -> Maybe<&2, Run>:
  Bool.pick(Maybe<&2, Run>, Bool.and(only_todos(ds), Paths.is_laws(path)), Some{run_of(proof_path(path))}, None{})
