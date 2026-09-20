# bolt/cli: the command line as the runtime hands it over — which word is the
# subcommand and which are files — and the glob behind a bare `bolt`, over a
# canned tree (walk/fake.bend). The words are passed in rather than read: a
# test that reads its own command line cannot share a binary with another.
import Base
import ../args.bend as Args
import ../glob.bend as Glob
import ../walk/fake.bend as FakeWalk
import ../../core/check/kit.bend as Check
import ../../core/check/print.bend as Report

def joined(ps: List<&2, String>) -> String:
  String.join(ps, " ")

def split(+av: List<&2, String>) -> String:
  "[" ++ Args.command(av) ++ "] " ++ joined(Args.files(av))

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str(~Report.new(), "args: a bare bolt is lint over no files", split([]), "[] ")
    Check.eq_str(~Report.new(), "args: a leading subcommand is the command, the rest files",
      split(["lint", "a.bend", "b.bend"]), "[lint] a.bend b.bend")
    Check.eq_str(~Report.new(), "args: check and lsp too", split(["check", "a.bend"]) ++ split(["lsp"]),
      "[check] a.bend[lsp] ")
    Check.eq_str(~Report.new(), "args: a first word that is no subcommand is a file",
      split(["a.bend", "b.bend"]), "[] a.bend b.bend")
    files : List<&2, String> <- Glob.find(~FakeWalk.new(), ".")
    Check.eq_str(~Report.new(), "glob: every .bend under a directory, sorted, hidden and node_modules skipped",
      joined(files), "./b.bend ./bolt/a.bend ./bolt/lsp/run.bend")

#|ok args: a bare bolt is lint over no files
#|ok args: a leading subcommand is the command, the rest files
#|ok args: check and lsp too
#|ok args: a first word that is no subcommand is a file
#|ok glob: every .bend under a directory, sorted, hidden and node_modules skipped
