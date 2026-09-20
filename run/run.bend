# run/run: the one effect the end-to-end tests have -- a program run with its
# arguments. An effect, not pure: it forks and waits, so it belongs to the CPU
# event loop and may never sit under a `!` call.
#
# bolt's own code runs no program but the checker (bolt/lsp/checker/exec.*).
# This is for the tests above bolt rather than inside it, the ones that have to
# drive the real `bend`, the real `node` and the real `nix` because no fake can
# answer what they ask.
import Base

# the program and its arguments, newline separated, execvp'd with no shell
# between them, so no argument can ever be read as shell syntax. The answer is
# the exit status on its own first line, then stdout and stderr together.
def bootrun.exec(cmd: String) -> IO(String):
  import "./exec.c"
  import "./exec.js"

# the arguments as the effect wants them
def line(args: List<&2, String>) -> String:
  String.join(args, "\n")

# a program run with its arguments
def exec(args: List<&2, String>) -> IO(String):
  bootrun.exec(line(args))

# the first line of an answer, which is the exit status. A missing answer is a
# program that could not be started at all.
def code.of(ls: List<&2, String>) -> String:
  match ls:
    case []:
      "127"
    case h <> t:
      h

# the exit status a run answered with
def code(out: String) -> String:
  code.of(String.lines(out))

# everything after the first line, which is what the program printed
def text.of(ls: List<&2, String>) -> String:
  match ls:
    case []:
      ""
    case h <> t:
      String.join(t, "\n")

# what the program printed, stdout and stderr together, without the blank line
# the last newline leaves behind
def text(out: String) -> String:
  String.trim(text.of(String.lines(out)))
