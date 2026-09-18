# lanes: native
# syntax/lex on real files of this repo (run from its root): lossless on each
import Base
import ../lex.bend as Lex
import ../../lsp/files/service.bend as F
import ../../lsp/files/disk.bend as Disk
import ../../wire/check/kit.bend as Check
import ../../wire/check/print.bend as Report

# passes when the file was read and its tokens spell it back
def lossless.on(path: String, +text: String) -> IO(Unit):
  Check.eq_str(~Report.new(), path,
    Lex.text(Lex.tokens(text)) ++ Bool.pick(String, String.is_empty(text), "<unread>", ""), text)

def lossless(~fs: F.Files, +path: String) -> IO(Unit):
  do IO<Unit>:
    r : Maybe<&2, String> <- F.read(fs, path)
    lossless.on(path, Maybe.default(&2, String, r, ""))

def main() -> IO(Unit):
  do IO<Unit>:
    lossless(~Disk.new(), "lsp/server.bend")
    lossless(~Disk.new(), "syntax/outline.bend")
    lossless(~Disk.new(), "wire/PROOF.bend")
    lossless(~Disk.new(), "json/lex.bend")

#|ok lsp/server.bend
#|ok syntax/outline.bend
#|ok wire/PROOF.bend
#|ok json/lex.bend
