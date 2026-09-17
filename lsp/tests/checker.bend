# lsp/checker/bend: the real checker behind the server (run from the repo
# root, as the gate does). The second file's main prints; a checker that ran
# it would leak that line into the output below.
import Base
import ../server.bend as Server
import ../transport/script.bend as Script
import ../files/disk.bend as Disk
import ../checker/bend.bend as BendChecker

def inbox() -> List<&2, String>:
  ["{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file://lsp/tests/fixtures/mistyped.bend\"}}}",
   "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didSave\",\"params\":{\"textDocument\":{\"uri\":\"file://lsp/tests/fixtures/effectful.bend\"}}}"]

def main() -> IO(Unit):
  Server.serve(~Script.Script, ~Script.new(), ~BendChecker.new(), ~Disk.new(), 100n, Script.Script{inbox()}, [])

#|{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://lsp/tests/fixtures/mistyped.bend","diagnostics":[{"range":{"start":{"line":3,"character":0},"end":{"line":4,"character":0}},"severity":1,"source":"bend","message":"expected : String\nobserved : U32\nContext:\nx : U32"}]}}
#|{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://lsp/tests/fixtures/effectful.bend","diagnostics":[]}}
