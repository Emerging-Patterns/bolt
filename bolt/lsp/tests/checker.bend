# lsp/checker/bend: the real checker behind the server (run from the repo
# root, as the gate does). The second file's main prints; a checker that ran
# it would leak that line into the output below. A LAWS.bend alone always has
# open laws: they are an error only while the PROOF.bend beside it does not
# check clean, and `unproven/` has none at all, which is the same verdict.
# A fixture holding an *incomplete* PROOF.bend cannot live in this tree: the
# gate checks every PROOF.bend it finds, and that one is meant to fail.
import Base
import ../server.bend as Server
import ../transport/script.bend as Script
import ../files/disk.bend as Disk
import ../checker/bend.bend as BendChecker

def inbox() -> List<&2, String>:
  ["{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file://bolt/lsp/fixtures/mistyped.bend\"}}}",
   "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didSave\",\"params\":{\"textDocument\":{\"uri\":\"file://bolt/lsp/fixtures/effectful.bend\"}}}",
   "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file://bolt/lsp/fixtures/proven/LAWS.bend\"}}}",
   "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file://bolt/lsp/fixtures/unproven/LAWS.bend\"}}}"]

def main() -> IO(Unit):
  Server.serve(~Script.Script, ~Script.new(), ~BendChecker.new(), ~Disk.new(), 100n, Script.Script{inbox()}, [])

#|{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://bolt/lsp/fixtures/mistyped.bend","diagnostics":[{"range":{"start":{"line":4,"character":0},"end":{"line":5,"character":0}},"severity":1,"source":"bend","message":"expected : String\nobserved : U32\nContext:\nxx : U32"}]}}
#|{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://bolt/lsp/fixtures/effectful.bend","diagnostics":[]}}
#|{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://bolt/lsp/fixtures/proven/LAWS.bend","diagnostics":[]}}
#|{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://bolt/lsp/fixtures/unproven/LAWS.bend","diagnostics":[{"range":{"start":{"line":0,"character":0},"end":{"line":1,"character":0}},"severity":1,"source":"bend","message":"1 TODO found.\nThe code is incomplete, and not a valid proof yet."}]}}
