# lsp/server: a whole session over the script transport and the fake checker;
# the lines below are every body the server sent, in order
import Base
import ../server.bend as Server
import ../transport/script.bend as Script
import ../checker/fake.bend as FakeChecker

def inbox() -> List<&2, String>:
  ["{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{}}",
   "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}",
   "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/my%20bad.bend\",\"text\":\"x\"}}}",
   "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didSave\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/good.bend\"}}}",
   "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/hover\",\"params\":{}}",
   "not json at all",
   "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didClose\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/my%20bad.bend\"}}}",
   "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"shutdown\"}",
   "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}",
   "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"initialize\"}"]

def main() -> IO(Unit):
  Server.serve(~Script.Script, ~Script.new(), ~FakeChecker.new(), 100n, Script.Script{inbox()})

#|{"jsonrpc":"2.0","id":1,"result":{"capabilities":{"textDocumentSync":{"openClose":true,"change":0,"save":true}},"serverInfo":{"name":"bend-lsp"}}}
#|{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///w/my%20bad.bend","diagnostics":[{"range":{"start":{"line":3,"character":0},"end":{"line":4,"character":0}},"severity":1,"source":"bend","message":"expected : String\nobserved : U32"}]}}
#|{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///w/good.bend","diagnostics":[]}}
#|{"jsonrpc":"2.0","id":2,"error":{"code":-32601,"message":"method not found"}}
#|{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///w/my%20bad.bend","diagnostics":[]}}
#|{"jsonrpc":"2.0","id":3,"result":null}
