# lsp/lint: the linter's warnings ride with the checker's errors, and follow
# the text as it is edited (the checker's errors stay until the next save)
import Base
import ../server.bend as Server
import ../transport/script.bend as Script
import ../checker/fake.bend as FakeChecker
import ../files/disk.bend as Disk

def opened() -> String:
  "import Base\\n\\ndef f(x: U32) -> U32:\\n  y = 1\\n  x\\n"

def edited() -> String:
  "import Base\\n\\n# the identity\\ndef f(x: U32) -> U32:\\n  x\\n"

def change(text: String) -> String:
  "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/bad.bend\"},\"contentChanges\":[{\"text\":\"" ++ text ++ "\"}]}}"

def inbox() -> List<&2, String>:
  ["{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/bad.bend\",\"text\":\"" ++ opened() ++ "\"}}}",
   change(edited()),
   "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didSave\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/bad.bend\"}}}"]

def main() -> IO(Unit):
  Server.serve(~Script.Script, ~Script.new(), ~FakeChecker.new(), ~Disk.new(), 100n, Script.Script{inbox()}, [])
#|{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///w/bad.bend","diagnostics":[{"range":{"start":{"line":3,"character":0},"end":{"line":4,"character":0}},"severity":1,"source":"bend","message":"expected : String\nobserved : U32"},{"range":{"start":{"line":2,"character":0},"end":{"line":3,"character":0}},"severity":2,"code":"doc","source":"bolt","message":"def f has no comment above it"},{"range":{"start":{"line":3,"character":2},"end":{"line":3,"character":3}},"severity":2,"code":"unused","source":"bolt","message":"local y is never used"}]}}
#|{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///w/bad.bend","diagnostics":[{"range":{"start":{"line":3,"character":0},"end":{"line":4,"character":0}},"severity":1,"source":"bend","message":"expected : String\nobserved : U32"}]}}
#|{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///w/bad.bend","diagnostics":[{"range":{"start":{"line":3,"character":0},"end":{"line":4,"character":0}},"severity":1,"source":"bend","message":"expected : String\nobserved : U32"}]}}
