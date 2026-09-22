# lsp/levels: a finding's severity comes from the bolt.bend nearest the
# document (here lsp/fixtures/levels/bolt.bend, above the repo's): style is an
# error, suspicious is off; and a bolt.bend itself is never linted
import Base
import ../server.bend as Server
import ../transport/script.bend as Script
import ../checker/fake.bend as FakeChecker
import ../files/disk.bend as Disk

def opened() -> String:
  "import Base\\n\\n# f  \\ndef f(x: U32) -> U32:\\n  y = 1\\n  x\\n"

def open(uri: String, text: String) -> String:
  "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"" ++ uri ++ "\",\"text\":\"" ++ text ++ "\"}}}"

def inbox() -> List<&2, String>:
  [open("file://bolt/lsp/fixtures/levels/deep/a.bend", opened()),
   open("file://bolt/lsp/fixtures/levels/bolt.bend", opened())]

def main() -> IO(Unit):
  Server.serve(~Script.Script, ~Script.new(), ~FakeChecker.new(), ~Disk.new(), 100n, Script.Script{inbox()}, [])
#|{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://bolt/lsp/fixtures/levels/deep/a.bend","diagnostics":[{"range":{"start":{"line":2,"character":4},"end":{"line":2,"character":5}},"severity":1,"code":"S002","source":"bolt(style:space)","message":"Line has trailing whitespace."},{"range":{"start":{"line":3,"character":6},"end":{"line":3,"character":7}},"severity":1,"code":"S004","source":"bolt(style:param)","message":"Parameter x is shorter than 2 characters."}]}}
#|{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://bolt/lsp/fixtures/levels/bolt.bend","diagnostics":[]}}
