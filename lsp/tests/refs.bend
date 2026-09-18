# lsp/refs: references, rename and semantic tokens in a session over a
# document. 1 and 2 are on a parameter (its uses, then renamed); 3 is on an
# item of the file, 4 on a constructor of it, 5 on a Base name (found, but
# not renamable: 6 is refused); 7 is the whole document classified.
import Base
import ../server.bend as Server
import ../transport/script.bend as Script
import ../checker/fake.bend as FakeChecker
import ../files/service.bend as F

def text() -> String:
  "import Base\\n\\ntype Shape is Data:\\n  Circle{r: U32}\\n\\n# the area\\ndef area(+x: U32) -> U32:\\n  match x:\\n    case Circle{r}:\\n      (x * r : U32)\\n\\ndef main() -> U32:\\n  area(Circle{2})\\n"

def fake.read(_path: String) -> IO(Maybe<&2, String>):
  IO.pure(Maybe<&2, String>, None{})

def fake.base_path(_u: Unit) -> IO(String):
  IO.pure(String, "/base.bend")

def fake() -> F.Files:
  F.Files{fake.read, fake.base_path}

def ask(id: String, method: String, line: String, col: String, extra: String) -> String:
  "{\"jsonrpc\":\"2.0\",\"id\":" ++ id ++ ",\"method\":\"textDocument/" ++ method ++ "\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/a.bend\"},\"position\":{\"line\":" ++ line ++ ",\"character\":" ++ col ++ "}" ++ extra ++ "}}"

def inbox() -> List<&2, String>:
  ["{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/a.bend\",\"text\":\"" ++ text() ++ "\"}}}",
   ask("1", "references", "7", "8", ",\"context\":{\"includeDeclaration\":true}"),
   ask("2", "rename", "9", "7", ",\"newName\":\"shape\""),
   ask("3", "references", "12", "3", ""),
   ask("4", "references", "3", "3", ""),
   ask("5", "references", "0", "2", ""),
   ask("6", "rename", "6", "20", ",\"newName\":\"Word\""),
   "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"textDocument/semanticTokens/full\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/a.bend\"}}}"]

def main() -> IO(Unit):
  Server.serve(~Script.Script, ~Script.new(), ~FakeChecker.new(), ~fake(), 100n, Script.Script{inbox()}, [])

#|{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///w/a.bend","diagnostics":[{"range":{"start":{"line":2,"character":0},"end":{"line":3,"character":0}},"severity":2,"code":"doc","source":"bend-lint","message":"type Shape has no comment above it"}]}}
#|{"jsonrpc":"2.0","id":1,"result":[{"uri":"file:///w/a.bend","range":{"start":{"line":6,"character":10},"end":{"line":6,"character":11}}},{"uri":"file:///w/a.bend","range":{"start":{"line":7,"character":8},"end":{"line":7,"character":9}}},{"uri":"file:///w/a.bend","range":{"start":{"line":9,"character":7},"end":{"line":9,"character":8}}}]}
#|{"jsonrpc":"2.0","id":2,"result":{"changes":{"file:///w/a.bend":[{"range":{"start":{"line":6,"character":10},"end":{"line":6,"character":11}},"newText":"shape"},{"range":{"start":{"line":7,"character":8},"end":{"line":7,"character":9}},"newText":"shape"},{"range":{"start":{"line":9,"character":7},"end":{"line":9,"character":8}},"newText":"shape"}]}}}
#|{"jsonrpc":"2.0","id":3,"result":[{"uri":"file:///w/a.bend","range":{"start":{"line":6,"character":4},"end":{"line":6,"character":8}}},{"uri":"file:///w/a.bend","range":{"start":{"line":12,"character":2},"end":{"line":12,"character":6}}}]}
#|{"jsonrpc":"2.0","id":4,"result":[{"uri":"file:///w/a.bend","range":{"start":{"line":3,"character":2},"end":{"line":3,"character":8}}},{"uri":"file:///w/a.bend","range":{"start":{"line":8,"character":9},"end":{"line":8,"character":15}}},{"uri":"file:///w/a.bend","range":{"start":{"line":12,"character":7},"end":{"line":12,"character":13}}}]}
#|{"jsonrpc":"2.0","id":5,"result":[]}
#|{"jsonrpc":"2.0","id":6,"error":{"code":-32803,"message":"only a name bound in this file can be renamed"}}
#|{"jsonrpc":"2.0","id":7,"result":{"data":[0,0,6,0,0,0,7,4,2,0,2,0,4,0,0,0,5,5,2,0,0,6,2,0,0,0,3,4,0,0,1,2,6,3,0,0,7,1,6,0,0,3,3,2,0,3,0,3,0,0,0,4,4,1,0,0,6,1,4,0,0,3,3,2,0,0,8,3,2,0,1,2,5,0,0,0,6,1,4,0,1,4,4,0,0,0,5,6,3,0,0,7,1,5,0,1,7,1,4,0,0,4,1,5,0,0,4,3,2,0,2,0,3,0,0,0,4,4,1,0,0,10,3,2,0,1,2,4,1,0,0,5,6,3,0]}}
