# lsp/nav: hover, definition and symbols in a session over fake files (9 and
# 10 are on a parameter's use: its declaration, and exactly its binder). The
# open document is never on the fake disk: it is read from the store, as the
# editor shows it, and its edit is what the last hover sees.
import Base
import ../server.bend as Server
import ../transport/script.bend as Script
import ../checker/fake.bend as FakeChecker
import ../files/service.bend as F

def math() -> String:
  "import Base\n\n# squares a number\ndef square(+x: U32) -> U32:\n  (x * x : U32)\n\ntype Shape is Data:\n  Circle{r: U32}\n"

def base() -> String:
  "# shows a number\ndef U32.show(n: U32) -> String:\n  \"\"\n"

def fake.at(+path: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.eq(path, "/w/lib/math.bend"), Some{math()},
    Bool.pick(Maybe<&2, String>, String.eq(path, "/base.bend"), Some{base()}, None{}))

def fake.read(path: String) -> IO(Maybe<&2, String>):
  IO.pure(Maybe<&2, String>, fake.at(path))

def fake.base_path(u: Unit) -> IO(String):
  IO.pure(String, "/base.bend")

def fake() -> F.Files:
  F.Files{fake.read, fake.base_path}

def main_text() -> String:
  "import Base\\nimport ../lib/math.bend as M\\n\\n# doubles\\ndef twice(x: U32) -> U32:\\n  M.square(x)\\n\\ndef main() -> String:\\n  U32.show(twice(M.Circle{2}))\\n"

def edited_text() -> String:
  "import Base\\n\\n# triples now\\ndef twice(x: U32) -> U32:\\n  x\\n\\ndef main() -> U32:\\n  twice(1)\\n"

def ask(id: String, method: String, line: String, col: String) -> String:
  "{\"jsonrpc\":\"2.0\",\"id\":" ++ id ++ ",\"method\":\"textDocument/" ++ method ++ "\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/app/main.bend\"},\"position\":{\"line\":" ++ line ++ ",\"character\":" ++ col ++ "}}}"

def inbox() -> List<&2, String>:
  ["{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/app/main.bend\",\"text\":\"" ++ main_text() ++ "\"}}}",
   ask("1", "hover", "5", "5"),
   ask("2", "definition", "5", "5"),
   ask("3", "hover", "8", "20"),
   ask("4", "hover", "8", "6"),
   ask("5", "definition", "8", "13"),
   ask("6", "hover", "4", "12"),
   ask("7", "documentSymbol", "0", "0"),
   ask("9", "hover", "5", "11"),
   ask("10", "definition", "5", "11"),
   "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/app/main.bend\"},\"contentChanges\":[{\"text\":\"" ++ edited_text() ++ "\"}]}}",
   ask("8", "hover", "7", "3")]

def main() -> IO(Unit):
  Server.serve(~Script.Script, ~Script.new(), ~FakeChecker.new(), ~fake(), 100n, Script.Script{inbox()}, [])

#|{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///w/app/main.bend","diagnostics":[]}}
#|{"jsonrpc":"2.0","id":1,"result":{"contents":{"kind":"markdown","value":"```bend\ndef square(+x: U32) -> U32:\n```\n\nsquares a number"}}}
#|{"jsonrpc":"2.0","id":2,"result":{"uri":"file:///w/lib/math.bend","range":{"start":{"line":3,"character":0},"end":{"line":4,"character":0}}}}
#|{"jsonrpc":"2.0","id":3,"result":{"contents":{"kind":"markdown","value":"```bend\nCircle{r: U32}\n```"}}}
#|{"jsonrpc":"2.0","id":4,"result":{"contents":{"kind":"markdown","value":"```bend\ndef U32.show(n: U32) -> String:\n```\n\nshows a number"}}}
#|{"jsonrpc":"2.0","id":5,"result":{"uri":"file:///w/app/main.bend","range":{"start":{"line":4,"character":0},"end":{"line":5,"character":0}}}}
#|{"jsonrpc":"2.0","id":6,"result":null}
#|{"jsonrpc":"2.0","id":7,"result":[{"name":"Base","kind":2,"range":{"start":{"line":0,"character":0},"end":{"line":1,"character":0}},"selectionRange":{"start":{"line":0,"character":0},"end":{"line":1,"character":0}}},{"name":"M","kind":2,"range":{"start":{"line":1,"character":0},"end":{"line":2,"character":0}},"selectionRange":{"start":{"line":1,"character":0},"end":{"line":2,"character":0}}},{"name":"twice","kind":12,"range":{"start":{"line":4,"character":0},"end":{"line":5,"character":0}},"selectionRange":{"start":{"line":4,"character":0},"end":{"line":5,"character":0}}},{"name":"main","kind":12,"range":{"start":{"line":7,"character":0},"end":{"line":8,"character":0}},"selectionRange":{"start":{"line":7,"character":0},"end":{"line":8,"character":0}}}]}
#|{"jsonrpc":"2.0","id":9,"result":{"contents":{"kind":"markdown","value":"```bend\nx: U32\n```\n\nparameter"}}}
#|{"jsonrpc":"2.0","id":10,"result":{"uri":"file:///w/app/main.bend","range":{"start":{"line":4,"character":10},"end":{"line":4,"character":11}}}}
#|{"jsonrpc":"2.0","id":8,"result":{"contents":{"kind":"markdown","value":"```bend\ndef twice(x: U32) -> U32:\n```\n\ntriples now"}}}
