# lsp/nav: completion in a session over fake files: through an alias, among
# the document's own names and aliases, and from Base once something is typed
import Base
import ../server.bend as Server
import ../transport/script.bend as Script
import ../checker/fake.bend as FakeChecker
import ../files/service.bend as F

def math() -> String:
  "import Base\n\n# squares a number\ndef square(+x: U32) -> U32:\n  (x * x : U32)\n\ndef sqrt(x: U32) -> U32:\n  x\n\ndef cube(x: U32) -> U32:\n  x\n"

def base() -> String:
  "law U32.show:\n  U32 -> String\n\ndef U32.show.go(n: U32) -> String:\n  \"\"\n\n# shows a number\ndef U32.show(n):\n  \"\"\n\ndef U32.add(a: U32, b: U32) -> U32:\n  a\n\ndef Nat.show(n: Nat) -> String:\n  \"\"\n"

def fake.at(+path: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.eq(path, "/w/lib/math.bend"), Some{math()},
    Bool.pick(Maybe<&2, String>, String.eq(path, "/base.bend"), Some{base()}, None{}))

def fake.read(path: String) -> IO(Maybe<&2, String>):
  IO.pure(Maybe<&2, String>, fake.at(path))

def fake.base_path(_u: Unit) -> IO(String):
  IO.pure(String, "/base.bend")

def fake() -> F.Files:
  F.Files{fake.read, fake.base_path}

def main_text() -> String:
  "import Base\\nimport ../lib/math.bend as M\\n\\ndef mine(x: U32) -> U32:\\n  M.sq\\n  U32.s\\n  m\\n  x\\n"

def ask(id: String, line: String, col: String) -> String:
  "{\"jsonrpc\":\"2.0\",\"id\":" ++ id ++ ",\"method\":\"textDocument/completion\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/app/main.bend\"},\"position\":{\"line\":" ++ line ++ ",\"character\":" ++ col ++ "}}}"

def inbox() -> List<&2, String>:
  ["{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/app/main.bend\",\"text\":\"" ++ main_text() ++ "\"}}}",
   ask("1", "4", "6"),
   ask("2", "5", "7"),
   ask("3", "6", "3"),
   ask("4", "7", "3")]

def main() -> IO(Unit):
  Server.serve(~Script.Script, ~Script.new(), ~FakeChecker.new(), ~fake(), 100n, Script.Script{inbox()}, [])

#|{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///w/app/main.bend","diagnostics":[]}}
#|{"jsonrpc":"2.0","id":1,"result":{"isIncomplete":true,"items":[{"label":"M.square","kind":3,"detail":"def square(+x: U32) -> U32:","documentation":{"kind":"markdown","value":"squares a number"},"filterText":"M.square","textEdit":{"range":{"start":{"line":4,"character":2},"end":{"line":4,"character":6}},"newText":"M.square"}},{"label":"M.sqrt","kind":3,"detail":"def sqrt(x: U32) -> U32:","documentation":{"kind":"markdown","value":""},"filterText":"M.sqrt","textEdit":{"range":{"start":{"line":4,"character":2},"end":{"line":4,"character":6}},"newText":"M.sqrt"}}]}}
#|{"jsonrpc":"2.0","id":2,"result":{"isIncomplete":true,"items":[{"label":"U32.show","kind":21,"detail":"law U32.show:","documentation":{"kind":"markdown","value":""},"filterText":"U32.show","textEdit":{"range":{"start":{"line":5,"character":2},"end":{"line":5,"character":7}},"newText":"U32.show"}},{"label":"U32.show.go","kind":3,"detail":"def U32.show.go(n: U32) -> String:","documentation":{"kind":"markdown","value":""},"filterText":"U32.show.go","textEdit":{"range":{"start":{"line":5,"character":2},"end":{"line":5,"character":7}},"newText":"U32.show.go"}}]}}
#|{"jsonrpc":"2.0","id":3,"result":{"isIncomplete":true,"items":[{"label":"mine","kind":3,"detail":"def mine(x: U32) -> U32:","documentation":{"kind":"markdown","value":""},"filterText":"mine","textEdit":{"range":{"start":{"line":6,"character":2},"end":{"line":6,"character":3}},"newText":"mine"}}]}}
#|{"jsonrpc":"2.0","id":4,"result":{"isIncomplete":true,"items":[{"label":"x","kind":6,"detail":"x: U32","documentation":{"kind":"markdown","value":"parameter"},"filterText":"x","textEdit":{"range":{"start":{"line":7,"character":2},"end":{"line":7,"character":3}},"newText":"x"}}]}}
