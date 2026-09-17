# lsp/path and lsp/docs
import Base
import ../path.bend as Path
import ../docs.bend as Docs
import ../../wire/check/kit.bend as Check
import ../../wire/check/print.bend as Report

def docs() -> List<&2, Docs.Doc>:
  Docs.set(Docs.set(Docs.set([], "a", "1"), "b", "2"), "a", "3")

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str(~Report.new(), "a file's directory", Path.dir("/w/lsp/server.bend"), "/w/lsp")
    Check.eq_str(~Report.new(), "a sibling import", Path.join("/w/lsp", "./frame.bend"), "/w/lsp/frame.bend")
    Check.eq_str(~Report.new(), "a parent import", Path.join("/w/lsp/tests", "../../json/value.bend"), "/w/json/value.bend")
    Check.eq_str(~Report.new(), "a set replaces", Maybe.default(&2, String, Docs.get(docs(), "a"), "?"), "3")
    Check.eq_str(~Report.new(), "others stay", Maybe.default(&2, String, Docs.get(docs(), "b"), "?"), "2")
    Check.eq_str(~Report.new(), "a closed doc is gone", Maybe.default(&2, String, Docs.get(Docs.del(docs(), "a"), "a"), "?"), "?")

#|ok a file's directory
#|ok a sibling import
#|ok a parent import
#|ok a set replaces
#|ok others stay
#|ok a closed doc is gone
