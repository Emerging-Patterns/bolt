# bend-lsp: the container. Build it native (`bend lsp/main.bend -o bend-lsp`):
# the JS lane overflows its stack on big messages.
import Base
import ./server.bend as Server
import ./transport/stdio.bend as Stdio
import ./checker/bend.bend as BendChecker

def main() -> IO(Unit):
  do IO<Unit>:
    h : Stdio.Stdio <- Stdio.open()
    Server.serve(~Stdio.Stdio, ~Stdio.new(), ~BendChecker.new(), U32.to_nat(4294967295), h)
