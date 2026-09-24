# lsp/run: the container; `bolt lsp` runs it. Native only: the JS lane
# overflows its stack on big messages.
import Base
import ./server.bend as Server
import ./transport/stdio.bend as Stdio
import ./files/disk.bend as Disk

# the server over stdio, reading the disk
def run() -> IO(Unit):
  do IO<Unit>:
    h : Stdio.Stdio <- Stdio.open()
    Server.serve(~Stdio.Stdio, ~Stdio.new(), ~Disk.new(), U32.to_nat(4294967295), h, [])
