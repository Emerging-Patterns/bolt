# probe: main.bend's `lsp` arm alone
import Base
import ../bolt/lsp/run.bend as M

def main() -> IO(Unit):
  M.run()
