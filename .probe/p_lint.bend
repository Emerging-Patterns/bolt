# probe: main.bend's `lint` arm alone
import Base
import ../bolt/lint.bend as M

def main() -> IO(Unit):
  M.run()
