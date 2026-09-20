# probe: main.bend's `check` arm alone
import Base
import ../bolt/check.bend as M

def main() -> IO(Unit):
  M.run()
