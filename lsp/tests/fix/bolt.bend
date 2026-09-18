# bolt.bend for lsp/tests/levels: comments are errors, slips are silent
import Base

# comments and width
def style() -> String:
  "error"

# a slip
def suspicious() -> String:
  "off"
