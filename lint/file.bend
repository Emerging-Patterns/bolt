# lint/file: a file the linter read, as the project rules see the set of them
import Base

# a path as given, and the text at it
type File is Data:
  File{path: String, text: String}
