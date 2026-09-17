# syntax

What an editor needs to know about a Bend source without checking it.

- `outline.bend`: the top-level items — imports (with alias and path), defs,
  laws, types and their constructors — each with its line, its signature text
  and the comment block above it. It reads line by line: a top-level item
  starts at column 0, so a line it does not understand is skipped and the items
  around it still stand. Half-written files are the normal case in an editor.
- `word.bend`: the name under a (line, col).

Not here yet: a lexer and an expression-level tree. Hover, definition and
symbols do not need them; locals and semantic tokens will.
