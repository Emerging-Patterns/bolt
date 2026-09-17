# syntax

What an editor needs to know about a Bend source without checking it.

- `outline.bend`: the top-level items — imports (with alias and path), defs,
  laws, types and their constructors — each with its line, its signature text
  and the comment block above it. It reads line by line: a top-level item
  starts at column 0, so a line it does not understand is skipped and the items
  around it still stand. Half-written files are the normal case in an editor.
- `word.bend`: the name under a (line, col), and the name being typed there.
- `lex.bend`: a lossless lexer with positions (the texts spell the source
  back, whatever it is).
- `scope.bend`: the parameters and locals visible at a line, with where each
  was bound. Tokens and indentation, not an expression tree: parameters from
  the def header, body binders by line shape (`case`, `for`, lets, do-binds,
  lambdas), blocks by indentation. Names and binding sites, not types.

Not here yet: an expression-level tree. Nothing has needed one: hover,
definition, symbols, completion and locals all run on the outline, the lexer
and the scope. Rename, references and semantic tokens would be the reasons.
