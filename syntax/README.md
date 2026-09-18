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
  Token kinds tell apart what binds from what does not (keywords, dotted and
  capitalized names, `_`, and the operators `:` `=` `<-` `->` `=>` `@` `&`),
  so a walk can branch by constructor.
- `tree.bend`: a concrete syntax tree: statements by line and indentation,
  groups by brackets (`(..)`, `[..]`, `{..}` and type arguments `<..>`),
  cells inside the type. One stack machine over the tokens, tolerant by
  construction: an unclosed bracket is closed by the next line at column 0
  (so damage stays in one item) or the end of the file, a stray close
  bracket is a leaf. Trivia stays in the token stream. Not a term-level AST
  with operator precedence: nothing has needed one; a precedence pass can be
  layered on a group later.
- `bind.bend`: where every name is bound and what every other name refers
  to. One walk threads an environment through Bend's binding forms (item
  names, telescopes, `case` patterns, `for`/`exs`, lets of every shape,
  do-binds, `x =>`, `@x:` and `&x:`), each statement recording the names in
  scope. A use resolves to a binder of the file, an item of the file, an
  item behind an import alias, or nothing (Base, or unknown). Names and
  binding sites, not types.

The tree and the binder are what [lsp](../lsp/) navigates, references,
renames and colours with, and what [lint](../lint/) checks.
