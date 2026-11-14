# What the language server sends, entry by entry. Every reply that lists
# things (diagnostics, findings, symbols, completions, locations, edits, the
# numbers of a semantic tokens reply, notifications) lists one entry for each
# thing, in order: nothing is dropped on the way to the editor. The server
# says what it can do in one place. And the small readings the replies rest
# on are stated: a `%XX` of a file URI, a path segment of a relative import,
# which binder or use sits at or behind a token, an entry's way down the
# semantic index.
import Base
import ezjson@1.2.0.0/main.bend as Ezjson
import ezjson@1.2.0.0/src/value.bend as J
import ../src/lsp/frame.bend as Frame
import ../src/lsp/report.bend as Rep
import ../src/syntax/outline.bend as Outline
import ../src/syntax/bind.bend as Bind
import ../src/lsp/semantic.bend as Semantic
import ../src/finding.bend as Lint
import ../src/codes.bend as Codes
import ../src/config.bend as Config
import ../src/version.bend as Ver
import ../src/lsp/enc.bend as Enc
import ../src/lsp/proto.bend as Proto
import ../src/lsp/nav.bend as Nav
import ../src/lsp/path.bend as Path
import ../src/lsp/server.bend as Server
import ../src/lsp/checker/argv.bend as Argv
import ../src/syntax/lex.bend as Lex

# LAW: the server answers initialize, for any negotiated encoding, with these
# capabilities and this name: open, close, full-text change and save;
# hover, definition, document symbols, completion on `.`, references,
# rename, and full semantic tokens over the legend
law lsp_capabilities:
  for e: Enc.Enc
  {Proto.capabilities(e)
    ==
      Ezjson.obj([
        ("capabilities", Ezjson.obj([
          ("positionEncoding", J.JStr{Enc.name(e)}),
          ("textDocumentSync", Ezjson.obj([("openClose", J.JBool{True{}}), ("change", J.JNum{U32.show(1)}), ("save", J.JBool{True{}})])),
          ("hoverProvider", J.JBool{True{}}),
          ("definitionProvider", J.JBool{True{}}),
          ("documentSymbolProvider", J.JBool{True{}}),
          ("completionProvider", Ezjson.obj([("triggerCharacters", Ezjson.arr([J.JStr{"."}]))])),
          ("referencesProvider", J.JBool{True{}}),
          ("renameProvider", J.JBool{True{}}),
          ("semanticTokensProvider", Ezjson.obj([
            ("legend", Ezjson.obj([("tokenTypes", Ezjson.arr(Proto.strings(Semantic.legend()))), ("tokenModifiers", Ezjson.arr([]))])),
            ("full", J.JBool{True{}})]))])),
        ("serverInfo", Ezjson.obj([("name", J.JStr{"bolt"}), ("version", J.JStr{Ver.text()})]))])
    : J.Json}

# LAW: every diagnostic is sent, in order
law lsp_diagnostics_each:
  for d: Rep.Diag
  for t: List<&2, Rep.Diag>
  for +c: Enc.Cols
  {Proto.diagnostics(d <> t, c) == Proto.diagnostic(c, d) <> Proto.diagnostics(t, c) : List<&2, J.Json>}

# LAW: every finding is sent, in order
law lsp_findings_each:
  for d: Lint.Graded
  for t: List<&2, Lint.Graded>
  for +c: Enc.Cols
  {Proto.findings(d <> t, c) == Proto.finding(c, d) <> Proto.findings(t, c) : List<&2, J.Json>}

# LAW: every item, as a symbol is sent, in order
law lsp_symbols_each:
  for d: Outline.Item
  for t: List<&2, Outline.Item>
  for +c: Enc.Cols
  {Proto.symbols.go(d <> t, c) == Proto.symbol(c, d) <> Proto.symbols.go(t, c) : List<&2, J.Json>}

# LAW: every candidate is sent as a completion, in order
law lsp_completions_each:
  for item: Outline.Item
  for t: List<&2, Outline.Item>
  for +c: Enc.Cols
  for +line: U32
  for +start: U32
  for +col: U32
  {Proto.completions.go(item <> t, c, line, start, col)
    == Proto.completion(c, item, line, start, col) <> Proto.completions.go(t, c, line, start, col) : List<&2, J.Json>}

# LAW: a completion list says it is incomplete, so the editor asks again as
# the prefix grows, and holds its items
law lsp_completions_incomplete:
  for c: Enc.Cols
  for items: List<&2, Outline.Item>
  for line: U32
  for start: U32
  for col: U32
  {Proto.completions(c, items, line, start, col)
    == Ezjson.obj([("isIncomplete", J.JBool{True{}}),
      ("items", Ezjson.arr(Proto.completions.go(items, c, line, start, col)))]) : J.Json}

# LAW: every position a name is at is sent as a location in the document,
# over the name, in order
law lsp_locations_each:
  for l: U32
  for c: U32
  for rest: List<&2, Bind.Pos>
  for +cc: Enc.Cols
  for +uri: String
  for +name: String
  {Proto.locations.go(Bind.Pos{l, c} <> rest, cc, uri, name)
    == Ezjson.obj([("uri", J.JStr{uri}), ("range", Proto.name_range(cc, l, c, name))])
      <> Proto.locations.go(rest, cc, uri, name) : List<&2, J.Json>}

# LAW: a rename edits every position the name is at, over the old name, to
# the new one, in order
law lsp_edits_each:
  for l: U32
  for c: U32
  for rest: List<&2, Bind.Pos>
  for +cc: Enc.Cols
  for +name: String
  for +new: String
  {Proto.edits.go(Bind.Pos{l, c} <> rest, cc, name, new)
    == Ezjson.obj([("range", Proto.name_range(cc, l, c, name)), ("newText", J.JStr{new})])
      <> Proto.edits.go(rest, cc, name, new) : List<&2, J.Json>}

# LAW: every number of a semantic tokens reply is sent, in order
law lsp_nums_each:
  for h: U32
  for t: List<&2, U32>
  {Proto.nums(h <> t) == J.JNum{U32.show(h)} <> Proto.nums(t) : List<&2, J.Json>}

# LAW: in a file URI, `%` and two hex digits are one byte, sixteen times the
# first digit plus the second
law lsp_unpercent_decodes_byte:
  for a: Char
  for b: Char
  for t: List<&2, Char>
  {Proto.unpercent('%' <> a <> b <> t) == (Proto.hex(a) * 16 + Proto.hex(b) : U32) <> Proto.unpercent(t)
    : List<&2, U32>}

# LAW: a check that says only that laws are open is one diagnostic whose
# message is bend's count of TODOs
law argv_only_todos_one_report:
  for line: U32
  for +msg: String
  {Argv.only_todos(Rep.Diag{line, msg} <> Nil{})
    == Bool.or(String.contains(msg, "TODO found"), String.contains(msg, "TODOs found")) : Bool}

# LAW: two or more diagnostics are more than that
law argv_only_todos_not_more:
  for d1: Rep.Diag
  for d2: Rep.Diag
  for rest: List<&2, Rep.Diag>
  {Argv.only_todos(d1 <> d2 <> rest) == False{} : Bool}

# LAW: and none is not that either
law argv_only_todos_needs_report:
  for ds: List<&2, Rep.Diag>
  for e: {List.is_empty(&2, Rep.Diag, ds) == True{} : Bool}
  {Argv.only_todos(ds) == False{} : Bool}

# LAW: some line holds a char past the Basic Multilingual Plane when the
# first does or a later one does
law enc_wide_any_line:
  for l: String
  for t: List<&2, String>
  {Enc.wide_any(l <> t) == Bool.or(Enc.wide_in(String.to_list(l)), Enc.wide_any(t)) : Bool}

# LAW: no lines hold none
law enc_wide_any_needs_lines:
  for lines: List<&2, String>
  for e: {List.is_empty(&2, String, lines) == True{} : Bool}
  {Enc.wide_any(lines) == False{} : Bool}

# LAW: every visible binder is offered as a candidate, in order: a local, by
# its name and line, its note as its signature and its kind's name as its
# doc
law nav_as_items_each:
  for name: String
  for line: U32
  for col: U32
  for kind: Bind.BindKind
  for note: String
  for t: List<&2, Bind.Bind>
  {Nav.as_items(Bind.Bind{name, line, col, kind, note} <> t)
    == Outline.Item{Outline.ILocal{}, name, line, note, Proto.kind_name(kind), ""} <> Nav.as_items(t)
    : List<&2, Outline.Item>}

# LAW: following a relative import, `..` drops the segment before it, `.`
# and an empty segment change nothing, and any other segment is kept
law path_push_segment:
  for +seg: String
  for +acc: List<&2, String>
  {Path.push(seg, acc)
    == Bool.pick(List<&2, String>, String.eq(seg, ".."), List.tail(&2, String, acc),
      Bool.pick(List<&2, String>, Bool.or(String.eq(seg, "."), String.is_empty(seg)), acc, seg <> acc))
    : List<&2, String>}

# LAW: every notification is sent as a reply, in order
law server_notices_each:
  for n: String
  for t: List<&2, String>
  {Server.notices(n <> t) == Server.RNote{n} <> Server.notices(t) : List<&2, Server.Reply>}

# LAW: a name starts with a capital when its first char is one
law sem_upper_first_char:
  for c: Char
  for t: List<&2, Char>
  {Semantic.upper_first(c <> t) == Char.is_upper(c) : Bool}

# LAW: no chars start with none
law sem_upper_first_needs_char:
  for cs: List<&2, Char>
  for e: {List.is_empty(&2, Char, cs) == True{} : Bool}
  {Semantic.upper_first(cs) == False{} : Bool}

# LAW: the next bind sits at a position when it starts on that line at that
# column
law sem_at_head_bind:
  for n: String
  for l: U32
  for c: U32
  for k: Bind.BindKind
  for note: String
  for rest: List<&2, Bind.Bind>
  for +line: U32
  for +col: U32
  {Semantic.at_head_bind(Bind.Bind{n, l, c, k, note} <> rest, line, col)
    == Bool.and(U32.is_eq(l, line), U32.is_eq(c, col)) : Bool}

# LAW: with none left, none sits there
law sem_at_head_bind_needs_one:
  for xs: List<&2, Bind.Bind>
  for +line: U32
  for +col: U32
  for e: {List.is_empty(&2, Bind.Bind, xs) == True{} : Bool}
  {Semantic.at_head_bind(xs, line, col) == False{} : Bool}

# LAW: the next bind is behind a position when it is on an earlier line, or on
# the same line at an earlier column
law sem_behind_bind:
  for n: String
  for +l: U32
  for c: U32
  for k: Bind.BindKind
  for note: String
  for rest: List<&2, Bind.Bind>
  for +line: U32
  for +col: U32
  {Semantic.behind_bind(Bind.Bind{n, l, c, k, note} <> rest, line, col)
    == Bool.or(U32.is_lt(l, line), Bool.and(U32.is_eq(l, line), U32.is_lt(c, col))) : Bool}

# LAW: with none left, none is behind
law sem_behind_bind_needs_one:
  for xs: List<&2, Bind.Bind>
  for +line: U32
  for +col: U32
  for e: {List.is_empty(&2, Bind.Bind, xs) == True{} : Bool}
  {Semantic.behind_bind(xs, line, col) == False{} : Bool}

# LAW: the next use sits at a position when it starts on that line at that
# column
law sem_at_head_use:
  for n: String
  for l: U32
  for c: U32
  for tg: Bind.Target
  for rest: List<&2, Bind.Use>
  for +line: U32
  for +col: U32
  {Semantic.at_head_use(Bind.Use{n, l, c, tg} <> rest, line, col)
    == Bool.and(U32.is_eq(l, line), U32.is_eq(c, col)) : Bool}

# LAW: with none left, none sits there
law sem_at_head_use_needs_one:
  for xs: List<&2, Bind.Use>
  for +line: U32
  for +col: U32
  for e: {List.is_empty(&2, Bind.Use, xs) == True{} : Bool}
  {Semantic.at_head_use(xs, line, col) == False{} : Bool}

# LAW: the next use is behind a position when it is on an earlier line, or on
# the same line at an earlier column
law sem_behind_use:
  for n: String
  for +l: U32
  for c: U32
  for tg: Bind.Target
  for rest: List<&2, Bind.Use>
  for +line: U32
  for +col: U32
  {Semantic.behind_use(Bind.Use{n, l, c, tg} <> rest, line, col)
    == Bool.or(U32.is_lt(l, line), Bool.and(U32.is_eq(l, line), U32.is_lt(c, col))) : Bool}

# LAW: with none left, none is behind
law sem_behind_use_needs_one:
  for xs: List<&2, Bind.Use>
  for +line: U32
  for +col: U32
  for e: {List.is_empty(&2, Bind.Use, xs) == True{} : Bool}
  {Semantic.behind_use(xs, line, col) == False{} : Bool}

# LAW: a key's way down the index is its low bits, lowest first, one a level
law sem_path_low_bits_first:
  for p: Nat
  for +key: U32
  {Semantic.path(1n+p, key) == U32.is_even(key) <> Semantic.path(p, U32.shr(key)) : List<&2, Bool>}

# LAW: an entry is put down its path: into the half its bit names, the other
# half kept as it was
law sem_idx_put_down_the_path:
  for +b: Bool
  for rest: List<&2, Bool>
  for +i: Semantic.Index
  for +e: Semantic.Entry
  {Semantic.idx.put(b <> rest, i, e)
    == Semantic.idx.join(b, Semantic.idx.put(rest, Semantic.idx.near(b, i), e),
      Semantic.idx.near(Bool.not(b), i)) : Semantic.Index}

# LAW: among a leaf's entries, the one at a position is the first that
# starts exactly there
law sem_at_first_entry_there:
  for n: String
  for l: U32
  for c: U32
  for k: Bind.BindKind
  for rest: List<&2, Semantic.Entry>
  for +line: U32
  for +col: U32
  {Semantic.at.go(Semantic.Entry{n, l, c, k} <> rest, line, col)
    == Bool.pick(Maybe<&2, Bind.BindKind>, Bool.and(U32.is_eq(l, line), U32.is_eq(c, col)), Some{k},
      Semantic.at.go(rest, line, col)) : Maybe<&2, Bind.BindKind>}

# LAW: tokens start with `{` when the first one's text is `{`
law sem_opens_brace_first_token:
  for k: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  {Semantic.opens_brace(Lex.Tok{k, t, l, c} <> rest) == String.eq(t, "{") : Bool}

# LAW: no tokens start with nothing
law sem_opens_brace_needs_token:
  for toks: List<&2, Lex.Tok>
  for e: {List.is_empty(&2, Lex.Tok, toks) == True{} : Bool}
  {Semantic.opens_brace(toks) == False{} : Bool}

# LAW: every classified token is sent, in order, its column and length put
# in the negotiated encoding against the text of its own line, the lines read
# forward from where the last token left them
law sem_sent_each_token:
  for +line: U32
  for col: U32
  for len: U32
  for typ: U32
  for rest: List<&2, Semantic.Sem>
  for +e: Enc.Enc
  for lines: List<&2, String>
  for cur: U32
  {Semantic.sent(Semantic.Sem{line, col, len, typ} <> rest, e, lines, cur)
    == Semantic.sent.one(e,
      String.to_list(Maybe.default(&2, String, List.head(&2, String, Semantic.sent.seek(lines, cur, line)), "")),
      Semantic.Sem{line, col, len, typ})
      <> Semantic.sent(rest, e, Semantic.sent.seek(lines, cur, line), line) : List<&2, Semantic.Sem>}
