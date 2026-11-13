# The name under a cursor, read straight from the text (the language server
# asks it before a file parses). A name's chars are letters, digits, `_` and
# `.`; a run of them is a name; the run that holds the cursor's column, from
# its first char to the column just past its last, is the name there. The
# line is found by counting newlines from the top.
import Base
import ../src/syntax/word.bend as Word

# LAW: a char belongs to a name exactly when it is a letter, a digit, `_` or
# `.`
law name_chars:
  for +cc: Char
  {Word.is_name(cc)
    == Bool.or(Bool.or(Char.is_alpha(cc), Char.is_digit(cc)), Bool.or(Char.is_eq(cc, '_'), Char.is_eq(cc, '.')))
    : Bool}

# LAW: a run that ends at column ii is the name at col exactly when it
# starts at or before col and col is at or before ii; otherwise what was
# found before stands
law run_holds_its_columns:
  for h: Char
  for t: List<&2, Char>
  for +start: U32
  for +ii: U32
  for +col: U32
  for hit: Maybe<&2, String>
  {Word.close.run(h <> t, start, ii, col, hit)
    == Bool.pick(Maybe<&2, String>, Bool.and(U32.is_le(start, col), U32.is_le(col, ii)), Some{Word.text(h <> t)},
      hit) : Maybe<&2, String>}

# LAW: an empty run is no name: what was found before stands
law empty_run_is_no_name:
  for +start: U32
  for +ii: U32
  for +col: U32
  for hit: Maybe<&2, String>
  {Word.close.run(Nil{}, start, ii, col, hit) == hit : Maybe<&2, String>}

# LAW: the wanted line starts after a newline when one line was left to skip
law line_starts_after_last_newline:
  for nn: U32
  {Word.at.skip.done(True{}, nn) == U32.is_eq(nn, 1) : Bool}

# LAW: any other char starts no line
law line_needs_a_newline:
  for nn: U32
  {Word.at.skip.done(False{}, nn) == False{} : Bool}

# LAW: the name at a line and column is read from that line's start, the
# source's own start when the line is the first
law at_reads_from_the_line:
  for source: String
  for +line: U32
  for col: U32
  {Word.at(source, line, col)
    == Word.at.read(Word.at.skip(source, line, U32.is_eq(line, 0)), False{}, Word.W{0, 0, [], None{}}, col) : String}

# LAW: the leading run of name chars takes a char that belongs to a name and
# goes on, and stops at the first that does not
law run_of_name_chars:
  for +c: Char
  for t: List<&2, Char>
  {Word.run_of(c <> t) == Bool.pick(List<&2, Char>, Word.is_name(c), c <> Word.run_of(t), Nil{}) : List<&2, Char>}

# LAW: a name char joins the run, and the scan moves one column on
law step_joins_a_name_char:
  for cc: Char
  for +ii: U32
  for start: U32
  for run: List<&2, Char>
  for hit: Maybe<&2, String>
  for col: U32
  {Word.step.on(True{}, cc, ii, start, run, hit, col) == Word.W{(ii + 1 : U32), start, cc <> run, hit} : Word.W}

# LAW: any other char ends the run at its own column, where the run is read
# for the cursor, and the next run starts at the column after it
law step_ends_the_run:
  for cc: Char
  for +ii: U32
  for +start: U32
  for run: List<&2, Char>
  for hit: Maybe<&2, String>
  for +col: U32
  {Word.step.on(False{}, cc, ii, start, run, hit, col)
    == Word.W{(ii + 1 : U32), (ii + 1 : U32), [], Word.close(ii, start, run, hit, col)} : Word.W}
