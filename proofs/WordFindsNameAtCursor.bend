# proofs of laws/WordFindsNameAtCursor.bend
import Base
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/word.bend as Word
import ../laws/WordFindsNameAtCursor.bend as Laws

# keeping the run when it holds the column is a pick
law wf.yes:
  for ok: Bool
  for -run: List<&2, Char>
  for -hit: Maybe<&2, String>
  {Word.close.yes(ok, run, hit) == Bool.pick(Maybe<&2, String>, ok, Some{Word.text(run)}, hit) : Maybe<&2, String>}

def wf.yes(ok, _run, _hit):
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# a stop at a char that is no name char is the pick the other way round
law wf.stop:
  for c: Bool
  for -x: List<&2, Char>
  {Lazy.stop(List<&2, Char>, Bool.not(c), Nil{}, _u => x) == Bool.pick(List<&2, Char>, c, x, Nil{}) : List<&2, Char>}

def wf.stop(c, _x):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.name_chars(_cc):
  {==}

def Laws.run_holds_its_columns(h, t, start, i, col, hit):
  wf.yes(Bool.and(U32.is_le(start, col), U32.is_le(col, i)), h <> t, hit)

def Laws.empty_run_is_no_name(_start, _ii, _col, _hit):
  {==}

def Laws.line_starts_after_last_newline(_nn):
  {==}

def Laws.line_needs_a_newline(_nn):
  {==}

def Laws.at_reads_from_the_line(_source, _line, _col):
  {==}

def Laws.run_of_name_chars(c, t):
  wf.stop(Word.is_name(c), c <> Word.run_of(t))

def Laws.step_joins_a_name_char(_cc, _ii, _start, _run, _hit, _col):
  {==}

def Laws.step_ends_the_run(_cc, _ii, _start, _run, _hit, _col):
  {==}
