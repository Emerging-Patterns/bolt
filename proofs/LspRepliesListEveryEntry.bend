# proofs of laws/LspRepliesListEveryEntry.bend
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
import ../src/lazy/lazy.bend as Lazy
import ../laws/LspRepliesListEveryEntry.bend as Laws
import ./lemmas/BoolEmptiness.bend as M1

# a stop at the first True is the plain or
law lh.or_else:
  for c: Bool
  for -x: Bool
  {Lazy.or_else(c, _u => x) == Bool.or(c, x) : Bool}

def lh.or_else(c, _x):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# a search that stops at the first hit is the pick of it
law lh.stop:
  for c: Bool
  for -x: Maybe<&2, Bind.BindKind>
  for -y: Maybe<&2, Bind.BindKind>
  {Lazy.stop(Maybe<&2, Bind.BindKind>, c, x, _u => y) == Bool.pick(Maybe<&2, Bind.BindKind>, c, x, y)
    : Maybe<&2, Bind.BindKind>}

def lh.stop(c, _x, _y):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.lsp_capabilities(_ee):
  {==}

def Laws.lsp_diagnostics_each(_d, _t, _cc):
  {==}

def Laws.lsp_findings_each(_d, _t, _cc):
  {==}

def Laws.lsp_symbols_each(_d, _t, _cc):
  {==}

def Laws.lsp_completions_each(_item, _t, _cc, _line, _start, _col):
  {==}

def Laws.lsp_completions_incomplete(_cc, _items, _line, _start, _col):
  {==}

def Laws.lsp_locations_each(_l, _c, _rest, _cc, _uri, _name):
  {==}

def Laws.lsp_edits_each(_l, _c, _rest, _cc, _name, _new):
  {==}

def Laws.lsp_nums_each(_h, _t):
  {==}

def Laws.lsp_unpercent_decodes_byte(_a, _b, _t):
  {==}

def Laws.argv_only_todos_one_report(_line, _msg):
  {==}

def Laws.argv_only_todos_not_more(d1, _d2, _rest):
  match d1:
    case Rep.Diag{_line, _msg}:
      {==}

def Laws.argv_only_todos_needs_report(ds, e):
  match ds:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Argv.only_todos(ds) == False{} : Bool}, M1.false_true(e))

def Laws.enc_wide_any_line(l, t):
  lh.or_else(Enc.wide_in(String.to_list(l)), Enc.wide_any(t))

def Laws.enc_wide_any_needs_lines(lines, e):
  match lines:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Enc.wide_any(lines) == False{} : Bool}, M1.false_true(e))

def Laws.nav_as_items_each(_name, _line, _col, _kind, _note, _t):
  {==}

def Laws.path_push_segment(_seg, _acc):
  {==}

def Laws.server_notices_each(_n, _t):
  {==}

def Laws.sem_upper_first_char(_c, _t):
  {==}

def Laws.sem_upper_first_needs_char(cs, e):
  match cs:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Semantic.upper_first(cs) == False{} : Bool}, M1.false_true(e))

def Laws.sem_at_head_bind(_n, _l, _c, _k, _note, _rest, _line, _col):
  {==}

def Laws.sem_at_head_bind_needs_one(xs, line, col, e):
  match xs:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Semantic.at_head_bind(xs, line, col) == False{} : Bool}, M1.false_true(e))

def Laws.sem_behind_bind(_n, _l, _c, _k, _note, _rest, _line, _col):
  {==}

def Laws.sem_behind_bind_needs_one(xs, line, col, e):
  match xs:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Semantic.behind_bind(xs, line, col) == False{} : Bool}, M1.false_true(e))

def Laws.sem_at_head_use(_n, _l, _c, _tg, _rest, _line, _col):
  {==}

def Laws.sem_at_head_use_needs_one(xs, line, col, e):
  match xs:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Semantic.at_head_use(xs, line, col) == False{} : Bool}, M1.false_true(e))

def Laws.sem_behind_use(_n, _l, _c, _tg, _rest, _line, _col):
  {==}

def Laws.sem_behind_use_needs_one(xs, line, col, e):
  match xs:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Semantic.behind_use(xs, line, col) == False{} : Bool}, M1.false_true(e))

def Laws.sem_path_low_bits_first(_p, _key):
  {==}

def Laws.sem_idx_put_down_the_path(_bb, _rest, _ii, _ee):
  {==}

def Laws.sem_at_first_entry_there(_n, l, c, k, rest, line, col):
  lh.stop(Bool.and(U32.is_eq(l, line), U32.is_eq(c, col)), Some{k}, Semantic.at.go(rest, line, col))

def Laws.sem_opens_brace_first_token(_k, _t, _l, _c, _rest):
  {==}

def Laws.sem_opens_brace_needs_token(toks, e):
  match toks:
    case Nil{}:
      {==}
    case Con{_h, _t}:
      Empty.absurd({Semantic.opens_brace(toks) == False{} : Bool}, M1.false_true(e))

def Laws.sem_sent_each_token(_line, _col, _len, _typ, _rest, _ee, _lines, _cur):
  {==}
