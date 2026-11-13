# Where a finding is put and what it says, for the rules whose own law only
# counts their findings. A count says a rule fires when it should; it does not
# say the finding lands on the right line, covers the right chars, or reads as
# it should. Each rule here builds its finding in one small def, and each law
# is that def's result for any position it is handed: the path, line and
# column as given, the length, the rule, and the words.
import Base
import ../src/finding.bend as F
import ../src/noqa.bend as Noqa
import ../src/rules/table.bend as Table
import ../src/rules/correctness/arms.bend as Arms
import ../src/rules/correctness/escape.bend as Escape
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/style/blank.bend as Blank
import ../src/rules/style/transcong.bend as Transcong
import ../src/rules/style/noqa.bend as NoqaRule
import ../src/rules/style/wrap.bend as Wrap
import ../src/rules/suspicious/thunk.bend as Thunk
import ../src/rules/suspicious/prefix.bend as Prefix
import ../src/rules/suspicious/empty.bend as Empty
import ../src/rules/pedantic/rewalk.bend as Rewalk

# LAW: table cites a List.get where it is, over the length it is handed
law table_cites_get:
  for +path: String
  for +line: U32
  for +col: U32
  for +len: U32
  {Table.cite(True{}, path, line, col, len) == F.Finding{path, line, col, len, "table",
    "List.get in a recursive def walks the table from its head on every step; keep the table in an Array and use Array.get."} : F.Finding}

# LAW: and a List.set the same way, with its own words
law table_cites_set:
  for +path: String
  for +line: U32
  for +col: U32
  for +len: U32
  {Table.cite(False{}, path, line, col, len) == F.Finding{path, line, col, len, "table",
    "List.set in a recursive def copies the list to change one element; keep the table in an Array and use Array.set."} : F.Finding}

# LAW: arms cites a covered arm at the position it is handed, with no length,
# naming the line of the arm that covers it counted from 1, before the rest
law arms_cites_covered_arm:
  for line: U32
  for +path: String
  for ll: U32
  for cc: U32
  for more: List<&2, F.Finding>
  {Arms.cover.hit(Some{line}, path, ll, cc, more) == F.Finding{path, ll, cc, 0, "arms",
    "Unreachable: the case on line " ++ U32.show((line + 1 : U32))
      ++ " already matches everything this one does; delete this arm, or move it above that one."} <> more
    : List<&2, F.Finding>}

# LAW: an arm nothing covers adds nothing
law arms_passes_uncovered_arm:
  for +path: String
  for ll: U32
  for cc: U32
  for more: List<&2, F.Finding>
  {Arms.cover.hit(None{}, path, ll, cc, more) == more : List<&2, F.Finding>}

# LAW: escape cites a NUL escape with no digit after it over its three chars
law escape_cites_lone_nul:
  for +ds: List<&2, Char>
  for +path: String
  for +line: U32
  for +col: U32
  for e: {List.is_empty(&2, Char, ds) == True{} : Bool}
  {Escape.finding(ds, path, line, col) == F.Finding{path, line, col, 3, "escape",
    "\\0 followed by digits is a NUL character and then those digits, not an octal escape; write \\u{..} instead."} : F.Finding}

# LAW: escape cites a NUL escape and the digits after it over all of them,
# and says the digits and the escape to write instead
law escape_cites_nul_and_digits:
  for +ds: List<&2, Char>
  for +path: String
  for +line: U32
  for +col: U32
  for e: {List.is_empty(&2, Char, ds) == False{} : Bool}
  {Escape.finding(ds, path, line, col)
    == F.Finding{path, line, col, (U32.from_nat(String.length(String.from_list(ds))) + 2 : U32), "escape",
    "\\0" ++ String.from_list(ds)
      ++ " is a NUL character followed by \"" ++ String.from_list(ds)
      ++ "\", not an octal escape; write \\u{"
      ++ Escape.hex(Escape.value(ds, 0)) ++ "}."} : F.Finding}

# LAW: pick cites a search that binds its own call, at the name, over the
# name's length; a tail call is told to carry the test
law pick_cites_tail_search:
  for +ll: U32
  for +cc: U32
  for +name: String
  for +path: String
  {Pick.search.cite(ll, cc, name, path, True{})
    == F.Finding{path, ll, cc, U32.from_nat(String.length(name)), "pick",
    name ++ " binds its own call above a Bool.pick that reads it only in the else branch, so the walk runs even when the condition holds and the search never stops early; carry the test as a Bool into the next call (`go(rest, k, test(h))`) and `match hit` first, so the search stops and stays a loop."} : F.Finding}

# LAW: and any other is told to branch with `match`
law pick_cites_other_search:
  for +ll: U32
  for +cc: U32
  for +name: String
  for +path: String
  {Pick.search.cite(ll, cc, name, path, False{})
    == F.Finding{path, ll, cc, U32.from_nat(String.length(name)), "pick",
    name ++ " binds its own call above a Bool.pick that reads it only in the else branch, so the walk runs even when the condition holds and the search never stops early; branch with `match` on the condition in a helper that takes it as a parameter, so the call runs only in the branch that needs it."} : F.Finding}

# LAW: blank says the test it found and the word for it
law blank_says_the_test:
  for +xx: String
  {Blank.say(xx)
    == "String.eq(" ++ xx ++ ", \"\") asks whether " ++ xx ++ " is empty; String.is_empty(" ++ xx ++ ") says so."
    : String}

# LAW: blank cites a test at the position it is handed, over the nine chars
# of `String.eq`, before the rest
law blank_cites_test:
  for +xx: String
  for +path: String
  for ll: U32
  for cc: U32
  for more: List<&2, F.Finding>
  {Blank.hit(Some{xx}, path, ll, cc, more) == F.Finding{path, ll, cc, 9, "blank", Blank.say(xx)} <> more
    : List<&2, F.Finding>}

# LAW: no test adds nothing
law blank_passes_no_test:
  for +path: String
  for ll: U32
  for cc: U32
  for more: List<&2, F.Finding>
  {Blank.hit(None{}, path, ll, cc, more) == more : List<&2, F.Finding>}

# LAW: transcong cites the `Equal.trans` leaf over its eleven chars
law transcong_cites_trans:
  for +ll: U32
  for +cc: U32
  for +path: String
  {Transcong.cite(ll, cc, path) == F.Finding{path, ll, cc, 11, "transcong",
    "this Equal.trans is fed an Equal.cong: rewrite instead, `%e : {F(_) == c : T}` with the other proof below it, which names the motive once and drops the middle term."} : F.Finding}

# LAW: a `# noqa` that names no code is cited where the mark is, over the
# mark's length
law noqa_cites_bare_mark:
  for line: U32
  for col: U32
  for len: U32
  for +whole: Bool
  for +path: String
  for +gs: List<&2, F.Graded>
  {NoqaRule.check.mark(Noqa.Mark{line, col, len, Nil{}}, whole, path, gs)
    == [F.Finding{path, line, col, len, "noqa", NoqaRule.say.bare()}] : List<&2, F.Finding>}

# LAW: thunk cites the self-call at its name, over the name's length
law thunk_cites_self_call:
  for +ll: U32
  for +cc: U32
  for +name: String
  for +path: String
  {Thunk.cite(ll, cc, name, path) == F.Finding{path, ll, cc, U32.from_nat(String.length(name)), "thunk",
    name ++ " calls itself inside a thunk, which allocates a closure and leaves the loop on every step; carry the test as a Bool into the next call (`go(rest, k, test(h))`) and match on it first, so the search stays a loop."} : F.Finding}

# LAW: prefix cites a run at the position it is handed, over nine chars, with
# the words it is handed, before the rest
law prefix_cites_run:
  for msg: String
  for +path: String
  for +ll: U32
  for +cc: U32
  for more: List<&2, F.Finding>
  {Prefix.hit(Some{msg}, path, ll, cc, more) == F.Finding{path, ll, cc, 9, "prefix", msg} <> more
    : List<&2, F.Finding>}

# LAW: no run adds nothing
law prefix_passes_no_run:
  for +path: String
  for +ll: U32
  for +cc: U32
  for more: List<&2, F.Finding>
  {Prefix.hit(None{}, path, ll, cc, more) == more : List<&2, F.Finding>}

# LAW: empty cites a test at the test's own position, over nine chars, with
# the test's own words, before the rest
law empty_cites_test:
  for ll: U32
  for cc: U32
  for msg: String
  for +path: String
  for more: List<&2, F.Finding>
  {Empty.hit(Some{Empty.Hit{ll, cc, msg}}, path, more) == F.Finding{path, ll, cc, 9, "empty", msg} <> more
    : List<&2, F.Finding>}

# LAW: no test adds nothing
law empty_passes_no_test:
  for +path: String
  for more: List<&2, F.Finding>
  {Empty.hit(None{}, path, more) == more : List<&2, F.Finding>}

# LAW: rewalk cites the first narrow site of a call made twice, where and as
# long as it is handed, naming the call
law rewalk_cites_first_site:
  for +name: String
  for +line: U32
  for +col: U32
  for +len: U32
  for +path: String
  {Rewalk.report_fresh(False{}, name, line, col, len, path) == [F.Finding{path, line, col, len, "rewalk",
    name ++ " is called twice on the same argument, and one result is used only for a single value; take that value from the other result."}]
    : List<&2, F.Finding>}

# LAW: a site already reported is not reported again
law rewalk_reports_once:
  for +name: String
  for +line: U32
  for +col: U32
  for +len: U32
  for +path: String
  {Rewalk.report_fresh(True{}, name, line, col, len, path) == Nil{} : List<&2, F.Finding>}

# LAW: wrap cites a return type off the `)` line on its own line of the header, counted from the
# header's first line, at its column, with no length, before the rest
law wrap_cites_loose_return:
  for +line: U32
  for end: U32
  for +col: U32
  for +base: U32
  for +path: String
  for +more: List<&2, F.Finding>
  {Wrap.check.place_loose(Some{Wrap.Span{line, end, col}}, base, path, more)
    == F.Finding{path, (base + line : U32), col, 0, "wrap",
    "The return type is not on the `)` line; write `) -> T` on one line."}
      <> more : List<&2, F.Finding>}

# LAW: with none, the next shape is looked for
law wrap_cites_loose_return_or_next:
  for +base: U32
  for +path: String
  for +more: List<&2, F.Finding>
  {Wrap.check.place_loose(None{}, base, path, more)
    == more : List<&2, F.Finding>}

# LAW: wrap cites a `)` on the last parameter's line on its own line of the header, counted from the
# header's first line, at its column, with no length, before the rest
law wrap_cites_shut_paren:
  for +line: U32
  for end: U32
  for +col: U32
  for loose: Maybe<&2, Wrap.Span>
  for +base: U32
  for +path: String
  for +more: List<&2, F.Finding>
  {Wrap.check.place_shut(Some{Wrap.Span{line, end, col}}, loose, base, path, more)
    == F.Finding{path, (base + line : U32), col, 0, "wrap",
    "The `)` shares a line with the last parameter; put `)` and the return type on a line of their own."}
      <> more : List<&2, F.Finding>}

# LAW: with none, the next shape is looked for
law wrap_cites_shut_paren_or_next:
  for loose: Maybe<&2, Wrap.Span>
  for +base: U32
  for +path: String
  for +more: List<&2, F.Finding>
  {Wrap.check.place_shut(None{}, loose, base, path, more)
    == Wrap.check.place_loose(loose, base, path, more) : List<&2, F.Finding>}

# LAW: wrap cites an empty parameter list across lines on its own line of the header, counted from the
# header's first line, at its column, with no length, before the rest
law wrap_cites_empty_list:
  for +line: U32
  for end: U32
  for +col: U32
  for shut: Maybe<&2, Wrap.Span>
  for loose: Maybe<&2, Wrap.Span>
  for +base: U32
  for +path: String
  for +more: List<&2, F.Finding>
  {Wrap.check.place_empty(Some{Wrap.Span{line, end, col}}, shut, loose, base, path, more)
    == F.Finding{path, (base + line : U32), col, 0, "wrap",
    "This def header has no parameters but spans several lines; put it on one line."}
      <> more : List<&2, F.Finding>}

# LAW: with none, the next shape is looked for
law wrap_cites_empty_list_or_next:
  for shut: Maybe<&2, Wrap.Span>
  for loose: Maybe<&2, Wrap.Span>
  for +base: U32
  for +path: String
  for +more: List<&2, F.Finding>
  {Wrap.check.place_empty(None{}, shut, loose, base, path, more)
    == Wrap.check.place_shut(shut, loose, base, path, more) : List<&2, F.Finding>}

# LAW: wrap cites the parameter that breaks one a line on its own line of the header, counted from the
# header's first line, at its column, with no length, before the rest
law wrap_cites_jammed_parameter:
  for +line: U32
  for end: U32
  for +col: U32
  for empty: Maybe<&2, Wrap.Span>
  for shut: Maybe<&2, Wrap.Span>
  for loose: Maybe<&2, Wrap.Span>
  for +base: U32
  for +path: String
  for +more: List<&2, F.Finding>
  {Wrap.check.place(Some{Wrap.Span{line, end, col}}, empty, shut, loose, base, path, more)
    == F.Finding{path, (base + line : U32), col, 0, "wrap",
    "This wrapped def header does not have one parameter per line; put each parameter on its own line."}
      <> more : List<&2, F.Finding>}

# LAW: with none, the next shape is looked for
law wrap_cites_jammed_parameter_or_next:
  for empty: Maybe<&2, Wrap.Span>
  for shut: Maybe<&2, Wrap.Span>
  for loose: Maybe<&2, Wrap.Span>
  for +base: U32
  for +path: String
  for +more: List<&2, F.Finding>
  {Wrap.check.place(None{}, empty, shut, loose, base, path, more)
    == Wrap.check.place_empty(empty, shut, loose, base, path, more) : List<&2, F.Finding>}
