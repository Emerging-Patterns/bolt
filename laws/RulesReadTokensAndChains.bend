# What the rules that are on by default read off tokens and chains before
# they decide: where a pattern ends, what a literal's chars are, whether a
# string is closed, which lines are imports, how many angle brackets a run of
# `>` closes, what a fixed table looks like, whether a value is read again,
# whether a def is a proof. Each rule's own law file says what the rule
# reports given these; this file says what these are, one step or one case
# at a time. A search that finds nothing answers no, and each such end is
# stated over an input with a hypothesis, since a law must bind something.
import Base
import ../src/finding.bend as F
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/table.bend as Table
import ../src/rules/correctness/arms.bend as Arms
import ../src/rules/correctness/escape.bend as Escape
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/perf/strings.bend as Strings
import ../src/rules/style/blank.bend as Blank
import ../src/rules/style/space.bend as Space
import ../src/rules/style/wrap.bend as Wrap
import ../src/rules/suspicious/concat.bend as Concat
import ../src/rules/suspicious/empty.bend as Empty
import ./defs/TokenKinds.bend as D1
import ./defs/Chains.bend as D2

# arms: a pattern ends among its own nodes at a `:`
# LAW: a `:` leaf ends the pattern
law arms_ended_at_colon:
  for t: String
  for l: U32
  for c: U32
  for rest: Tree.Node
  {Arms.ended(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}}, rest}) == True{} : Bool}

# LAW: any other node is passed over
law arms_ended_passes_other:
  for h: Tree.Node
  for rest: Tree.Node
  for e: {D2.chains.node_of(h, [Lex.TColon{}]) == False{} : Bool}
  {Arms.ended(Tree.NCons{h, rest}) == Arms.ended(rest) : Bool}

# LAW: a pattern with no node left has not ended: its last part wrapped onto
# the next line
law arms_ended_needs_colon:
  for pat: Tree.Node
  for e: {D2.chains.is_cons(pat) == False{} : Bool}
  {Arms.ended(pat) == False{} : Bool}

# LAW: tokens open with a text as the kind wanted when the first token is of
# that kind and has that text
law arms_opens_as_kind_and_text:
  for want: Bool
  for +t: String
  for +text: String
  {Arms.opens.as(want, t, text) == Bool.and(want, String.eq(t, text)) : Bool}

# LAW: tokens open with the operator `+` when their first token is one
law arms_opens_plus_first:
  for k: Lex.TokKind
  for t: String
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  {Arms.opens.plus(Lex.Tok{k, t, l, c} <> rest) == Arms.opens.as(Arms.opens.op(k), t, "+") : Bool}

# LAW: no tokens open with nothing
law arms_opens_plus_needs_token:
  for toks: List<&2, Lex.Tok>
  for e: {List.is_empty(&2, Lex.Tok, toks) == True{} : Bool}
  {Arms.opens.plus(toks) == False{} : Bool}

# LAW: in a list pattern, a `<>` after an item wants the next item, and the
# pattern is still a chain
law arms_skip_after_item:
  for rest: List<&2, Arms.Part>
  {Arms.skip(Arms.PCons{} <> rest, Arms.SGot{}, True{}) == Arms.skip(rest, Arms.SWant{}, True{})
    : Maybe<&2, List<&2, Arms.Part>>}

# LAW: and the same after a bare word
law arms_skip_after_word:
  for rest: List<&2, Arms.Part>
  {Arms.skip(Arms.PCons{} <> rest, Arms.SWord{}, True{}) == Arms.skip(rest, Arms.SWant{}, True{})
    : Maybe<&2, List<&2, Arms.Part>>}

# LAW: with no n+p arm above, the Nat check reports no arm
law arms_told_needs_wide_arm:
  for a: Arms.Arm
  {Arms.told(None{}, a) == False{} : Bool}

# LAW: an arm that is neither a literal nor an n+p is never reported by it
law arms_told_skips_other_arms:
  for w2: Arms.Wide
  {Arms.told(Some{w2}, Arms.AOther{}) == False{} : Bool}

# LAW: under an n+p arm that starts at k, a later n+p arm is reported
# exactly when it starts at k or above: every Nat it matches is matched
# already
law arms_told_plus_from_k:
  for +k: U32
  for text: String
  for +j: U32
  for t: String
  for l: U32
  for c: U32
  for n: U32
  {Arms.told(Some{Arms.Wide{k, text}}, Arms.APlus{j, t, l, c, n}) == U32.is_ge(j, k) : Bool}

# LAW: and a later literal arm exactly when the literal is k or above
law arms_told_literal_from_k:
  for +k: U32
  for text: String
  for +m: U32
  for l: U32
  for c: U32
  for n: U32
  {Arms.told(Some{Arms.Wide{k, text}}, Arms.ALit{m, l, c, n}) == U32.is_ge(m, k) : Bool}

# arms: an operator in a pattern, as the part it is
# LAW: a `+` (a quantity mark, or the plus of `kn+`) is no part of its own
law arms_plus_is_no_part:
  for +more: List<&2, Arms.Part>
  {Arms.part.op("+", more) == more : List<&2, Arms.Part>}

# LAW: a `<>` is the cons between two items
law arms_cons_is_a_part:
  for +more: List<&2, Arms.Part>
  {Arms.part.op("<>", more) == Arms.PCons{} <> more : List<&2, Arms.Part>}

# LAW: any other operator is not understood, so the pattern covers nothing
law arms_other_operator_is_bad:
  for +t: String
  for +more: List<&2, Arms.Part>
  for e1: {String.eq(t, "+") == False{} : Bool}
  for e2: {String.eq(t, "<>") == False{} : Bool}
  {Arms.part.op(t, more) == Arms.PBad{} <> more : List<&2, Arms.Part>}

# escape: a literal's chars as the four things the rule tells apart
# LAW: a backslash, a `0`, a digit from 1 to 9, and any other char
law escape_sym_by_code:
  for +x: U32
  {Escape.sym(Chr{x})
    == Bool.pick(Escape.Sym, U32.is_eq(x, 92), Escape.SSlash{},
      Bool.pick(Escape.Sym, U32.is_eq(x, 48), Escape.SZero{},
        Bool.pick(Escape.Sym, Bool.and(U32.is_ge(x, 49), U32.is_le(x, 57)), Escape.SDigit{Chr{x}},
          Escape.SOther{Chr{x}}))) : Escape.Sym}

# LAW: every char is read, in order
law escape_syms_in_order:
  for c: Char
  for t: List<&2, Char>
  {Escape.syms(c <> t) == Escape.sym(c) <> Escape.syms(t) : List<&2, Escape.Sym>}

# pick: a chain that is one name alone
# LAW: a chain that starts with a leaf is the name alone when the leaf's
# text is the name and nothing follows it
law pick_lone_is_one_leaf:
  for k: Lex.TokKind
  for t: String
  for l: U32
  for c: U32
  for rest: Tree.Node
  for +x: String
  {Pick.search.lone(Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, rest}, x)
    == Bool.and(String.eq(t, x), Pick.search.empty(rest))
    : Bool}

# LAW: what is no chain is no name
law pick_lone_needs_a_chain:
  for n: Tree.Node
  for +x: String
  for e: {D2.chains.is_cons(n) == False{} : Bool}
  {Pick.search.lone(n, x) == False{} : Bool}

# strings: is a string token closed
# LAW: reading a char, the next is escaped when this one is an unescaped
# backslash, and the text has just shut when this one is an unescaped quote
law strings_closes_reads_escapes:
  for ch: Char
  for rest: List<&2, Char>
  for +esc: Bool
  for +shut: Bool
  {Strings.closes(ch <> rest, esc, shut)
    == Strings.closes(rest, Bool.and(Bool.not(esc), U32.is_eq(Char.to_u32(ch), 92)),
      Bool.and(Bool.not(esc), U32.is_eq(Char.to_u32(ch), 34))) : Bool}

# LAW: the text ends closed exactly when its last char shut it
law strings_closes_at_the_end:
  for +esc: Bool
  for shut: Bool
  {Strings.closes(Nil{}, esc, shut) == shut : Bool}

# LAW: past its opening char, a text is read with nothing escaped and
# nothing shut
law strings_opened_past_first_char:
  for q: Char
  for rest: List<&2, Char>
  {Strings.opened(q <> rest) == Strings.closes(rest, False{}, False{}) : Bool}

# LAW: no chars are no closed string
law strings_opened_needs_chars:
  for cs: List<&2, Char>
  for e: {List.is_empty(&2, Char, cs) == True{} : Bool}
  {Strings.opened(cs) == False{} : Bool}

# blank: a test against the empty string literal
# LAW: the literal `""` is a string token whose text is its two quotes
law blank_lit_is_two_quotes:
  for k: Lex.TokKind
  for t: String
  {Blank.lit(k, t) == Bool.and(D1.kinds.among(k, [Lex.TStr{}]), String.eq(t, "\"\"")) : Bool}

# LAW: the name compared is the first argument when it is a plain name and
# the second is `""`, else the second when the first is `""` and it is a
# plain name, else none
law blank_name_either_side:
  for +ka: Lex.TokKind
  for +ta: String
  for +kb: Lex.TokKind
  for +tb: String
  {Blank.name(ka, ta, kb, tb)
    == Bool.pick(Maybe<&2, String>, Bool.and(Empty.plain(ka), Blank.lit(kb, tb)), Some{ta},
      Bool.pick(Maybe<&2, String>, Bool.and(Blank.lit(ka, ta), Empty.plain(kb)), Some{tb}, None{}))
    : Maybe<&2, String>}

# space: a line's width counts no import line
# LAW: a newline is kept, and the token after it opens a line that is not
# yet being cut
law space_unimported_keeps_newline:
  for t: String
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  for start: Bool
  for cutting: Bool
  {Space.unimported(Lex.Tok{Lex.TNewline{}, t, l, c} <> rest, start, cutting)
    == Lex.Tok{Lex.TNewline{}, t, l, c} <> Space.unimported(rest, True{}, False{}) : List<&2, Lex.Tok>}

# LAW: any other token is cut when its line is being cut or when it opens
# its line and is `import`; else it is kept and the line is not cut
law space_unimported_cuts_import_lines:
  for +k: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for +rest: List<&2, Lex.Tok>
  for start: Bool
  for cutting: Bool
  for e: {D1.kinds.among(k, [Lex.TNewline{}]) == False{} : Bool}
  {Space.unimported(Lex.Tok{k, t, l, c} <> rest, start, cutting)
    == Bool.pick(List<&2, Lex.Tok>, Bool.or(cutting, Bool.and(start, String.eq(t, "import"))),
      Space.unimported(rest, False{}, True{}), Lex.Tok{k, t, l, c} <> Space.unimported(rest, False{}, False{}))
    : List<&2, Lex.Tok>}

# wrap: a run of `>` closes that many angle brackets
# LAW: chars are all `>` when the first is and the rest are
law wrap_gt_chars_each:
  for +c: Char
  for t: List<&2, Char>
  {Wrap.check.gt_chars(c <> t) == Bool.and(Char.is_eq(c, '>'), Wrap.check.gt_chars(t)) : Bool}

# LAW: no chars are all `>`
law wrap_gt_chars_of_none:
  for cs: List<&2, Char>
  for e: {List.is_empty(&2, Char, cs) == True{} : Bool}
  {Wrap.check.gt_chars(cs) == True{} : Bool}

# LAW: a text is a run of `>` when it is not empty and all its chars are
law wrap_all_gt_not_empty:
  for +tx: String
  {Wrap.check.all_gt(tx) == Bool.and(Bool.not(String.is_empty(tx)), Wrap.check.gt_chars(String.to_list(tx))) : Bool}

# LAW: a run of `>` closes as many angle brackets as it has chars, and any
# other text closes none
law wrap_ticks_of_run:
  for +tx: String
  {Wrap.check.ticks_of(tx)
    == Bool.pick(Nat, Wrap.check.all_gt(tx), Wrap.check.gt_count(String.to_list(tx)), 0n) : Nat}

# LAW: `<` or `<&` opens type arguments only when glued to what is before it
law wrap_angle_opens_when_glued:
  for glued: Bool
  for +tx: String
  {Wrap.check.opens_angle(glued, tx) == Bool.and(glued, Bool.or(String.eq(tx, "<"), String.eq(tx, "<&"))) : Bool}

# is an act the parameter list's own `(`, `)` or comma? Law vocabulary: bolt
# never calls it
def wraps.is_sep(act: Wrap.Act) -> Bool:
  match act:
    case Wrap.AOpen{}:
      True{}
    case Wrap.AParen{}:
      False{}
    case Wrap.AEnd{}:
      True{}
    case Wrap.AUnparen{}:
      False{}
    case Wrap.ABrack{}:
      False{}
    case Wrap.AUnbrack{}:
      False{}
    case Wrap.ABrace{}:
      False{}
    case Wrap.AUnbrace{}:
      False{}
    case Wrap.AAngle{}:
      False{}
    case Wrap.AUnangle{}:
      False{}
    case Wrap.AComma{}:
      True{}
    case Wrap.AArrow{}:
      False{}
    case Wrap.AStray{}:
      False{}
    case Wrap.ANone{}:
      False{}

# LAW: the list's own `(`, `)` and commas are no part of a parameter, and
# every other act is
law wrap_separators:
  for act: Wrap.Act
  {Wrap.check.is_sep(act) == wraps.is_sep(act) : Bool}

# concat: a parameter marked `+`
# LAW: a parameter's chain opens with `+` when its first node is the operator
# `+`
law concat_plus_first_operator:
  for +h: Tree.Node
  for rest: Tree.Node
  {Concat.plus(Tree.NCons{h, rest})
    == Bool.and(Calls.kind.leaf(~Calls.kind.oper, h), String.eq(Calls.leaf.text(h), "+")) : Bool}

# LAW: what is no chain opens with nothing
law concat_plus_needs_a_chain:
  for p: Tree.Node
  for e: {D2.chains.is_cons(p) == False{} : Bool}
  {Concat.plus(p) == False{} : Bool}

# table: what a fixed table looks like
# LAW: a top-level token is not looked for inside a group
law table_top_has_skips_groups:
  for open: Lex.Tok
  for kids: Tree.Node
  for close: Maybe<&2, Lex.Tok>
  for rest: Tree.Node
  for +want: String
  {Table.top_has(Tree.NCons{Tree.Group{open, kids, close}, rest}, want) == Table.top_has(rest, want) : Bool}

# LAW: a leaf is the token wanted when its text is, or the rest holds one
law table_top_has_reads_leaves:
  for k: Lex.TokKind
  for t: String
  for l: U32
  for c: U32
  for rest: Tree.Node
  for +want: String
  {Table.top_has(Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, rest}, want)
    == Bool.or(String.eq(t, want), Table.top_has(rest, want))
    : Bool}

# LAW: what is no chain holds no token
law table_top_has_needs_a_chain:
  for n: Tree.Node
  for +want: String
  for e: {D2.chains.is_cons(n) == False{} : Bool}
  {Table.top_has(n, want) == False{} : Bool}

# LAW: what is no chain is no sized array
law table_array_sized_needs_a_chain:
  for n: Tree.Node
  for e: {D2.chains.is_cons(n) == False{} : Bool}
  {Table.array_sized(n) == False{} : Bool}

# LAW: what is no chain is no built table
law table_built_needs_a_chain:
  for n: Tree.Node
  for e: {D2.chains.is_cons(n) == False{} : Bool}
  {Table.built(n) == False{} : Bool}

# LAW: a chain of one number leaf is a lone number
law table_lone_num_one_number:
  for t: String
  for l: U32
  for c: U32
  {Table.lone_num(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}}, Tree.NNil{}}) == True{} : Bool}

# LAW: what is no chain is no number
law table_lone_num_needs_a_chain:
  for n: Tree.Node
  for e: {D2.chains.is_cons(n) == False{} : Bool}
  {Table.lone_num(n) == False{} : Bool}

# LAW: `List.range`'s count is its last argument: one argument is a count
# when it is a lone number
law table_range_count_last_argument:
  for h: Tree.Node
  {Table.range_count(h <> Nil{}) == Table.lone_num(h) : Bool}

# LAW: no arguments give no count
law table_range_count_needs_arguments:
  for as: List<&2, Tree.Node>
  for e: {List.is_empty(&2, Tree.Node, as) == True{} : Bool}
  {Table.range_count(as) == False{} : Bool}

# LAW: table reports a call exactly when it is `List.get` or `List.set`
# applied (open), its index is no literal, and its table is one of the fixed
# ones; the finding is the call's, over its name
law table_hits_get_and_set:
  for +open: Bool
  for +t: String
  for kids: Tree.Node
  for +fixed: List<&2, String>
  for +path: String
  for +line: U32
  for +col: U32
  {Table.hit(open, t, kids, fixed, path, line, col)
    == Bool.pick(List<&2, F.Finding>,
      Bool.and(Bool.and(open, Bool.or(String.eq(t, "List.get"), String.eq(t, "List.set"))),
        Bool.and(Bool.not(Table.literal(Calls.arg(Calls.args(kids), 3n))),
          Table.owns(Calls.arg(Calls.args(kids), 2n), fixed))),
      [Table.cite(String.eq(t, "List.get"), path, line, col, U32.from_nat(String.length(t)))], [])
    : List<&2, F.Finding>}

# empty: is the value read again after the test
# LAW: a token closes the arguments at depth zero when it is a closing
# bracket
law empty_close_here_at_depth_zero:
  for k: Lex.TokKind
  {Empty.close.here(k, 0n) == D1.kinds.among(k, [Lex.TClose{}]) : Bool}

# LAW: and no token closes them deeper in
law empty_close_here_not_deeper:
  for k: Lex.TokKind
  for p: Nat
  {Empty.close.here(k, 1n+p) == False{} : Bool}

# LAW: once the value has been read, it is kept
law empty_kept_once_found:
  for +k: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  for +x: String
  for +d: Nat
  for live: Bool
  {Empty.kept(Lex.Tok{k, t, l, c} <> rest, x, d, True{}, live) == True{} : Bool}

# LAW: past the bracket that closes the group, it is not looked for
law empty_kept_stops_at_close:
  for +k: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  for +x: String
  for +d: Nat
  {Empty.kept(Lex.Tok{k, t, l, c} <> rest, x, d, False{}, False{}) == False{} : Bool}

# LAW: before it, each token is read: is it the value, and is it the bracket
# that closes the group
law empty_kept_reads_on:
  for +k: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  for +x: String
  for +d: Nat
  {Empty.kept(Lex.Tok{k, t, l, c} <> rest, x, d, False{}, True{})
    == Empty.kept(rest, x, Empty.close.depth(k, d), Empty.same(k, t, x), Bool.not(Empty.close.here(k, d))) : Bool}

# LAW: with no token left, the value is kept when the last token was it
law empty_kept_at_the_end:
  for +x: String
  for +d: Nat
  for found: Bool
  for live: Bool
  {Empty.kept(Nil{}, x, d, found, live) == found : Bool}

# LAW: a def whose parameters are followed by `:` writes no return type, so
# it is a proof
law empty_proofy_head_colon:
  for +k2: Lex.TokKind
  for +t2: String
  {Empty.proofy.head(Lex.TColon{}, k2, t2) == True{} : Bool}

# LAW: one followed by `->` is a proof when a `{` comes next
law empty_proofy_head_arrow:
  for +k2: Lex.TokKind
  for +t2: String
  {Empty.proofy.head(Lex.TArrow{}, k2, t2) == String.eq(Empty.code(k2, t2), "{") : Bool}

# LAW: one followed by anything else is not
law empty_proofy_head_other:
  for k1: Lex.TokKind
  for +k2: Lex.TokKind
  for +t2: String
  for e: {D1.kinds.among(k1, [Lex.TColon{}, Lex.TArrow{}]) == False{} : Bool}
  {Empty.proofy.head(k1, k2, t2) == False{} : Bool}

# LAW: the header's end is read off the two tokens after the parameters
law empty_proofy_end_two_tokens:
  for k1: Lex.TokKind
  for t1: String
  for l1: U32
  for c1: U32
  for k2: Lex.TokKind
  for t2: String
  for l2: U32
  for c2: U32
  for rest: List<&2, Lex.Tok>
  {Empty.proofy.end(Lex.Tok{k1, t1, l1, c1} <> Lex.Tok{k2, t2, l2, c2} <> rest) == Empty.proofy.head(k1, k2, t2)
    : Bool}

# LAW: with one token left, it is read with nothing after it
law empty_proofy_end_one_token:
  for k1: Lex.TokKind
  for t1: String
  for l1: U32
  for c1: U32
  {Empty.proofy.end(Lex.Tok{k1, t1, l1, c1} <> Nil{}) == Empty.proofy.head(k1, Lex.TSpace{}, "") : Bool}

# LAW: with none, the def is no proof
law empty_proofy_end_needs_token:
  for toks: List<&2, Lex.Tok>
  for e: {List.is_empty(&2, Lex.Tok, toks) == True{} : Bool}
  {Empty.proofy.end(toks) == False{} : Bool}

# LAW: a token closes the parameters when it is a closing bracket at depth
# one
law empty_proofy_fin_at_depth_one:
  for k: Lex.TokKind
  {Empty.proofy.fin(k, 1n) == D1.kinds.among(k, [Lex.TClose{}]) : Bool}

# LAW: not at depth zero
law empty_proofy_fin_not_at_zero:
  for k: Lex.TokKind
  {Empty.proofy.fin(k, 0n) == False{} : Bool}

# LAW: and not deeper than one
law empty_proofy_fin_not_deeper:
  for k: Lex.TokKind
  for p: Nat
  {Empty.proofy.fin(k, 1n+1n+p) == False{} : Bool}

# LAW: right after the bracket that closes the parameters, the header's end
# decides
law empty_proofy_decides_after_parameters:
  for +k: Lex.TokKind
  for t: String
  for l: U32
  for c: U32
  for +rest: List<&2, Lex.Tok>
  for +d: Nat
  {Empty.proofy(Lex.Tok{k, t, l, c} <> rest, d, True{}) == Empty.proofy.end(Lex.Tok{k, t, l, c} <> rest) : Bool}

# LAW: before it, each token is read for its depth and for whether it is
# that bracket
law empty_proofy_reads_on:
  for +k: Lex.TokKind
  for t: String
  for l: U32
  for c: U32
  for +rest: List<&2, Lex.Tok>
  for +d: Nat
  {Empty.proofy(Lex.Tok{k, t, l, c} <> rest, d, False{})
    == Empty.proofy(rest, Empty.close.depth(k, d), Empty.proofy.fin(k, d)) : Bool}

# LAW: a header with no tokens is no proof
law empty_proofy_needs_tokens:
  for toks: List<&2, Lex.Tok>
  for +d: Nat
  for fin: Bool
  for e: {List.is_empty(&2, Lex.Tok, toks) == True{} : Bool}
  {Empty.proofy(toks, d, fin) == False{} : Bool}

# LAW: after a keyword that is no def, tokens are skipped from `law` on, read
# again from `type` or `import`, and otherwise as before
law empty_item_other_by_keyword:
  for +word: String
  for skip: Bool
  {Empty.item.other(word, skip)
    == Bool.pick(Bool, String.eq(word, "law"), True{},
      Bool.pick(Bool, Bool.or(String.eq(word, "type"), String.eq(word, "import")), False{}, skip)) : Bool}

# concat: how many times a plain name is read
# LAW: a name leaf that spells the name is one read of it
law concat_uses_counts_the_name:
  for +t: String
  for l: U32
  for c: U32
  for +name: String
  for e: {String.eq(t, name) == True{} : Bool}
  {Concat.uses(Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, name) == 1n : Nat}

# LAW: a name leaf that spells another name is none
law concat_uses_skips_other_names:
  for +t: String
  for l: U32
  for c: U32
  for +name: String
  for e: {String.eq(t, name) == False{} : Bool}
  {Concat.uses(Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, name) == 0n : Nat}

# table: the names in scope without one
# LAW: the name itself is dropped, wherever it stands
law table_drop_takes_the_name:
  for +h: String
  for +rest: List<&2, String>
  for +nm: String
  for e: {String.eq(h, nm) == True{} : Bool}
  {Table.drop(h <> rest, nm) == Table.drop(rest, nm) : List<&2, String>}

# LAW: every other name stays, in order
law table_drop_keeps_other_names:
  for +h: String
  for +rest: List<&2, String>
  for +nm: String
  for e: {String.eq(h, nm) == False{} : Bool}
  {Table.drop(h <> rest, nm) == h <> Table.drop(rest, nm) : List<&2, String>}

# wrap: an operator's angle motion in a header
# LAW: a run of `>` closes angles, unless the operator opens one
law wrap_gt_run_closes_angles:
  for +tx: String
  for glued: Bool
  for e: {Wrap.check.all_gt(tx) == True{} : Bool}
  {Wrap.check.op_angle(tx, glued) == Wrap.check.prefer_open(Wrap.check.opens_angle(glued, tx), Wrap.AUnangle{})
    : Wrap.Act}

# LAW: any other operator moves no angle, unless it opens one
law wrap_other_operator_moves_no_angle:
  for +tx: String
  for glued: Bool
  for e: {Wrap.check.all_gt(tx) == False{} : Bool}
  {Wrap.check.op_angle(tx, glued) == Wrap.check.prefer_open(Wrap.check.opens_angle(glued, tx), Wrap.ANone{})
    : Wrap.Act}

# pick: a term's text, as two searches are compared by it
# LAW: a leaf is its token and then a space
law pick_search_text_of_a_leaf:
  for k: Lex.TokKind
  for t: String
  for l: U32
  for c: U32
  {Pick.search.text(Tree.Leaf{Lex.Tok{k, t, l, c}}) == t ++ " " : String}

# LAW: a group is its open bracket, a space, and then what it holds
law pick_search_text_of_a_group:
  for k: Lex.TokKind
  for o: String
  for l: U32
  for c: U32
  for kids: Tree.Node
  for cl: Maybe<&2, Lex.Tok>
  {Pick.search.text(Tree.Group{Lex.Tok{k, o, l, c}, kids, cl}) == o ++ " " ++ Pick.search.text(kids) : String}

# table: one use of a name, told apart from its other uses
# LAW: a use's key is its name, an `@`, and where it stands
law table_key_is_name_and_place:
  for +t: String
  for +line: U32
  for +col: U32
  {Table.key(t, line, col) == t ++ "@" ++ U32.show(line) ++ ":" ++ U32.show(col) : String}
