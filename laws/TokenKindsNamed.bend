# The lexer gives every token one of twenty-two kinds, and the binder, the
# outline and the rules each ask small questions of a kind: is it a name, a
# colon, something a call can start with. Each question is one def, and each
# holds for exactly the kinds listed here. A rule's own law reads these as
# its vocabulary, so this is where that vocabulary is said: a question that
# starts to hold for another kind changes what every law built on it means,
# and has to change here first.
import Base
import ../src/syntax/lex.bend as Lex
import ./defs/TokenKinds.bend as D1
import ../src/rules/calls.bend as Calls
import ../src/rules/correctness/arms.bend as Arms
import ../src/rules/correctness/put.bend as Put
import ../src/rules/pedantic/strict.bend as Strict
import ../src/rules/style/wrap.bend as Wrap
import ../src/rules/suspicious/concat.bend as Concat
import ../src/rules/suspicious/eager.bend as Eager
import ../src/rules/suspicious/empty.bend as Empty
import ../src/rules/suspicious/prefix.bend as Prefix
import ../src/syntax/bind.bend as Bind
import ../src/syntax/outline.bend as Outline

# LAW: Calls.kind.arrow holds for exactly a `->`
law calls_kind_arrow_kinds:
  for kk: Lex.TokKind
  {Calls.kind.arrow(kk) == D1.kinds.among(kk, [Lex.TArrow{}]) : Bool}

# LAW: Calls.kind.colon holds for exactly a `:`
law calls_kind_colon_kinds:
  for kk: Lex.TokKind
  {Calls.kind.colon(kk) == D1.kinds.among(kk, [Lex.TColon{}]) : Bool}

# LAW: Calls.kind.oper holds for exactly an operator
law calls_kind_oper_kinds:
  for kk: Lex.TokKind
  {Calls.kind.oper(kk) == D1.kinds.among(kk, [Lex.TOp{}]) : Bool}

# LAW: Calls.kind.upper holds for exactly a capitalized name
law calls_kind_upper_kinds:
  for kk: Lex.TokKind
  {Calls.kind.upper(kk) == D1.kinds.among(kk, [Lex.TUpper{}]) : Bool}

# LAW: Arms.binder holds for exactly a name and a `_` name
law arms_binder_kinds:
  for kk: Lex.TokKind
  {Arms.binder(kk) == D1.kinds.among(kk, [Lex.TName{}, Lex.TWild{}]) : Bool}

# LAW: Arms.opens.op holds for exactly an operator
law arms_opens_op_kinds:
  for kk: Lex.TokKind
  {Arms.opens.op(kk) == D1.kinds.among(kk, [Lex.TOp{}]) : Bool}

# LAW: Arms.opens.open holds for exactly an opening bracket
law arms_opens_open_kinds:
  for kk: Lex.TokKind
  {Arms.opens.open(kk) == D1.kinds.among(kk, [Lex.TOpen{}]) : Bool}

# LAW: Put.calls.dotted holds for exactly a dotted name
law put_calls_dotted_kinds:
  for kk: Lex.TokKind
  {Put.calls.dotted(kk) == D1.kinds.among(kk, [Lex.TDotted{}]) : Bool}

# LAW: Put.defines.key holds for exactly a keyword
law put_defines_key_kinds:
  for kk: Lex.TokKind
  {Put.defines.key(kk) == D1.kinds.among(kk, [Lex.TKey{}]) : Bool}

# LAW: Strict.seg_op.ends holds for exactly a `=>` and a comma
law strict_seg_op_ends_kinds:
  for kk: Lex.TokKind
  {Strict.seg_op.ends(kk) == D1.kinds.among(kk, [Lex.TLam{}, Lex.TComma{}]) : Bool}

# LAW: Wrap.check.is_arrow holds for exactly a `->`
law wrap_check_is_arrow_kinds:
  for kk: Lex.TokKind
  {Wrap.check.is_arrow(kk) == D1.kinds.among(kk, [Lex.TArrow{}]) : Bool}

# LAW: Wrap.check.is_colon holds for exactly a `:`
law wrap_check_is_colon_kinds:
  for kk: Lex.TokKind
  {Wrap.check.is_colon(kk) == D1.kinds.among(kk, [Lex.TColon{}]) : Bool}

# LAW: Wrap.check.is_op holds for exactly an operator
law wrap_check_is_op_kinds:
  for kk: Lex.TokKind
  {Wrap.check.is_op(kk) == D1.kinds.among(kk, [Lex.TOp{}]) : Bool}

# LAW: Concat.bound.eq holds for exactly a `=`
law concat_bound_eq_kinds:
  for kk: Lex.TokKind
  {Concat.bound.eq(kk) == D1.kinds.among(kk, [Lex.TEq{}]) : Bool}

# LAW: Eager.work.name holds for every kind but a `=>` and a comma
law eager_work_name_kinds:
  for kk: Lex.TokKind
  {Eager.work.name(kk) == Bool.not(D1.kinds.among(kk, [Lex.TLam{}, Lex.TComma{}])) : Bool}

# LAW: Empty.dotted holds for exactly a dotted name
law empty_dotted_kinds:
  for kk: Lex.TokKind
  {Empty.dotted(kk) == D1.kinds.among(kk, [Lex.TDotted{}]) : Bool}

# LAW: Empty.opener holds for exactly an opening bracket and a comma
law empty_opener_kinds:
  for kk: Lex.TokKind
  {Empty.opener(kk) == D1.kinds.among(kk, [Lex.TOpen{}, Lex.TComma{}]) : Bool}

# LAW: Empty.plain holds for exactly a name
law empty_plain_kinds:
  for kk: Lex.TokKind
  {Empty.plain(kk) == D1.kinds.among(kk, [Lex.TName{}]) : Bool}

# LAW: Prefix.dotted holds for exactly a dotted name
law prefix_dotted_kinds:
  for kk: Lex.TokKind
  {Prefix.dotted(kk) == D1.kinds.among(kk, [Lex.TDotted{}]) : Bool}

# LAW: Bind.declared.is_key holds for exactly a keyword
law bind_declared_is_key_kinds:
  for kk: Lex.TokKind
  {Bind.declared.is_key(kk) == D1.kinds.among(kk, [Lex.TKey{}]) : Bool}

# LAW: Bind.declared.is_name holds for exactly a name, a capitalized name and
# a dotted name
law bind_declared_is_name_kinds:
  for kk: Lex.TokKind
  {Bind.declared.is_name(kk) == D1.kinds.among(kk, [Lex.TName{}, Lex.TUpper{}, Lex.TDotted{}]) : Bool}

# LAW: Lex.is_comma holds for exactly a comma
law lex_is_comma_kinds:
  for kk: Lex.TokKind
  {Lex.is_comma(kk) == D1.kinds.among(kk, [Lex.TComma{}]) : Bool}

# LAW: Lex.is_name holds for exactly a name, a capitalized name, a dotted
# name, a `_` name and a keyword
law lex_is_name_kinds:
  for kk: Lex.TokKind
  {Lex.is_name(kk) == D1.kinds.among(kk, [Lex.TName{}, Lex.TUpper{}, Lex.TDotted{}, Lex.TWild{}, Lex.TKey{}]) : Bool}

# LAW: Lex.is_nl holds for exactly a newline
law lex_is_nl_kinds:
  for kk: Lex.TokKind
  {Lex.is_nl(kk) == D1.kinds.among(kk, [Lex.TNewline{}]) : Bool}

# LAW: Lex.is_open holds for exactly an opening bracket
law lex_is_open_kinds:
  for kk: Lex.TokKind
  {Lex.is_open(kk) == D1.kinds.among(kk, [Lex.TOpen{}]) : Bool}

# LAW: Lex.is_str holds for exactly a string
law lex_is_str_kinds:
  for kk: Lex.TokKind
  {Lex.is_str(kk) == D1.kinds.among(kk, [Lex.TStr{}]) : Bool}

# LAW: Lex.significant holds for every kind but a comment and a space and a
# newline
law lex_significant_kinds:
  for kk: Lex.TokKind
  {Lex.significant(kk) == Bool.not(D1.kinds.among(kk, [Lex.TComment{}, Lex.TSpace{}, Lex.TNewline{}])) : Bool}

# LAW: Outline.ends_colon.is holds for exactly a `:`
law outline_ends_colon_is_kinds:
  for kk: Lex.TokKind
  {Outline.ends_colon.is(kk) == D1.kinds.among(kk, [Lex.TColon{}]) : Bool}
