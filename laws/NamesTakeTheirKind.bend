# The lexer reads a run of name chars whole, then gives it one kind
# (Lex.refine_name), the first that holds of: one of Bend's sixteen
# keywords; a dotted name (it holds a `.`); the wild name `_`; a name that
# starts with a capital; any other name. Every rule that asks whether a
# token is a keyword, a constructor or a qualified name reads that kind
# (laws/TokenKindsNamed.bend says which kinds each question holds for).
import Base
import ../src/syntax/lex.bend as Lex

# Bend's keywords, as law vocabulary
def keywords() -> List<&2, String>:
  ["def", "type", "law", "match", "case", "do", "return", "for", "exs", "where", "is", "import",
   "Type", "Data", "Kind", "Quant"]

# a listed keyword is the lexer's keyword; past the end holds
def keyword.is_key(mm: Maybe<&2, String>) -> Bool:
  match mm:
    case None{}:
      True{}
    case Some{+kw}:
      Lex.is_keyword(kw)

# LAW: each of the sixteen keywords is one to the lexer
law keywords_are_keywords:
  for +n: Nat
  {keyword.is_key(List.get(&2, String, keywords(), n)) == True{} : Bool}

# LAW: a keyword is a keyword token
law name_keyword:
  for +tt: String
  for e1: {Lex.is_keyword(tt) == True{} : Bool}
  {Lex.refine_name(tt) == Lex.TKey{} : Lex.TokKind}

# LAW: any other name holding a `.` is a dotted name
law name_dotted:
  for +tt: String
  for e1: {Lex.is_keyword(tt) == False{} : Bool}
  for e2: {String.contains(tt, ".") == True{} : Bool}
  {Lex.refine_name(tt) == Lex.TDotted{} : Lex.TokKind}

# LAW: `_` is the wild name
law name_wild:
  for +tt: String
  for e1: {Lex.is_keyword(tt) == False{} : Bool}
  for e2: {String.contains(tt, ".") == False{} : Bool}
  for e3: {String.eq(tt, "_") == True{} : Bool}
  {Lex.refine_name(tt) == Lex.TWild{} : Lex.TokKind}

# LAW: any other name that starts with a capital is a capitalized name
law name_upper:
  for +tt: String
  for e1: {Lex.is_keyword(tt) == False{} : Bool}
  for e2: {String.contains(tt, ".") == False{} : Bool}
  for e3: {String.eq(tt, "_") == False{} : Bool}
  for e4: {Lex.upper_first(String.to_list(tt)) == True{} : Bool}
  {Lex.refine_name(tt) == Lex.TUpper{} : Lex.TokKind}

# LAW: every other name is a plain name
law name_plain:
  for +tt: String
  for e1: {Lex.is_keyword(tt) == False{} : Bool}
  for e2: {String.contains(tt, ".") == False{} : Bool}
  for e3: {String.eq(tt, "_") == False{} : Bool}
  for e4: {Lex.upper_first(String.to_list(tt)) == False{} : Bool}
  {Lex.refine_name(tt) == Lex.TName{} : Lex.TokKind}
