# proofs of laws/NamesTakeTheirKind.bend: the keywords one by one, and each
# kind of name by rewriting the lexer's choice with what is known of the text
import Base
import ../src/syntax/lex.bend as Lex
import ../laws/NamesTakeTheirKind.bend as Laws

# the lexer's choice once a name is not `_` either
def tail.upper(+t: String) -> Lex.TokKind:
  Bool.pick(Lex.TokKind, Lex.upper_first(String.to_list(t)), Lex.TUpper{}, Lex.TName{})

# the lexer's choice once a name is not dotted either
def tail.wild(+t: String) -> Lex.TokKind:
  Bool.pick(Lex.TokKind, String.eq(t, "_"), Lex.TWild{}, tail.upper(t))

# the lexer's choice once a name is not a keyword
def tail.dot(+t: String) -> Lex.TokKind:
  Bool.pick(Lex.TokKind, String.contains(t, "."), Lex.TDotted{}, tail.wild(t))

def Laws.keywords_are_keywords(n):
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n+_:
      {==}

def Laws.name_keyword(t, e1):
  %Equal.sym(Bool, Lex.is_keyword(t), True{}, e1) :
    {Bool.pick(Lex.TokKind, _, Lex.TKey{}, tail.dot(t)) == Lex.TKey{} : Lex.TokKind}
  {==}

def Laws.name_dotted(t, e1, e2):
  %Equal.sym(Bool, Lex.is_keyword(t), False{}, e1) :
    {Bool.pick(Lex.TokKind, _, Lex.TKey{}, tail.dot(t)) == Lex.TDotted{} : Lex.TokKind}
  %Equal.sym(Bool, String.contains(t, "."), True{}, e2) :
    {Bool.pick(Lex.TokKind, _, Lex.TDotted{}, tail.wild(t)) == Lex.TDotted{} : Lex.TokKind}
  {==}

def Laws.name_wild(t, e1, e2, e3):
  %Equal.sym(Bool, Lex.is_keyword(t), False{}, e1) :
    {Bool.pick(Lex.TokKind, _, Lex.TKey{}, tail.dot(t)) == Lex.TWild{} : Lex.TokKind}
  %Equal.sym(Bool, String.contains(t, "."), False{}, e2) :
    {Bool.pick(Lex.TokKind, _, Lex.TDotted{}, tail.wild(t)) == Lex.TWild{} : Lex.TokKind}
  %Equal.sym(Bool, String.eq(t, "_"), True{}, e3) :
    {Bool.pick(Lex.TokKind, _, Lex.TWild{}, tail.upper(t)) == Lex.TWild{} : Lex.TokKind}
  {==}

def Laws.name_upper(t, e1, e2, e3, e4):
  %Equal.sym(Bool, Lex.is_keyword(t), False{}, e1) :
    {Bool.pick(Lex.TokKind, _, Lex.TKey{}, tail.dot(t)) == Lex.TUpper{} : Lex.TokKind}
  %Equal.sym(Bool, String.contains(t, "."), False{}, e2) :
    {Bool.pick(Lex.TokKind, _, Lex.TDotted{}, tail.wild(t)) == Lex.TUpper{} : Lex.TokKind}
  %Equal.sym(Bool, String.eq(t, "_"), False{}, e3) :
    {Bool.pick(Lex.TokKind, _, Lex.TWild{}, tail.upper(t)) == Lex.TUpper{} : Lex.TokKind}
  %Equal.sym(Bool, Lex.upper_first(String.to_list(t)), True{}, e4) :
    {Bool.pick(Lex.TokKind, _, Lex.TUpper{}, Lex.TName{}) == Lex.TUpper{} : Lex.TokKind}
  {==}

def Laws.name_plain(t, e1, e2, e3, e4):
  %Equal.sym(Bool, Lex.is_keyword(t), False{}, e1) :
    {Bool.pick(Lex.TokKind, _, Lex.TKey{}, tail.dot(t)) == Lex.TName{} : Lex.TokKind}
  %Equal.sym(Bool, String.contains(t, "."), False{}, e2) :
    {Bool.pick(Lex.TokKind, _, Lex.TDotted{}, tail.wild(t)) == Lex.TName{} : Lex.TokKind}
  %Equal.sym(Bool, String.eq(t, "_"), False{}, e3) :
    {Bool.pick(Lex.TokKind, _, Lex.TWild{}, tail.upper(t)) == Lex.TName{} : Lex.TokKind}
  %Equal.sym(Bool, Lex.upper_first(String.to_list(t)), False{}, e4) :
    {Bool.pick(Lex.TokKind, _, Lex.TUpper{}, Lex.TName{}) == Lex.TName{} : Lex.TokKind}
  {==}
