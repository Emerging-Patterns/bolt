# proofs of laws/DefSignatureRunsToItsColon.bend
import Base
import ../laws/DefSignatureRunsToItsColon.bend as Laws
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/calls.bend as Calls

# a header with no `:` on its own line is read off what wrap finds
law header.wraps:
  for +kids: Tree.Node
  for body: Tree.Node
  for e0: {Calls.has_colon(kids) == False{} : Bool}
  {Calls.header(kids, body) == Calls.header.of(kids, Calls.wrap(body)) : Tree.Node}

def header.wraps(kids, body, e0):
  %Equal.sym(Bool, Calls.has_colon(kids), False{}, e0) :
    {Lazy.stop(Tree.Node, _, kids, _u => Calls.header.of(kids, Calls.wrap(body)))
      == Calls.header.of(kids, Calls.wrap(body)) : Tree.Node}
  {==}

# a body under a line with no `:` is read off what wrap finds
law under.wraps:
  for kids: Tree.Node
  for +body: Tree.Node
  for e0: {Calls.has_colon(kids) == False{} : Bool}
  {Calls.under(kids, body) == Calls.under.of(body, Calls.wrap(body)) : Tree.Node}

def under.wraps(kids, body, e0):
  %Equal.sym(Bool, Calls.has_colon(kids), False{}, e0) :
    {Lazy.stop(Tree.Node, _, body, _u => Calls.under.of(body, Calls.wrap(body)))
      == Calls.under.of(body, Calls.wrap(body)) : Tree.Node}
  {==}

def Laws.defs_read_header(_kids, _body, _rest):
  {==}

def Laws.one_line_header(kids, body, e):
  %Equal.sym(Bool, Calls.has_colon(kids), True{}, e) :
    {Lazy.stop(Tree.Node, _, kids, _u => Calls.header.of(kids, Calls.wrap(body))) == kids : Tree.Node}
  {==}

def Laws.one_line_body(kids, body, e):
  %Equal.sym(Bool, Calls.has_colon(kids), True{}, e) :
    {Lazy.stop(Tree.Node, _, body, _u => Calls.under.of(body, Calls.wrap(body))) == body : Tree.Node}
  {==}

# a statement that holds a `:` ends the header: its tokens, then what is
# under it and what follows it as the body
law wrap.ends:
  for kind: Tree.StmtKind
  for +line: Tree.Node
  for below: Tree.Node
  for +rest: Tree.Node
  for e1: {Calls.has_colon(line) == True{} : Bool}
  {Calls.wrap(Tree.NCons{Tree.Stmt{kind, line, below}, rest})
    == Some{Calls.Wrap{line, Calls.join(below, rest)}} : Maybe<&2, Calls.Wrap>}

def wrap.ends(_kind, line, below, rest, e1):
  match below:
    case Tree.Leaf{tok}:
      %Equal.sym(Bool, Calls.has_colon(line), True{}, e1) :
        {Lazy.stop(Maybe<&2, Calls.Wrap>, Bool.not(_), None{},
          _u => Some{Calls.Wrap{line, Calls.join(Tree.Leaf{tok}, rest)}})
          == Some{Calls.Wrap{line, Calls.join(Tree.Leaf{tok}, rest)}} : Maybe<&2, Calls.Wrap>}
      {==}
    case Tree.Group{o, gk, cl}:
      %Equal.sym(Bool, Calls.has_colon(line), True{}, e1) :
        {Lazy.stop(Maybe<&2, Calls.Wrap>, Bool.not(_), None{},
          _u => Some{Calls.Wrap{line, Calls.join(Tree.Group{o, gk, cl}, rest)}})
          == Some{Calls.Wrap{line, Calls.join(Tree.Group{o, gk, cl}, rest)}} : Maybe<&2, Calls.Wrap>}
      {==}
    case Tree.Stmt{sk, k, sb}:
      %Equal.sym(Bool, Calls.has_colon(line), True{}, e1) :
        {Lazy.stop(Maybe<&2, Calls.Wrap>, Bool.not(_), None{},
          _u => Some{Calls.Wrap{line, Calls.join(Tree.Stmt{sk, k, sb}, rest)}})
          == Some{Calls.Wrap{line, Calls.join(Tree.Stmt{sk, k, sb}, rest)}} : Maybe<&2, Calls.Wrap>}
      {==}
    case Tree.NNil{}:
      %Equal.sym(Bool, Calls.has_colon(line), True{}, e1) :
        {Lazy.stop(Maybe<&2, Calls.Wrap>, _, Some{Calls.Wrap{line, rest}},
          _u => Calls.wrap.more(line, Calls.wrap(rest)))
          == Some{Calls.Wrap{line, rest}} : Maybe<&2, Calls.Wrap>}
      {==}
    case Tree.NCons{h, t}:
      %Equal.sym(Bool, Calls.has_colon(line), True{}, e1) :
        {Lazy.stop(Maybe<&2, Calls.Wrap>, Bool.not(_), None{},
          _u => Some{Calls.Wrap{line, Calls.join(Tree.NCons{h, t}, rest)}})
          == Some{Calls.Wrap{line, Calls.join(Tree.NCons{h, t}, rest)}} : Maybe<&2, Calls.Wrap>}
      {==}

# a statement with no `:` and nothing under it is passed through
law wrap.passes:
  for kind: Tree.StmtKind
  for +line: Tree.Node
  for +rest: Tree.Node
  for e1: {Calls.has_colon(line) == False{} : Bool}
  {Calls.wrap(Tree.NCons{Tree.Stmt{kind, line, Tree.NNil{}}, rest})
    == Calls.wrap.more(line, Calls.wrap(rest)) : Maybe<&2, Calls.Wrap>}

def wrap.passes(_kind, line, rest, e1):
  %Equal.sym(Bool, Calls.has_colon(line), False{}, e1) :
    {Lazy.stop(Maybe<&2, Calls.Wrap>, _, Some{Calls.Wrap{line, rest}},
      _u => Calls.wrap.more(line, Calls.wrap(rest)))
      == Calls.wrap.more(line, Calls.wrap(rest)) : Maybe<&2, Calls.Wrap>}
  {==}

# a statement with no `:` and statements of its own under it stops the reading
law wrap.stops:
  for kind: Tree.StmtKind
  for +line: Tree.Node
  for inner: Tree.Node
  for more: Tree.Node
  for rest: Tree.Node
  for e1: {Calls.has_colon(line) == False{} : Bool}
  {Calls.wrap(Tree.NCons{Tree.Stmt{kind, line, Tree.NCons{inner, more}}, rest}) == None{} : Maybe<&2, Calls.Wrap>}

def wrap.stops(_kind, line, inner, more, rest, e1):
  %Equal.sym(Bool, Calls.has_colon(line), False{}, e1) :
    {Lazy.stop(Maybe<&2, Calls.Wrap>, Bool.not(_), None{},
      _u => Some{Calls.Wrap{line, Calls.join(Tree.NCons{inner, more}, rest)}})
      == None{} : Maybe<&2, Calls.Wrap>}
  {==}

def Laws.wrapped_header(kids, kind, line, below, rest, e0, e1):
  %Equal.sym(Tree.Node, Calls.header(kids, Tree.NCons{Tree.Stmt{kind, line, below}, rest}),
    Calls.header.of(kids, Calls.wrap(Tree.NCons{Tree.Stmt{kind, line, below}, rest})),
    header.wraps(kids, Tree.NCons{Tree.Stmt{kind, line, below}, rest}, e0)) :
    {_ == Calls.join(kids, line) : Tree.Node}
  %Equal.sym(Maybe<&2, Calls.Wrap>, Calls.wrap(Tree.NCons{Tree.Stmt{kind, line, below}, rest}),
    Some{Calls.Wrap{line, Calls.join(below, rest)}}, wrap.ends(kind, line, below, rest, e1)) :
    {Calls.header.of(kids, _) == Calls.join(kids, line) : Tree.Node}
  {==}

def Laws.wrapped_body(kids, kind, line, below, rest, e0, e1):
  %Equal.sym(Tree.Node, Calls.under(kids, Tree.NCons{Tree.Stmt{kind, line, below}, rest}),
    Calls.under.of(Tree.NCons{Tree.Stmt{kind, line, below}, rest},
      Calls.wrap(Tree.NCons{Tree.Stmt{kind, line, below}, rest})),
    under.wraps(kids, Tree.NCons{Tree.Stmt{kind, line, below}, rest}, e0)) :
    {_ == Calls.join(below, rest) : Tree.Node}
  %Equal.sym(Maybe<&2, Calls.Wrap>, Calls.wrap(Tree.NCons{Tree.Stmt{kind, line, below}, rest}),
    Some{Calls.Wrap{line, Calls.join(below, rest)}}, wrap.ends(kind, line, below, rest, e1)) :
    {Calls.under.of(Tree.NCons{Tree.Stmt{kind, line, below}, rest}, _) == Calls.join(below, rest) : Tree.Node}
  {==}

def Laws.wrapped_twice_header(kids, k1, line1, k2, line2, below, rest, e0, e1, e2):
  %Equal.sym(Tree.Node,
    Calls.header(kids, Tree.NCons{Tree.Stmt{k1, line1, Tree.NNil{}}, Tree.NCons{Tree.Stmt{k2, line2, below}, rest}}),
    Calls.header.of(kids,
      Calls.wrap(Tree.NCons{Tree.Stmt{k1, line1, Tree.NNil{}}, Tree.NCons{Tree.Stmt{k2, line2, below}, rest}})),
    header.wraps(kids, Tree.NCons{Tree.Stmt{k1, line1, Tree.NNil{}}, Tree.NCons{Tree.Stmt{k2, line2, below}, rest}},
      e0)) :
    {_ == Calls.join(kids, Calls.join(line1, line2)) : Tree.Node}
  %Equal.sym(Maybe<&2, Calls.Wrap>,
    Calls.wrap(Tree.NCons{Tree.Stmt{k1, line1, Tree.NNil{}}, Tree.NCons{Tree.Stmt{k2, line2, below}, rest}}),
    Calls.wrap.more(line1, Calls.wrap(Tree.NCons{Tree.Stmt{k2, line2, below}, rest})),
    wrap.passes(k1, line1, Tree.NCons{Tree.Stmt{k2, line2, below}, rest}, e1)) :
    {Calls.header.of(kids, _) == Calls.join(kids, Calls.join(line1, line2)) : Tree.Node}
  %Equal.sym(Maybe<&2, Calls.Wrap>, Calls.wrap(Tree.NCons{Tree.Stmt{k2, line2, below}, rest}),
    Some{Calls.Wrap{line2, Calls.join(below, rest)}}, wrap.ends(k2, line2, below, rest, e2)) :
    {Calls.header.of(kids, Calls.wrap.more(line1, _)) == Calls.join(kids, Calls.join(line1, line2)) : Tree.Node}
  {==}

def Laws.wrapped_twice_body(kids, k1, line1, k2, line2, below, rest, e0, e1, e2):
  %Equal.sym(Tree.Node,
    Calls.under(kids, Tree.NCons{Tree.Stmt{k1, line1, Tree.NNil{}}, Tree.NCons{Tree.Stmt{k2, line2, below}, rest}}),
    Calls.under.of(Tree.NCons{Tree.Stmt{k1, line1, Tree.NNil{}}, Tree.NCons{Tree.Stmt{k2, line2, below}, rest}},
      Calls.wrap(Tree.NCons{Tree.Stmt{k1, line1, Tree.NNil{}}, Tree.NCons{Tree.Stmt{k2, line2, below}, rest}})),
    under.wraps(kids, Tree.NCons{Tree.Stmt{k1, line1, Tree.NNil{}}, Tree.NCons{Tree.Stmt{k2, line2, below}, rest}},
      e0)) :
    {_ == Calls.join(below, rest) : Tree.Node}
  %Equal.sym(Maybe<&2, Calls.Wrap>,
    Calls.wrap(Tree.NCons{Tree.Stmt{k1, line1, Tree.NNil{}}, Tree.NCons{Tree.Stmt{k2, line2, below}, rest}}),
    Calls.wrap.more(line1, Calls.wrap(Tree.NCons{Tree.Stmt{k2, line2, below}, rest})),
    wrap.passes(k1, line1, Tree.NCons{Tree.Stmt{k2, line2, below}, rest}, e1)) :
    {Calls.under.of(Tree.NCons{Tree.Stmt{k1, line1, Tree.NNil{}}, Tree.NCons{Tree.Stmt{k2, line2, below}, rest}}, _)
      == Calls.join(below, rest) : Tree.Node}
  %Equal.sym(Maybe<&2, Calls.Wrap>, Calls.wrap(Tree.NCons{Tree.Stmt{k2, line2, below}, rest}),
    Some{Calls.Wrap{line2, Calls.join(below, rest)}}, wrap.ends(k2, line2, below, rest, e2)) :
    {Calls.under.of(Tree.NCons{Tree.Stmt{k1, line1, Tree.NNil{}}, Tree.NCons{Tree.Stmt{k2, line2, below}, rest}},
      Calls.wrap.more(line1, _)) == Calls.join(below, rest) : Tree.Node}
  {==}

# one statement with no `:`, whatever is under it, ends no header
law wrap.none:
  for +kind: Tree.StmtKind
  for +line: Tree.Node
  for +below: Tree.Node
  for e1: {Calls.has_colon(line) == False{} : Bool}
  {Calls.wrap(Tree.NCons{Tree.Stmt{kind, line, below}, Tree.NNil{}}) == None{} : Maybe<&2, Calls.Wrap>}

def wrap.none(kind, line, below, e1):
  match below:
    case Tree.Leaf{tok}:
      %Equal.sym(Bool, Calls.has_colon(line), False{}, e1) :
        {Lazy.stop(Maybe<&2, Calls.Wrap>, Bool.not(_), None{},
          _u => Some{Calls.Wrap{line, Calls.join(Tree.Leaf{tok}, Tree.NNil{})}})
          == None{} : Maybe<&2, Calls.Wrap>}
      {==}
    case Tree.Group{o, gk, cl}:
      %Equal.sym(Bool, Calls.has_colon(line), False{}, e1) :
        {Lazy.stop(Maybe<&2, Calls.Wrap>, Bool.not(_), None{},
          _u => Some{Calls.Wrap{line, Calls.join(Tree.Group{o, gk, cl}, Tree.NNil{})}})
          == None{} : Maybe<&2, Calls.Wrap>}
      {==}
    case Tree.Stmt{sk, k, sb}:
      %Equal.sym(Bool, Calls.has_colon(line), False{}, e1) :
        {Lazy.stop(Maybe<&2, Calls.Wrap>, Bool.not(_), None{},
          _u => Some{Calls.Wrap{line, Calls.join(Tree.Stmt{sk, k, sb}, Tree.NNil{})}})
          == None{} : Maybe<&2, Calls.Wrap>}
      {==}
    case Tree.NNil{}:
      %Equal.sym(Maybe<&2, Calls.Wrap>, Calls.wrap(Tree.NCons{Tree.Stmt{kind, line, Tree.NNil{}}, Tree.NNil{}}),
        Calls.wrap.more(line, Calls.wrap(Tree.NNil{})), wrap.passes(kind, line, Tree.NNil{}, e1)) :
        {_ == None{} : Maybe<&2, Calls.Wrap>}
      {==}
    case Tree.NCons{h, t}:
      wrap.stops(kind, line, h, t, Tree.NNil{}, e1)

def Laws.unended_header(kids, kind, line, below, e0, e1):
  %Equal.sym(Tree.Node, Calls.header(kids, Tree.NCons{Tree.Stmt{kind, line, below}, Tree.NNil{}}),
    Calls.header.of(kids, Calls.wrap(Tree.NCons{Tree.Stmt{kind, line, below}, Tree.NNil{}})),
    header.wraps(kids, Tree.NCons{Tree.Stmt{kind, line, below}, Tree.NNil{}}, e0)) :
    {_ == kids : Tree.Node}
  %Equal.sym(Maybe<&2, Calls.Wrap>, Calls.wrap(Tree.NCons{Tree.Stmt{kind, line, below}, Tree.NNil{}}), None{},
    wrap.none(kind, line, below, e1)) :
    {Calls.header.of(kids, _) == kids : Tree.Node}
  {==}

def Laws.unended_body(kids, kind, line, below, e0, e1):
  %Equal.sym(Tree.Node, Calls.under(kids, Tree.NCons{Tree.Stmt{kind, line, below}, Tree.NNil{}}),
    Calls.under.of(Tree.NCons{Tree.Stmt{kind, line, below}, Tree.NNil{}},
      Calls.wrap(Tree.NCons{Tree.Stmt{kind, line, below}, Tree.NNil{}})),
    under.wraps(kids, Tree.NCons{Tree.Stmt{kind, line, below}, Tree.NNil{}}, e0)) :
    {_ == Tree.NCons{Tree.Stmt{kind, line, below}, Tree.NNil{}} : Tree.Node}
  %Equal.sym(Maybe<&2, Calls.Wrap>, Calls.wrap(Tree.NCons{Tree.Stmt{kind, line, below}, Tree.NNil{}}), None{},
    wrap.none(kind, line, below, e1)) :
    {Calls.under.of(Tree.NCons{Tree.Stmt{kind, line, below}, Tree.NNil{}}, _)
      == Tree.NCons{Tree.Stmt{kind, line, below}, Tree.NNil{}} : Tree.Node}
  {==}

def Laws.nested_line_header(kids, kind, line, inner, more, rest, e0, e1):
  %Equal.sym(Tree.Node, Calls.header(kids, Tree.NCons{Tree.Stmt{kind, line, Tree.NCons{inner, more}}, rest}),
    Calls.header.of(kids, Calls.wrap(Tree.NCons{Tree.Stmt{kind, line, Tree.NCons{inner, more}}, rest})),
    header.wraps(kids, Tree.NCons{Tree.Stmt{kind, line, Tree.NCons{inner, more}}, rest}, e0)) :
    {_ == kids : Tree.Node}
  %Equal.sym(Maybe<&2, Calls.Wrap>, Calls.wrap(Tree.NCons{Tree.Stmt{kind, line, Tree.NCons{inner, more}}, rest}),
    None{}, wrap.stops(kind, line, inner, more, rest, e1)) :
    {Calls.header.of(kids, _) == kids : Tree.Node}
  {==}

def Laws.arrow_below_is_proof(
  _dt,
  _dl,
  _dc,
  _nt,
  _nl,
  _nc,
  _po,
  _pk,
  _pc,
  _kind,
  _at,
  _al,
  _ac,
  _bl,
  _bc,
  _bk,
  _bz,
  _ct,
  _cl,
  _cc,
  below,
  _rest
):
  match below:
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{o, gk, cl}:
      {==}
    case Tree.Stmt{sk, k, sb}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{h, t}:
      {==}

def Laws.type_below_is_proof(
  _dt,
  _dl,
  _dc,
  _nt,
  _nl,
  _nc,
  _po,
  _pk,
  _pc,
  _kind,
  _at,
  _al,
  _ac,
  _bl,
  _bc,
  _bk,
  _bz,
  _ct,
  _cl,
  _cc,
  below,
  _rest
):
  match below:
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{o, gk, cl}:
      {==}
    case Tree.Stmt{sk, k, sb}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{h, t}:
      {==}
