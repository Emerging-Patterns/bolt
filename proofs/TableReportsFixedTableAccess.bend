# proofs of laws/TableReportsFixedTableAccess.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/suspicious/table.bend as Table
import ../laws/TableReportsFixedTableAccess.bend as Laws
import ./lemmas/Pick.bend as M1

# a call site's own finding: one exactly when the law's site test holds
law table.one:
  for +tt: String
  for +o: String
  for +kids: Tree.Node
  for +fixed: List<&2, String>
  for +path: String
  for +line: U32
  for +col: U32
  {List.length(&2, F.Finding, Table.hit(String.eq(o, "("), tt, kids, fixed, path, line, col))
    == Bool.pick(Nat, Laws.table.site(tt, o, kids, fixed), 1n, 0n) : Nat}

def table.one(tt, o, kids, fixed, path, line, col):
  M1.chars.one(Laws.table.site(tt, o, kids, fixed),
    Table.cite(String.eq(tt, "List.get"), path, line, col, U32.from_nat(String.length(tt))))

def Laws.table_walk_counts(nn, path, fixed):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{Lex.Tok{k, +t, +l, +c}}:
          match rest:
            case Tree.NCons{h2, +r2}:
              match h2:
                case Tree.Group{Lex.Tok{k2, +o, l2, c2}, +kids, cl}:
                  M1.table.three(Table.hit(String.eq(o, "("), t, kids, fixed, path, l, c), Table.walk(kids, path,
                      fixed),
                    Table.walk(r2, path, fixed), Bool.pick(Nat, Laws.table.site(t, o, kids, fixed), 1n, 0n),
                    Laws.table.count(kids, fixed), Laws.table.count(r2, fixed),
                    table.one(t, o, kids, fixed, path, l, c),
                    Laws.table_walk_counts(kids, path, fixed), Laws.table_walk_counts(r2, path, fixed))
                case Tree.Leaf{x}:
                  Laws.table_walk_counts(rest, path, fixed)
                case Tree.Stmt{a, b, d}:
                  Laws.table_walk_counts(rest, path, fixed)
                case Tree.NNil{}:
                  Laws.table_walk_counts(rest, path, fixed)
                case Tree.NCons{a, b}:
                  Laws.table_walk_counts(rest, path, fixed)
            case Tree.Leaf{x}:
              Laws.table_walk_counts(rest, path, fixed)
            case Tree.Group{a, b, d}:
              Laws.table_walk_counts(rest, path, fixed)
            case Tree.Stmt{a, b, d}:
              Laws.table_walk_counts(rest, path, fixed)
            case Tree.NNil{}:
              Laws.table_walk_counts(rest, path, fixed)
        case Tree.Group{open, +kids, close}:
          M1.table.two(Table.walk(kids, path, fixed), Table.walk(rest, path, fixed),
            Laws.table.count(kids, fixed), Laws.table.count(rest, fixed),
            Laws.table_walk_counts(kids, path, fixed), Laws.table_walk_counts(rest, path, fixed))
        case Tree.Stmt{kind, +kids, +body}:
          M1.table.three(Table.walk(kids, path, fixed), Table.walk(body, path, fixed), Table.walk(rest, path, fixed),
            Laws.table.count(kids, fixed), Laws.table.count(body, fixed), Laws.table.count(rest, fixed),
            Laws.table_walk_counts(kids, path, fixed), Laws.table_walk_counts(body, path, fixed),
            Laws.table_walk_counts(rest, path, fixed))
        case Tree.NNil{}:
          Laws.table_walk_counts(rest, path, fixed)
        case Tree.NCons{a, b}:
          Laws.table_walk_counts(rest, path, fixed)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{a, b, d}:
      {==}
    case Tree.Stmt{a, b, d}:
      {==}
    case Tree.NNil{}:
      {==}

# one def's findings: walked when its guard keeps it, else none
law table.stop:
  for +b: Bool
  for +body: Tree.Node
  for +path: String
  for +fixed: List<&2, String>
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(b), [], _u => Table.walk(body, path, fixed)))
    == Bool.pick(Nat, b, Laws.table.count(body, fixed), 0n) : Nat}

def table.stop(b, body, path, fixed):
  match b:
    case True{}:
      Laws.table_walk_counts(body, path, fixed)
    case False{}:
      {==}

# table's def walk: the findings gathered so far, then each def's
law table.go:
  for ds: List<&2, Calls.Def>
  for +mods: List<&2, String>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Table.check.go(ds, mods, path, acc)) == M1.pick.sum(acc, Laws.table.defs(ds, mods, path))
    : Nat}

def table.go(ds, mods, path, acc):
  match ds:
    case Nil{}:
      M1.pick.rev(acc, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +keep = Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))
      +x = Lazy.stop(List<&2, F.Finding>, Bool.not(keep), [], _u => Table.walk(body, path, Table.scope(body, mods)))
      +cb = Bool.pick(Nat, keep, Laws.table.count(body, Table.scope(body, mods)), 0n)
      Equal.trans(Nat, List.length(&2, F.Finding, Table.check.go(rest, mods, path, x <> acc)),
        M1.pick.sum(acc, Nat.add(List.length(&2, F.Finding, x), Laws.table.defs(rest, mods, path))),
        M1.pick.sum(acc, Nat.add(cb, Laws.table.defs(rest, mods, path))),
        table.go(rest, mods, path, x <> acc),
        Equal.cong(Nat, Nat, n => M1.pick.sum(acc, Nat.add(n, Laws.table.defs(rest, mods, path))),
          List.length(&2, F.Finding, x), cb, table.stop(keep, body, path, Table.scope(body, mods))))

def Laws.table_counts(path, _text, _toks, tree, _bound, _items):
  table.go(Calls.defs(tree), Table.modules(Calls.defs(tree), []), path, Nil{})
