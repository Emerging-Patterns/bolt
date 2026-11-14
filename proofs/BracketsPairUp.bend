# proofs of laws/BracketsPairUp.bend: each law is checked bracket by bracket
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/syntax/bind.bend as Bind
import ../src/rules/style/wrap.bend as Wrap
import ../src/rules/correctness/arms.bend as Arms
import ../src/rules/table.bend as Table
import ../src/rules/pedantic/rewalk.bend as Rewalk
import ../laws/defs/Brackets.bend as B
import ../laws/BracketsPairUp.bend as Laws

def Laws.lex_classes_opener(b):
  match b:
    case B.BParen{}:
      {==}
    case B.BSquare{}:
      {==}
    case B.BBrace{}:
      {==}
    case B.BAngle{}:
      {==}

def Laws.lex_classes_closer(b):
  match b:
    case B.BParen{}:
      {==}
    case B.BSquare{}:
      {==}
    case B.BBrace{}:
      {==}
    case B.BAngle{}:
      {==}

def Laws.tree_closer_pairs(b):
  match b:
    case B.BParen{}:
      {==}
    case B.BSquare{}:
      {==}
    case B.BBrace{}:
      {==}
    case B.BAngle{}:
      {==}

def Laws.wrap_open_raises(b):
  match b:
    case B.BParen{}:
      {==}
    case B.BSquare{}:
      {==}
    case B.BBrace{}:
      {==}
    case B.BAngle{}:
      {==}

def Laws.wrap_close_lowers(b):
  match b:
    case B.BParen{}:
      {==}
    case B.BSquare{}:
      {==}
    case B.BBrace{}:
      {==}
    case B.BAngle{}:
      {==}

def Laws.wrap_oparen_is_round(b):
  match b:
    case B.BParen{}:
      {==}
    case B.BSquare{}:
      {==}
    case B.BBrace{}:
      {==}
    case B.BAngle{}:
      {==}

def Laws.wrap_cparen_is_round(b):
  match b:
    case B.BParen{}:
      {==}
    case B.BSquare{}:
      {==}
    case B.BBrace{}:
      {==}
    case B.BAngle{}:
      {==}

def Laws.bind_tele_kind_by_bracket(b):
  match b:
    case B.BParen{}:
      {==}
    case B.BSquare{}:
      {==}
    case B.BBrace{}:
      {==}
    case B.BAngle{}:
      {==}

def Laws.arms_part_open_by_bracket(b):
  match b:
    case B.BParen{}:
      {==}
    case B.BSquare{}:
      {==}
    case B.BBrace{}:
      {==}
    case B.BAngle{}:
      {==}

def Laws.table_call_name_round(b):
  match b:
    case B.BParen{}:
      {==}
    case B.BSquare{}:
      {==}
    case B.BBrace{}:
      {==}
    case B.BAngle{}:
      {==}

def Laws.rewalk_as_call_round(b):
  match b:
    case B.BParen{}:
      {==}
    case B.BSquare{}:
      {==}
    case B.BBrace{}:
      {==}
    case B.BAngle{}:
      {==}

def Laws.rewalk_as_call_wrapped_round(b):
  match b:
    case B.BParen{}:
      {==}
    case B.BSquare{}:
      {==}
    case B.BBrace{}:
      {==}
    case B.BAngle{}:
      {==}

def Laws.rewalk_as_call_inside_round(b):
  match b:
    case B.BParen{}:
      {==}
    case B.BSquare{}:
      {==}
    case B.BBrace{}:
      {==}
    case B.BAngle{}:
      {==}
