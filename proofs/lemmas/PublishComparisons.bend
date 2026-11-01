# string and word comparison facts for publishing diagnostics
import Base
import ../../src/syntax/word.bend as Word

# Publishing (laws/LspDiagnosticsMatchCli.bend, laws/LspPublishesOnDocumentEvents.bend). The documents are looked up by
# String.eq, so the keep laws need it to be reflexive; that goes down to the
# words a U32 is made of. The CLI side walks the planner's run over one named
# file, cased on whether that file is a bolt.bend.

# a bit compares equal to itself
law pub.bcmp:
  for b: Bool
  {Bool.cmp(b, b) == EQ{} : Cmp}

def pub.bcmp(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a word compares equal to itself
law pub.weq_refl:
  for n: Nat
  for a: Word(n)
  {Word.cmp(n, a, a) == EQ{} : Cmp}

def pub.weq_refl(n, a):
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      match a:
        case WCon{b, +t}:
          e = Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, pub.weq_refl(p, t))
          %e : {Word.cmp.fin(b, b, _) == EQ{} : Cmp}
          pub.bcmp(b)

# a string is equal to itself (String.eq walks with String.order.go since
# bend 2.0.37)
law pub.seq_refl:
  for s: String
  {String.eq(s, s) == True{} : Bool}

def pub.seq_refl(s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{U32{+w}}, +t}:
      e = Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, pub.weq_refl(32n, w))
      %e : {Cmp.is_eq(String.order.go(t, t, _)) == True{} : Bool}
      pub.seq_refl(t)
