# proofs of laws/LexRoundTripsText.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../laws/LexRoundTripsText.bend as Laws
import ./lemmas/LexAndTreeFacts.bend as M1

# the texts of a list reversed onto another: the first's, reversed, then the other's
law spell.rev:
  for +xs: List<&2, Lex.Tok>
  for +acc: List<&2, Lex.Tok>
  {M1.spell(List.reverse.go(&2, Lex.Tok, xs, acc)) == String.append(M1.rspell(xs), M1.spell(acc)) : String}

def spell.rev(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, t, l, c}, rest}:
      Equal.trans(String,
        M1.spell(List.reverse.go(&2, Lex.Tok, rest, Lex.Tok{k, t, l, c} <> acc)),
        String.append(M1.rspell(rest), String.append(t, M1.spell(acc))),
        String.append(String.append(M1.rspell(rest), t), M1.spell(acc)),
        spell.rev(rest, Lex.Tok{k, t, l, c} <> acc),
        Equal.sym(String, String.append(String.append(M1.rspell(rest), t), M1.spell(acc)),
          String.append(M1.rspell(rest), String.append(t, M1.spell(acc))),
          M1.app.assoc(M1.rspell(rest), t, M1.spell(acc))))

# the finished tokens spell what the machine read
law finish:
  for +st: Lex.St
  {Lex.text(Lex.finish(st)) == M1.seen(st) : String}

def finish(st):
  match st:
    case Lex.St{m, k, l, c, sl, sc, buf, toks}:
      Equal.trans(String,
        Lex.text(Lex.finish(Lex.St{m, k, l, c, sl, sc, buf, toks})),
        String.append(M1.rspell(Lex.flush(k, sl, sc, buf, toks)), SNil{}),
        String.append(M1.rspell(toks), M1.rword(buf)),
        Equal.trans(String,
          Lex.text(Lex.finish(Lex.St{m, k, l, c, sl, sc, buf, toks})),
          M1.spell(Lex.finish(Lex.St{m, k, l, c, sl, sc, buf, toks})),
          String.append(M1.rspell(Lex.flush(k, sl, sc, buf, toks)), SNil{}),
          M1.text(Lex.finish(Lex.St{m, k, l, c, sl, sc, buf, toks})),
          spell.rev(Lex.flush(k, sl, sc, buf, toks), [])),
        Equal.trans(String,
          String.append(M1.rspell(Lex.flush(k, sl, sc, buf, toks)), SNil{}),
          M1.rspell(Lex.flush(k, sl, sc, buf, toks)),
          String.append(M1.rspell(toks), M1.rword(buf)),
          M1.app.nil(M1.rspell(Lex.flush(k, sl, sc, buf, toks))),
          M1.flush(k, sl, sc, buf, toks)))

def Laws.lossless(s):
  Equal.trans(String,
    Lex.text(Lex.tokens(s)),
    String.from_list(String.to_list(s)),
    s,
    Equal.trans(String,
      Lex.text(Lex.tokens(s)),
      M1.seen(Lex.run(String.to_list(s), Lex.St{Lex.Fresh{}, Lex.TSpace{}, 0, 0, 0, 0, [], []})),
      String.from_list(String.to_list(s)),
      finish(Lex.run(String.to_list(s), Lex.St{Lex.Fresh{}, Lex.TSpace{}, 0, 0, 0, 0, [], []})),
      M1.run(String.to_list(s), Lex.St{Lex.Fresh{}, Lex.TSpace{}, 0, 0, 0, 0, [], []})),
    M1.chars(s))
