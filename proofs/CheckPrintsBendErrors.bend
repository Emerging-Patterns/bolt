# proofs of laws/CheckPrintsBendErrors.bend
import Base
import ../src/lazy/lazy.bend as Lazy
import ../src/check.bend as Check
import ../src/lsp/checker/answer.bend as Checker
import ../src/lsp/report.bend as Rep
import ../laws/CheckPrintsBendErrors.bend as Laws
import ./lemmas/PlannerWalkInduction.bend as M1

# False is not True. shake proves the same two lemmas for its walker
# (wk.false_true, wk.true_false in its src/walk.bend), but bolt reads shake
# through main.bend only (trusted in src/args.bend), which does not export them, and
# bolt's own proofs below use them, so bolt keeps its copies.

# Unit for False, Empty for True: a motive that tells them apart
def bool.false_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Unit
    case True{}:
      Empty

# False is never True
law bool.false_true:
  for e: {False{} == True{} : Bool}
  Empty

def bool.false_true(e):
  %e : bool.false_ty(_)
  Unit{}

# True is never False
law bool.true_false:
  for e: {True{} == False{} : Bool}
  Empty

def bool.true_false(e):
  bool.false_true(Equal.sym(Bool, True{}, False{}, e))

# a file's error lines, then more, are its lines onto more
law chk.file:
  for ds: List<&2, Rep.Diag>
  for +path: String
  for +more: List<&2, String>
  {List.append(&2, String, Check.show_all(ds, path), more) == Laws.chk_file(ds, path, more) : List<&2, String>}

def chk.file(ds, path, more):
  match ds:
    case Nil{}:
      {==}
    case Con{Rep.Diag{+line, +msg}, rest}:
      %chk.file(rest, path, more) : {List.append(&2, String, Check.show_all(Rep.Diag{line, msg} <> rest, path), more)
        == Laws.chk_line(path, Rep.Diag{line, msg}) <> _ : List<&2, String>}
      {==}

def Laws.check_lines(runs):
  match runs:
    case Nil{}:
      {==}
    case Con{Check.Run{+path, +ds}, +rest}:
      %Laws.check_lines(rest) : {List.append(&2, String, Check.show_all(ds, path), Check.lines_of(rest))
        == Laws.chk_file(ds, path, _) : List<&2, String>}
      chk.file(ds, path, Check.lines_of(rest))
    case Con{Check.Failed{+path}, +rest}:
      %Laws.check_lines(rest) : {(path ++ ":1:1: error: could not run bend") <> Check.lines_of(rest)
        == (path ++ ":1:1: error: could not run bend") <> _ : List<&2, String>}
      {==}

# the length of two lists appended is the sum of their lengths
law chk.len_append:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  {List.length(&2, String, List.append(&2, String, xs, ys))
    == Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)) : Nat}

def chk.len_append(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{_x, tl}:
      %chk.len_append(tl, ys) : {1n+List.length(&2, String, List.append(&2, String, tl, ys)) == 1n+_ : Nat}
      {==}

# a file has one error line per diagnostic
law chk.len_show:
  for ds: List<&2, Rep.Diag>
  for +path: String
  {List.length(&2, String, Check.show_all(ds, path)) == List.length(&2, Rep.Diag, ds) : Nat}

def chk.len_show(ds, path):
  match ds:
    case Nil{}:
      {==}
    case Con{Rep.Diag{_line, _msg}, tl}:
      %chk.len_show(tl, path) : {1n+List.length(&2, String, Check.show_all(tl, path)) == 1n+_ : Nat}
      {==}

def Laws.check_one_each(runs):
  match runs:
    case Nil{}:
      {==}
    case Con{Check.Run{+path, +ds}, +rest}:
      %Laws.check_one_each(rest) : {List.length(&2, String,
          List.append(&2, String, Check.show_all(ds, path), Check.lines_of(rest)))
        == Nat.add(List.length(&2, Rep.Diag, ds), _) : Nat}
      %chk.len_show(ds, path) : {List.length(&2, String,
          List.append(&2, String, Check.show_all(ds, path), Check.lines_of(rest)))
        == Nat.add(_, List.length(&2, String, Check.lines_of(rest))) : Nat}
      chk.len_append(Check.show_all(ds, path), Check.lines_of(rest))
    case Con{Check.Failed{_path}, +rest}:
      %Laws.check_one_each(rest) : {1n+List.length(&2, String, Check.lines_of(rest)) == 1n+_ : Nat}
      {==}

# a Nat's type when it is zero: inhabited only at zero
def chk.zero_ty(nn: Nat) -> Type:
  match nn:
    case 0n:
      Unit
    case 1n+_p:
      Empty

# a successor is never zero
law chk.succ_zero:
  for nn: Nat
  for e: {1n+nn == 0n : Nat}
  Empty

def chk.succ_zero(nn, e):
  e2 = Equal.sym(Nat, 1n+nn, 0n, e)
  %e2 : chk.zero_ty(_)
  Unit{}

# a list of no length is empty
law chk.nil:
  for xs: List<&2, String>
  for h: {List.length(&2, String, xs) == 0n : Nat}
  {xs == [] : List<&2, String>}

def chk.nil(xs, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +tl}:
      Empty.absurd({x <> tl == [] : List<&2, String>}, chk.succ_zero(List.length(&2, String, tl), h))

def Laws.check_clean(runs, h):
  +e1 = Equal.trans(Nat, List.length(&2, String, Check.lines_of(runs)), Laws.chk_count(runs), 0n,
    Laws.check_one_each(runs), h)
  e2 = Equal.sym(Nat, List.length(&2, String, Check.lines_of(runs)), 0n, e1)
  %e2 : {Check.out.at(Check.lines_of(runs), _) == Check.Out{["clean"], 0} : Check.Out}
  e3 = Equal.sym(List<&2, String>, Check.lines_of(runs), [], chk.nil(Check.lines_of(runs), e1))
  %e3 : {Check.Out{List.append(&2, String, _, ["clean"]), 0} == Check.Out{["clean"], 0} : Check.Out}
  {==}

def Laws.check_one(runs, h):
  e1 = Equal.sym(Nat, List.length(&2, String, Check.lines_of(runs)), 1n,
    Equal.trans(Nat, List.length(&2, String, Check.lines_of(runs)), Laws.chk_count(runs), 1n,
      Laws.check_one_each(runs), h))
  %e1 : {Check.out.at(Check.lines_of(runs), _)
    == Check.Out{List.append(&2, String, Laws.chk_lines(runs), ["1 error, 0 warnings"]), 1} : Check.Out}
  %Laws.check_lines(runs) : {Check.Out{List.append(&2, String, Check.lines_of(runs), ["1 error, 0 warnings"]), 1}
    == Check.Out{List.append(&2, String, _, ["1 error, 0 warnings"]), 1} : Check.Out}
  {==}

def Laws.check_many(runs, more, h):
  e1 = Equal.sym(Nat, List.length(&2, String, Check.lines_of(runs)), 2n+more,
    Equal.trans(Nat, List.length(&2, String, Check.lines_of(runs)), Laws.chk_count(runs), 2n+more,
      Laws.check_one_each(runs), h))
  %e1 : {Check.out.at(Check.lines_of(runs), _)
    == Check.Out{List.append(&2, String, Laws.chk_lines(runs),
      [U32.show(U32.from_nat(2n+more)) ++ " errors, 0 warnings"]), 1} : Check.Out}
  %Laws.check_lines(runs) : {Check.Out{List.append(&2, String, Check.lines_of(runs),
      [U32.show(U32.from_nat(2n+more)) ++ " errors, 0 warnings"]), 1}
    == Check.Out{List.append(&2, String, _, [U32.show(U32.from_nat(2n+more)) ++ " errors, 0 warnings"]), 1}
    : Check.Out}
  {==}

# a count past zero exits 1, whatever the lines
law chk.code_succ:
  for ls: List<&2, String>
  for nn: Nat
  {Laws.chk_code(Check.out.at(ls, 1n+nn)) == 1 : U32}

def chk.code_succ(_ls, nn):
  match nn:
    case 0n:
      {==}
    case 1n+_p:
      {==}

def Laws.check_unrun_error(path, runs):
  chk.code_succ((path ++ ":1:1: error: could not run bend") <> Check.lines_of(runs),
    List.length(&2, String, Check.lines_of(runs)))

def Laws.check_run_of(_path, _ds):
  {==}

def Laws.check_run_unrun(_path):
  {==}

def Laws.check_exec_ran(_names, _text):
  {==}

def Laws.check_exec_unrun(_names, _text):
  {==}

def Laws.check_exec_died(names, text, h):
  %Equal.sym(List<&2, Rep.Diag>, Rep.parse_in(names, text), [], h) : {Checker.died(_)
    == Checker.Unrun{} : Checker.Answer}
  {==}

def Laws.check_exec_died_reported(names, text, dd, ds, h):
  %Equal.sym(List<&2, Rep.Diag>, Rep.parse_in(names, text), dd <> ds, h) : {Checker.died(_)
    == Checker.Checked{dd <> ds} : Checker.Answer}
  {==}

# neither tag is no check
law chk.untagged:
  for ran: Bool
  for killed: Bool
  for -names: Maybe<&2, List<&2, String>>
  for text: String
  for h: {Bool.or(ran, killed) == False{} : Bool}
  {Checker.answer.tag(ran, killed, names, text) == Checker.Unrun{} : Checker.Answer}

def chk.untagged(ran, killed, names, text, h):
  match ran killed:
    case True{} _k:
      Empty.absurd({Checker.answer.tag(True{}, _k, names, text) == Checker.Unrun{} : Checker.Answer},
        bool.true_false(h))
    case False{} True{}:
      Empty.absurd({Checker.answer.tag(False{}, True{}, names, text) == Checker.Unrun{} : Checker.Answer},
        bool.true_false(h))
    case False{} False{}:
      {==}

def Laws.check_exec_untagged(names, cc, text, h):
  chk.untagged(Char.is_eq(cc, 'r'), Char.is_eq(cc, 's'), names, text, h)

def Laws.check_proof_unrun(_ds):
  {==}

# The line bend marks (laws/CheckPrintsBendErrors.bend). chk.report's text is its lines, each
# ended by a newline (mk.lines); Rep.parse walks them a line at a time, and
# each error's lines leave the parser's state holding that error, the one
# before it flushed (mk.block, mk.flush).

# a string opens with the empty string
law mk.sw_nil:
  for ss: String
  {String.starts_with(ss, SNil{}) == True{} : Bool}

def mk.sw_nil(ss):
  match ss:
    case SNil{}:
      {==}
    case SCon{_hh, _tt}:
      {==}

# a line's first character, the rest split at newlines: the character is no
# newline, as the line holds none
law mk.split.at:
  for +cc: Char
  for +tt: String
  for +rr: String
  for bb: Bool
  for hh: {String.contains.if(tt, "\n", String.starts_with.go.if(SNil{}, tt, bb)) == False{} : Bool}
  for ih: {String.contains(tt, "\n") == False{} : Bool}
    -> {String.split(String.append(tt, SCon{'\n', rr}), '\n') == tt <> String.split(rr, '\n') : List<&2,
      String>}
  {String.split.fin(cc, String.split(String.append(tt, SCon{'\n', rr}), '\n'), bb)
    == SCon{cc, tt} <> String.split(rr, '\n') : List<&2, String>}

def mk.split.at(cc, tt, rr, bb, hh, ih):
  match bb:
    case True{}:
      Empty.absurd({String.split.fin(cc, String.split(String.append(tt, SCon{'\n', rr}), '\n'), True{})
          == SCon{cc, tt} <> String.split(rr, '\n') : List<&2, String>},
        bool.true_false(Equal.trans(Bool, True{}, String.contains.if(tt, "\n", String.starts_with(tt,
          SNil{})), False{},
          Equal.sym(Bool, String.contains.if(tt, "\n", String.starts_with(tt, SNil{})), True{},
            Equal.cong(Bool, Bool, xx => String.contains.if(tt, "\n", xx), String.starts_with(tt, SNil{}),
              True{},
              mk.sw_nil(tt))),
          hh)))
    case False{}:
      Equal.cong(List<&2, String>, List<&2, String>, xs => String.split.push(cc, xs),
        String.split(String.append(tt, SCon{'\n', rr}), '\n'), tt <> String.split(rr, '\n'), ih(hh))

# a line with no newline in it, then a newline: split there, the line comes
# out whole
law mk.split:
  for ll: String
  for +rr: String
  for hh: {String.contains(ll, "\n") == False{} : Bool}
  {String.split(String.append(ll, SCon{'\n', rr}), '\n') == ll <> String.split(rr, '\n') : List<&2, String>}

def mk.split(ll, rr, hh):
  match ll:
    case SNil{}:
      {==}
    case SCon{+cc, +tt}:
      mk.split.at(cc, tt, rr, Char.is_eq(cc, '\n'), hh, xx => mk.split(tt, rr, xx))

# a report's text splits into its lines, and the empty line after the last
# newline
law mk.lines:
  for +ls: List<&2, String>
  for flat: Laws.chk.flat(ls)
  {String.split(Laws.chk.text(ls), '\n') == List.append(&2, String, ls, [""]) : List<&2, String>}

def mk.lines(ls, flat):
  match ls:
    case Nil{}:
      {==}
    case Con{+ll, +rest}:
      (h1, h2) = flat
      Equal.trans(List<&2, String>, String.split(String.append(ll, SCon{'\n', Laws.chk.text(rest)}), '\n'),
        ll <> String.split(Laws.chk.text(rest), '\n'), ll <> List.append(&2, String, rest, [""]),
        mk.split(ll, Laws.chk.text(rest), h1),
        Equal.cong(List<&2, String>, List<&2, String>, xs => ll <> xs, String.split(Laws.chk.text(rest),
          '\n'),
          List.append(&2, String, rest, [""]), mk.lines(rest, h2)))

# the parser over two runs of lines is the parser over the first, then the
# second
law mk.run_app:
  for aa: List<&2, String>
  for bb: List<&2, String>
  for st: Rep.St
  {Rep.run(List.append(&2, String, aa, bb), st) == Rep.run(bb, Rep.run(aa, st)) : Rep.St}

def mk.run_app(aa, bb, st):
  match aa:
    case Nil{}:
      {==}
    case Con{ll, rest}:
      mk.run_app(rest, bb, Rep.step(ll, st))

# an empty line changes nothing
law mk.blank:
  for st: Rep.St
  {Rep.step("", st) == st : Rep.St}

def mk.blank(st):
  match st:
    case Rep.St{seen, located, _msg, _line, _place, _out}:
      match seen located:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}

# what a state flushes: its diagnostics so far, reversed, the pending one on
# top
def mk.pend(st: Rep.St) -> List<&2, Rep.Raw>:
  Rep.St{seen, _located, msg, line, place, out} = st
  Rep.flush(seen, msg, line, place, out)

# the parser's answer is what its last state flushes, in order
law mk.finish:
  for st: Rep.St
  {Rep.finish(st) == List.reverse(&2, Rep.Raw, mk.pend(st)) : List<&2, Rep.Raw>}

def mk.finish(st):
  match st:
    case Rep.St{_seen, _located, _msg, _line, _place, _out}:
      {==}

# reversing onto acc, then onto ys: acc back in order, then the list, then ys
law mk.rev_go:
  for -A: Kind(&2)
  for xs: List<&2, A>
  for acc: List<&2, A>
  for ys: List<&2, A>
  {List.reverse.go(&2, A, List.reverse.go(&2, A, xs, acc), ys)
    == List.reverse.go(&2, A, acc, List.append(&2, A, xs, ys)) : List<&2, A>}

def mk.rev_go(A, xs, acc, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{xx, rest}:
      mk.rev_go(A, rest, xx <> acc, ys)

# a list reversed twice is itself
law mk.rev_rev:
  for -A: Kind(&2)
  for +xs: List<&2, A>
  {List.reverse(&2, A, List.reverse(&2, A, xs)) == xs : List<&2, A>}

def mk.rev_rev(A, xs):
  Equal.trans(List<&2, A>, List.reverse(&2, A, List.reverse(&2, A, xs)), List.append(&2, A, xs, []), xs,
    mk.rev_go(A, xs, [], []), M1.lint.app_nil(A, xs))

# two lists reversed onto acc: the first, then the second
law mk.rev_app:
  for -A: Kind(&2)
  for xs: List<&2, A>
  for ys: List<&2, A>
  for acc: List<&2, A>
  {List.reverse.go(&2, A, List.append(&2, A, xs, ys), acc)
    == List.reverse.go(&2, A, ys, List.reverse.go(&2, A, xs, acc)) : List<&2, A>}

def mk.rev_app(A, xs, ys, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{xx, rest}:
      mk.rev_app(A, rest, ys, xx <> acc)

# a digit is not whitespace
law mk.digit_trim:
  for dd: Laws.chk.Dig
  for +xx: String
  {String.trim_start(SCon{Laws.chk.digit(dd), xx}) == SCon{Laws.chk.digit(dd), xx} : String}

def mk.digit_trim(dd, _xx):
  match dd:
    case Laws.ChkD0{}:
      {==}
    case Laws.ChkD1{}:
      {==}
    case Laws.ChkD2{}:
      {==}
    case Laws.ChkD3{}:
      {==}
    case Laws.ChkD4{}:
      {==}
    case Laws.ChkD5{}:
      {==}
    case Laws.ChkD6{}:
      {==}
    case Laws.ChkD7{}:
      {==}
    case Laws.ChkD8{}:
      {==}
    case Laws.ChkD9{}:
      {==}

# a number's padding trims away, down to its first digit
law mk.pad_trim:
  for kk: Nat
  for dd: Laws.chk.Dig
  for +xx: String
  {String.trim_start(String.append(Laws.chk.pad(kk), SCon{Laws.chk.digit(dd), xx}))
    == SCon{Laws.chk.digit(dd), xx} : String}

def mk.pad_trim(kk, dd, xx):
  match kk:
    case 0n:
      mk.digit_trim(dd, xx)
    case 1n+pp:
      mk.pad_trim(pp, dd, xx)

# the marker reader counts a digit and reads on
law mk.go_digit:
  for dd: Laws.chk.Dig
  for +xx: String
  for +whole: String
  for +kk: Nat
  {Rep.marker.go(SCon{Laws.chk.digit(dd), xx}, whole, kk) == Rep.marker.go(xx, whole, 1n+kk) : Maybe<&2, U32>}

def mk.go_digit(dd, _xx, _whole, _kk):
  match dd:
    case Laws.ChkD0{}:
      {==}
    case Laws.ChkD1{}:
      {==}
    case Laws.ChkD2{}:
      {==}
    case Laws.ChkD3{}:
      {==}
    case Laws.ChkD4{}:
      {==}
    case Laws.ChkD5{}:
      {==}
    case Laws.ChkD6{}:
      {==}
    case Laws.ChkD7{}:
      {==}
    case Laws.ChkD8{}:
      {==}
    case Laws.ChkD9{}:
      {==}

# one more on the right is one more
law mk.add_succ:
  for aa: Nat
  for +bb: Nat
  {Nat.add(aa, 1n+bb) == 1n+Nat.add(aa, bb) : Nat}

def mk.add_succ(aa, bb):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 1n+bb), 1n+Nat.add(pp, bb), mk.add_succ(pp, bb))

# nothing on the right adds nothing
law mk.add_zero:
  for aa: Nat
  {Nat.add(aa, 0n) == aa : Nat}

def mk.add_zero(aa):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 0n), pp, mk.add_zero(pp))

# the marker reader counts a numeral's digits and reads on past them
law mk.digits:
  for ds: List<&2, Laws.chk.Dig>
  for +rr: String
  for +whole: String
  for +kk: Nat
  {Rep.marker.go(String.append(Laws.chk.num(ds), rr), whole, kk)
    == Rep.marker.go(rr, whole, Nat.add(List.length(&2, Laws.chk.Dig, ds), kk)) : Maybe<&2, U32>}

def mk.digits(ds, rr, whole, kk):
  match ds:
    case Nil{}:
      {==}
    case Con{dd, +rest}:
      Equal.trans(Maybe<&2, U32>,
        Rep.marker.go(SCon{Laws.chk.digit(dd), String.append(Laws.chk.num(rest), rr)}, whole, kk),
        Rep.marker.go(String.append(Laws.chk.num(rest), rr), whole, 1n+kk),
        Rep.marker.go(rr, whole, 1n+Nat.add(List.length(&2, Laws.chk.Dig, rest), kk)),
        mk.go_digit(dd, String.append(Laws.chk.num(rest), rr), whole, kk),
        Equal.trans(Maybe<&2, U32>, Rep.marker.go(String.append(Laws.chk.num(rest), rr), whole, 1n+kk),
          Rep.marker.go(rr, whole, Nat.add(List.length(&2, Laws.chk.Dig, rest), 1n+kk)),
          Rep.marker.go(rr, whole, 1n+Nat.add(List.length(&2, Laws.chk.Dig, rest), kk)),
          mk.digits(rest, rr, whole, 1n+kk),
          Equal.cong(Nat, Maybe<&2, U32>, xx => Rep.marker.go(rr, whole, xx),
            Nat.add(List.length(&2, Laws.chk.Dig, rest), 1n+kk), 1n+Nat.add(List.length(&2, Laws.chk.Dig,
              rest), kk),
            mk.add_succ(List.length(&2, Laws.chk.Dig, rest), kk))))

# as many characters as a numeral has digits, taken from the numeral and what
# follows it, are the numeral
law mk.take:
  for ds: List<&2, Laws.chk.Dig>
  for +rr: String
  {String.take(String.append(Laws.chk.num(ds), SCon{'>', rr}), List.length(&2, Laws.chk.Dig, ds))
    == Laws.chk.num(ds) : String}

def mk.take(ds, rr):
  match ds:
    case Nil{}:
      {==}
    case Con{dd, +rest}:
      Equal.cong(String, String, xx => SCon{Laws.chk.digit(dd), xx},
        String.take(String.append(Laws.chk.num(rest), SCon{'>', rr}), List.length(&2, Laws.chk.Dig, rest)),
        Laws.chk.num(rest), mk.take(rest, rr))

# the marked line marks the number its numeral reads as
law mk.mark:
  for +pad: Nat
  for +first: Laws.chk.Dig
  for +rest: List<&2, Laws.chk.Dig>
  for +code: String
  {Rep.marker(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code},
    ">| ")) == U32.read(Laws.chk.num(first <> rest))
    : Maybe<&2, U32>}

def mk.mark(pad, first, rest, code):
  Equal.trans(Maybe<&2, U32>,
    Rep.marker(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ")),
    Rep.marker.go(String.append(Laws.chk.num(first <> rest), ">| " ++ code),
      String.append(Laws.chk.num(first <> rest), ">| " ++ code), 0n),
    U32.read(Laws.chk.num(first <> rest)),
    Equal.cong(String, Maybe<&2, U32>, xx => Rep.marker.go(xx, xx, 0n),
      String.trim_start(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ")),
      String.append(Laws.chk.num(first <> rest), ">| " ++ code),
      mk.pad_trim(pad, first, String.append(Laws.chk.num(rest), ">| " ++ code))),
    Equal.trans(Maybe<&2, U32>,
      Rep.marker.go(String.append(Laws.chk.num(first <> rest), ">| " ++ code),
        String.append(Laws.chk.num(first <> rest), ">| " ++ code), 0n),
      U32.read(String.take(String.append(Laws.chk.num(first <> rest), ">| " ++ code),
        Nat.add(List.length(&2, Laws.chk.Dig, first <> rest), 0n))),
      U32.read(Laws.chk.num(first <> rest)),
      mk.digits(first <> rest, ">| " ++ code, String.append(Laws.chk.num(first <> rest), ">| " ++ code), 0n),
      Equal.trans(Maybe<&2, U32>,
        U32.read(String.take(String.append(Laws.chk.num(first <> rest), ">| " ++ code),
          Nat.add(List.length(&2, Laws.chk.Dig, first <> rest), 0n))),
        U32.read(String.take(String.append(Laws.chk.num(first <> rest), ">| " ++ code),
          List.length(&2, Laws.chk.Dig, first <> rest))),
        U32.read(Laws.chk.num(first <> rest)),
        Equal.cong(Nat, Maybe<&2, U32>,
          xx => U32.read(String.take(String.append(Laws.chk.num(first <> rest), ">| " ++ code), xx)),
          Nat.add(List.length(&2, Laws.chk.Dig, first <> rest), 0n), List.length(&2, Laws.chk.Dig,
            first <> rest),
          mk.add_zero(List.length(&2, Laws.chk.Dig, first <> rest))),
        Equal.cong(String, Maybe<&2, U32>, xx => U32.read(xx),
          String.take(String.append(Laws.chk.num(first <> rest), ">| " ++ code),
            List.length(&2, Laws.chk.Dig, first <> rest)),
          Laws.chk.num(first <> rest), mk.take(first <> rest, "| " ++ code)))))

# a line of context marks nothing, whatever its code holds
law mk.ctx:
  for +pad: Nat
  for +first: Laws.chk.Dig
  for +rest: List<&2, Laws.chk.Dig>
  for +code: String
  {Rep.marker(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, " | ")) == None{} : Maybe<&2, U32>}

def mk.ctx(pad, first, rest, code):
  Equal.trans(Maybe<&2, U32>,
    Rep.marker(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, " | ")),
    Rep.marker.go(String.append(Laws.chk.num(first <> rest), " | " ++ code),
      String.append(Laws.chk.num(first <> rest), " | " ++ code), 0n),
    None{},
    Equal.cong(String, Maybe<&2, U32>, xx => Rep.marker.go(xx, xx, 0n),
      String.trim_start(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, " | ")),
      String.append(Laws.chk.num(first <> rest), " | " ++ code),
      mk.pad_trim(pad, first, String.append(Laws.chk.num(rest), " | " ++ code))),
    mk.digits(first <> rest, " | " ++ code, String.append(Laws.chk.num(first <> rest), " | " ++ code), 0n))

# a source line is no Error or Location line
law mk.classify:
  for +ss: Laws.chk.Src
  for +sep: String
  {Rep.classify(Laws.chk.src(ss, sep)) == Rep.KOther{Laws.chk.src(ss, sep)} : Rep.Line}

def mk.classify(ss, _sep):
  match ss:
    case Laws.ChkSrc{pad, first, _rest, _code}:
      match pad first:
        case 1n+_pp _first:
          {==}
        case 0n Laws.ChkD0{}:
          {==}
        case 0n Laws.ChkD1{}:
          {==}
        case 0n Laws.ChkD2{}:
          {==}
        case 0n Laws.ChkD3{}:
          {==}
        case 0n Laws.ChkD4{}:
          {==}
        case 0n Laws.ChkD5{}:
          {==}
        case 0n Laws.ChkD6{}:
          {==}
        case 0n Laws.ChkD7{}:
          {==}
        case 0n Laws.ChkD8{}:
          {==}
        case 0n Laws.ChkD9{}:
          {==}

# a line of context, after the Location line, leaves the state as it was
law mk.context:
  for mm: Maybe<&2, Laws.chk.Src>
  for +msg: List<&2, String>
  for +line: U32
  for +place: String
  for +out: List<&2, Rep.Raw>
  {Rep.run(Laws.chk.context(mm), Rep.St{True{}, True{}, msg, line, place, out})
    == Rep.St{True{}, True{}, msg, line, place, out} : Rep.St}

def mk.context(mm, msg, line, place, out):
  match mm:
    case None{}:
      {==}
    case Some{Laws.ChkSrc{+pad, +first, +rest, +code}}:
      Equal.trans(Rep.St,
        Rep.step.go(Rep.classify(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, " | ")), True{}, True{},
          msg, line, place, out),
        Rep.St{True{}, True{}, msg,
          Maybe.default(&2, U32, Rep.marker(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, " | ")),
            line), place, out},
        Rep.St{True{}, True{}, msg, line, place, out},
        Equal.cong(Rep.Line, Rep.St, kk => Rep.step.go(kk, True{}, True{}, msg, line, place, out),
          Rep.classify(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, " | ")),
          Rep.KOther{Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, " | ")},
          mk.classify(Laws.ChkSrc{pad, first, rest, code}, " | ")),
        Equal.cong(Maybe<&2, U32>, Rep.St,
          mm => Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, mm, line), place, out},
          Rep.marker(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, " | ")), None{},
          mk.ctx(pad, first, rest, code)))

# the marked line, after the Location line, sets the line to the number it
# marks, or leaves it when the numeral does not read
law mk.mark_step:
  for +pad: Nat
  for +first: Laws.chk.Dig
  for +rest: List<&2, Laws.chk.Dig>
  for +code: String
  for +msg: List<&2, String>
  for +line: U32
  for +place: String
  for +out: List<&2, Rep.Raw>
  {Rep.step(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| "), Rep.St{True{}, True{}, msg, line,
    place, out})
    == Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, U32.read(Laws.chk.num(first <> rest)), line),
      place, out}
    : Rep.St}

def mk.mark_step(pad, first, rest, code, msg, line, place, out):
  Equal.trans(Rep.St,
    Rep.step.go(Rep.classify(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ")), True{}, True{},
      msg, line, place, out),
    Rep.St{True{}, True{}, msg,
      Maybe.default(&2, U32, Rep.marker(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ")), line),
        place, out},
    Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, U32.read(Laws.chk.num(first <> rest)), line), place,
      out},
    Equal.cong(Rep.Line, Rep.St, kk => Rep.step.go(kk, True{}, True{}, msg, line, place, out),
      Rep.classify(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ")),
      Rep.KOther{Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ")},
      mk.classify(Laws.ChkSrc{pad, first, rest, code}, ">| ")),
    Equal.cong(Maybe<&2, U32>, Rep.St,
      mm => Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, mm, line), place, out},
      Rep.marker(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ")),
        U32.read(Laws.chk.num(first <> rest)),
      mk.mark(pad, first, rest, code)))

# an excerpt, after the Location line, sets the line to the number it marks
law mk.span:
  for mm: Maybe<&2, Laws.chk.Span>
  for +msg: List<&2, String>
  for +place: String
  for +out: List<&2, Rep.Raw>
  {Rep.run(Laws.chk.span(mm), Rep.St{True{}, True{}, msg, 0, place, out})
    == Rep.St{True{}, True{}, msg, Laws.chk.marks(mm), place, out} : Rep.St}

def mk.span(mm, msg, place, out):
  match mm:
    case None{}:
      {==}
    case Some{Laws.ChkSpan{+before, Laws.ChkSrc{+pad, +first, +rest, +code}, +after}}:
      Equal.trans(Rep.St,
        Rep.run(List.append(&2, String, Laws.chk.context(before),
          Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ") <> Laws.chk.context(after)),
          Rep.St{True{}, True{}, msg, 0, place, out}),
        Rep.run(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ") <> Laws.chk.context(after),
          Rep.run(Laws.chk.context(before), Rep.St{True{}, True{}, msg, 0, place, out})),
        Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, U32.read(Laws.chk.num(first <> rest)), 0), place,
          out},
        mk.run_app(Laws.chk.context(before),
          Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ") <> Laws.chk.context(after),
          Rep.St{True{}, True{}, msg, 0, place, out}),
        Equal.trans(Rep.St,
          Rep.run(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ") <> Laws.chk.context(after),
            Rep.run(Laws.chk.context(before), Rep.St{True{}, True{}, msg, 0, place, out})),
          Rep.run(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| ") <> Laws.chk.context(after),
            Rep.St{True{}, True{}, msg, 0, place, out}),
          Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, U32.read(Laws.chk.num(first <> rest)), 0),
            place, out},
          Equal.cong(Rep.St, Rep.St,
            ss => Rep.run(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code},
              ">| ") <> Laws.chk.context(after), ss),
            Rep.run(Laws.chk.context(before), Rep.St{True{}, True{}, msg, 0, place, out}),
            Rep.St{True{}, True{}, msg, 0, place, out},
            mk.context(before, msg, 0, place, out)),
          Equal.trans(Rep.St,
            Rep.run(Laws.chk.context(after),
              Rep.step(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| "), Rep.St{True{}, True{}, msg,
                0, place, out})),
            Rep.run(Laws.chk.context(after),
              Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, U32.read(Laws.chk.num(first <> rest)), 0),
                place, out}),
            Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, U32.read(Laws.chk.num(first <> rest)), 0),
              place, out},
            Equal.cong(Rep.St, Rep.St, ss => Rep.run(Laws.chk.context(after), ss),
              Rep.step(Laws.chk.src(Laws.ChkSrc{pad, first, rest, code}, ">| "), Rep.St{True{}, True{}, msg,
                0, place, out}),
              Rep.St{True{}, True{}, msg, Maybe.default(&2, U32, U32.read(Laws.chk.num(first <> rest)), 0),
                place, out},
              mk.mark_step(pad, first, rest, code, msg, 0, place, out)),
            mk.context(after, msg, Maybe.default(&2, U32, U32.read(Laws.chk.num(first <> rest)), 0), place,
              out))))

# bend's note, after the Location line, leaves the state as it was
law mk.note_loc:
  for nb: Bool
  for +msg: List<&2, String>
  for +line: U32
  for +place: String
  for +out: List<&2, Rep.Raw>
  {Rep.run(Laws.chk.note(nb), Rep.St{True{}, True{}, msg, line, place, out})
    == Rep.St{True{}, True{}, msg, line, place, out} : Rep.St}

def mk.note_loc(nb, _msg, _line, _place, _out):
  match nb:
    case False{}:
      {==}
    case True{}:
      {==}

# bend's note, with no Location line before it, joins the message
law mk.note_unloc:
  for nb: Bool
  for +msg: List<&2, String>
  for +line: U32
  for +place: String
  for +out: List<&2, Rep.Raw>
  {Rep.run(Laws.chk.note(nb), Rep.St{True{}, False{}, msg, line, place, out})
    == Rep.St{True{}, False{}, List.reverse.go(&2, String, Laws.chk.note(nb), msg), line, place,
      out} : Rep.St}

def mk.note_unloc(nb, _msg, _line, _place, _out):
  match nb:
    case False{}:
      {==}
    case True{}:
      {==}

# a `- text` line reads as its text
law mk.clean:
  for +text: String
  {Rep.clean("- " ++ text) == text : String}

def mk.clean(text):
  match text:
    case SNil{}:
      {==}
    case SCon{_hh, _tt}:
      {==}

# a line neither empty nor the nag joins the message
law mk.push.at:
  for aa: Bool
  for bb: Bool
  for -text: String
  for -msg: List<&2, String>
  for ea: {aa == False{} : Bool}
  for eb: {bb == False{} : Bool}
  {Bool.pick(List<&2, String>, Bool.or(aa, bb), msg, text <> msg) == text <> msg : List<&2, String>}

def mk.push.at(aa, bb, text, msg, ea, eb):
  match aa bb:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({Bool.pick(List<&2, String>, True{}, msg, text <> msg) == text <> msg : List<&2, String>},
        bool.true_false(eb))
    case True{} _bb:
      Empty.absurd({Bool.pick(List<&2, String>, True{}, msg, text <> msg) == text <> msg : List<&2, String>},
        bool.true_false(ea))

# a message line joins the message
law mk.push:
  for +text: String
  for +msg: List<&2, String>
  for e1: {String.is_empty(text) == False{} : Bool}
  for e2: {String.contains(text, "is available: run bend update") == False{} : Bool}
  {Rep.push(text, msg) == text <> msg : List<&2, String>}

def mk.push(text, msg, e1, e2):
  mk.push.at(String.is_empty(text), String.contains(text, "is available: run bend update"), text, msg, e1, e2)

# the message lines, after `Error:`, each join the message
law mk.parts:
  for ps: List<&2, Laws.chk.Part>
  for +msg: List<&2, String>
  for +line: U32
  for +place: String
  for +out: List<&2, Rep.Raw>
  for ok: Laws.chk.parts_ok(ps)
  {Rep.run(Laws.chk.parts(ps), Rep.St{True{}, False{}, msg, line, place, out})
    == Rep.St{True{}, False{}, List.reverse.go(&2, String, Laws.chk.texts(ps), msg), line, place,
      out} : Rep.St}

def mk.parts(ps, msg, line, place, out, ok):
  match ps:
    case Nil{}:
      {==}
    case Con{Laws.ChkItem{+text}, +rest}:
      ((e1, e2), okr) = ok
      Equal.trans(Rep.St,
        Rep.run(Laws.chk.parts(rest), Rep.St{True{}, False{}, Rep.push(Rep.clean("- " ++ text), msg), line,
          place, out}),
        Rep.run(Laws.chk.parts(rest), Rep.St{True{}, False{}, text <> msg, line, place, out}),
        Rep.St{True{}, False{}, List.reverse.go(&2, String, Laws.chk.texts(rest), text <> msg), line, place,
          out},
        Equal.cong(List<&2, String>, Rep.St,
          mm => Rep.run(Laws.chk.parts(rest), Rep.St{True{}, False{}, mm, line, place, out}),
          Rep.push(Rep.clean("- " ++ text), msg), text <> msg,
          Equal.trans(List<&2, String>, Rep.push(Rep.clean("- " ++ text), msg), Rep.push(text, msg),
            text <> msg,
            Equal.cong(String, List<&2, String>, xx => Rep.push(xx, msg), Rep.clean("- " ++ text), text,
              mk.clean(text)),
            mk.push(text, msg, e1, e2))),
        mk.parts(rest, text <> msg, line, place, out, okr))
    case Con{Laws.ChkCtx{}, rest}:
      mk.parts(rest, "Context:" <> msg, line, place, out, ok)

# whether bend said where an error is
def mk.located(at: Maybe<&2, Laws.chk.Where>) -> Bool:
  match at:
    case None{}:
      False{}
    case Some{_ww}:
      True{}

# the Location line and the excerpt set where the error is and its line
law mk.where:
  for at: Maybe<&2, Laws.chk.Where>
  for +msg: List<&2, String>
  for +out: List<&2, Rep.Raw>
  for ok: Laws.chk.name_ok(at)
  {Rep.run(Laws.chk.where(at), Rep.St{True{}, False{}, msg, 0, "", out})
    == Rep.St{True{}, mk.located(at), msg, Laws.chk.marked(at), Laws.chk.place(at), out} : Rep.St}

def mk.where(at, msg, out, ok):
  match at:
    case None{}:
      {==}
    case Some{Laws.ChkWhere{None{}, span}}:
      mk.span(span, msg, "", out)
    case Some{Laws.ChkWhere{Some{+nn}, +span}}:
      Equal.trans(Rep.St,
        Rep.run(Laws.chk.span(span), Rep.St{True{}, True{}, msg, 0, String.trim_start(nn), out}),
        Rep.run(Laws.chk.span(span), Rep.St{True{}, True{}, msg, 0, nn, out}),
        Rep.St{True{}, True{}, msg, Laws.chk.marks(span), nn, out},
        Equal.cong(String, Rep.St, pp => Rep.run(Laws.chk.span(span), Rep.St{True{}, True{}, msg, 0, pp,
          out}),
          String.trim_start(nn), nn, ok),
        mk.span(span, msg, nn, out))

# the state after an error's lines: the error pending, what came before it
# flushed to out
def mk.after(ee: Laws.chk.Err, out: List<&2, Rep.Raw>) -> Rep.St:
  Laws.ChkErr{parts, +at, note} = ee
  Rep.St{True{}, mk.located(at),
    List.reverse.go(&2, String, Laws.chk.said(at, Laws.chk.texts(parts), Laws.chk.note(note)), []),
    Laws.chk.marked(at), Laws.chk.place(at), out}

# bend's note, last in an error's lines, leaves the message it said
law mk.block.note:
  for at: Maybe<&2, Laws.chk.Where>
  for +ts: List<&2, String>
  for +nb: Bool
  for +out: List<&2, Rep.Raw>
  {Rep.run(Laws.chk.note(nb),
      Rep.St{True{}, mk.located(at), List.reverse.go(&2, String, ts, []), Laws.chk.marked(at),
        Laws.chk.place(at), out})
    == Rep.St{True{}, mk.located(at), List.reverse.go(&2, String, Laws.chk.said(at, ts, Laws.chk.note(nb)),
      []),
      Laws.chk.marked(at), Laws.chk.place(at), out} : Rep.St}

def mk.block.note(at, ts, nb, out):
  match at:
    case None{}:
      Equal.trans(Rep.St,
        Rep.run(Laws.chk.note(nb), Rep.St{True{}, False{}, List.reverse.go(&2, String, ts, []), 0, "", out}),
        Rep.St{True{}, False{}, List.reverse.go(&2, String, Laws.chk.note(nb), List.reverse.go(&2, String,
          ts, [])),
          0, "", out},
        Rep.St{True{}, False{}, List.reverse.go(&2, String, List.append(&2, String, ts, Laws.chk.note(nb)),
          []),
          0, "", out},
        mk.note_unloc(nb, List.reverse.go(&2, String, ts, []), 0, "", out),
        Equal.cong(List<&2, String>, Rep.St, mm => Rep.St{True{}, False{}, mm, 0, "", out},
          List.reverse.go(&2, String, Laws.chk.note(nb), List.reverse.go(&2, String, ts, [])),
          List.reverse.go(&2, String, List.append(&2, String, ts, Laws.chk.note(nb)), []),
          Equal.sym(List<&2, String>,
            List.reverse.go(&2, String, List.append(&2, String, ts, Laws.chk.note(nb)), []),
            List.reverse.go(&2, String, Laws.chk.note(nb), List.reverse.go(&2, String, ts, [])),
            mk.rev_app(String, ts, Laws.chk.note(nb), []))))
    case Some{+ww}:
      mk.note_loc(nb, List.reverse.go(&2, String, ts, []), Laws.chk.marked(Some{ww}),
        Laws.chk.place(Some{ww}), out)

# an error's lines leave the parser holding that error, what came before it
# flushed
law mk.block:
  for ee: Laws.chk.Err
  for st: Rep.St
  for okp: Laws.chk.parts_ok(Laws.chk.err_parts(ee))
  for okn: Laws.chk.name_ok(Laws.chk.err_at(ee))
  {Rep.run(Laws.chk.lines(ee), st) == mk.after(ee, mk.pend(st)) : Rep.St}

def mk.block(ee, st, okp, okn):
  match ee st:
    case Laws.ChkErr{+parts, +at, +note} Rep.St{+seen, +located, +msg, +line, +place, +out}:
      +flushed = Rep.flush(seen, msg, line, place, out)
      +said = List.reverse.go(&2, String, Laws.chk.texts(parts), [])
      +lp = Laws.chk.parts(parts)
      +lw = Laws.chk.where(at)
      +ln = Laws.chk.note(note)
      Equal.trans(Rep.St,
        Rep.run(List.append(&2, String, lp, List.append(&2, String, lw, ln)), Rep.St{True{}, False{}, [], 0,
          "", flushed}),
        Rep.run(List.append(&2, String, lw, ln), Rep.run(lp, Rep.St{True{}, False{}, [], 0, "", flushed})),
        mk.after(Laws.ChkErr{parts, at, note}, flushed),
        mk.run_app(lp, List.append(&2, String, lw, ln), Rep.St{True{}, False{}, [], 0, "", flushed}),
        Equal.trans(Rep.St,
          Rep.run(List.append(&2, String, lw, ln), Rep.run(lp, Rep.St{True{}, False{}, [], 0, "", flushed})),
          Rep.run(List.append(&2, String, lw, ln), Rep.St{True{}, False{}, said, 0, "", flushed}),
          mk.after(Laws.ChkErr{parts, at, note}, flushed),
          Equal.cong(Rep.St, Rep.St, ss => Rep.run(List.append(&2, String, lw, ln), ss),
            Rep.run(lp, Rep.St{True{}, False{}, [], 0, "", flushed}), Rep.St{True{}, False{}, said, 0, "",
              flushed},
            mk.parts(parts, [], 0, "", flushed, okp)),
          Equal.trans(Rep.St,
            Rep.run(List.append(&2, String, lw, ln), Rep.St{True{}, False{}, said, 0, "", flushed}),
            Rep.run(ln, Rep.run(lw, Rep.St{True{}, False{}, said, 0, "", flushed})),
            mk.after(Laws.ChkErr{parts, at, note}, flushed),
            mk.run_app(lw, ln, Rep.St{True{}, False{}, said, 0, "", flushed}),
            Equal.trans(Rep.St,
              Rep.run(ln, Rep.run(lw, Rep.St{True{}, False{}, said, 0, "", flushed})),
              Rep.run(ln, Rep.St{True{}, mk.located(at), said, Laws.chk.marked(at), Laws.chk.place(at),
                flushed}),
              mk.after(Laws.ChkErr{parts, at, note}, flushed),
              Equal.cong(Rep.St, Rep.St, ss => Rep.run(ln, ss),
                Rep.run(lw, Rep.St{True{}, False{}, said, 0, "", flushed}),
                Rep.St{True{}, mk.located(at), said, Laws.chk.marked(at), Laws.chk.place(at), flushed},
                mk.where(at, said, flushed, okn)),
              mk.block.note(at, Laws.chk.texts(parts), note, flushed)))))

# an error as the parser holds it before placing it: its place, the number
# it marks, and its message lines as one text
def mk.raw(+ee: Laws.chk.Err) -> Rep.Raw:
  +at = Laws.chk.err_at(ee)
  Rep.Raw{Laws.chk.place(at), Laws.chk.marked(at), Laws.chk.body(ee)}

# the errors as the parser holds them, in order
def mk.raws(es: List<&2, Laws.chk.Err>) -> List<&2, Rep.Raw>:
  match es:
    case Nil{}:
      []
    case Con{+ee, rest}:
      mk.raw(ee) <> mk.raws(rest)

# a message that is not "no main to run" is flushed
law mk.flush.pick:
  for bb: Bool
  for eb: {bb == False{} : Bool}
  for -yes: List<&2, Rep.Raw>
  for -no: List<&2, Rep.Raw>
  {Bool.pick(List<&2, Rep.Raw>, Bool.and(True{}, Bool.not(bb)), yes, no) == yes : List<&2, Rep.Raw>}

def mk.flush.pick(bb, eb, yes, no):
  match bb:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({Bool.pick(List<&2, Rep.Raw>, False{}, yes, no) == yes : List<&2, Rep.Raw>},
        bool.true_false(eb))

# the parser's message text, equal to the one said, flushed
law mk.flush.at:
  for +text: String
  for +spec: String
  for et: {text == spec : String}
  for hmain: {String.eq(spec, "no main to run") == False{} : Bool}
  for +place: String
  for +line: U32
  for +out: List<&2, Rep.Raw>
  {Bool.pick(List<&2, Rep.Raw>, Bool.and(True{}, Bool.not(String.eq(text, "no main to run"))),
      Rep.Raw{place, line, text} <> out, out) == Rep.Raw{place, line, spec} <> out : List<&2, Rep.Raw>}

def mk.flush.at(text, spec, et, hmain, place, line, out):
  %Equal.sym(String, text, spec, et) : {Bool.pick(List<&2, Rep.Raw>,
      Bool.and(True{}, Bool.not(String.eq(_, "no main to run"))),
      Rep.Raw{place, line, _} <> out, out) == Rep.Raw{place, line, spec} <> out : List<&2, Rep.Raw>}
  mk.flush.pick(String.eq(spec, "no main to run"), hmain, Rep.Raw{place, line, spec} <> out, out)

# the error the parser holds after its lines is flushed as it was said
law mk.flush:
  for +ee: Laws.chk.Err
  for +out: List<&2, Rep.Raw>
  for hmain: {String.eq(Laws.chk.body(ee), "no main to run") == False{} : Bool}
  {mk.pend(mk.after(ee, out)) == mk.raw(ee) <> out : List<&2, Rep.Raw>}

def mk.flush(ee, out, hmain):
  match ee:
    case Laws.ChkErr{+parts, +at, +note}:
      +said = Laws.chk.said(at, Laws.chk.texts(parts), Laws.chk.note(note))
      mk.flush.at(
        String.join(List.reverse(&2, String, List.reverse(&2, String, said)), "\n"),
        String.join(said, "\n"),
        Equal.cong(List<&2, String>, String, xs => String.join(xs, "\n"),
          List.reverse(&2, String, List.reverse(&2, String, said)), said, mk.rev_rev(String, said)),
        hmain, Laws.chk.place(at), Laws.chk.marked(at), out)

# every error's lines, one after another: each is flushed as it was said
law mk.all:
  for es: List<&2, Laws.chk.Err>
  for +st: Rep.St
  for fits: Laws.chk.fits(es)
  {mk.pend(Rep.run(Laws.chk.all(es), st))
    == List.reverse.go(&2, Rep.Raw, mk.raws(es), mk.pend(st)) : List<&2, Rep.Raw>}

def mk.all(es, st, fits):
  match es:
    case Nil{}:
      {==}
    case Con{+ee, +rest}:
      (((okp, okn), hmain), okr) = fits
      Equal.trans(List<&2, Rep.Raw>,
        mk.pend(Rep.run(List.append(&2, String, Laws.chk.lines(ee), Laws.chk.all(rest)), st)),
        mk.pend(Rep.run(Laws.chk.all(rest), Rep.run(Laws.chk.lines(ee), st))),
        List.reverse.go(&2, Rep.Raw, mk.raws(rest), mk.raw(ee) <> mk.pend(st)),
        Equal.cong(Rep.St, List<&2, Rep.Raw>, ss => mk.pend(ss),
          Rep.run(List.append(&2, String, Laws.chk.lines(ee), Laws.chk.all(rest)), st),
          Rep.run(Laws.chk.all(rest), Rep.run(Laws.chk.lines(ee), st)),
          mk.run_app(Laws.chk.lines(ee), Laws.chk.all(rest), st)),
        Equal.trans(List<&2, Rep.Raw>,
          mk.pend(Rep.run(Laws.chk.all(rest), Rep.run(Laws.chk.lines(ee), st))),
          mk.pend(Rep.run(Laws.chk.all(rest), mk.after(ee, mk.pend(st)))),
          List.reverse.go(&2, Rep.Raw, mk.raws(rest), mk.raw(ee) <> mk.pend(st)),
          Equal.cong(Rep.St, List<&2, Rep.Raw>, ss => mk.pend(Rep.run(Laws.chk.all(rest), ss)),
            Rep.run(Laws.chk.lines(ee), st), mk.after(ee, mk.pend(st)), mk.block(ee, st, okp, okn)),
          Equal.trans(List<&2, Rep.Raw>,
            mk.pend(Rep.run(Laws.chk.all(rest), mk.after(ee, mk.pend(st)))),
            List.reverse.go(&2, Rep.Raw, mk.raws(rest), mk.pend(mk.after(ee, mk.pend(st)))),
            List.reverse.go(&2, Rep.Raw, mk.raws(rest), mk.raw(ee) <> mk.pend(st)),
            mk.all(rest, mk.after(ee, mk.pend(st)), okr),
            Equal.cong(List<&2, Rep.Raw>, List<&2, Rep.Raw>, ds => List.reverse.go(&2, Rep.Raw,
              mk.raws(rest), ds),
              mk.pend(mk.after(ee, mk.pend(st))), mk.raw(ee) <> mk.pend(st), mk.flush(ee, mk.pend(st),
                hmain)))))

# one character looked at: the parser's stem is the spec's
law mk.stem.at:
  for bb: Bool
  for +hh: Char
  for -xx: String
  for -yy: String
  for ih: {xx == yy : String}
  {Lazy.stop(String, bb, SNil{}, _u => SCon{hh, xx}) == Bool.pick(String, bb, SNil{}, SCon{hh, yy}) : String}

def mk.stem.at(bb, hh, xx, yy, ih):
  match bb:
    case True{}:
      {==}
    case False{}:
      Equal.cong(String, String, zz => SCon{hh, zz}, xx, yy, ih)

# the parser's stem is the spec's
law mk.stem:
  for ss: String
  {Rep.stem(ss) == Laws.chk.stem(ss) : String}

def mk.stem(ss):
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      mk.stem.at(Char.is_eq(hh, '~'), hh, Rep.stem(tt), Laws.chk.stem(tt), mk.stem(tt))

# one name looked at: the parser's search is the spec's
law mk.owns.at:
  for bb: Bool
  for -rest: Bool
  for -more: Bool
  for ih: {rest == more : Bool}
  {Lazy.or_else(bb, _u => rest) == Bool.or(bb, more) : Bool}

def mk.owns.at(bb, _rest, _more, ih):
  match bb:
    case True{}:
      {==}
    case False{}:
      ih

# the parser's search for a name is the spec's
law mk.owns:
  for ks: List<&2, String>
  for +name: String
  {Rep.owns(ks, name) == Laws.chk.among(ks, name) : Bool}

def mk.owns(ks, name):
  match ks:
    case Nil{}:
      {==}
    case Con{+kk, +rest}:
      mk.owns.at(String.eq(kk, name), Rep.owns(rest, name), Laws.chk.among(rest, name), mk.owns(rest, name))

# the parser says an error is the file's exactly when the spec does
law mk.mine:
  for names: Maybe<&2, List<&2, String>>
  for +place: String
  {Rep.mine(names, place) == Laws.chk.own(names, place) : Bool}

def mk.mine(names, place):
  match names:
    case None{}:
      {==}
    case Some{+ks}:
      Equal.trans(Bool,
        Bool.or(String.is_empty(place), Rep.owns(ks, Rep.stem(place))),
        Bool.or(String.is_empty(place), Rep.owns(ks, Laws.chk.stem(place))),
        Bool.or(String.is_empty(place), Laws.chk.among(ks, Laws.chk.stem(place))),
        Equal.cong(String, Bool, xx => Bool.or(String.is_empty(place), Rep.owns(ks, xx)),
          Rep.stem(place), Laws.chk.stem(place), mk.stem(place)),
        Equal.cong(Bool, Bool, xx => Bool.or(String.is_empty(place), xx),
          Rep.owns(ks, Laws.chk.stem(place)), Laws.chk.among(ks, Laws.chk.stem(place)),
          mk.owns(ks, Laws.chk.stem(place))))

# an error placed by the parser is placed as the spec says
law mk.diag:
  for +names: Maybe<&2, List<&2, String>>
  for +ee: Laws.chk.Err
  {Rep.diag(names, mk.raw(ee)) == Laws.chk.diag(names, ee) : Rep.Diag}

def mk.diag(names, ee):
  +place = Laws.chk.place(Laws.chk.err_at(ee))
  +line = Laws.chk.marked(Laws.chk.err_at(ee))
  +body = Laws.chk.body(ee)
  Equal.cong(Bool, Rep.Diag, bb => Rep.diag.at(bb, place, line, body),
    Rep.mine(names, place), Laws.chk.own(names, place), mk.mine(names, place))

# every error placed by the parser is placed as the spec says
law mk.diags:
  for es: List<&2, Laws.chk.Err>
  for +names: Maybe<&2, List<&2, String>>
  {Rep.diags(mk.raws(es), names) == Laws.chk.diags(es, names) : List<&2, Rep.Diag>}

def mk.diags(es, names):
  match es:
    case Nil{}:
      {==}
    case Con{+ee, +rest}:
      Equal.trans(List<&2, Rep.Diag>,
        Rep.diag(names, mk.raw(ee)) <> Rep.diags(mk.raws(rest), names),
        Laws.chk.diag(names, ee) <> Rep.diags(mk.raws(rest), names),
        Laws.chk.diag(names, ee) <> Laws.chk.diags(rest, names),
        Equal.cong(Rep.Diag, List<&2, Rep.Diag>, dd => dd <> Rep.diags(mk.raws(rest), names),
          Rep.diag(names, mk.raw(ee)), Laws.chk.diag(names, ee), mk.diag(names, ee)),
        Equal.cong(List<&2, Rep.Diag>, List<&2, Rep.Diag>, ds => Laws.chk.diag(names, ee) <> ds,
          Rep.diags(mk.raws(rest), names), Laws.chk.diags(rest, names), mk.diags(rest, names)))

def Laws.check_marked(names, es, flat, fits):
  +init = {Rep.St{False{}, False{}, [], 0, "", []} : Rep.St}
  +ls = Laws.chk.all(es)
  Equal.trans(List<&2, Rep.Diag>,
    Rep.diags(Rep.finish(Rep.run(String.split(Laws.chk.text(ls), '\n'), init)), names),
    Rep.diags(Rep.finish(Rep.run(List.append(&2, String, ls, [""]), init)), names),
    Laws.chk.diags(es, names),
    Equal.cong(List<&2, String>, List<&2, Rep.Diag>, xs => Rep.diags(Rep.finish(Rep.run(xs, init)), names),
      String.split(Laws.chk.text(ls), '\n'), List.append(&2, String, ls, [""]), mk.lines(ls, flat)),
    Equal.trans(List<&2, Rep.Diag>,
      Rep.diags(Rep.finish(Rep.run(List.append(&2, String, ls, [""]), init)), names),
      Rep.diags(Rep.finish(Rep.step("", Rep.run(ls, init))), names),
      Laws.chk.diags(es, names),
      Equal.cong(Rep.St, List<&2, Rep.Diag>, ss => Rep.diags(Rep.finish(ss), names),
        Rep.run(List.append(&2, String, ls, [""]), init), Rep.run([""], Rep.run(ls, init)),
        mk.run_app(ls, [""], init)),
      Equal.trans(List<&2, Rep.Diag>,
        Rep.diags(Rep.finish(Rep.step("", Rep.run(ls, init))), names),
        Rep.diags(List.reverse(&2, Rep.Raw, mk.pend(Rep.run(ls, init))), names),
        Laws.chk.diags(es, names),
        Equal.trans(List<&2, Rep.Diag>,
          Rep.diags(Rep.finish(Rep.step("", Rep.run(ls, init))), names),
          Rep.diags(Rep.finish(Rep.run(ls, init)), names),
          Rep.diags(List.reverse(&2, Rep.Raw, mk.pend(Rep.run(ls, init))), names),
          Equal.cong(Rep.St, List<&2, Rep.Diag>, ss => Rep.diags(Rep.finish(ss), names),
            Rep.step("", Rep.run(ls, init)), Rep.run(ls, init), mk.blank(Rep.run(ls, init))),
          Equal.cong(List<&2, Rep.Raw>, List<&2, Rep.Diag>, rs => Rep.diags(rs, names),
            Rep.finish(Rep.run(ls, init)), List.reverse(&2, Rep.Raw, mk.pend(Rep.run(ls, init))),
            mk.finish(Rep.run(ls, init)))),
        Equal.trans(List<&2, Rep.Diag>,
          Rep.diags(List.reverse(&2, Rep.Raw, mk.pend(Rep.run(ls, init))), names),
          Rep.diags(mk.raws(es), names),
          Laws.chk.diags(es, names),
          Equal.cong(List<&2, Rep.Raw>, List<&2, Rep.Diag>, rs => Rep.diags(rs, names),
            List.reverse(&2, Rep.Raw, mk.pend(Rep.run(ls, init))), mk.raws(es),
            Equal.trans(List<&2, Rep.Raw>,
              List.reverse(&2, Rep.Raw, mk.pend(Rep.run(ls, init))),
              List.reverse(&2, Rep.Raw, List.reverse(&2, Rep.Raw, mk.raws(es))),
              mk.raws(es),
              Equal.cong(List<&2, Rep.Raw>, List<&2, Rep.Raw>, ds => List.reverse(&2, Rep.Raw, ds),
                mk.pend(Rep.run(ls, init)), List.reverse(&2, Rep.Raw, mk.raws(es)),
                mk.all(es, init, fits)),
              mk.rev_rev(Rep.Raw, mk.raws(es)))),
          mk.diags(es, names)))))

# a bit the same on both sides, the rest equal
law mk.wsub.arm:
  for -p: Nat
  for -h: Bool
  for -lhs: Word(p)
  for -at: Word(p)
  for e: {lhs == at : Word(p)}
  {WCon{h, lhs} == WCon{h, at} : Word.Con<p>}

def mk.wsub.arm(p, h, lhs, at, e):
  Equal.cong(Word(p), Word.Con<p>, w => WCon{h, w}, lhs, at, e)

# a word less another, plus it again, is itself: the two carries in, c and
# not c, add up to the one a subtraction borrows
law mk.wsub:
  for n: Nat
  for a: Word(n)
  for +b: Word(n)
  for c: Bool
  {Word.adc(n, Word.adc(n, a, b, True{}, c), b, False{}, Bool.not(c)) == a : Word(n)}

def mk.wsub(n, a, b, c):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+(+p):
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          mk.wsub.arm(p, False{}, Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, True{}), at,
            mk.wsub(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          mk.wsub.arm(p, False{}, Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, False{}), at,
            mk.wsub(p, at, bt, True{}))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          mk.wsub.arm(p, False{}, Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, True{}), at,
            mk.wsub(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          mk.wsub.arm(p, False{}, Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, True{}), at,
            mk.wsub(p, at, bt, False{}))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          mk.wsub.arm(p, True{}, Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, False{}), at,
            mk.wsub(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          mk.wsub.arm(p, True{}, Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, False{}), at,
            mk.wsub(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          mk.wsub.arm(p, True{}, Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, True{}), at,
            mk.wsub(p, at, bt, False{}))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          mk.wsub.arm(p, True{}, Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, False{}), at,
            mk.wsub(p, at, bt, True{}))

# a number less one, plus one, is itself
law mk.usub:
  for a: U32
  {U32.add(U32.sub(a, 1), 1) == a : U32}

def mk.usub(a):
  match a:
    case U32{w}:
      Equal.cong(Word(32n), U32, x => U32{x},
        Word.adc(32n, Word.adc(32n, w, WCon{True{}, Word.zero(31n)}, True{}, True{}), WCon{True{},
          Word.zero(31n)},
          False{}, False{}), w, mk.wsub(32n, w, WCon{True{}, Word.zero(31n)}, True{}))

# the printed number is the 0-based line plus one
law mk.shown:
  for bb: Bool
  for +vv: U32
  {U32.add(Bool.pick(U32, bb, 0, (vv - 1 : U32)), 1) == Bool.pick(U32, bb, 1, vv) : U32}

def mk.shown(bb, vv):
  match bb:
    case True{}:
      {==}
    case False{}:
      mk.usub(vv)

# each diagnostic printed: on the number chk.shown says, with its message
law mk.show_all:
  for es: List<&2, Laws.chk.Err>
  for +path: String
  for +names: Maybe<&2, List<&2, String>>
  {Check.show_all(Laws.chk.diags(es, names), path) == Laws.chk.printed(es, path, names) : List<&2, String>}

def mk.show_all(es, path, names):
  match es:
    case Nil{}:
      {==}
    case Con{+ee, +rest}:
      +own = Laws.chk.own(names, Laws.chk.place(Laws.chk.err_at(ee)))
      +vv = Laws.chk.marked(Laws.chk.err_at(ee))
      +msg = Laws.chk.msg(names, ee)
      Equal.trans(List<&2, String>,
        (path ++ ":" ++ U32.show((Laws.chk.row(own, vv) + 1 : U32)) ++ ":1: error: " ++ Check.message(msg))
          <> Check.show_all(Laws.chk.diags(rest, names), path),
        (path ++ ":" ++ U32.show(Laws.chk.shown(own, vv)) ++ ":1: error: " ++ Check.message(msg))
          <> Check.show_all(Laws.chk.diags(rest, names), path),
        Laws.chk.printed(Con{ee, rest}, path, names),
        Equal.cong(U32, List<&2, String>,
          xx => (path ++ ":" ++ U32.show(xx) ++ ":1: error: " ++ Check.message(msg))
            <> Check.show_all(Laws.chk.diags(rest, names), path),
          (Laws.chk.row(own, vv) + 1 : U32), Laws.chk.shown(own, vv),
          mk.shown(Bool.or(Bool.not(own), U32.is_eq(vv, 0)), vv)),
        Equal.cong(List<&2, String>, List<&2, String>,
          xs => (path ++ ":" ++ U32.show(Laws.chk.shown(own,
            vv)) ++ ":1: error: " ++ Check.message(msg)) <> xs,
          Check.show_all(Laws.chk.diags(rest, names), path), Laws.chk.printed(rest, path, names),
          mk.show_all(rest, path, names)))

def Laws.check_marked_line(names, path, es, flat, fits):
  Equal.trans(List<&2, String>,
    List.append(&2, String, Check.show_all(Rep.parse_in(names, Laws.chk.report(es)), path), []),
    List.append(&2, String, Check.show_all(Laws.chk.diags(es, names), path), []),
    Laws.chk.printed(es, path, names),
    Equal.cong(List<&2, Rep.Diag>, List<&2, String>, ds => List.append(&2, String, Check.show_all(ds, path),
      []),
      Rep.parse_in(names, Laws.chk.report(es)), Laws.chk.diags(es, names), Laws.check_marked(names, es,
        flat, fits)),
    Equal.trans(List<&2, String>,
      List.append(&2, String, Check.show_all(Laws.chk.diags(es, names), path), []),
      Check.show_all(Laws.chk.diags(es, names), path),
      Laws.chk.printed(es, path, names),
      M1.lint.app_nil(String, Check.show_all(Laws.chk.diags(es, names), path)),
      mk.show_all(es, path, names)))

# an error in another file prints on line 1, headed by where it is
law mk.import.at:
  for bb: Bool
  for eb: {bb == False{} : Bool}
  for +path: String
  for +name: String
  for +vv: U32
  for +body: String
  {[path ++ ":" ++ U32.show(Bool.pick(U32, Bool.or(Bool.not(bb), U32.is_eq(vv, 0)), 1, vv)) ++ ":1: error: "
      ++ Check.message(Bool.pick(String, bb, body, "in " ++ name ++ ":\n" ++ body))]
    == [path ++ ":1:1: error: " ++ Check.message("in " ++ name ++ ":\n" ++ body)] : List<&2, String>}

def mk.import.at(bb, eb, path, name, vv, body):
  match bb:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({[path ++ ":" ++ U32.show(Bool.pick(U32, Bool.or(False{}, U32.is_eq(vv, 0)), 1,
        vv)) ++ ":1: error: "
          ++ Check.message(Bool.pick(String, True{}, body, "in " ++ name ++ ":\n" ++ body))]
        == [path ++ ":1:1: error: " ++ Check.message("in " ++ name ++ ":\n" ++ body)] : List<&2, String>},
        bool.true_false(eb))

def Laws.check_import_first(names, path, parts, name, span, note, other, flat, fits):
  Equal.trans(List<&2, String>,
    Check.lines_of([Check.Run{path,
      Rep.parse_in(names, Laws.chk.report([Laws.ChkErr{parts, Some{Laws.ChkWhere{Some{name}, span}},
        note}]))}]),
    Laws.chk.printed([Laws.ChkErr{parts, Some{Laws.ChkWhere{Some{name}, span}}, note}], path, names),
    [path ++ ":1:1: error: " ++ Check.message("in " ++ name ++ ":\n" ++ String.join(Laws.chk.texts(parts),
      "\n"))],
    Laws.check_marked_line(names, path, [Laws.ChkErr{parts, Some{Laws.ChkWhere{Some{name}, span}}, note}],
      flat, fits),
    mk.import.at(Laws.chk.own(names, name), other, path, name, Laws.chk.marks(span),
      String.join(Laws.chk.texts(parts), "\n")))

# an error the file owns, with a marked line, prints on that line
law mk.own.at:
  for bb: Bool
  for eb: {bb == True{} : Bool}
  for cc: Bool
  for ec: {cc == False{} : Bool}
  for +path: String
  for +name: String
  for +vv: U32
  for +body: String
  {[path ++ ":" ++ U32.show(Bool.pick(U32, Bool.or(Bool.not(bb), cc), 1, vv)) ++ ":1: error: "
      ++ Check.message(Bool.pick(String, bb, body, "in " ++ name ++ ":\n" ++ body))]
    == [path ++ ":" ++ U32.show(vv) ++ ":1: error: " ++ Check.message(body)] : List<&2, String>}

def mk.own.at(bb, eb, cc, ec, path, name, vv, body):
  match bb cc:
    case True{} False{}:
      {==}
    case True{} True{}:
      Empty.absurd({[path ++ ":" ++ U32.show(Bool.pick(U32, Bool.or(False{}, True{}), 1, vv)) ++ ":1: error: "
          ++ Check.message(Bool.pick(String, True{}, body, "in " ++ name ++ ":\n" ++ body))]
        == [path ++ ":" ++ U32.show(vv) ++ ":1: error: " ++ Check.message(body)] : List<&2, String>},
        bool.true_false(ec))
    case False{} _cc:
      Empty.absurd({[path ++ ":" ++ U32.show(Bool.pick(U32, Bool.or(True{}, _cc), 1, vv)) ++ ":1: error: "
          ++ Check.message(Bool.pick(String, False{}, body, "in " ++ name ++ ":\n" ++ body))]
        == [path ++ ":" ++ U32.show(vv) ++ ":1: error: " ++ Check.message(body)] : List<&2, String>},
        bool.false_true(eb))

def Laws.check_own_marked(names, path, parts, name, span, note, own, some, flat, fits):
  Equal.trans(List<&2, String>,
    Check.lines_of([Check.Run{path,
      Rep.parse_in(names, Laws.chk.report([Laws.ChkErr{parts, Some{Laws.ChkWhere{Some{name}, Some{span}}},
        note}]))}]),
    Laws.chk.printed([Laws.ChkErr{parts, Some{Laws.ChkWhere{Some{name}, Some{span}}}, note}], path, names),
    [path ++ ":" ++ U32.show(Laws.chk.marks(Some{span})) ++ ":1: error: "
      ++ Check.message(String.join(Laws.chk.texts(parts), "\n"))],
    Laws.check_marked_line(names, path, [Laws.ChkErr{parts, Some{Laws.ChkWhere{Some{name}, Some{span}}},
      note}],
      flat, fits),
    mk.own.at(Laws.chk.own(names, name), own, U32.is_eq(Laws.chk.marks(Some{span}), 0), some, path, name,
      Laws.chk.marks(Some{span}), String.join(Laws.chk.texts(parts), "\n")))

def Laws.proved_clean_shows_none(pds, ds, e):
  %Equal.sym(Bool, List.is_empty(&2, Rep.Diag, pds), True{}, e) :
    {Checker.Checked{Bool.pick(List<&2, Rep.Diag>, _, [], ds)} == Checker.Checked{[]} : Checker.Answer}
  {==}

def Laws.proved_failing_shows_its_own(pds, ds, e):
  %Equal.sym(Bool, List.is_empty(&2, Rep.Diag, pds), False{}, e) :
    {Checker.Checked{Bool.pick(List<&2, Rep.Diag>, _, [], ds)} == Checker.Checked{ds} : Checker.Answer}
  {==}
