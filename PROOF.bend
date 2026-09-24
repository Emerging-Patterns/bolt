# bolt: the proofs of LAWS.bend. `bend PROOF.bend` is the gate.
import Base
import ./src/args.bend as Args
import ./src/version.bend as Ver
import ./src/build_rev.bend as Rev
import 0xba6940aab8a335b70bf79944bd9b53c4/main.bend as Shake
import ./LAWS.bend as Laws

# The command line (BOLT-CLI)
# ---------------------------
# shake walks argv one word at a time. A plain word in a free walker whose
# only positional left is the `files` rest binds one more file, and after
# `--` every word does; `help` collects the rest as a path, and an error
# keeps the walker dead. The laws below walk each shape over every word list,
# then read the finished walker back through Args.out.

# Unit for False, Empty for True: a motive that tells them apart
def cli.false_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Unit
    case True{}:
      Empty

# False is never True
law cli.false_true:
  for e: {False{} == True{} : Bool}
  Empty

def cli.false_true(e):
  %e : cli.false_ty(_)
  Unit{}

# True is never False
law cli.true_false:
  for e: {True{} == False{} : Bool}
  Empty

def cli.true_false(e):
  cli.false_true(Equal.sym(Bool, True{}, False{}, e))

# the left of a true nor is false
law cli.nor_l:
  for a: Bool
  for -b: Bool
  for h: {Bool.not(Bool.or(a, b)) == True{} : Bool}
  {a == False{} : Bool}

def cli.nor_l(a, _b, h):
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, cli.false_true(h))
    case False{}:
      {==}

# the right of a true nor is not true
law cli.nor_r:
  for a: Bool
  for b: Bool
  for h: {Bool.not(Bool.or(a, b)) == True{} : Bool}
  {Bool.not(b) == True{} : Bool}

def cli.nor_r(a, b, h):
  match a:
    case True{}:
      Empty.absurd({Bool.not(b) == True{} : Bool}, cli.false_true(h))
    case False{}:
      h

# a Bool whose negation is true is false
law cli.not_true:
  for b: Bool
  for h: {Bool.not(b) == True{} : Bool}
  {b == False{} : Bool}

def cli.not_true(b, h):
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, cli.false_true(h))
    case False{}:
      {==}

# the left of a true and is true
law cli.and_l:
  for a: Bool
  for -b: Bool
  for h: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def cli.and_l(a, _b, h):
  match a:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, cli.false_true(h))
    case True{}:
      {==}

# the right of a true and is true
law cli.and_r:
  for a: Bool
  for b: Bool
  for h: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def cli.and_r(a, b, h):
  match a:
    case False{}:
      Empty.absurd({b == True{} : Bool}, cli.false_true(h))
    case True{}:
      h

# two true Bools make a true and
law cli.and_true:
  for a: Bool
  for b: Bool
  for ha: {a == True{} : Bool}
  for hb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def cli.and_true(a, b, ha, hb):
  e = Equal.sym(Bool, a, True{}, ha)
  %e : {Bool.and(_, b) == True{} : Bool}
  hb

# a Maybe that is none is None
law cli.none_of:
  for mm: Maybe<&2, Shake.Sub>
  for h: {Maybe.is_none(&2, Shake.Sub, mm) == True{} : Bool}
  {mm == None{} : Maybe<&2, Shake.Sub>}

def cli.none_of(mm, h):
  match mm:
    case None{}:
      {==}
    case Some{s}:
      Empty.absurd({Some{s} == None{} : Maybe<&2, Shake.Sub>}, cli.false_true(h))

# a word past its first `-` test: the `--` test fails wherever the `-` one does
law cli.dash.if:
  for b: Bool
  for xt: String
  for h: {String.starts_with.if(xt, "", b) == False{} : Bool}
  {String.starts_with.if(xt, "-", b) == False{} : Bool}

def cli.dash.if(b, xt, h):
  match b:
    case False{}:
      {==}
    case True{}:
      match xt:
        case SNil{}:
          Empty.absurd({String.starts_with.if(SNil{}, "-", True{}) == False{} : Bool}, cli.true_false(h))
        case SCon{x, t}:
          Empty.absurd({String.starts_with.if(SCon{x, t}, "-", True{}) == False{} : Bool}, cli.true_false(h))

# a word that does not start with `-` does not start with `--`
law cli.dash:
  for ww: String
  for h: {String.starts_with(ww, "-") == False{} : Bool}
  {String.starts_with(ww, "--") == False{} : Bool}

def cli.dash(ww, h):
  match ww:
    case SNil{}:
      {==}
    case SCon{+x, xt}:
      cli.dash.if(Char.is_eq(x, '-'), xt, h)

# a plain word is not `--`
law cli.plain_dd:
  for +ww: String
  for h: {Laws.plain_word(ww) == True{} : Bool}
  {String.eq(ww, "--") == False{} : Bool}

def cli.plain_dd(ww, h):
  cli.nor_l(String.eq(ww, "--"), Bool.or(String.eq(ww, "help"), String.starts_with(ww, "-")), h)

# a plain word is not `help`
law cli.plain_help:
  for +ww: String
  for h: {Laws.plain_word(ww) == True{} : Bool}
  {String.eq(ww, "help") == False{} : Bool}

def cli.plain_help(ww, h):
  cli.nor_l(String.eq(ww, "help"), String.starts_with(ww, "-"),
    cli.nor_r(String.eq(ww, "--"), Bool.or(String.eq(ww, "help"), String.starts_with(ww, "-")), h))

# a plain word does not start with `-`
law cli.plain_dash:
  for +ww: String
  for h: {Laws.plain_word(ww) == True{} : Bool}
  {String.starts_with(ww, "-") == False{} : Bool}

def cli.plain_dash(ww, h):
  cli.not_true(String.starts_with(ww, "-"),
    cli.nor_r(String.eq(ww, "help"), String.starts_with(ww, "-"),
      cli.nor_r(String.eq(ww, "--"), Bool.or(String.eq(ww, "help"), String.starts_with(ww, "-")), h)))

# a spec's top-level arguments
def cli.args_of(app: Shake.Cli) -> List<&2, Shake.Arg>:
  Shake.Cli{_n, _a, _v, args, _s} = app
  args

# a spec's subcommands
def cli.subs_of(app: Shake.Cli) -> List<&2, Shake.Sub>:
  Shake.Cli{_n, _a, _v, _args, subs} = app
  subs

# the `files` rest positional, with its help line
def cli.rest(+hlp: String) -> Shake.Arg:
  Shake.Arg{"files", None{}, None{}, Shake.Rest{}, hlp, False{}, None{}, []}

# the binds a walk pushes for files, onto the ones it had, newest first
def cli.pushed(fs: List<&2, String>, bs: List<&2, Shake.Bind>) -> List<&2, Shake.Bind>:
  match fs:
    case Nil{}:
      bs
    case Con{ff, rest}:
      cli.pushed(rest, Shake.Bind{"files", ff} <> bs)

# whether a walker has seen a positional, after the words
def cli.seen(fs: List<&2, String>, seen: Bool) -> Bool:
  match fs:
    case Nil{}:
      seen
    case Con{_ff, rest}:
      cli.seen(rest, True{})

# the files as binds, in order
def cli.as_files(fs: List<&2, String>) -> List<&2, Shake.Bind>:
  match fs:
    case Nil{}:
      []
    case Con{ff, rest}:
      Shake.Bind{"files", ff} <> cli.as_files(rest)

# whether no word names one of the subcommands
def cli.unfound(+subs: List<&2, Shake.Sub>, ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+ww, rest}:
      Bool.and(Maybe.is_none(&2, Shake.Sub, Shake.find_sub(subs, ww)), cli.unfound(subs, rest))

# a word that is not `--`, not `help`, not a flag and no subcommand here
# reaches the positional it binds
law cli.word_step:
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +seen: Bool
  for h_dd: {String.eq(tok, "--") == False{} : Bool}
  for h_help: {String.eq(tok, "help") == False{} : Bool}
  for +h_dash: {String.starts_with(tok, "-") == False{} : Bool}
  for h_sub: {Shake.find_sub(subs, tok) == None{} : Maybe<&2, Shake.Sub>}
  {Shake.parse.step(tok, Shake.St{Shake.Free{}, args, specs, subs, path, bs, pos, False{}, seen})
    == Shake.parse.take_pos(tok, args, specs, subs, path, bs, pos, False{}) : Shake.St}

def cli.word_step(tok, args, specs, subs, path, bs, pos, seen, h_dd, h_help, h_dash, h_sub):
  e1 = Equal.sym(Bool, String.eq(tok, "--"), False{}, h_dd)
  %e1 : {Shake.parse.step.end(_, tok, args, specs, subs, path, bs, pos, seen)
    == Shake.parse.take_pos(tok, args, specs, subs, path, bs, pos, False{}) : Shake.St}
  e2 = Equal.sym(Bool, String.eq(tok, "help"), False{}, h_help)
  %e2 : {Shake.parse.step.help(Bool.and(_, Bool.not(seen)), tok, args, specs, subs, path, bs, pos, seen)
    == Shake.parse.take_pos(tok, args, specs, subs, path, bs, pos, False{}) : Shake.St}
  e3 = Equal.sym(Bool, String.starts_with(tok, "--"), False{}, cli.dash(tok, h_dash))
  %e3 : {Shake.parse.step.kind.go(_, String.starts_with(tok, "-"), tok, args, specs, subs, path, bs, pos, seen)
    == Shake.parse.take_pos(tok, args, specs, subs, path, bs, pos, False{}) : Shake.St}
  e4 = Equal.sym(Bool, String.starts_with(tok, "-"), False{}, h_dash)
  %e4 : {Shake.parse.step.kind.go(False{}, _, tok, args, specs, subs, path, bs, pos, seen)
    == Shake.parse.take_pos(tok, args, specs, subs, path, bs, pos, False{}) : Shake.St}
  e5 = Equal.sym(Maybe<&2, Shake.Sub>, Shake.find_sub(subs, tok), None{}, h_sub)
  %e5 : {Shake.parse.word.go(_, tok, args, specs, subs, path, bs, pos, False{}, seen)
    == Shake.parse.take_pos(tok, args, specs, subs, path, bs, pos, False{}) : Shake.St}
  {==}

# plain words, none a subcommand here, each bind one more file
law cli.walk_plain:
  for fs: List<&2, String>
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, Shake.Bind>
  for +hlp: String
  for +seen: Bool
  for +hp: {Laws.all_plain(fs) == True{} : Bool}
  for +hu: {cli.unfound(subs, fs) == True{} : Bool}
  {Shake.parse.walk(fs, Shake.St{Shake.Free{}, args, specs, subs, path, bs, [cli.rest(hlp)], False{}, seen})
    == Shake.St{Shake.Free{}, args, specs, subs, path, cli.pushed(fs, bs), [cli.rest(hlp)], False{},
      cli.seen(fs, seen)} : Shake.St}

def cli.walk_plain(fs, args, specs, subs, path, bs, hlp, seen, hp, hu):
  match fs:
    case Nil{}:
      {==}
    case Con{+ww, +tl}:
      +pl = cli.and_l(Laws.plain_word(ww), Laws.all_plain(tl), hp)
      su = cli.and_l(Maybe.is_none(&2, Shake.Sub, Shake.find_sub(subs, ww)), cli.unfound(subs, tl), hu)
      e = Equal.sym(Shake.St,
        Shake.parse.step(ww, Shake.St{Shake.Free{}, args, specs, subs, path, bs, [cli.rest(hlp)], False{}, seen}),
        Shake.parse.take_pos(ww, args, specs, subs, path, bs, [cli.rest(hlp)], False{}),
        cli.word_step(ww, args, specs, subs, path, bs, [cli.rest(hlp)], seen, cli.plain_dd(ww, pl),
          cli.plain_help(ww, pl), cli.plain_dash(ww, pl), cli.none_of(Shake.find_sub(subs, ww), su)))
      %e : {Shake.parse.walk(tl, _)
        == Shake.St{Shake.Free{}, args, specs, subs, path, cli.pushed(tl, Shake.Bind{"files", ww} <> bs),
          [cli.rest(hlp)], False{}, cli.seen(tl, True{})} : Shake.St}
      cli.walk_plain(tl, args, specs, subs, path, Shake.Bind{"files", ww} <> bs, hlp, True{},
        cli.and_r(Laws.plain_word(ww), Laws.all_plain(tl), hp),
        cli.and_r(Maybe.is_none(&2, Shake.Sub, Shake.find_sub(subs, ww)), cli.unfound(subs, tl), hu))

# after `--`, every word binds one more file
law cli.walk_raw:
  for fs: List<&2, String>
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for bs: List<&2, Shake.Bind>
  for +hlp: String
  for seen: Bool
  {Shake.parse.walk(fs, Shake.St{Shake.Free{}, args, specs, subs, path, bs, [cli.rest(hlp)], True{}, seen})
    == Shake.St{Shake.Free{}, args, specs, subs, path, cli.pushed(fs, bs), [cli.rest(hlp)], True{},
      cli.seen(fs, seen)} : Shake.St}

def cli.walk_raw(fs, args, specs, subs, path, bs, hlp, _seen):
  match fs:
    case Nil{}:
      {==}
    case Con{ww, tl}:
      cli.walk_raw(tl, args, specs, subs, path, Shake.Bind{"files", ww} <> bs, hlp, True{})

# a dead walker stays as it is
law cli.walk_dead:
  for ws: List<&2, String>
  for +ee: Shake.ParseErr
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  {Shake.parse.walk(ws, Shake.St{Shake.Dead{ee}, args, specs, subs, path, bs, pos, raw, seen})
    == Shake.St{Shake.Dead{ee}, args, specs, subs, path, bs, pos, raw, seen} : Shake.St}

def cli.walk_dead(ws, ee, args, specs, subs, path, bs, pos, raw, seen):
  match ws:
    case Nil{}:
      {==}
    case Con{_ww, tl}:
      cli.walk_dead(tl, ee, args, specs, subs, path, bs, pos, raw, seen)

# appending nothing leaves a list as it is
law cli.append_nil:
  for -A: Data
  for xs: List<&2, A>
  {List.append(&2, A, xs, []) == xs : List<&2, A>}

def cli.append_nil(A, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, tl}:
      %cli.append_nil(A, tl) : {x <> List.append(&2, A, tl, []) == x <> _ : List<&2, A>}
      {==}

# appending one word, then more, is appending them all
law cli.append_one:
  for xs: List<&2, String>
  for +pp: String
  for +tl: List<&2, String>
  {List.append(&2, String, List.append(&2, String, xs, [pp]), tl) == List.append(&2, String, xs, pp <> tl)
    : List<&2, String>}

def cli.append_one(xs, pp, tl):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, rest}:
      %cli.append_one(rest, pp, tl) : {x <> List.append(&2, String, List.append(&2, String, rest, [pp]), tl)
        == x <> _ : List<&2, String>}
      {==}

# a help walker collects every word onto its path
law cli.walk_help:
  for ps: List<&2, String>
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  {Shake.parse.walk(ps, Shake.St{Shake.Help{}, args, specs, subs, path, bs, pos, raw, seen})
    == Shake.St{Shake.Help{}, args, specs, subs, List.append(&2, String, path, ps), bs, pos, raw, seen}
    : Shake.St}

def cli.walk_help(ps, args, specs, subs, path, bs, pos, raw, seen):
  match ps:
    case Nil{}:
      %cli.append_nil(String, path) : {Shake.St{Shake.Help{}, args, specs, subs, _, bs, pos, raw, seen}
        == Shake.St{Shake.Help{}, args, specs, subs, List.append(&2, String, path, []), bs, pos, raw, seen}
        : Shake.St}
      {==}
    case Con{+pp, +tl}:
      %cli.append_one(path, pp, tl) : {Shake.parse.walk(tl,
          Shake.St{Shake.Help{}, args, specs, subs, List.append(&2, String, path, [pp]), bs, pos, raw, seen})
        == Shake.St{Shake.Help{}, args, specs, subs, _, bs, pos, raw, seen} : Shake.St}
      cli.walk_help(tl, args, specs, subs, List.append(&2, String, path, [pp]), bs, pos, raw, seen)

# the pushed binds, reversed onto more, are the older binds reversed onto
# the files in order and then more
law cli.rev_pushed:
  for fs: List<&2, String>
  for bs: List<&2, Shake.Bind>
  for acc: List<&2, Shake.Bind>
  {List.reverse.go(&2, Shake.Bind, cli.pushed(fs, bs), acc)
    == List.reverse.go(&2, Shake.Bind, bs, List.append(&2, Shake.Bind, cli.as_files(fs), acc))
    : List<&2, Shake.Bind>}

def cli.rev_pushed(fs, bs, acc):
  match fs:
    case Nil{}:
      {==}
    case Con{ff, tl}:
      cli.rev_pushed(tl, Shake.Bind{"files", ff} <> bs, acc)

# file binds hold no version
law cli.no_version:
  for fs: List<&2, String>
  {Shake.get.bind(cli.as_files(fs), "version") == "" : String}

def cli.no_version(fs):
  match fs:
    case Nil{}:
      {==}
    case Con{_ff, tl}:
      cli.no_version(tl)

# file binds read back as the files
law cli.files_back:
  for fs: List<&2, String>
  {Shake.get_all.bind(cli.as_files(fs), "files") == fs : List<&2, String>}

def cli.files_back(fs):
  match fs:
    case Nil{}:
      {==}
    case Con{+ff, tl}:
      %cli.files_back(tl) : {ff <> Shake.get_all.bind(cli.as_files(tl), "files") == ff <> _ : List<&2, String>}
      {==}

# a parse that bound only files runs its command over them
law cli.files_out:
  for +fs: List<&2, String>
  for +path: List<&2, String>
  {Args.out.done(Shake.Matched{path, List.reverse(&2, Shake.Bind, cli.pushed(fs, []))})
    == Args.Go{Args.command(String.join(path, "/")), fs} : Args.Out}

def cli.files_out(fs, path):
  e1 = Equal.sym(List<&2, Shake.Bind>, List.reverse.go(&2, Shake.Bind, cli.pushed(fs, []), []),
    List.append(&2, Shake.Bind, cli.as_files(fs), []), cli.rev_pushed(fs, [], []))
  %e1 : {Args.out.done(Shake.Matched{path, _}) == Args.Go{Args.command(String.join(path, "/")), fs} : Args.Out}
  e2 = Equal.sym(List<&2, Shake.Bind>, List.append(&2, Shake.Bind, cli.as_files(fs), []), cli.as_files(fs),
    cli.append_nil(Shake.Bind, cli.as_files(fs)))
  %e2 : {Args.out.done(Shake.Matched{path, _}) == Args.Go{Args.command(String.join(path, "/")), fs} : Args.Out}
  e3 = Equal.sym(String, Shake.get.bind(cli.as_files(fs), "version"), "", cli.no_version(fs))
  %e3 : {Args.out.run(String.eq(_, "true"), Shake.Matched{path, cli.as_files(fs)})
    == Args.Go{Args.command(String.join(path, "/")), fs} : Args.Out}
  e4 = Equal.sym(List<&2, String>, Shake.get_all.bind(cli.as_files(fs), "files"), fs, cli.files_back(fs))
  %e4 : {Args.Go{Args.command(String.join(path, "/")), _} == Args.Go{Args.command(String.join(path, "/")), fs}
    : Args.Out}
  {==}

# no word names a subcommand when there are none
law cli.unfound_nil:
  for ws: List<&2, String>
  {cli.unfound([], ws) == True{} : Bool}

def cli.unfound_nil(ws):
  match ws:
    case Nil{}:
      {==}
    case Con{_ww, tl}:
      cli.unfound_nil(tl)

# loose words are plain
law cli.loose_plain:
  for ws: List<&2, String>
  for +h: {Laws.all_loose(ws) == True{} : Bool}
  {Laws.all_plain(ws) == True{} : Bool}

def cli.loose_plain(ws, h):
  match ws:
    case Nil{}:
      {==}
    case Con{+ww, +tl}:
      cli.and_true(Laws.plain_word(ww), Laws.all_plain(tl),
        cli.and_l(Laws.plain_word(ww),
          Bool.not(Bool.or(String.eq("lint", ww), Bool.or(String.eq("check", ww), String.eq("lsp", ww)))),
          cli.and_l(Laws.loose_word(ww), Laws.all_loose(tl), h)),
        cli.loose_plain(tl, cli.and_r(Laws.loose_word(ww), Laws.all_loose(tl), h)))

# a lookup among three subcommands, none of whose names match, finds none
law cli.miss3:
  for a: Bool
  for b: Bool
  for c: Bool
  for -x: Shake.Sub
  for -y: Shake.Sub
  for -z: Shake.Sub
  for h: {Bool.not(Bool.or(a, Bool.or(b, c))) == True{} : Bool}
  {Maybe.is_none(&2, Shake.Sub, Bool.pick(Maybe<&2, Shake.Sub>, a, Some{x},
    Bool.pick(Maybe<&2, Shake.Sub>, b, Some{y}, Bool.pick(Maybe<&2, Shake.Sub>, c, Some{z}, None{}))))
    == True{} : Bool}

def cli.miss3(a, b, c, x, y, z, h):
  match a b c:
    case True{} _b _c:
      Empty.absurd({Maybe.is_none(&2, Shake.Sub, Bool.pick(Maybe<&2, Shake.Sub>, True{}, Some{x},
        Bool.pick(Maybe<&2, Shake.Sub>, _b, Some{y}, Bool.pick(Maybe<&2, Shake.Sub>, _c, Some{z}, None{}))))
        == True{} : Bool}, cli.false_true(h))
    case False{} True{} _c:
      Empty.absurd({Maybe.is_none(&2, Shake.Sub, Bool.pick(Maybe<&2, Shake.Sub>, False{}, Some{x},
        Bool.pick(Maybe<&2, Shake.Sub>, True{}, Some{y}, Bool.pick(Maybe<&2, Shake.Sub>, _c, Some{z}, None{}))))
        == True{} : Bool}, cli.false_true(h))
    case False{} False{} True{}:
      Empty.absurd({Maybe.is_none(&2, Shake.Sub, Bool.pick(Maybe<&2, Shake.Sub>, False{}, Some{x},
        Bool.pick(Maybe<&2, Shake.Sub>, False{}, Some{y}, Bool.pick(Maybe<&2, Shake.Sub>, True{}, Some{z}, None{}))))
        == True{} : Bool}, cli.false_true(h))
    case False{} False{} False{}:
      {==}

# loose words name no subcommand of bolt's
law cli.loose_unfound:
  for ws: List<&2, String>
  for +h: {Laws.all_loose(ws) == True{} : Bool}
  {cli.unfound(cli.subs_of(Args.spec()), ws) == True{} : Bool}

def cli.loose_unfound(ws, h):
  match ws:
    case Nil{}:
      {==}
    case Con{+ww, +tl}:
      cli.and_true(Maybe.is_none(&2, Shake.Sub, Shake.find_sub(cli.subs_of(Args.spec()), ww)),
        cli.unfound(cli.subs_of(Args.spec()), tl),
        cli.miss3(String.eq("lint", ww), String.eq("check", ww), String.eq("lsp", ww),
          Shake.sub("lint", "Lint files", [Args.spec.files("Files to lint")], []),
          Shake.sub("check", "Check files", [Args.spec.files("Files to check")], []),
          Shake.sub("lsp", "Serve an editor over stdio", [], []),
          cli.and_r(Laws.plain_word(ww),
            Bool.not(Bool.or(String.eq("lint", ww), Bool.or(String.eq("check", ww), String.eq("lsp", ww)))),
            cli.and_l(Laws.loose_word(ww), Laws.all_loose(tl), h))),
        cli.loose_unfound(tl, cli.and_r(Laws.loose_word(ww), Laws.all_loose(tl), h)))

def Laws.cli_bare(fs, h):
  e = Equal.sym(Shake.St,
    Shake.parse.walk(fs, Shake.St{Shake.Free{}, cli.args_of(Args.spec()), cli.args_of(Args.spec()),
      cli.subs_of(Args.spec()), [], [], [cli.rest("Files to lint")], False{}, False{}}),
    Shake.St{Shake.Free{}, cli.args_of(Args.spec()), cli.args_of(Args.spec()), cli.subs_of(Args.spec()), [],
      cli.pushed(fs, []), [cli.rest("Files to lint")], False{}, cli.seen(fs, False{})},
    cli.walk_plain(fs, cli.args_of(Args.spec()), cli.args_of(Args.spec()), cli.subs_of(Args.spec()), [], [],
      "Files to lint", False{}, cli.loose_plain(fs, h), cli.loose_unfound(fs, h)))
  %e : {Args.out(Shake.parse.finish(_)) == Args.Go{Args.CLint{}, fs} : Args.Out}
  cli.files_out(fs, [])

def Laws.cli_bare_raw(fs):
  e = Equal.sym(Shake.St,
    Shake.parse.walk(fs, Shake.St{Shake.Free{}, cli.args_of(Args.spec()), cli.args_of(Args.spec()),
      cli.subs_of(Args.spec()), [], [], [cli.rest("Files to lint")], True{}, False{}}),
    Shake.St{Shake.Free{}, cli.args_of(Args.spec()), cli.args_of(Args.spec()), cli.subs_of(Args.spec()), [],
      cli.pushed(fs, []), [cli.rest("Files to lint")], True{}, cli.seen(fs, False{})},
    cli.walk_raw(fs, cli.args_of(Args.spec()), cli.args_of(Args.spec()), cli.subs_of(Args.spec()), [], [],
      "Files to lint", False{}))
  %e : {Args.out(Shake.parse.finish(_)) == Args.Go{Args.CLint{}, fs} : Args.Out}
  cli.files_out(fs, [])

# the specs a subcommand's walker holds: bolt's own, then the command's
def cli.specs_in(+hlp: String) -> List<&2, Shake.Arg>:
  List.append(&2, Shake.Arg, cli.args_of(Args.spec()), [cli.rest(hlp)])

# the walk after a files subcommand's name, over plain words
law cli.sub_plain:
  for +fs: List<&2, String>
  for +name: String
  for +hlp: String
  for h: {Laws.all_plain(fs) == True{} : Bool}
  {Shake.parse.walk(fs, Shake.St{Shake.Free{}, [cli.rest(hlp)], cli.specs_in(hlp), [], [name], [],
      [cli.rest(hlp)], False{}, False{}})
    == Shake.St{Shake.Free{}, [cli.rest(hlp)], cli.specs_in(hlp), [], [name], cli.pushed(fs, []),
      [cli.rest(hlp)], False{}, cli.seen(fs, False{})} : Shake.St}

def cli.sub_plain(fs, name, hlp, h):
  cli.walk_plain(fs, [cli.rest(hlp)], cli.specs_in(hlp), [], [name], [], hlp, False{}, h, cli.unfound_nil(fs))

def Laws.cli_lint(fs, h):
  e = Equal.sym(Shake.St,
    Shake.parse.walk(fs, Shake.St{Shake.Free{}, [cli.rest("Files to lint")], cli.specs_in("Files to lint"), [],
      ["lint"], [], [cli.rest("Files to lint")], False{}, False{}}),
    Shake.St{Shake.Free{}, [cli.rest("Files to lint")], cli.specs_in("Files to lint"), [], ["lint"],
      cli.pushed(fs, []), [cli.rest("Files to lint")], False{}, cli.seen(fs, False{})},
    cli.sub_plain(fs, "lint", "Files to lint", h))
  %e : {Args.out(Shake.parse.finish(_)) == Args.Go{Args.CLint{}, fs} : Args.Out}
  cli.files_out(fs, ["lint"])

def Laws.cli_check(fs, h):
  e = Equal.sym(Shake.St,
    Shake.parse.walk(fs, Shake.St{Shake.Free{}, [cli.rest("Files to check")], cli.specs_in("Files to check"), [],
      ["check"], [], [cli.rest("Files to check")], False{}, False{}}),
    Shake.St{Shake.Free{}, [cli.rest("Files to check")], cli.specs_in("Files to check"), [], ["check"],
      cli.pushed(fs, []), [cli.rest("Files to check")], False{}, cli.seen(fs, False{})},
    cli.sub_plain(fs, "check", "Files to check", h))
  %e : {Args.out(Shake.parse.finish(_)) == Args.Go{Args.CCheck{}, fs} : Args.Out}
  cli.files_out(fs, ["check"])

def Laws.cli_lint_raw(fs):
  e = Equal.sym(Shake.St,
    Shake.parse.walk(fs, Shake.St{Shake.Free{}, [cli.rest("Files to lint")], cli.specs_in("Files to lint"), [],
      ["lint"], [], [cli.rest("Files to lint")], True{}, False{}}),
    Shake.St{Shake.Free{}, [cli.rest("Files to lint")], cli.specs_in("Files to lint"), [], ["lint"],
      cli.pushed(fs, []), [cli.rest("Files to lint")], True{}, cli.seen(fs, False{})},
    cli.walk_raw(fs, [cli.rest("Files to lint")], cli.specs_in("Files to lint"), [], ["lint"], [],
      "Files to lint", False{}))
  %e : {Args.out(Shake.parse.finish(_)) == Args.Go{Args.CLint{}, fs} : Args.Out}
  cli.files_out(fs, ["lint"])

def Laws.cli_check_raw(fs):
  e = Equal.sym(Shake.St,
    Shake.parse.walk(fs, Shake.St{Shake.Free{}, [cli.rest("Files to check")], cli.specs_in("Files to check"), [],
      ["check"], [], [cli.rest("Files to check")], True{}, False{}}),
    Shake.St{Shake.Free{}, [cli.rest("Files to check")], cli.specs_in("Files to check"), [], ["check"],
      cli.pushed(fs, []), [cli.rest("Files to check")], True{}, cli.seen(fs, False{})},
    cli.walk_raw(fs, [cli.rest("Files to check")], cli.specs_in("Files to check"), [], ["check"], [],
      "Files to check", False{}))
  %e : {Args.out(Shake.parse.finish(_)) == Args.Go{Args.CCheck{}, fs} : Args.Out}
  cli.files_out(fs, ["check"])

# the specs the `lsp` walker holds: bolt's own, and none of its own
def cli.specs_lsp() -> List<&2, Shake.Arg>:
  List.append(&2, Shake.Arg, cli.args_of(Args.spec()), [])

def Laws.cli_lsp(ws, h):
  match ws:
    case Nil{}:
      {==}
    case Con{+ww, +tl}:
      +pl = cli.and_l(Laws.plain_word(ww), Laws.all_plain(tl), h)
      e1 = Equal.sym(Shake.St,
        Shake.parse.step(ww, Shake.St{Shake.Free{}, [], cli.specs_lsp(), [], ["lsp"], [], [], False{}, False{}}),
        Shake.parse.take_pos(ww, [], cli.specs_lsp(), [], ["lsp"], [], [], False{}),
        cli.word_step(ww, [], cli.specs_lsp(), [], ["lsp"], [], [], False{}, cli.plain_dd(ww, pl),
          cli.plain_help(ww, pl), cli.plain_dash(ww, pl), {==}))
      %e1 : {Args.out(Shake.parse.finish(Shake.parse.walk(tl, _)))
        == Args.Stop{Args.Err{}, Args.err_text(Shake.Unexpected{ww}), 1} : Args.Out}
      e2 = Equal.sym(Shake.St,
        Shake.parse.walk(tl, Shake.St{Shake.Dead{Shake.Unexpected{ww}}, [], cli.specs_lsp(), [], ["lsp"], [], [],
          False{}, True{}}),
        Shake.St{Shake.Dead{Shake.Unexpected{ww}}, [], cli.specs_lsp(), [], ["lsp"], [], [], False{}, True{}},
        cli.walk_dead(tl, Shake.Unexpected{ww}, [], cli.specs_lsp(), [], ["lsp"], [], [], False{}, True{}))
      %e2 : {Args.out(Shake.parse.finish(_)) == Args.Stop{Args.Err{}, Args.err_text(Shake.Unexpected{ww}), 1}
        : Args.Out}
      {==}

def Laws.cli_help(ps):
  e = Equal.sym(Shake.St,
    Shake.parse.walk(ps, Shake.St{Shake.Help{}, cli.args_of(Args.spec()), cli.args_of(Args.spec()),
      cli.subs_of(Args.spec()), [], [], [cli.rest("Files to lint")], False{}, False{}}),
    Shake.St{Shake.Help{}, cli.args_of(Args.spec()), cli.args_of(Args.spec()), cli.subs_of(Args.spec()),
      List.append(&2, String, [], ps), [], [cli.rest("Files to lint")], False{}, False{}},
    cli.walk_help(ps, cli.args_of(Args.spec()), cli.args_of(Args.spec()), cli.subs_of(Args.spec()), [], [],
      [cli.rest("Files to lint")], False{}, False{}))
  %e : {Args.out(Shake.parse.finish(_)) == Args.Stop{Args.Page{}, Args.help_text(ps), 0} : Args.Out}
  {==}

def Laws.cli_version(fs, h):
  e1 = Equal.sym(Shake.St,
    Shake.parse.walk(fs, Shake.St{Shake.Free{}, cli.args_of(Args.spec()), cli.args_of(Args.spec()),
      cli.subs_of(Args.spec()), [], [Shake.Bind{"version", "true"}], [cli.rest("Files to lint")], False{},
      False{}}),
    Shake.St{Shake.Free{}, cli.args_of(Args.spec()), cli.args_of(Args.spec()), cli.subs_of(Args.spec()), [],
      cli.pushed(fs, [Shake.Bind{"version", "true"}]), [cli.rest("Files to lint")], False{},
      cli.seen(fs, False{})},
    cli.walk_plain(fs, cli.args_of(Args.spec()), cli.args_of(Args.spec()), cli.subs_of(Args.spec()), [],
      [Shake.Bind{"version", "true"}], "Files to lint", False{}, cli.loose_plain(fs, h), cli.loose_unfound(fs, h)))
  %e1 : {Args.out(Shake.parse.finish(_))
    == Args.Stop{Args.Line{}, "bolt " ++ Args.version.at(Ver.text(), Rev.text()), 0} : Args.Out}
  e2 = Equal.sym(List<&2, Shake.Bind>,
    List.reverse.go(&2, Shake.Bind, cli.pushed(fs, [Shake.Bind{"version", "true"}]), []),
    List.reverse.go(&2, Shake.Bind, [Shake.Bind{"version", "true"}],
      List.append(&2, Shake.Bind, cli.as_files(fs), [])),
    cli.rev_pushed(fs, [Shake.Bind{"version", "true"}], []))
  %e2 : {Args.out.done(Shake.Matched{[], _})
    == Args.Stop{Args.Line{}, "bolt " ++ Args.version.at(Ver.text(), Rev.text()), 0} : Args.Out}
  {==}

# a failed parse that asks for no usage stops on its error with 1
law cli.err_stop:
  for +ee: Shake.ParseErr
  for h: {Laws.asks_help(ee) == False{} : Bool}
  {Args.out.fail(ee) == Args.Stop{Args.Err{}, Args.err_text(ee), 1} : Args.Out}

def cli.err_stop(ee, h):
  match ee:
    case Shake.UnknownFlag{_ww}:
      {==}
    case Shake.Missing{_nn}:
      {==}
    case Shake.BadValue{_nn, _vv}:
      {==}
    case Shake.NeedHelp{path}:
      Empty.absurd({Args.out.fail(Shake.NeedHelp{path})
        == Args.Stop{Args.Err{}, Args.err_text(Shake.NeedHelp{path}), 1} : Args.Out}, cli.true_false(h))
    case Shake.Unexpected{_ww}:
      {==}

def Laws.cli_error_exits(av, ee, h, h_help):
  e = Equal.sym(Result<&2, &2, Shake.ParseErr, Shake.Matched>, Args.parse(av), Fail{ee}, h)
  %e : {Args.out(_) == Args.Stop{Args.Err{}, Args.err_text(ee), 1} : Args.Out}
  cli.err_stop(ee, h_help)

def Laws.cli_help_exits(av, ps, h):
  e = Equal.sym(Result<&2, &2, Shake.ParseErr, Shake.Matched>, Args.parse(av), Fail{Shake.NeedHelp{ps}}, h)
  %e : {Args.out(_) == Args.Stop{Args.Page{}, Args.help_text(ps), 0} : Args.Out}
  {==}

def Laws.cli_version_exits(av, mm, h, h_ver):
  e = Equal.sym(Result<&2, &2, Shake.ParseErr, Shake.Matched>, Args.parse(av), Done{mm}, h)
  %e : {Args.out(_)
    == Args.Stop{Args.Line{}, "bolt " ++ Args.version.at(Ver.text(), Rev.text()), 0} : Args.Out}
  v = Equal.sym(Bool, Shake.on(mm, "version"), True{}, h_ver)
  %v : {Args.out.run(_, mm)
    == Args.Stop{Args.Line{}, "bolt " ++ Args.version.at(Ver.text(), Rev.text()), 0} : Args.Out}
  {==}

def Laws.cli_runs(av, mm, h, h_ver):
  e = Equal.sym(Result<&2, &2, Shake.ParseErr, Shake.Matched>, Args.parse(av), Done{mm}, h)
  %e : {Args.out(_)
    == Args.Go{Args.command(String.join(Shake.path_of(mm), "/")), Shake.get_all(mm, "files")} : Args.Out}
  v = Equal.sym(Bool, Shake.on(mm, "version"), False{}, h_ver)
  %v : {Args.out.run(_, mm)
    == Args.Go{Args.command(String.join(Shake.path_of(mm), "/")), Shake.get_all(mm, "files")} : Args.Out}
  {==}

def Laws.version_release(rel, rev, h):
  e = Equal.sym(Bool, String.is_empty(rev), True{}, h)
  %e : {Bool.pick(String, _, rel, rel ++ " (" ++ rev ++ ")") == rel : String}
  {==}

def Laws.version_commit(rel, rev, h):
  e = Equal.sym(Bool, String.is_empty(rev), False{}, h)
  %e : {Bool.pick(String, _, rel, rel ++ " (" ++ rev ++ ")") == rel ++ " (" ++ rev ++ ")" : String}
  {==}
