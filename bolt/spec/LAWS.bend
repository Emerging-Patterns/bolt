# bolt: the laws. Closed equalities of src, args, glob, rules, frame, path,
# report, and canned LSP sessions over the script transport.
import Base
import ./cases.bend as C
import ../src.bend as Src
import ../rules.bend as Rules
import ../rules/style/doc.bend as Doc
import ../rules/suspicious/unused.bend as Unused
import ../rules/correctness/shadow.bend as Shadow
import ../rules/correctness/hole.bend as Hole
import ../rules/style/space.bend as Space
import ../rules/style/wrap.bend as Wrap
import ../rules/style/param.bend as Param
import ../rules/correctness/pick.bend as Pick
import ../rules/laws/law.bend as Law
import ../rules/digest.bend as Digest
import ../config.bend as Config
import ../finding.bend as F
import ../args.bend as Args
import ../glob.bend as Glob
import ../walk/fake.bend as FakeWalk
import ../rules/laws/unsafe.bend as Unsafe
import ../rules/correctness/foreign.bend as Foreign
import ../rules/suspicious/fuel.bend as Fuel
import ../rules/laws/closed.bend as Closed
import ../rules/imports.bend as Imports
import ../rules/correctness/put.bend as Put
import ../rules/correctness/escape.bend as Escape
import ../rules/suspicious/nat.bend as NatLit
import ../rules/correctness/strings.bend as Strings
import ../rules/correctness/chars.bend as Chars
import ../rules/correctness/twice.bend as Twice
import ../rules/correctness/arms.bend as Arms
import ../rules/suspicious/strict.bend as Strict
import ../rules/suspicious/eager.bend as Eager
import ../rules/pedantic/tail.bend as Tail
import ../rules/suspicious/concat.bend as Concat
import ../rules/suspicious/index.bend as Index
import ../lsp/frame.bend as Frame
import ../lsp/path.bend as Path
import ../lsp/docs.bend as Docs
import ../lsp/server.bend as Server
import ../lsp/transport/script.bend as Script
import ../lsp/checker/fake.bend as FakeChecker

# findings as one semicolon-separated line
def lines(fs: List<&2, F.Finding>) -> String:
  C.show.lines(fs)

# graded findings as lines
def shown(gs: List<&2, F.Graded>) -> List<&2, String>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{g, rest}:
      F.show_graded(g) <> shown(rest)

# the level word of a rule under the config
def at(cfg: Config.Config, +rule: String) -> String:
  Config.show(Config.level(cfg, Rules.group(rule), rule))

# the levels of every rule, `rule=level`
def levels(+cfg: Config.Config, rules: List<&2, String>) -> String:
  match rules:
    case Nil{}:
      ""
    case Con{+r, rest}:
      r ++ "=" ++ at(cfg, r) ++ " " ++ levels(cfg, rest)

# LAW: Src.of's fields equal Lex.tokens, Tree.parse and Bind.bound of the text
law src_fields:
  {C.src.fields(Src.of("a.bend", C.src.sample())) == C.src.direct("a.bend", C.src.sample())
    : String}

# LAW: the text and path are carried unchanged
law src_path:
  {C.src.fields(Src.of("b/c.bend", "def f() -> U32:\n  1\n"))
    == C.src.direct("b/c.bend", "def f() -> U32:\n  1\n") : String}

# LAW: Rules.all is Rules.on of Src.of
law rules_all_is_on:
  {lines(Rules.all("a.bend", C.src.sample())) == lines(Rules.on(Src.of("a.bend", C.src.sample())))
    : String}

# LAW: the sample's findings, read once
law rules_sample:
  {lines(Rules.on(Src.of("a.bend", C.src.sample()))) ==
    "a.bend:8:1: doc: def go has no comment above it; a.bend:4:9: param: parameter n is shorter than 2 characters; a.bend:13:7: pick: go recurses in both branches; Bool.pick runs both"
    : String}

# LAW: a bare bolt is lint over no files
law args_bare:
  {C.args.split([]) == "[] " : String}

# LAW: a leading subcommand is the command, the rest files
law args_lint:
  {C.args.split(["lint", "a.bend", "b.bend"]) == "[lint] a.bend b.bend" : String}

# LAW: check and lsp too
law args_check_lsp:
  {C.args.split(["check", "a.bend"]) ++ C.args.split(["lsp"]) == "[check] a.bend[lsp] " : String}

# LAW: a first word that is no subcommand is a file
law args_files:
  {C.args.split(["a.bend", "b.bend"]) == "[] a.bend b.bend" : String}

# LAW: check takes every leftover file
law args_check_many:
  {C.args.split(["check", "a.bend", "b.bend"]) == "[check] a.bend b.bend" : String}

# LAW: words after `--` are files
law args_dash:
  {C.args.split(["--", "a.bend", "b.bend"]) == "[] a.bend b.bend" : String}

# LAW: `help` is NeedHelp at the root
law args_help:
  {Args.shown(["help"]) == "err help " : String}

# LAW: `help lint` is NeedHelp at lint
law args_help_lint:
  {Args.shown(["help", "lint"]) == "err help lint" : String}

# LAW: the root usage page is this exact text
law args_help_root:
  {Args.help_text([]) == C.args.help_root() : String}

# LAW: a short commit is the release, then the id in parentheses
law args_version_rev:
  {Args.version.at("0.4.0", "2886b08") == "0.4.0 (2886b08)" : String}

# LAW: an empty commit id is the release alone
law args_version_none:
  {Args.version.at("0.4.0", "") == "0.4.0" : String}

# LAW: argv is IO.args, widened
law args_argv:
  {Args.argv() == (do IO<List<&2, String>>:
    ss : List<&1, String> <- IO.args()
    return Args.widen(ss)) : IO(List<&2, String>)}

# LAW: glob over the canned tree
law glob_fake:
  {Glob.find(~FakeWalk.new(), ".")
    == IO.pure(List<&2, String>, ["./b.bend", "./bolt/a.bend", "./bolt/lsp/run.bend"])
    : IO(List<&2, String>)}

# LAW: FakeWalk.at of .
law walk_at_root:
  {FakeWalk.at(".") == ["bolt/", "b.bend", "node_modules/", ".gate/", "notes.md"]
    : List<&2, String>}

# LAW: FakeWalk.entries is pure at
law walk_entries:
  {FakeWalk.entries(".") == IO.pure(List<&2, String>, FakeWalk.at(".")) : IO(List<&2, String>)}

# LAW: doc: undotted defs, types and laws, not helpers or main
law doc_undotted:
  {lines(Doc.check(Src.of("a.bend", C.rules.undocumented()))) ==
    "a.bend:7:1: doc: def dec has no comment above it; a.bend:13:1: doc: type T has no comment above it; a.bend:16:1: doc: law l has no comment above it"
    : String}

# LAW: a proof file is exempt from doc
law doc_proof:
  {lines(Doc.check(Src.of("x/PROOF.bend", C.rules.undocumented()))) == "" : String}

# LAW: a test is exempt from doc
law doc_test:
  {lines(Doc.check(Src.of("x/tests/a.bend", C.rules.undocumented()))) == "" : String}

# LAW: unused: lets, lambdas and parameters
law unused_names:
  {lines(Unused.check(Src.of("a.bend", C.rules.unused()))) ==
    "a.bend:1:7: unused: parameter x is never used; a.bend:3:3: unused: local b is never used; a.bend:4:3: unused: local g is never used; a.bend:5:3: unused: local h is never used; a.bend:5:7: unused: local w is never used"
    : String}

# LAW: shadow: a let or a pattern named like a def above
law shadow_def:
  {lines(Shadow.check(Src.of("a.bend", C.rules.shadowed()))) ==
    "a.bend:9:3: shadow: k is a def above; imported, this binder would read as it; a.bend:14:12: shadow: k is a def above; imported, this binder would read as it"
    : String}

# LAW: a ?TODO
law hole_todo:
  {lines(Hole.check(Src.of("a.bend", C.rules.holes()))) == "a.bend:2:3: hole: a ?TODO is left here"
    : String}

# LAW: LAWS.bend is exempt from hole
law hole_laws:
  {lines(Hole.check(Src.of("LAWS.bend", C.rules.holes()))) == "" : String}

# LAW: space: trailing, tab, width
law space_width:
  {lines(Space.check(Src.of("a.bend", C.rules.spaced()))) ==
    "a.bend:1:17: space: trailing whitespace; a.bend:2:1: space: a tab; indent with spaces; a.bend:3:121: space: over 120 characters wide"
    : String}

# LAW: wrap: a one-line header over 120, not one that fits or is already wrapped
law wrap_header:
  {lines(Wrap.check(Src.of("a.bend", C.rules.headers()))) ==
    "a.bend:3:121: wrap: def header over 120 characters wide" : String}

# LAW: param: a one-letter value parameter, not a type, a quantity or a local
law param_short:
  {lines(Param.check(Src.of("a.bend", C.rules.params()))) ==
    "a.bend:1:9: param: parameter n is shorter than 2 characters" : String}

# LAW: pick: a def in both branches
law pick_both:
  {lines(Pick.check(Src.of("a.bend", C.rules.picked()))) ==
    "a.bend:6:7: pick: go recurses in both branches; Bool.pick runs both; a.bend:19:7: pick: nested recurses in both branches; Bool.pick runs both"
    : String}

# LAW: defs under a LAWS.bend that no law names, IO and main included
law law_gaps:
  {lines(Law.check(Digest.all(C.rules.lawful()))) ==
    "./p/m.bend:4:1: law: def g is named by no law; ./p/m.bend:13:1: law: def main is named by no law; ./p/o.bend:1:1: law: type O: no law reaches this module; ./p/o.bend:4:1: law: def h is named by no law; ./p/io.bend:1:1: law: def say is named by no law; ./p/io.bend:4:1: law: def k is named by no law"
    : String}

# LAW: a project without laws is not under it
law law_none:
  {lines(Law.check(Digest.all([Src.of("./q/n.bend", "def y() -> U32:\n  1\n")]))) == "" : String}

# LAW: config defaults
law config_defaults:
  {levels(Config.none(), ["shadow", "hole", "pick", "unused", "doc", "space", "wrap", "param", "law"]) ==
    "shadow=error hole=error pick=error unused=warning doc=warning space=warning wrap=warning param=warning law=warning "
    : String}

# LAW: a group sets its rules, a rule set apart wins, a typo is an error
law config_group:
  {levels(Config.parse(C.rules.config()), ["doc", "space", "unused", "law", "shadow"]) ==
    "doc=error space=warning unused=off law=error shadow=error " : String}

# LAW: the bolt.bend candidates, nearest first
law config_candidates:
  {String.join(Config.candidates(64n, Config.dir_of("a/b/c.bend")), " ")
    == "a/b/bolt.bend a/bolt.bend bolt.bend" : String}

# LAW: an absolute path stops at /
law config_abs:
  {String.join(Config.candidates(64n, Config.dir_of("/w/x.bend")), " ") == "/w/bolt.bend /bolt.bend"
    : String}

# LAW: the nearest file that exists is the config
law config_nearest:
  {at(Config.nearest([None{}, Some{C.rules.config()}, Some{"def style() -> String:\n  \"off\"\n"}]),
    "doc") == "error" : String}

# LAW: findings at their levels, the off ones dropped
law rules_graded:
  {String.join(shown(Rules.graded(Config.parse(C.rules.config()),
    List.append(&2, F.Finding, Doc.check(Src.of("a.bend", C.rules.undocumented())),
      Unused.check(Src.of("a.bend", C.rules.unused()))))), "; ") ==
    "a.bend:7:1: error: doc: def dec has no comment above it; a.bend:13:1: error: doc: type T has no comment above it; a.bend:16:1: error: doc: law l has no comment above it"
    : String}

# LAW: all rules on a clean file
law rules_clean:
  {lines(Rules.all("a.bend", "# one\ndef one() -> U32:\n  1\n")) == "" : String}

# LAW: a closure over relative imports
law imports_closure:
  {String.join(Imports.closure(C.proj.reached(), "./p/PROOF.bend"), " ")
    == "p/PROOF.bend p/LAWS.bend p/m.bend lib/u.bend p/w.bend" : String}

# LAW: an @unsafe def a law file reaches
law unsafe_reached:
  {lines(Unsafe.check(Digest.all(C.proj.reached()))) ==
    "./lib/u.bend:2:1: unsafe: @unsafe def spin is reached from ./p/PROOF.bend: the checker only warns there and exits 0; recurse on a shrinking argument or fuel; ./p/w.bend:2:1: unsafe: @unsafe def walk is reached from ./p/PROOF.bend: the checker only warns there and exits 0; recurse on a shrinking argument or fuel"
    : String}

# LAW: quiet when no law file reaches it
law unsafe_quiet:
  {lines(Unsafe.check(Digest.all(C.proj.unreached()))) == "" : String}

# LAW: a project without law files is exempt
law unsafe_lawless:
  {lines(Unsafe.check(Digest.all(C.proj.lawless()))) == "" : String}

# LAW: a .c body without .js, and the reverse
law foreign_lanes:
  {lines(Foreign.check(Src.of("a.bend", C.proj.foreigns()))) ==
    "a.bend:2:1: foreign: foreign def a.b has a .c body but no .js body: the JS lane cannot run it; a.bend:6:1: foreign: foreign def a.c has a .js body but no .c body: a native build cannot run it"
    : String}

# LAW: quiet on both bodies and on a plain def
law foreign_both:
  {lines(Foreign.check(Src.of("a.bend",
    "# both\ndef a.d(x: U32) -> IO(U32):\n  import \"./d.c\"\n  import \"./d.js\"\n"))) == ""
    : String}

# LAW: a # lanes: native file needs no .js
law foreign_native:
  {lines(Foreign.check(Src.of("a.bend", C.proj.native()))) ==
    "a.bend:9:1: foreign: foreign def a.c has a .js body but no .c body: a native build cannot run it"
    : String}

# LAW: a Nat literal in a fuel parameter
law fuel_fixed:
  {lines(Fuel.check(Src.of("a.bend", C.proj.fuels()))) ==
    "a.bend:19:13: fuel: a fixed fuel of 1000n: input past it is cut short silently; derive the fuel from the input's size; a.bend:20:23: fuel: a fixed fuel of 10n: input past it is cut short silently; derive the fuel from the input's size"
    : String}

# LAW: quiet on a derived fuel
law fuel_derived:
  {lines(Fuel.check(Src.of("a.bend",
    "# fuel\ndef walk(fuel: Nat) -> U32:\n  0\n\n# n\ndef main() -> U32:\n  walk(Nat.add(2n, 1n))\n")))
    == "" : String}

# LAW: a def's own call is exempt
law fuel_self:
  {lines(Fuel.check(Src.of("a.bend", "# gas\ndef spin(gas: Nat) -> U32:\n  spin(2n)\n"))) == ""
    : String}

# LAW: quiet on an equality, including IO
law closed_eq:
  {lines(Closed.check(Src.of("p/LAWS.bend", C.proj.laws()))) == "" : String}

# LAW: a law with no for, exs, or equality
law closed_noneq:
  {lines(Closed.check(Src.of("p/LAWS.bend", "# LAW: a type\nlaw inhabited:\n  {True{} : Bool}\n")))
    == "p/LAWS.bend:2:1: closed: law inhabited has no for and is not an equality: state {lhs == rhs : T}, including IO(T)"
    : String}

# LAW: quiet on laws with for
law closed_for:
  {lines(Closed.check(Src.of("p/LAWS.bend",
    "# LAW: f\nlaw f_id:\n  for a: U32\n  {M.f(a) == a : U32}\n"))) == "" : String}

# LAW: a law outside a LAWS.bend is exempt
law closed_outside:
  {lines(Closed.check(Src.of("p/a.bend", C.proj.laws()))) == "" : String}

# LAW: Map.put
law put_call:
  {lines(Put.check(Src.of("a.bend", C.tok.put_src()))) ==
    "a.bend:2:3: put: Map.put never compares keys; a new key overwrites another entry: use Map.set"
    : String}

# LAW: a file that defines Map.put is exempt
law put_own:
  {lines(Put.check(Src.of("a.bend", C.tok.put_own()))) == "" : String}

# LAW: \0 then digits
law escape_octal:
  {lines(Escape.check(Src.of("a.bend", C.tok.escape_src()))) == String.join([
    "a.bend:2:14: escape: \\033 is NUL then \"33\", not octal: write \\u{1B}",
    "a.bend:2:62: escape: \\012 is NUL then \"12\", not octal: write \\u{A}",
    "a.bend:6:4: escape: \\07 is NUL then \"7\", not octal: write \\u{7}",
    "a.bend:9:4: escape: \\0 then digits is NUL and the digits, not octal: write \\u{..}"], "; ")
    : String}

# LAW: a Nat literal of 1000 or more
law nat_big:
  {lines(NatLit.check(Src.of("a.bend", C.tok.nat_src()))) == String.join([
    "a.bend:2:11: nat: 1000n is 1000 unary cells; use U32 (or U32.to_nat at run time) for big counts",
    "a.bend:2:26: nat: 4294967295n is 4294967295 unary cells; use U32 (or U32.to_nat at run time) for big counts"],
    "; ") : String}

# LAW: a match over long string literals
law strings_long:
  {lines(Strings.check(Src.of("a.bend", C.tok.strings_src()))) ==
    "a.bend:2:3: strings: a match over 3 string literals (79 characters) blows up compile time and memory; map the string to a sum type once (a lookup table)"
    : String}

# LAW: a match over many char literals
law chars_many:
  {lines(Chars.check(Src.of("a.bend", C.tok.chars_src()))) ==
    "a.bend:2:3: chars: a match over 9 character literals blows up compile time and memory; compare Char.to_u32(c) instead"
    : String}

# LAW: the same literal twice in a recursive def
law twice_lit:
  {lines(Twice.check(Src.of("a.bend", C.tok.twice_src()))) == String.join([
    "a.bend:3:16: twice: the same literal twice in one list pattern hangs the checker; match one element per step",
    "a.bend:16:23: twice: the same literal twice in one list pattern hangs the checker; match one element per step"],
    "; ") : String}

# LAW: a Nat arm under a wider n+p arm
law arms_wide:
  {lines(Arms.check(Src.of("a.bend", C.tok.arms_src()))) == String.join([
    "a.bend:7:10: arms: unreachable: case 1n+p above already matches every 2n+..",
    "a.bend:9:10: arms: unreachable: case 1n+p above already matches 3n",
    "a.bend:29:10: arms: unreachable: case Succ{p} above already matches 5n"], "; ") : String}

# LAW: pick: one branch recurses
law pick_once:
  {lines(Pick.check(Src.of("a.bend", C.rec.picked()))) ==
    "a.bend:6:7: pick: get recurses in one branch; Bool.pick runs it whatever the condition (no early exit); a.bend:11:7: pick: nested recurses in one branch; Bool.pick runs it whatever the condition (no early exit); a.bend:26:7: pick: two recurses in both branches; Bool.pick runs both"
    : String}

# LAW: a self-call under &&, || and Bool.or
law strict_and:
  {lines(Strict.check(Src.of("a.bend", C.rec.stricted()))) ==
    "a.bend:6:27: strict: digits recurses inside Bool.and/or; both sides always run (no short-circuit); a.bend:13:32: strict: has0 recurses inside Bool.and/or; both sides always run (no short-circuit); a.bend:20:7: strict: all0 recurses inside Bool.and/or; both sides always run (no short-circuit)"
    : String}

# LAW: a looping def called in a pick branch
law eager_cost:
  {lines(Eager.check(Src.of("a.bend", C.rec.eagered()))) ==
    "a.bend:9:38: eager: cost runs in both branches; Bool.pick runs it whatever the condition; bind it above, or Lazy.stop"
    : String}

# LAW: a proof file is exempt from eager
law eager_proof:
  {lines(Eager.check(Src.of("x/PROOF.bend", C.rec.eagered()))) == "" : String}

# LAW: a proof file is exempt from strict
law strict_proof:
  {lines(Strict.check(Src.of("x/PROOF.bend", C.rec.stricted()))) == "" : String}

# LAW: non-tail self-calls over a list or string
law tail_acc:
  {lines(Tail.check(Src.of("a.bend", C.rec.tailed()))) ==
    "a.bend:6:12: tail: len is not a tail call here; on a long list/string the JS lane overflows its stack; carry an accumulator; a.bend:20:15: tail: up is not a tail call here; on a long list/string the JS lane overflows its stack; carry an accumulator; a.bend:42:12: tail: count is not a tail call here; on a long list/string the JS lane overflows its stack; carry an accumulator"
    : String}

# LAW: a law file is exempt from tail
law tail_laws:
  {lines(Tail.check(Src.of("x/LAWS.bend", C.rec.tailed()))) == "" : String}

# LAW: ++ and List.append onto the carried parameter
law concat_acc:
  {lines(Concat.check(Src.of("a.bend", C.rec.concatted()))) ==
    "a.bend:6:15: concat: acc grows by appending each step: quadratic; prepend and reverse once, or build with <>; a.bend:13:36: concat: acc grows by appending each step: quadratic; prepend and reverse once, or build with <>"
    : String}

# LAW: List.get and String.get in a recursive def
law index_get:
  {lines(Index.check(Src.of("a.bend", C.rec.indexed()))) ==
    "a.bend:6:17: index: List.get inside a recursive def walks the list each step: quadratic; walk the list itself; a.bend:13:12: index: String.get inside a recursive def walks the list each step: quadratic; walk the list itself"
    : String}

# LAW: wrap counts bytes
law frame_wrap:
  {Frame.wrap("{}") == "Content-Length: 2\r\n\r\n{}" : String}

# LAW: wrap counts UTF-8 bytes, not chars
law frame_wrap_utf8:
  {Frame.wrap("é€😀") == "Content-Length: 9\r\n\r\né€😀" : String}

# LAW: UTF-8 round-trips
law frame_roundtrip:
  {Frame.decode(Frame.encode("aé€😀z")) == "aé€😀z" : String}

# LAW: a whole message cuts
law frame_cut:
  {C.frame.show(Frame.cut(Frame.encode(Frame.wrap("{\"a\":1}") ++ "Cont"))) == "{\"a\":1} +4"
    : String}

# LAW: other headers are skipped
law frame_headers:
  {C.frame.show(Frame.cut(Frame.encode("Content-Type: x; charset=utf-8\r\nContent-Length: 2\r\n\r\n[]")))
    == "[] +0" : String}

# LAW: a partial header waits
law frame_partial_header:
  {C.frame.show(Frame.cut(Frame.encode("Content-Length: 12\r\n"))) == "more" : String}

# LAW: a partial body waits
law frame_partial_body:
  {C.frame.show(Frame.cut(Frame.encode("Content-Length: 12\r\n\r\n{\"a\":"))) == "more" : String}

# LAW: a multi-byte body cuts by bytes
law frame_multibyte:
  {C.frame.show(Frame.cut(Frame.encode(Frame.wrap("\"é\"") ++ "x"))) == "\"é\" +1" : String}

# LAW: a file's directory
law path_dir:
  {Path.dir("/w/lsp/server.bend") == "/w/lsp" : String}

# LAW: a sibling import
law path_join_sib:
  {Path.join("/w/lsp", "./frame.bend") == "/w/lsp/frame.bend" : String}

# LAW: a parent import
law path_join_up:
  {Path.join("/w/lsp/tests", "../../json/value.bend") == "/w/json/value.bend" : String}

# LAW: a set replaces
law docs_set:
  {Maybe.default(&2, String, Docs.get(C.docs.sample(), "a"), "?") == "3" : String}

# LAW: others stay
law docs_other:
  {Maybe.default(&2, String, Docs.get(C.docs.sample(), "b"), "?") == "2" : String}

# LAW: a closed doc is gone
law docs_del:
  {Maybe.default(&2, String, Docs.get(Docs.del(C.docs.sample(), "a"), "a"), "?") == "?" : String}

# LAW: clean output has no diagnostics
law report_clean:
  {C.rep.show("All terms check.\n") == "" : String}

# LAW: an unsafe/foreign verdict is not a diagnostic
law report_unsafe:
  {C.rep.show("All terms check, but 2 defs rely on unsafe or foreign code:\n- spin\n- main\n")
    == "" : String}

# LAW: a module with no main is clean
law report_no_main:
  {C.rep.show("Error: no main to run\n") == "" : String}

# LAW: a type error lands on its marked line
law report_type:
  {C.rep.show("Error:\n- expected : String\n- observed : U32\nContext:\n- x : U32\nLocation: f\n3 | def f(x: U32) -> String:\n4>|   x\n5 | \n")
    == "[3|expected : String\nobserved : U32\nContext:\nx : U32]" : String}

# LAW: a syntax error has no def name
law report_syntax:
  {C.rep.show("Error:\n- expected : a name\n- observed : ':'\nLocation:\n2 | \n3>| def f(x: U32 -> U32:\n4 |   x\n")
    == "[2|expected : a name\nobserved : ':']" : String}

# LAW: a > in the source line does not hide the marker
law report_arrow:
  {C.rep.show("Error:\n- message  : bad\nLocation: g\n 9 | def g() -> U32:\n10>|   (x => x)(y > 2)\n11 | \n")
    == "[9|message  : bad]" : String}

# LAW: an error in an import lands on line 0, named
law report_import:
  {C.rep.show("Error:\n- expected : c\n- observed : c (consumed more than once)\nLocation: ../lex.feed\n133 | \n134>| def feed(c: Char, st: Lex) -> Lex:\n135 |   Lex{mode, buf, toks} = st\n")
    == "[0|in ../lex.feed:\nexpected : c\nobserved : c (consumed more than once)]" : String}

# LAW: an open goal count has no location
law report_todo:
  {C.rep.show("Error: 1 TODO found.\nThe code is incomplete, and not a valid proof yet.\n")
    == "[0|1 TODO found.\nThe code is incomplete, and not a valid proof yet.]" : String}

# LAW: an update nag is not part of the diagnostic
law report_todo_nag:
  {C.rep.show("Error: 1 TODO found.\nThe code is incomplete, and not a valid proof yet.\nbend 2.0.24 is available: run bend update\n")
    == "[0|1 TODO found.\nThe code is incomplete, and not a valid proof yet.]" : String}

# LAW: two errors are two diagnostics
law report_two:
  {C.rep.show("Error:\n- message  : one\nLocation: a\n1>| x\nError:\n- message  : two\nLocation: b\n7>| y\n")
    == "[0|message  : one][6|message  : two]" : String}

# LAW: the refs session prints its bodies
law refs_session:
  {Server.serve(~Script.Script, ~Script.new(), ~FakeChecker.new(), ~C.fake.files(), 100n,
    Script.Script{C.refs.inbox()}, [])
    == C.io.prints([
      "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":\"file:///w/a.bend\",\"diagnostics\":[{\"range\":{\"start\":{\"line\":2,\"character\":0},\"end\":{\"line\":3,\"character\":0}},\"severity\":2,\"code\":\"doc\",\"source\":\"bolt\",\"message\":\"type Shape has no comment above it\"},{\"range\":{\"start\":{\"line\":6,\"character\":10},\"end\":{\"line\":6,\"character\":11}},\"severity\":2,\"code\":\"param\",\"source\":\"bolt\",\"message\":\"parameter x is shorter than 2 characters\"}]}}",
      "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":[{\"uri\":\"file:///w/a.bend\",\"range\":{\"start\":{\"line\":6,\"character\":10},\"end\":{\"line\":6,\"character\":11}}},{\"uri\":\"file:///w/a.bend\",\"range\":{\"start\":{\"line\":7,\"character\":8},\"end\":{\"line\":7,\"character\":9}}},{\"uri\":\"file:///w/a.bend\",\"range\":{\"start\":{\"line\":9,\"character\":7},\"end\":{\"line\":9,\"character\":8}}}]}",
      "{\"jsonrpc\":\"2.0\",\"id\":2,\"result\":{\"changes\":{\"file:///w/a.bend\":[{\"range\":{\"start\":{\"line\":6,\"character\":10},\"end\":{\"line\":6,\"character\":11}},\"newText\":\"shape\"},{\"range\":{\"start\":{\"line\":7,\"character\":8},\"end\":{\"line\":7,\"character\":9}},\"newText\":\"shape\"},{\"range\":{\"start\":{\"line\":9,\"character\":7},\"end\":{\"line\":9,\"character\":8}},\"newText\":\"shape\"}]}}}",
      "{\"jsonrpc\":\"2.0\",\"id\":3,\"result\":[{\"uri\":\"file:///w/a.bend\",\"range\":{\"start\":{\"line\":6,\"character\":4},\"end\":{\"line\":6,\"character\":8}}},{\"uri\":\"file:///w/a.bend\",\"range\":{\"start\":{\"line\":12,\"character\":2},\"end\":{\"line\":12,\"character\":6}}}]}",
      "{\"jsonrpc\":\"2.0\",\"id\":4,\"result\":[{\"uri\":\"file:///w/a.bend\",\"range\":{\"start\":{\"line\":3,\"character\":2},\"end\":{\"line\":3,\"character\":8}}},{\"uri\":\"file:///w/a.bend\",\"range\":{\"start\":{\"line\":8,\"character\":9},\"end\":{\"line\":8,\"character\":15}}},{\"uri\":\"file:///w/a.bend\",\"range\":{\"start\":{\"line\":12,\"character\":7},\"end\":{\"line\":12,\"character\":13}}}]}",
      "{\"jsonrpc\":\"2.0\",\"id\":5,\"result\":[]}",
      "{\"jsonrpc\":\"2.0\",\"id\":6,\"error\":{\"code\":-32803,\"message\":\"only a name bound in this file can be renamed\"}}",
      "{\"jsonrpc\":\"2.0\",\"id\":7,\"result\":{\"data\":[0,0,6,0,0,0,7,4,2,0,2,0,4,0,0,0,5,5,2,0,0,6,2,0,0,0,3,4,0,0,1,2,6,3,0,0,7,1,6,0,0,3,3,2,0,3,0,3,0,0,0,4,4,1,0,0,6,1,4,0,0,3,3,2,0,0,8,3,2,0,1,2,5,0,0,0,6,1,4,0,1,4,4,0,0,0,5,6,3,0,0,7,1,5,0,1,7,1,4,0,0,4,1,5,0,0,4,3,2,0,2,0,3,0,0,0,4,4,1,0,0,10,3,2,0,1,2,4,1,0,0,5,6,3,0]}}"
    ]) : IO(Unit)}

# LAW: hover, definition and symbols over fake files
law nav_session:
  {Server.serve(~Script.Script, ~Script.new(), ~FakeChecker.new(), ~C.nav.files(), 100n,
    Script.Script{C.nav.inbox()}, [])
    == C.io.prints([
      "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":\"file:///w/app/main.bend\",\"diagnostics\":[{\"range\":{\"start\":{\"line\":4,\"character\":10},\"end\":{\"line\":4,\"character\":11}},\"severity\":2,\"code\":\"param\",\"source\":\"bolt\",\"message\":\"parameter x is shorter than 2 characters\"}]}}",
      "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":{\"contents\":{\"kind\":\"markdown\",\"value\":\"```bend\\ndef square(+x: U32) -> U32:\\n```\\n\\nsquares a number\"}}}",
      "{\"jsonrpc\":\"2.0\",\"id\":2,\"result\":{\"uri\":\"file:///w/lib/math.bend\",\"range\":{\"start\":{\"line\":3,\"character\":0},\"end\":{\"line\":4,\"character\":0}}}}",
      "{\"jsonrpc\":\"2.0\",\"id\":3,\"result\":{\"contents\":{\"kind\":\"markdown\",\"value\":\"```bend\\nCircle{r: U32}\\n```\"}}}",
      "{\"jsonrpc\":\"2.0\",\"id\":4,\"result\":{\"contents\":{\"kind\":\"markdown\",\"value\":\"```bend\\ndef U32.show(n: U32) -> String:\\n```\\n\\nshows a number\"}}}",
      "{\"jsonrpc\":\"2.0\",\"id\":5,\"result\":{\"uri\":\"file:///w/app/main.bend\",\"range\":{\"start\":{\"line\":4,\"character\":0},\"end\":{\"line\":5,\"character\":0}}}}",
      "{\"jsonrpc\":\"2.0\",\"id\":6,\"result\":null}",
      "{\"jsonrpc\":\"2.0\",\"id\":7,\"result\":[{\"name\":\"Base\",\"kind\":2,\"range\":{\"start\":{\"line\":0,\"character\":0},\"end\":{\"line\":1,\"character\":0}},\"selectionRange\":{\"start\":{\"line\":0,\"character\":0},\"end\":{\"line\":1,\"character\":0}}},{\"name\":\"M\",\"kind\":2,\"range\":{\"start\":{\"line\":1,\"character\":0},\"end\":{\"line\":2,\"character\":0}},\"selectionRange\":{\"start\":{\"line\":1,\"character\":0},\"end\":{\"line\":2,\"character\":0}}},{\"name\":\"twice\",\"kind\":12,\"range\":{\"start\":{\"line\":4,\"character\":0},\"end\":{\"line\":5,\"character\":0}},\"selectionRange\":{\"start\":{\"line\":4,\"character\":0},\"end\":{\"line\":5,\"character\":0}}},{\"name\":\"main\",\"kind\":12,\"range\":{\"start\":{\"line\":7,\"character\":0},\"end\":{\"line\":8,\"character\":0}},\"selectionRange\":{\"start\":{\"line\":7,\"character\":0},\"end\":{\"line\":8,\"character\":0}}}]}",
      "{\"jsonrpc\":\"2.0\",\"id\":9,\"result\":{\"contents\":{\"kind\":\"markdown\",\"value\":\"```bend\\nx: U32\\n```\\n\\nparameter\"}}}",
      "{\"jsonrpc\":\"2.0\",\"id\":10,\"result\":{\"uri\":\"file:///w/app/main.bend\",\"range\":{\"start\":{\"line\":4,\"character\":10},\"end\":{\"line\":4,\"character\":11}}}}",
      "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":\"file:///w/app/main.bend\",\"diagnostics\":[{\"range\":{\"start\":{\"line\":3,\"character\":10},\"end\":{\"line\":3,\"character\":11}},\"severity\":2,\"code\":\"param\",\"source\":\"bolt\",\"message\":\"parameter x is shorter than 2 characters\"}]}}",
      "{\"jsonrpc\":\"2.0\",\"id\":8,\"result\":{\"contents\":{\"kind\":\"markdown\",\"value\":\"```bend\\ndef twice(x: U32) -> U32:\\n```\\n\\ntriples now\"}}}"
    ]) : IO(Unit)}

# LAW: a law name and the proof that fills it hover as the law's comment
law law_hover:
  {Server.serve(~Script.Script, ~Script.new(), ~FakeChecker.new(), ~C.lawhover.files(), 100n,
    Script.Script{C.lawhover.inbox()}, [])
    == C.io.prints([
      "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":\"file:///w/io/LAWS.bend\",\"diagnostics\":[]}}",
      "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":{\"contents\":{\"kind\":\"markdown\",\"value\":\"```bend\\nlaw text_of_none:\\n  {F.text_of(None{}) == \\\"\\\" : String}\\n```\\n\\nLAW: and the text of nothing is the empty string.\"}}}",
      "{\"jsonrpc\":\"2.0\",\"id\":2,\"result\":{\"uri\":\"file:///w/io/LAWS.bend\",\"range\":{\"start\":{\"line\":5,\"character\":4},\"end\":{\"line\":5,\"character\":16}}}}",
      "{\"jsonrpc\":\"2.0\",\"id\":3,\"result\":{\"contents\":{\"kind\":\"markdown\",\"value\":\"```bend\\ndef text_of(m: Maybe<&2, String>) -> String:\\n```\\n\\nthe text a read answered\"}}}",
      "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":\"file:///w/io/PROOF.bend\",\"diagnostics\":[]}}",
      "{\"jsonrpc\":\"2.0\",\"id\":4,\"result\":{\"contents\":{\"kind\":\"markdown\",\"value\":\"```bend\\nlaw text_of_none:\\n  {F.text_of(None{}) == \\\"\\\" : String}\\n```\\n\\nLAW: and the text of nothing is the empty string.\"}}}",
      "{\"jsonrpc\":\"2.0\",\"id\":5,\"result\":{\"uri\":\"file:///w/io/PROOF.bend\",\"range\":{\"start\":{\"line\":3,\"character\":4},\"end\":{\"line\":3,\"character\":21}}}}"
    ]) : IO(Unit)}

# LAW: completion over fake files
law completion_session:
  {Server.serve(~Script.Script, ~Script.new(), ~FakeChecker.new(), ~C.completion.files(), 100n,
    Script.Script{C.completion.inbox()}, [])
    == C.io.prints([
      "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":\"file:///w/app/main.bend\",\"diagnostics\":[{\"range\":{\"start\":{\"line\":3,\"character\":0},\"end\":{\"line\":4,\"character\":0}},\"severity\":2,\"code\":\"doc\",\"source\":\"bolt\",\"message\":\"def mine has no comment above it\"},{\"range\":{\"start\":{\"line\":3,\"character\":9},\"end\":{\"line\":3,\"character\":10}},\"severity\":2,\"code\":\"param\",\"source\":\"bolt\",\"message\":\"parameter x is shorter than 2 characters\"}]}}",
      "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":{\"isIncomplete\":true,\"items\":[{\"label\":\"M.square\",\"kind\":3,\"detail\":\"def square(+x: U32) -> U32:\",\"documentation\":{\"kind\":\"markdown\",\"value\":\"squares a number\"},\"filterText\":\"M.square\",\"textEdit\":{\"range\":{\"start\":{\"line\":4,\"character\":2},\"end\":{\"line\":4,\"character\":6}},\"newText\":\"M.square\"}},{\"label\":\"M.sqrt\",\"kind\":3,\"detail\":\"def sqrt(x: U32) -> U32:\",\"documentation\":{\"kind\":\"markdown\",\"value\":\"\"},\"filterText\":\"M.sqrt\",\"textEdit\":{\"range\":{\"start\":{\"line\":4,\"character\":2},\"end\":{\"line\":4,\"character\":6}},\"newText\":\"M.sqrt\"}}]}}",
      "{\"jsonrpc\":\"2.0\",\"id\":2,\"result\":{\"isIncomplete\":true,\"items\":[{\"label\":\"U32.show\",\"kind\":21,\"detail\":\"law U32.show:\",\"documentation\":{\"kind\":\"markdown\",\"value\":\"\"},\"filterText\":\"U32.show\",\"textEdit\":{\"range\":{\"start\":{\"line\":5,\"character\":2},\"end\":{\"line\":5,\"character\":7}},\"newText\":\"U32.show\"}},{\"label\":\"U32.show.go\",\"kind\":3,\"detail\":\"def U32.show.go(n: U32) -> String:\",\"documentation\":{\"kind\":\"markdown\",\"value\":\"\"},\"filterText\":\"U32.show.go\",\"textEdit\":{\"range\":{\"start\":{\"line\":5,\"character\":2},\"end\":{\"line\":5,\"character\":7}},\"newText\":\"U32.show.go\"}}]}}",
      "{\"jsonrpc\":\"2.0\",\"id\":3,\"result\":{\"isIncomplete\":true,\"items\":[{\"label\":\"mine\",\"kind\":3,\"detail\":\"def mine(x: U32) -> U32:\",\"documentation\":{\"kind\":\"markdown\",\"value\":\"\"},\"filterText\":\"mine\",\"textEdit\":{\"range\":{\"start\":{\"line\":6,\"character\":2},\"end\":{\"line\":6,\"character\":3}},\"newText\":\"mine\"}}]}}",
      "{\"jsonrpc\":\"2.0\",\"id\":4,\"result\":{\"isIncomplete\":true,\"items\":[{\"label\":\"x\",\"kind\":6,\"detail\":\"x: U32\",\"documentation\":{\"kind\":\"markdown\",\"value\":\"parameter\"},\"filterText\":\"x\",\"textEdit\":{\"range\":{\"start\":{\"line\":7,\"character\":2},\"end\":{\"line\":7,\"character\":3}},\"newText\":\"x\"}}]}}"
    ]) : IO(Unit)}

# LAW: a script session over the fake checker
law session_session:
  {Server.serve(~Script.Script, ~Script.new(), ~FakeChecker.new(), ~C.fake.files(), 100n,
    Script.Script{C.session.inbox()}, [])
    == C.io.prints([
      "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":{\"capabilities\":{\"textDocumentSync\":{\"openClose\":true,\"change\":1,\"save\":true},\"hoverProvider\":true,\"definitionProvider\":true,\"documentSymbolProvider\":true,\"completionProvider\":{\"triggerCharacters\":[\".\"]},\"referencesProvider\":true,\"renameProvider\":true,\"semanticTokensProvider\":{\"legend\":{\"tokenTypes\":[\"keyword\",\"function\",\"type\",\"enumMember\",\"parameter\",\"variable\",\"property\",\"string\",\"number\",\"comment\",\"typeParameter\"],\"tokenModifiers\":[]},\"full\":true}},\"serverInfo\":{\"name\":\"bolt\",\"version\":\"0.6.0\"}}}", # x-release-please-version
      "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":\"file:///w/my%20bad.bend\",\"diagnostics\":[{\"range\":{\"start\":{\"line\":3,\"character\":0},\"end\":{\"line\":4,\"character\":0}},\"severity\":1,\"source\":\"bend\",\"message\":\"expected : String\\nobserved : U32\"}]}}",
      "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":\"file:///w/good.bend\",\"diagnostics\":[]}}",
      "{\"jsonrpc\":\"2.0\",\"id\":2,\"error\":{\"code\":-32601,\"message\":\"method not found\"}}",
      "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":\"file:///w/my%20bad.bend\",\"diagnostics\":[]}}",
      "{\"jsonrpc\":\"2.0\",\"id\":3,\"result\":null}"
    ]) : IO(Unit)}

# LAW: lint findings follow the open text
law lint_session:
  {Server.serve(~Script.Script, ~Script.new(), ~FakeChecker.new(), ~C.fake.files(), 100n,
    Script.Script{C.lint.inbox()}, [])
    == C.io.prints([
      "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":\"file:///w/bad.bend\",\"diagnostics\":[{\"range\":{\"start\":{\"line\":3,\"character\":0},\"end\":{\"line\":4,\"character\":0}},\"severity\":1,\"source\":\"bend\",\"message\":\"expected : String\\nobserved : U32\"},{\"range\":{\"start\":{\"line\":2,\"character\":0},\"end\":{\"line\":3,\"character\":0}},\"severity\":2,\"code\":\"doc\",\"source\":\"bolt\",\"message\":\"def f has no comment above it\"},{\"range\":{\"start\":{\"line\":3,\"character\":2},\"end\":{\"line\":3,\"character\":3}},\"severity\":2,\"code\":\"unused\",\"source\":\"bolt\",\"message\":\"local y is never used\"},{\"range\":{\"start\":{\"line\":2,\"character\":6},\"end\":{\"line\":2,\"character\":7}},\"severity\":2,\"code\":\"param\",\"source\":\"bolt\",\"message\":\"parameter x is shorter than 2 characters\"}]}}",
      "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":\"file:///w/bad.bend\",\"diagnostics\":[{\"range\":{\"start\":{\"line\":3,\"character\":0},\"end\":{\"line\":4,\"character\":0}},\"severity\":1,\"source\":\"bend\",\"message\":\"expected : String\\nobserved : U32\"},{\"range\":{\"start\":{\"line\":3,\"character\":6},\"end\":{\"line\":3,\"character\":7}},\"severity\":2,\"code\":\"param\",\"source\":\"bolt\",\"message\":\"parameter x is shorter than 2 characters\"}]}}",
      "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":\"file:///w/bad.bend\",\"diagnostics\":[{\"range\":{\"start\":{\"line\":3,\"character\":0},\"end\":{\"line\":4,\"character\":0}},\"severity\":1,\"source\":\"bend\",\"message\":\"expected : String\\nobserved : U32\"},{\"range\":{\"start\":{\"line\":3,\"character\":6},\"end\":{\"line\":3,\"character\":7}},\"severity\":2,\"code\":\"param\",\"source\":\"bolt\",\"message\":\"parameter x is shorter than 2 characters\"}]}}"
    ]) : IO(Unit)}
