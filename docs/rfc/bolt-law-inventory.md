# bolt law inventory

Read at `a38e87a` on `main` ("chore(main): release 0.9.0 (#43)"), bolt 0.9.0, with bend 2.0.25 (the version `flake.lock` pins through `bendlang/bend` at `a495242`).

This is the companion to [bolt-spec.md](bolt-spec.md). It records what bolt's LAWS.bend files state today, maps each law to the requirement it points toward, lists bolt's rule fixtures, and records what we found while checking the code. It follows the shape of ez's [ez-law-inventory.md](https://github.com/Emerging-Patterns/ez/blob/116d624c9e0e62c575de3ac7c920a72e647c3adb/docs/rfc/ez-law-inventory.md), and it takes the positions ez's specification reached: exactly two assurance levels, Proved and Trusted; pending is a status, not a level; a closed law has no standing; a test or fixture is never evidence for a requirement.

## The conflict everything else depends on

bolt#10 ("Prefer LAWS/PROOF over equality tests") made closed equalities first-class laws: the `closed` rule accepts `{lhs == rhs : T}` with no binder, including `IO(T)`, and 240 of bolt's own laws were written that way by moving `#|` tests into `syntax/spec/` and `bolt/spec/`. bolt#42 added `quantify` (L004), a strict mode of `closed` that flags every law without a binder, but made it opt in: no group setting reaches it, and bolt's own `bolt.bend` does not name it. ez's specification says closed laws have no standing. The maintainer's direction since #42 is that bolt should be strict about closed laws too, because they were made from tests that encoded wrong assumptions about Bend, and this cleanup exists to remove them. That direction is recorded as the first review item in the RFC, with the maintainer's follow-up decision that every closed law is deleted rather than kept as a `# toward <ID>` trail. "Points toward" below is therefore a map of what each closed law was reaching for, so the quantified law that replaces it can be written against the right requirement. It is not a list of laws to keep.

## How to read the tables

**Kind** is `Q` for a quantified law (at least one `for` or `exs` binder) and `C` for a closed law (no binder, one fixed input).

**Proof** is `{==}` when the whole proof in PROOF.bend is `{==}`: the two sides reduce to the same term with no case split. Every closed law in bolt is proved that way, which is what a closed law is. For a quantified law it means the binders are never inspected, so the law restates how a definition unfolds. `struct` means the proof matches, recurses or rewrites. `none` means no proof exists, which is on purpose in the one place it happens.

**Claim** is what the law states, in one line. A closed claim is about one fixed input even when the line reads like a general statement. "Pins the message text" means the expected value includes the full human-readable message of a finding, so a wording change breaks the proof.

**Points toward** names the requirement in the RFC that the law illustrates. For a closed law it records where the replacing quantified law belongs; the closed law itself is deleted either way. The IDs are the RFC's; the list is below. `none` has a reason in parentheses: `helper pin` is one private helper on one input, `core library` is code bolt does not run, `definitional` restates a definition, `wiring` restates how two defs are composed, `wording` pins text nobody depends on, `fixture` is a law about test scaffolding.

## Proposed requirement IDs

These are the IDs the RFC proposes. They are listed here so the tables can point at them; their wording and verdicts are in the RFC.

| ID | Short name |
| :---- | :---- |
| BOLT-RULE-`<code>` | One per per-file rule (C001 to C010, U001 to U012, S001 to S004, P001): the rule reports exactly the pattern its header comment describes. |
| BOLT-RULE-EXEMPT | A per-file rule returns no findings on a path its header exempts. |
| BOLT-RULE-INERT | For rules whose pattern is code, the contents of comments and string literals do not change the findings. |
| BOLT-LAW-1 | `law` (L001): every graded def and type is named by some law. |
| BOLT-LAW-2 | `closed` (L002): a law with no binder is a finding (strict, per the RFC). |
| BOLT-LAW-3 | `unsafe` (L003): an `@unsafe` def reached by relative imports from a law file is a finding. |
| BOLT-LAW-4 | `quantify` (L004): retired by the RFC, its ID and code reserved. |
| BOLT-LAW-5 | The proposed traceability rule over SPEC.md's requirement rows. |
| BOLT-CFG-1 | A rule's own setting wins over its group's, which wins over the group default. |
| BOLT-CFG-2 | Grading attaches the level to each finding and drops the `off` ones. |
| BOLT-CFG-3 | An unknown level word grades as error. |
| BOLT-CFG-4 | Each finding is graded by the nearest readable `bolt.bend`: its file's directory, then each parent. |
| BOLT-CFG-5 | Group defaults: correctness error, pedantic off, the rest warn. |
| BOLT-CFG-6 | An opt-in rule is on only when named. |
| BOLT-CFG-7 | An unknown setting name in a `bolt.bend` is a finding (proposed). |
| BOLT-SCOPE-1 | With no files, bolt lints every `.bend` under the current directory, skipping hidden directories and `node_modules`, in sorted order. |
| BOLT-SCOPE-2 | Per-file rules see one file; project rules see every file read. |
| BOLT-SCOPE-3 | A file is under law when it sits in or below a directory holding a LAWS.bend. |
| BOLT-SCOPE-4 | Exemptions are decided by path alone. |
| BOLT-SCOPE-5 | A `bolt.bend` is read, never linted. |
| BOLT-OUT-1 | Each rule has exactly one code, and each code names exactly one rule. |
| BOLT-OUT-2 | A finding prints as `path:line:col: level: CODE: message`, 1-based. |
| BOLT-OUT-3 | Output order is a function of the file list and the file contents. |
| BOLT-OUT-4 | The run ends with `clean` or the counts, and exits 1 exactly when a finding is an error. |
| BOLT-OUT-5 | A file that cannot be read is a finding, not a silent skip. |
| BOLT-OUT-6 | A released code is never renumbered or reused (Trusted). |
| BOLT-SYN-1 | Lexing is lossless. |
| BOLT-SYN-2 | Token lines and columns are the positions in the text. |
| BOLT-SYN-3 | The tree drops no token, and its leaves are the significant tokens in order. |
| BOLT-SYN-4 | The outline lists every top-level import, def, type, law and `@unsafe def`. |
| BOLT-SYN-5 | The binder resolves each use to the binding Bend would. |
| BOLT-SYN-6 | Every function in `syntax/` terminates without fuel (Trusted, through the checker). |
| BOLT-CLI-1 | Argument parsing: subcommand, files, `--`, help. |
| BOLT-CLI-2 | `--version` prints the release and the short commit when there is one. |
| BOLT-CHK-1 | `bolt check` turns bend's output into one diagnostic per error, on the line bend marks. |
| BOLT-LSP-1 | LSP framing counts UTF-8 bytes and never splits a message. |
| BOLT-LSP-2 | The LSP's diagnostics equal the CLI's per-file findings for the same file, text and `bolt.bend`. |
| BOLT-LSP-3 | Each request gets exactly one response with its id. |
| BOLT-LSP-4 | Open, change, save and close publish the diagnostics the RFC states. |
| BOLT-LSP-5 | The checker never runs `main`. |
| BOLT-LSP-6 | Hover, definition, references and completion follow the binder. |
| BOLT-LSP-7 | Positions are in the encoding the client negotiated. |
| BOLT-LIB-1 | `Lazy.stop`, `Lazy.or_else` and `Lazy.and_then` agree with `Bool.pick`, `Bool.or` and `Bool.and`. |

## The gate and bolt on itself

We ran every PROOF.bend under the gate (the first line bend prints must be exactly `All terms check.`), with `BEND_LIB` filled by `ez fetch` from the lock's git sources, and linted the tree with a binary built from it (`bend bolt/main.bend -o bin/bolt.bin`).

| Check | First line of output | Exit | Time |
| :---- | :---- | ----: | ----: |
| `bend bolt/lsp/fixtures/proven/PROOF.bend` | `All terms check.` | 0 | under 1 s |
| `bend bolt/spec/PROOF.bend` | `All terms check.` | 0 | 84 s |
| `bend core/PROOF.bend` | `All terms check.` | 0 | under 1 s |
| `bend lazy/PROOF.bend` | `All terms check.` | 0 | under 1 s |
| `bend syntax/spec/PROOF.bend` | `All terms check.` | 0 | 34 s |
| `bin/bolt.bin --gpu off` at the repo root | `clean` | 0 | 2.5 s |

All five pass. `bolt/lsp/fixtures/unproven/` has a LAWS.bend and no PROOF.bend on purpose: it is the LSP's example of an open law, and `bend LAWS.bend` there reports `Error: 1 TODO found.` Nothing gates it, since the gate looks for PROOF.bend files. `bend bolt/main.bend --check-only` prints `All terms check, but 5 defs rely on unsafe or foreign code:` (`dispatch`, `run.at`, `run`, `go`, `main`), which is expected for the binary's entry and outside the gate.

"clean" means less than it sounds. bolt's own `bolt.bend` does not name `quantify`, so none of the 257 closed laws is reported, and the `law` rule grades only the files under the six law directories (see "Findings").

## Summary

| File | Laws | Quantified | Closed | Quantified by `{==}` | Closed that pin message or protocol text |
| :---- | ----: | ----: | ----: | ----: | ----: |
| lazy/LAWS.bend | 3 | 3 | 0 | 0 | 0 |
| core/LAWS.bend | 26 | 9 | 17 | 6 | 0 |
| syntax/spec/LAWS.bend | 123 | 0 | 123 | 0 | 0 |
| bolt/spec/LAWS.bend | 117 | 0 | 117 | 0 | 46 |
| bolt/lsp/fixtures/proven/LAWS.bend | 1 | 1 | 0 | 0 | 0 |
| bolt/lsp/fixtures/unproven/LAWS.bend | 1 | 1 | 0 | 0 | 0 |
| **Total** | **271** | **14** | **257** | **6** | **46** |

core/PROOF.bend also states four lemma laws of its own (`Word.xor_zero`, `Word.xor_assoc.arm`, `Word.xor_assoc.go`, `Word.add_zero`). They are quantified and proved, and they serve `core/LAWS.bend`'s `xor_*` laws. They are not in the table because they are proof machinery, not claims.

What bolt proves today, in one paragraph: nothing about the linter. Every law about a rule, the config, the output, the parser, the command line, the checker report and the LSP is closed, 240 of them, each pinning the result of one call on one input, and 46 of those pin the full text of findings or LSP messages. The quantified laws are elsewhere. `lazy/` proves for all inputs that its three early-exit combinators agree with `Bool.pick`, `Bool.or` and `Bool.and` (BOLT-LIB-1), which matters because 79 call sites in `bolt/` and `syntax/` use them in place of the strict forms. `core/` proves monoid and fold identities of a dependency-injection library that the bolt binary does not import; only the host tests use `core/check` as their reporter. The two LSP fixture laws are examples the language server opens, not claims. So the proof gate passing tells us that 240 examples still compute what they computed when they were written, and that the lazy rewrite preserved meaning. It says nothing about whether any rule reports what its header describes for any other input.

## Inventory

### lazy/LAWS.bend

| Law | Line | Kind | Proof | Claim | Points toward |
| :---- | ----: | :---- | :---- | :---- | :---- |
| stop_is_pick | 9 | Q | struct | `Lazy.stop(c, a, _ => b) == Bool.pick(c, a, b)` for every `c`, `a`, `b`. | BOLT-LIB-1 |
| or_else_is_or | 16 | Q | struct | `Lazy.or_else(a, _ => b) == Bool.or(a, b)` for every `a`, `b`. | BOLT-LIB-1 |
| and_then_is_and | 22 | Q | struct | `Lazy.and_then(a, _ => b) == Bool.and(a, b)` for every `a`, `b`. | BOLT-LIB-1 |

### core/LAWS.bend

| Law | Line | Kind | Proof | Claim | Points toward |
| :---- | ----: | :---- | :---- | :---- | :---- |
| sum_unit_right | 22 | Q | struct | Sum's unit is a right identity: `M.join(Sum.new(), a, M.unit(Sum.new())) == a`. | none (core library) |
| xor_unit_right | 27 | Q | struct | Xor's unit is a right identity: `M.join(Xor.new(), a, M.unit(Xor.new())) == a`. | none (core library) |
| xor_assoc | 32 | Q | struct | Xor's join is associative. | none (core library) |
| one_at | 40 | Q | `{==}` | The one leaf is 1 at every index: `One.at(i) == 1`. | none (core library) |
| index_at | 45 | Q | `{==}` | The index leaf is its index: `Index.at(i) == i`. | none (core library) |
| one_leaf | 50 | Q | `{==}` | The one leaf, as a service, is One.at: `Leaf.at(One.new(), i) == One.at(i)`. | none (core library) |
| index_leaf | 55 | Q | `{==}` | The index leaf, as a service, is Index.at: `Leaf.at(Index.new(), i) == Index.at(i)`. | none (core library) |
| fold_leaf | 60 | Q | `{==}` | A fold over no levels is the leaf at i: `Fold.fold(~Sum.new(), ~One.new(), 0n, i) == Leaf.at(One.new(), i)`. | none (core library) |
| fold_split | 65 | Q | `{==}` | A fold over one level more joins the folds of its two halves. | none (core library) |
| fake_clock_now | 73 | C | `{==}` | The fake clock is 42: `FakeClock.now(Unit{}) == IO.pure(Nat, 42n)`. | none (core library) |
| fake_clock_via_service | 77 | C | `{==}` | The clock service reads the fake clock: `Clock.now(FakeClock.new()) == IO.pure(Nat, 42n)`. | none (core library) |
| real_clock_now | 81 | C | `{==}` | The real clock is IO.now: `RealClock.now(Unit{}) == IO.now()`. | none (core library) |
| real_clock_new | 85 | C | `{==}` | The real clock service is RealClock.now: `RealClock.new() == Clock.Clock{RealClock.now}`. | none (core library) |
| real_log_say | 89 | C | `{==}` | The real log prints the line: `Log.say(RealLog.new(), "hello") == IO.print("hello")`. | none (core library) |
| quiet_log_say | 93 | C | `{==}` | The quiet log is pure: `Log.say(QuietLog.new(), "unheard") == IO.pure(Unit, Unit{})`. | none (core library) |
| quiet_log_own | 97 | C | `{==}` | The quiet log's own say is pure: `QuietLog.say("unheard") == IO.pure(Unit, Unit{})`. | none (core library) |
| eq_u32_pass | 101 | C | `{==}` | Equal numbers print ok. | none (core library) |
| eq_u32_fail | 105 | C | `{==}` | Unequal numbers print FAIL. | none (core library) |
| eq_str_pass | 109 | C | `{==}` | Equal strings print ok. | none (core library) |
| eq_str_fail | 113 | C | `{==}` | Unequal strings print FAIL. | none (core library) |
| eq_u32_quiet | 117 | C | `{==}` | The quiet reporter says nothing. | none (core library) |
| print_pass | 122 | C | `{==}` | A pass is ok name: `Print.pass("n") == IO.print("ok n")`. | none (core library) |
| print_fail | 126 | C | `{==}` | A fail is FAIL name: `Print.fail("n") == IO.print("FAIL n")`. | none (core library) |
| report_pass | 130 | C | `{==}` | Report of True is pass: `Rep.report(True{}, Print.new(), "n") == Print.pass("n")`. | none (core library) |
| report_fail | 134 | C | `{==}` | Report of False is fail: `Rep.report(False{}, Print.new(), "n") == Print.fail("n")`. | none (core library) |
| quiet_say | 138 | C | `{==}` | The quiet reporter's say is pure: `Quiet.say("n") == IO.pure(Unit, Unit{})`. | none (core library) |

### syntax/spec/LAWS.bend

| Law | Line | Kind | Proof | Claim | Points toward |
| :---- | ----: | :---- | :---- | :---- | :---- |
| word_at_inside | 285 | C | `{==}` | Inside a qualified name: `Word.at(word_src(), 1, 9) == "Frame.decode"`. | BOLT-LSP-6 |
| word_at_first | 289 | C | `{==}` | At a name's first char: `Word.at(word_src(), 1, 2) == "Frame.decode"`. | BOLT-LSP-6 |
| word_at_after | 293 | C | `{==}` | Right after a name: `Word.at(word_src(), 1, 14) == "Frame.decode"`. | BOLT-LSP-6 |
| word_at_plain | 297 | C | `{==}` | A plain name: `Word.at(word_src(), 1, 16) == "body"`. | BOLT-LSP-6 |
| word_at_deep | 301 | C | `{==}` | A name deep in the line: `Word.at(word_src(), 1, 40) == "List.length"`. | BOLT-LSP-6 |
| word_at_op | 305 | C | `{==}` | On an operator there is none: `Word.at(word_src(), 1, 23) == ""`. | BOLT-LSP-6 |
| word_at_eol | 309 | C | `{==}` | Past the end of the line: `Word.at(word_src(), 1, 500) == ""`. | BOLT-LSP-6 |
| word_at_eof | 313 | C | `{==}` | Past the end of the text: `Word.at(word_src(), 9, 0) == ""`. | BOLT-LSP-6 |
| word_at_line0 | 317 | C | `{==}` | The first line: `Word.at(word_src(), 0, 8) == "Base"`. | BOLT-LSP-6 |
| word_before_mid | 321 | C | `{==}` | Typed so far, mid-name: `Word.before(word_src(), 1, 10) == "Frame.de"`. | BOLT-LSP-6 |
| word_before_dot | 325 | C | `{==}` | Typed so far, after an alias dot: `Word.before(word_src(), 1, 8) == "Frame."`. | BOLT-LSP-6 |
| word_before_paren | 329 | C | `{==}` | Nothing typed after a paren: `Word.before(word_src(), 1, 15) == ""`. | BOLT-LSP-6 |
| word_is_name | 333 | C | `{==}` | A letter is a name char: `Word.is_name('a') == True{}`. | none (helper pin) |
| word_is_name_op | 337 | C | `{==}` | An operator is not a name char: `Word.is_name('+') == False{}`. | none (helper pin) |
| word_text | 341 | C | `{==}` | Text of a reversed run: `Word.text(['b', 'a']) == "ab"`. | none (helper pin) |
| word_in_line | 345 | C | `{==}` | In_line is at on one line: `Word.in_line("Frame.decode", 2) == "Frame.decode"`. | none (helper pin) |
| word_finish_scan | 349 | C | `{==}` | Finish of a scanned line. | none (helper pin) |
| word_step | 353 | C | `{==}` | Step of a name char: `Word.finish(Word.step('a', Word.W{0, 0, [], None{}}, 0), 0) == "a"`. | none (helper pin) |
| word_close | 357 | C | `{==}` | Close of a run that holds the column: `Maybe.default(&2, String, Word.close(2, 0, ['b', 'a'], None{}, 1), "") == "ab"`. | none (helper pin) |
| word_head | 361 | C | `{==}` | Head of a dotted name: `Word.head("Alias.rest") == "Alias"`. | none (helper pin) |
| word_rest | 365 | C | `{==}` | Rest of a dotted name: `Word.rest("Alias.rest") == "rest"`. | none (helper pin) |
| word_cut_fst | 369 | C | `{==}` | Fst of a cut: `Word.fst(Word.cut("Alias.rest")) == "Alias"`. | none (helper pin) |
| word_cut_snd | 373 | C | `{==}` | Snd of a cut: `Word.snd(Word.cut("Alias.rest")) == "rest"`. | none (helper pin) |
| word_run_of | 377 | C | `{==}` | Run_of stops at a non-name: `String.from_list(Word.run_of(String.to_list("ab+"))) == "ab"`. | none (helper pin) |
| lex_lossless | 381 | C | `{==}` | Lex is lossless: `Lex.text(Lex.tokens(lex_src())) == lex_src()`. | BOLT-SYN-1 |
| lex_lossless_unclosed | 385 | C | `{==}` | Lex is lossless on an unclosed string: `Lex.text(Lex.tokens("x = \"abc\ny = 'q\nz")) == "x = \"abc\ny = 'q\nz"`. | BOLT-SYN-1 |
| lex_line_0 | 389 | C | `{==}` | The tokens of line 0 of the lexer fixture are exactly one kind:text@col list. | BOLT-SYN-2 |
| lex_line_1 | 395 | C | `{==}` | Line 1 of lex_src: `lex_show(1) == "k:case@2 #:1n@7 o:+@9 n:p@10 :::@11"`. | BOLT-SYN-2 |
| lex_line_2 | 399 | C | `{==}` | The tokens of line 2 of the lexer fixture are exactly one kind:text@col list. | BOLT-SYN-2 |
| lex_line_3 | 405 | C | `{==}` | Line 3 of lex_src: `lex_show(3) == "n:y@2 =:=@4 n:a@6 (:[@7 #:5@8 ):]@9 <:<-@11 #:42@14"`. | BOLT-SYN-2 |
| lex_is_keyword | 409 | C | `{==}` | Def is a keyword: `Lex.is_keyword("def") == True{}`. | none (helper pin) |
| lex_not_keyword | 413 | C | `{==}` | Foo is not a keyword: `Lex.is_keyword("foo") == False{}`. | none (helper pin) |
| lex_is_open | 417 | C | `{==}` | An open token: `Lex.is_open(Lex.TOpen{}) == True{}`. | none (helper pin) |
| lex_is_close | 421 | C | `{==}` | A close token: `Lex.is_close(Lex.TClose{}) == True{}`. | none (helper pin) |
| lex_is_comma | 425 | C | `{==}` | A comma token: `Lex.is_comma(Lex.TComma{}) == True{}`. | none (helper pin) |
| lex_is_name | 429 | C | `{==}` | A name token: `Lex.is_name(Lex.TName{}) == True{}`. | none (helper pin) |
| lex_is_op | 433 | C | `{==}` | An operator token: `Lex.is_op(Lex.TOp{}) == True{}`. | none (helper pin) |
| lex_is_nl | 437 | C | `{==}` | A newline token: `Lex.is_nl(Lex.TNewline{}) == True{}`. | none (helper pin) |
| lex_significant_space | 441 | C | `{==}` | Space is not significant: `Lex.significant(Lex.TSpace{}) == False{}`. | none (helper pin) |
| lex_word | 445 | C | `{==}` | A word's text: `Lex.word(['b', 'a']) == "ab"`. | none (helper pin) |
| lex_refine_name | 449 | C | `{==}` | Refine_name of def is a keyword: `Lex.refine_name("def") == Lex.TKey{}`. | none (helper pin) |
| lex_refine_op | 453 | C | `{==}` | Refine_op of -> is an arrow: `Lex.refine_op("->") == Lex.TArrow{}`. | none (helper pin) |
| lex_refine | 457 | C | `{==}` | Refine of a name: `Lex.refine(Lex.TName{}, "def") == Lex.TKey{}`. | none (helper pin) |
| lex_upper_first | 461 | C | `{==}` | Upper_first of U32: `Lex.upper_first(String.to_list("U32")) == True{}`. | none (helper pin) |
| lex_is_newline | 465 | C | `{==}` | Is_newline of CNewline: `Lex.is_newline(Lex.CNewline{}) == True{}`. | none (helper pin) |
| tree_nested | 469 | C | `{==}` | Statements nest by indent, groups by brackets. | BOLT-SYN-3 |
| tree_call_lines | 475 | C | `{==}` | A call over lines is one statement: `tree_show("f(a,\n  b)\nc") == "[f (a , b)] [c]"`. | BOLT-SYN-3 |
| tree_header_lines | 479 | C | `{==}` | A header over lines, then its body: `tree_show("def g(\n  a: U32\n) -> U32:\n  a") == "[def g (a : U32) -> U32 : {[a]}]"`. | BOLT-SYN-3 |
| tree_angles | 483 | C | `{==}` | >> closes two angle groups: `tree_show("x: List<List<U32>>") == "[x : List <List <U32>>]"`. | BOLT-SYN-3 |
| tree_lt | 487 | C | `{==}` | Less-than is not a bracket: `tree_show("a < b") == "[a < b]"`. | BOLT-SYN-3 |
| tree_ops | 491 | C | `{==}` | <> and <- are operators: `tree_show("a <> b <- c") == "[a <> b <- c]"`. | BOLT-SYN-3 |
| tree_unclosed | 495 | C | `{==}` | The next item closes an unclosed bracket. | BOLT-SYN-3 |
| tree_stray | 499 | C | `{==}` | A stray close is a leaf: `tree_show("f(x))") == "[f (x) )]"`. | BOLT-SYN-3 |
| tree_mismatch | 503 | C | `{==}` | A mismatched close reaches its match: `tree_show("f([x)\ny") == "[f ([x..)] [y]"`. | BOLT-SYN-3 |
| tree_eof | 507 | C | `{==}` | The end of the file closes everything: `tree_show("f(x\n  y") == "[f (x y..]"`. | BOLT-SYN-3 |
| tree_leaves | 511 | C | `{==}` | The leaves are the significant tokens: `tree_sig("def f(x):\n  g(x)  # c") == "deff(x):g(x)"`. | BOLT-SYN-3 |
| tree_empty | 515 | C | `{==}` | An empty source: `tree_show("") == ""`. | BOLT-SYN-3 |
| tree_of_tokens | 519 | C | `{==}` | Of_tokens is parse of the tokens: `Tree.show(Tree.of_tokens(Lex.tokens("x"))) == Tree.show(Tree.parse("x"))`. | none (definitional) |
| tree_closer | 523 | C | `{==}` | Closer of (: `Tree.closer("(") == ")"`. | none (helper pin) |
| tree_all_gt | 527 | C | `{==}` | All_gt of >>: `Tree.all_gt(['>', '>']) == True{}`. | none (helper pin) |
| tree_line | 531 | C | `{==}` | Line of a one-token source: `Tree.line(Tree.parse("x")) == 0`. | none (helper pin) |
| tree_col | 535 | C | `{==}` | Col of a one-token source: `Tree.col(Tree.parse("x")) == 0`. | none (helper pin) |
| tree_text | 539 | C | `{==}` | Text of a one-token source: `Tree.text(Tree.parse("x")) == "x"`. | none (helper pin) |
| tree_first | 543 | C | `{==}` | First of a one-token source is some: `Maybe.is_some(&2, Lex.Tok, Tree.first(Tree.parse("x"))) == True{}`. | none (helper pin) |
| tree_is_leaf | 547 | C | `{==}` | A leaf is a leaf: `Tree.is_leaf(Tree.Leaf{Lex.Tok{Lex.TName{}, "x", 0, 0}}) == True{}`. | none (helper pin) |
| tree_is_text | 551 | C | `{==}` | Is_text of that leaf: `Tree.is_text(Tree.Leaf{Lex.Tok{Lex.TName{}, "x", 0, 0}}, "x") == True{}`. | none (helper pin) |
| tree_is_name_tok | 555 | C | `{==}` | Is_name_tok of a name: `Tree.is_name_tok(Lex.Tok{Lex.TName{}, "x", 0, 0}) == True{}`. | none (helper pin) |
| tree_to_list | 559 | C | `{==}` | To_list of NNil: `List.is_empty(&2, Tree.Node, Tree.to_list(Tree.NNil{})) == True{}`. | none (helper pin) |
| tree_of_list | 563 | C | `{==}` | Of_list of none is NNil: `Tree.show(Tree.of_list([])) == ""`. | none (helper pin) |
| tree_reverse | 567 | C | `{==}` | Reverse of NNil is the acc: `Tree.show(Tree.reverse(Tree.NNil{}, Tree.NNil{})) == ""`. | none (helper pin) |
| tree_closes_with | 571 | C | `{==}` | Closes_with of a close paren: `Tree.closes_with(Lex.TClose{}, ")") == True{}`. | none (helper pin) |
| tree_opens_angle | 575 | C | `{==}` | Opens_angle of List<: `Tree.opens_angle(Lex.TOp{}, "<", True{}) == True{}`. | none (helper pin) |
| tree_opens | 579 | C | `{==}` | Opens of a group: `Tree.opens(Tree.parse("f(x)"), "(") == False{}`. | none (helper pin) |
| outline_items | 583 | C | `{==}` | The outline of outline_src. | BOLT-SYN-4 |
| outline_is_blank | 596 | C | `{==}` | A blank line: `Outline.is_blank("") == True{}`. | none (helper pin) |
| outline_is_import | 600 | C | `{==}` | An import kind: `Outline.is_import(Outline.IImport{}) == True{}`. | none (helper pin) |
| outline_is_def | 604 | C | `{==}` | A def kind: `Outline.is_def(Outline.IDef{}) == True{}`. | none (helper pin) |
| outline_name | 608 | C | `{==}` | Name up to a paren: `Outline.name("area(x: Shape) -> U32:") == "area"`. | none (helper pin) |
| outline_lstrip | 612 | C | `{==}` | Lstrip of a padded line: `Outline.lstrip("  x") == "x"`. | none (helper pin) |
| outline_nonempty | 616 | C | `{==}` | Nonempty of a word: `Outline.nonempty("x") == True{}`. | none (helper pin) |
| outline_words | 620 | C | `{==}` | Words of a line: `List.length(&2, String, Outline.words("def area")) == 2n`. | none (helper pin) |
| outline_undoc | 624 | C | `{==}` | Undoc drops a hash: `Outline.undoc("# hi") == "hi"`. | none (helper pin) |
| outline_doc_text | 628 | C | `{==}` | Doc_text of one line: `Outline.doc_text(["hi"]) == "hi"`. | none (helper pin) |
| outline_sig_text | 632 | C | `{==}` | Sig_text of one line: `Outline.sig_text(["def f():"]) == "def f():"`. | none (helper pin) |
| outline_def_name | 636 | C | `{==}` | Def_name of a def line: `Outline.def_name("def area(x: Shape) -> U32:") == "area"`. | none (helper pin) |
| outline_starts_upper | 640 | C | `{==}` | Starts_upper of Circle: `Outline.starts_upper("Circle{r: U32}") == True{}`. | none (helper pin) |
| outline_has | 644 | C | `{==}` | Has of a name: `Outline.has(["a"], "a") == True{}`. | none (helper pin) |
| outline_find | 648 | C | `{==}` | Find of area. | BOLT-LSP-6 |
| outline_import_path | 653 | C | `{==}` | Import_path of M. | BOLT-LSP-6 |
| outline_starting | 658 | C | `{==}` | Starting area. | BOLT-LSP-6 |
| outline_aliases | 663 | C | `{==}` | Aliases of M. | BOLT-LSP-6 |
| outline_add | 668 | C | `{==}` | Add of none: `List.is_empty(&2, Outline.Item, Outline.add(None{}, [])) == True{}`. | none (helper pin) |
| outline_classify | 672 | C | `{==}` | Classify of a def line: `Outline.classify("def f():") == Outline.LDef{}`. | none (helper pin) |
| bind_names_case | 676 | C | `{==}` | Deep in a case: `bind_names(9) == "g b a y r f A x"`. | BOLT-SYN-5 |
| bind_names_next | 680 | C | `{==}` | The next case sees none of the first: `bind_names(11) == "s f A x"`. | BOLT-SYN-5 |
| bind_names_do | 684 | C | `{==}` | Do-binds and typed lets: `bind_names(18) == "n n name"`. | BOLT-SYN-5 |
| bind_names_for | 688 | C | `{==}` | A law's for: `bind_names(22) == "x"`. | BOLT-SYN-5 |
| bind_names_header | 692 | C | `{==}` | A header over three lines: `bind_names(27) == "second first"`. | BOLT-SYN-5 |
| bind_at_param | 696 | C | `{==}` | A parameter: `bind_at(3, 10) == "bind 3:10 param \| +x: Shape"`. | BOLT-SYN-5 |
| bind_at_use | 700 | C | `{==}` | A parameter's use: `bind_at(4, 8) == "use x -> local 3:10"`. | BOLT-SYN-5 |
| bind_at_tele | 704 | C | `{==}` | A template parameter's arrow type: `bind_at(3, 31) == "bind 3:31 param \| ~f: U32 -> U32"`. | BOLT-SYN-5 |
| bind_at_case | 708 | C | `{==}` | A case binder: `bind_at(5, 17) == "bind 5:17 pat \| case Circle{+r}:"`. | BOLT-SYN-5 |
| bind_at_let | 712 | C | `{==}` | A destructured let: `bind_at(7, 12) == "bind 7:12 pat \| (a, K{b}) = pair(y)"`. | BOLT-SYN-5 |
| bind_at_ctor | 716 | C | `{==}` | A constructor in a pattern is a use: `bind_at(7, 10) == "use K -> free"`. | BOLT-SYN-5 |
| bind_at_lam | 720 | C | `{==}` | A lambda's binder: `bind_at(8, 16) == "use z -> local 8:10"`. | BOLT-SYN-5 |
| bind_at_do | 724 | C | `{==}` | A do-bind: `bind_at(15, 4) == "bind 15:4 local \| name : String <- IO.get_env(\"USER\")"`. | BOLT-SYN-5 |
| bind_at_rebind | 728 | C | `{==}` | A rebinding reads the old name: `bind_at(17, 17) == "use n -> local 16:4"`. | BOLT-SYN-5 |
| bind_at_alias | 732 | C | `{==}` | A name through an alias: `bind_at(17, 8) == "use Lex.step -> qual Lex step"`. | BOLT-SYN-5 |
| bind_at_free | 736 | C | `{==}` | A Base name is free: `bind_at(18, 4) == "use IO.print -> free"`. | BOLT-SYN-5 |
| bind_at_item | 740 | C | `{==}` | An item of the file: `bind_at(27, 2) == "use area -> item area"`. | BOLT-SYN-5 |
| bind_at_later | 744 | C | `{==}` | A later parameter with type arguments: `bind_at(25, 14) == "bind 25:14 param \| second: List<&2, U32>"`. | BOLT-SYN-5 |
| bind_at_field | 748 | C | `{==}` | A field: `bind_at(30, 20) == "bind 30:20 field \| join: @+p: U32 -> @+q: U32 -> U32"`. | BOLT-SYN-5 |
| bind_at_typevar | 752 | C | `{==}` | A type variable. | BOLT-SYN-5 |
| bind_at_kw | 757 | C | `{==}` | Nothing at a keyword: `bind_at(4, 2) == "-"`. | BOLT-SYN-5 |
| bind_sites_local | 761 | C | `{==}` | Every site of a local: `bind_sites(7, 12) == "7:12 9:8"`. | BOLT-SYN-5 |
| bind_item_area | 765 | C | `{==}` | Every site of an item: `bind_item_sites("area") == "3:4 27:2"`. | BOLT-SYN-5 |
| bind_at_ctor_line | 769 | C | `{==}` | A constructor line. | BOLT-SYN-5 |
| bind_head_of | 774 | C | `{==}` | Head_of of a dotted name: `Bind.head_of(String.to_list("Lex.step")) == "Lex"`. | none (helper pin) |
| bind_rest_of | 778 | C | `{==}` | Rest_of of a dotted name: `Bind.rest_of(String.to_list("Lex.step")) == "step"`. | none (helper pin) |
| bind_has | 782 | C | `{==}` | Has of a name: `Bind.has(["a", "b"], "a") == True{}`. | none (helper pin) |
| bind_spaced | 786 | C | `{==}` | Spaced of ->: `Bind.spaced("->") == " -> "`. | none (helper pin) |
| bind_named_sites | 790 | C | `{==}` | Named_sites of area: `List.length(&2, Bind.Pos, Bind.named_sites(Bind.bound(bind_src()), "area")) == 1n`. | none (helper pin) |
| bind_of_tree | 794 | C | `{==}` | Of_tree of a parse. | none (helper pin) |

### bolt/spec/LAWS.bend

| Law | Line | Kind | Proof | Claim | Points toward |
| :---- | ----: | :---- | :---- | :---- | :---- |
| src_fields | 78 | C | `{==}` | `Src.of`'s tokens, tree and binder equal `Lex.tokens`, `Tree.parse` and `Bind.bound` of one sample text. | none (definitional) |
| src_path | 83 | C | `{==}` | `Src.of` carries one path and text through unchanged. | none (definitional) |
| rules_all_is_on | 88 | C | `{==}` | `Rules.all(p, s)` gives the same findings as `Rules.on(Src.of(p, s))` on one sample. | none (wiring) |
| rules_sample | 93 | C | `{==}` | All per-file rules on one sample give exactly two findings, `doc` and `param`, with their text. | BOLT-RULE-S001, BOLT-RULE-S004 |
| args_bare | 99 | C | `{==}` | `bolt` with no words is lint over no files. | BOLT-CLI-1 |
| args_lint | 103 | C | `{==}` | `lint a b` selects lint with files a and b. | BOLT-CLI-1 |
| args_check_lsp | 107 | C | `{==}` | `check a` selects check with one file, and `lsp` selects lsp. | BOLT-CLI-1 |
| args_files | 111 | C | `{==}` | A first word that is no subcommand is a file. | BOLT-CLI-1 |
| args_check_many | 115 | C | `{==}` | `check` takes every leftover word as a file. | BOLT-CLI-1 |
| args_dash | 119 | C | `{==}` | Words after `--` are files. | BOLT-CLI-1 |
| args_help | 123 | C | `{==}` | `help` parses as NeedHelp at the root. | BOLT-CLI-1 |
| args_help_lint | 127 | C | `{==}` | `help lint` parses as NeedHelp at lint. | BOLT-CLI-1 |
| args_help_root | 131 | C | `{==}` | The root usage page is one exact text. | none (wording) |
| args_version_rev | 135 | C | `{==}` | `version.at("0.4.0", "2886b08")` is `0.4.0 (2886b08)`. | BOLT-CLI-2 |
| args_version_none | 139 | C | `{==}` | An empty commit id gives the release alone. | BOLT-CLI-2 |
| args_argv | 143 | C | `{==}` | `Args.argv()` is `IO.args()` widened; restates the definition. | none (definitional) |
| glob_fake | 149 | C | `{==}` | Over one canned tree, the walk finds the three `.bend` files, sorted, and skips `node_modules/` and `.gate/`. | BOLT-SCOPE-1 |
| walk_at_root | 155 | C | `{==}` | The fake walk's listing of `.` is its literal list. | none (fixture) |
| walk_entries | 160 | C | `{==}` | `FakeWalk.entries` is `IO.pure` of `FakeWalk.at`; restates the definition. | none (fixture) |
| doc_undotted | 164 | C | `{==}` | `doc` flags an undocumented def, type and law, and not a helper, a documented def or `main`, on one fixture. Pins the message text. | BOLT-RULE-S001 |
| doc_proof | 170 | C | `{==}` | The same fixture at `x/PROOF.bend` gives no `doc` finding. | BOLT-RULE-EXEMPT |
| doc_test | 174 | C | `{==}` | The same fixture at `x/tests/a.bend` gives no `doc` finding. | BOLT-RULE-EXEMPT |
| unused_names | 178 | C | `{==}` | `unused` flags an unused parameter, lets and a lambda binder, and not `_y`, `-A`, pattern binders, foreign parameters or a law's `for`, on one fixture. Pins the message text. | BOLT-RULE-U001 |
| shadow_def | 184 | C | `{==}` | `shadow` flags a let and a pattern binder named like a def above, and not one above the def or a parameter, on one fixture. Pins the message text. | BOLT-RULE-C001 |
| hole_todo | 190 | C | `{==}` | `hole` flags one `?TODO`. Pins the message text. | BOLT-RULE-C002 |
| hole_laws | 195 | C | `{==}` | The same `?TODO` in `LAWS.bend` gives no finding. | BOLT-RULE-EXEMPT |
| space_width | 199 | C | `{==}` | `space` flags trailing whitespace, a tab and a 121-wide comment, and not a long string literal or a `#\|` line. Pins the message text. | BOLT-RULE-S002 |
| wrap_header | 205 | C | `{==}` | `wrap` flags a one-line header over 120, and not one that fits, one already wrapped, or one long only by a string literal. Pins the message text. | BOLT-RULE-S003 |
| wrap_jammed | 210 | C | `{==}` | `wrap` flags seven badly broken multi-line headers and passes four others, including one that closes `)` on a parameter's line, on one fixture. Pins the message text. | BOLT-RULE-S003 |
| codes_table | 216 | C | `{==}` | The code table is exactly this slug, code, group list, in assignment order. | BOLT-OUT-1 |
| codes_source | 222 | C | `{==}` | `wrap` shows `S003` and `bolt(style:wrap)`; the non-rule `read` shows `read`, `bolt`, and grades with correctness. | BOLT-OUT-1, BOLT-OUT-5 |
| param_short | 227 | C | `{==}` | `param` flags a one-letter value parameter, and not type parameters, a bare quantity or a local. Pins the message text. | BOLT-RULE-S004 |
| pick_both | 232 | C | `{==}` | `pick` flags a self-call in both branches, including a nested pick, and not a call bound above. Pins the message text. | BOLT-RULE-C003 |
| law_gaps | 241 | C | `{==}` | Under one `LAWS.bend`, `law` flags each def and type no law names, IO defs included, and exempts helpers and `tests/`. Pins the message text. | BOLT-LAW-1 |
| law_none | 247 | C | `{==}` | A project with no `LAWS.bend` gets no `law` finding. | BOLT-LAW-1, BOLT-SCOPE-3 |
| config_defaults | 251 | C | `{==}` | With no config, nine named rules take their group defaults. | BOLT-CFG-5 |
| config_group | 257 | C | `{==}` | A group sets its rules, a rule set by name wins, and the typo `wran` grades as error, on one config. | BOLT-CFG-1, BOLT-CFG-3 |
| config_candidates | 262 | C | `{==}` | The candidates for `a/b/c.bend` are `a/b/`, `a/`, then top-level `bolt.bend`. | BOLT-CFG-4 |
| config_abs | 267 | C | `{==}` | The candidates for `/w/x.bend` stop at `/bolt.bend`. | BOLT-CFG-4 |
| config_nearest | 272 | C | `{==}` | The first readable candidate is the config, and later ones are ignored. | BOLT-CFG-4 |
| rules_graded | 277 | C | `{==}` | Grading one finding list under one config attaches levels and drops the `off` ones. Pins the message text. | BOLT-CFG-2 |
| rules_clean | 285 | C | `{==}` | Every per-file rule is quiet on one three-line documented file. | BOLT-RULE (all per-file) |
| imports_closure | 289 | C | `{==}` | The import closure of one `PROOF.bend` is this list, in discovery order. | BOLT-LAW-3 |
| unsafe_reached | 294 | C | `{==}` | `unsafe` flags the two `@unsafe` defs one PROOF.bend reaches, and not an unreached one. Pins the message text. | BOLT-LAW-3 |
| unsafe_quiet | 300 | C | `{==}` | `unsafe` is quiet when no law file reaches the `@unsafe` def. | BOLT-LAW-3 |
| unsafe_lawless | 304 | C | `{==}` | `unsafe` is quiet in a project with no law files. | BOLT-LAW-3, BOLT-SCOPE-3 |
| foreign_lanes | 308 | C | `{==}` | `foreign` flags a `.c` body with no `.js` and the reverse. Pins the message text. | BOLT-RULE-C010 |
| foreign_both | 314 | C | `{==}` | `foreign` is quiet on a def with both bodies. | BOLT-RULE-C010 |
| foreign_native | 320 | C | `{==}` | In a `# lanes: native` file only a missing `.c` body is flagged. Pins the message text. | BOLT-RULE-C010 |
| fuel_fixed | 326 | C | `{==}` | `fuel` flags `1000n` and `10n` passed as fuel, and not derived fuel, a qualified callee or an unknown callee. Pins the message text. | BOLT-RULE-U006 |
| fuel_derived | 332 | C | `{==}` | `fuel` is quiet on `Nat.add(2n, 1n)` as fuel. | BOLT-RULE-U006 |
| fuel_self | 338 | C | `{==}` | `fuel` is quiet on a def's own recursive call with a literal. | BOLT-RULE-U006 |
| closed_eq | 343 | C | `{==}` | `closed` is quiet on a closed equality, a one-line closed law, a `for` law and an `exs` law. | BOLT-LAW-2 |
| closed_noneq | 347 | C | `{==}` | `closed` flags a law with no binder that is not an equality. Pins the message text. | BOLT-LAW-2 |
| closed_for | 353 | C | `{==}` | `closed` is quiet on a law with `for`. | BOLT-LAW-2 |
| closed_outside | 358 | C | `{==}` | `closed` is quiet on laws outside a `LAWS.bend`. | BOLT-LAW-2, BOLT-SCOPE-4 |
| quantify_off | 362 | C | `{==}` | `quantify` is off with no config and with `laws` at error. | BOLT-CFG-6 |
| quantify_named | 368 | C | `{==}` | `quantify` set by name is on, and `closed` keeps its own level. | BOLT-CFG-6 |
| quantify_default_quiet | 373 | C | `{==}` | With `laws` at error and no `quantify`, a closed equality gives no finding. | BOLT-LAW-2, BOLT-CFG-6 |
| quantify_strict_graded | 378 | C | `{==}` | With `quantify` at error, the same closed equality is one L004 error. Pins the message text. | BOLT-LAW-4, BOLT-CFG-6 |
| quantify_eq | 385 | C | `{==}` | `quantify` flags a closed equality and a closed IO equality. Pins the message text. | BOLT-LAW-4 |
| quantify_noneq | 392 | C | `{==}` | `quantify` flags a closed non-equality. Pins the message text. | BOLT-LAW-4 |
| quantify_for | 398 | C | `{==}` | `quantify` is quiet on `for` and `exs` laws. | BOLT-LAW-4 |
| quantify_marked | 404 | C | `{==}` | A `# toward` line directly above `law` silences `quantify`; one above the doc comment does not. Pins the message text. | BOLT-LAW-4 |
| quantify_outside | 411 | C | `{==}` | `quantify` is quiet outside a `LAWS.bend`. | BOLT-LAW-4, BOLT-SCOPE-4 |
| put_call | 416 | C | `{==}` | `put` flags a `Map.put(` call, and not one in a comment, a string or `Map.put.bit`. Pins the message text. | BOLT-RULE-C004 |
| put_own | 422 | C | `{==}` | A file that defines `Map.put` is exempt. | BOLT-RULE-C004 |
| escape_octal | 426 | C | `{==}` | `escape` flags `\033`, `\012`, `\07` and `\09`, and not `\\033`, `\u{1B}`, `\0b` or a comment. Pins the message text. | BOLT-RULE-C006 |
| nat_big | 435 | C | `{==}` | `nat` flags `1000n` and `4294967295n`, and not `999n`, a U32 literal, a comment or a string. Pins the message text. | BOLT-RULE-U005 |
| strings_long | 442 | C | `{==}` | `strings` flags one match over string literals past 64 characters, and not the smaller ones. Pins the message text. | BOLT-RULE-C008 |
| chars_many | 448 | C | `{==}` | `chars` flags one match over nine char literals, and not the smaller ones or a comment. Pins the message text. | BOLT-RULE-C009 |
| twice_lit | 454 | C | `{==}` | `twice` flags two list patterns repeating a literal, and not one that does not. Pins the message text. | BOLT-RULE-C007 |
| arms_wide | 461 | C | `{==}` | `arms` flags three unreachable Nat arms under wider ones, and not well-ordered matches. Pins the message text. | BOLT-RULE-C005 |
| pick_once | 468 | C | `{==}` | `pick` flags a self-call in one branch and in both, and not a call bound above. Pins the message text. | BOLT-RULE-C003 |
| strict_and | 474 | C | `{==}` | `strict` flags self-calls under `&&`, `Bool.or` and `\|\|`, and not a bound call or one outside the Bool op. Pins the message text. | BOLT-RULE-U002 |
| eager_cost | 480 | C | `{==}` | `eager` flags one looping call in a pick branch, and not a bound call, a non-looping def or a self-call. Pins the message text. | BOLT-RULE-U003 |
| eager_proof | 486 | C | `{==}` | The same fixture at `x/PROOF.bend` gives no `eager` finding. | BOLT-RULE-EXEMPT |
| strict_proof | 490 | C | `{==}` | The same fixture at `x/PROOF.bend` gives no `strict` finding. | BOLT-RULE-EXEMPT |
| tail_acc | 494 | C | `{==}` | `tail` flags three non-tail self-calls over lists and strings, and not accumulators or a tree. Pins the message text. | BOLT-RULE-P001 |
| tail_laws | 500 | C | `{==}` | The same fixture at `x/LAWS.bend` gives no `tail` finding. | BOLT-RULE-EXEMPT |
| concat_acc | 504 | C | `{==}` | `concat` flags `++` and `List.append` onto the carried accumulator, and not prepends. Pins the message text. | BOLT-RULE-U004 |
| index_get | 510 | C | `{==}` | `index` flags `List.get` and `String.get` in recursive defs, and not a non-recursive def or a get on the element being walked. Pins the message text. | BOLT-RULE-U007 |
| table_set | 516 | C | `{==}` | A fixed table read or set in the loop is `table`, a data-dependent list stays `index`, and the same fixture at `x/PROOF.bend` gives no `table` finding. Pins the message text. | BOLT-RULE-U008, BOLT-RULE-U007 |
| hoist_table | 523 | C | `{==}` | `hoist` flags three tables rebuilt per step, and not one built in a base case, one built from the walked element, or a small array; `x/PROOF.bend` gives none. Pins the message text. | BOLT-RULE-U009 |
| ring_window | 529 | C | `{==}` | `ring` flags a list and a string window dropped and appended per step, and not plain growth or a drop of the walked list itself; `x/PROOF.bend` gives none. Pins the message text. | BOLT-RULE-U010 |
| rewalk_twice | 535 | C | `{==}` | `rewalk` flags two defs that walk the same argument twice and read one result for a single value, and not two walks of different arguments, two full uses, or walks in different arms; `x/PROOF.bend` gives none. Pins the message text. | BOLT-RULE-U011 |
| unit_one | 541 | C | `{==}` | `unit` flags three multiplies or divides by one on a recursive step, and not one in a base case, a non-recursive def or a subtraction; `x/PROOF.bend` gives none. Pins the message text. | BOLT-RULE-U012 |
| frame_wrap | 547 | C | `{==}` | `wrap("{}")` has `Content-Length: 2`. | BOLT-LSP-1 |
| frame_wrap_utf8 | 551 | C | `{==}` | `wrap` of three multi-byte characters has `Content-Length: 9`. | BOLT-LSP-1 |
| frame_roundtrip | 555 | C | `{==}` | `decode(encode(s)) == s` for one mixed-width string. | BOLT-LSP-1 |
| frame_cut | 559 | C | `{==}` | `cut` returns one whole message and leaves the four trailing bytes. | BOLT-LSP-1 |
| frame_headers | 564 | C | `{==}` | `cut` skips a `Content-Type` header. | BOLT-LSP-1 |
| frame_partial_header | 569 | C | `{==}` | `cut` waits on a header with no blank line. | BOLT-LSP-1 |
| frame_partial_body | 573 | C | `{==}` | `cut` waits on a short body. | BOLT-LSP-1 |
| frame_multibyte | 577 | C | `{==}` | `cut` measures a multi-byte body in bytes. | BOLT-LSP-1 |
| path_dir | 581 | C | `{==}` | `Path.dir` of one absolute path. | BOLT-LSP-6 |
| path_join_sib | 585 | C | `{==}` | `Path.join` of a sibling import. | BOLT-LSP-6 |
| path_join_up | 589 | C | `{==}` | `Path.join` of a two-level parent import. | BOLT-LSP-6 |
| docs_set | 593 | C | `{==}` | A second `set` of one key replaces the first. | BOLT-LSP-4 |
| docs_other | 597 | C | `{==}` | Other keys are untouched. | BOLT-LSP-4 |
| docs_del | 601 | C | `{==}` | A deleted key is gone. | BOLT-LSP-4 |
| report_clean | 605 | C | `{==}` | `All terms check.` gives no diagnostic. | BOLT-CHK-1 |
| report_unsafe | 609 | C | `{==}` | The unsafe-or-foreign verdict gives no diagnostic. | BOLT-CHK-1 |
| report_no_main | 614 | C | `{==}` | `Error: no main to run` gives no diagnostic. | BOLT-CHK-1 |
| report_type | 618 | C | `{==}` | A type error lands on the line bend marks with `>\|`. | BOLT-CHK-1 |
| report_syntax | 623 | C | `{==}` | A syntax error with no def name lands on its marked line. | BOLT-CHK-1 |
| report_arrow | 628 | C | `{==}` | A `>` inside the source line does not hide the marker. | BOLT-CHK-1 |
| report_import | 633 | C | `{==}` | An error located in an import lands on line 0. | BOLT-CHK-1 |
| report_todo | 638 | C | `{==}` | An open-goal count lands on line 0. | BOLT-CHK-1 |
| report_todo_nag | 643 | C | `{==}` | Bend's update nag is dropped from the diagnostic. | BOLT-CHK-1 |
| report_two | 648 | C | `{==}` | Two errors give two diagnostics. | BOLT-CHK-1 |
| refs_session | 653 | C | `{==}` | One scripted session of references requests prints exactly these responses. | BOLT-LSP-6 |
| nav_session | 668 | C | `{==}` | One scripted session of hover, definition and symbols prints exactly these responses. | BOLT-LSP-6 |
| law_hover | 687 | C | `{==}` | Hover on a law name and on its proof def shows the law's comment, in one session. Pins the message text. | BOLT-LSP-6 |
| completion_session | 701 | C | `{==}` | One scripted completion session prints exactly these responses. | BOLT-LSP-6 |
| session_session | 713 | C | `{==}` | One scripted open, change and close session over the fake checker prints exactly these messages. | BOLT-LSP-4 |
| lint_session | 726 | C | `{==}` | Lint diagnostics follow an open and an edit of one document, in one session. Pins the message text. | BOLT-LSP-2, BOLT-LSP-4 |

### bolt/lsp/fixtures/proven/LAWS.bend

| Law | Line | Kind | Proof | Claim | Points toward |
| :---- | ----: | :---- | :---- | :---- | :---- |
| add_zero | 4 | Q | struct | Zero is a right identity of addition. | none (LSP fixture) |

### bolt/lsp/fixtures/unproven/LAWS.bend

| Law | Line | Kind | Proof | Claim | Points toward |
| :---- | ----: | :---- | :---- | :---- | :---- |
| add_zero | 4 | Q | none | Zero is a right identity of addition. | none (LSP fixture) |

## Rule fixtures

bolt's examples of each pattern live in `bolt/spec/cases.bend` as source text, and the laws above run a rule over them. Under the spec's rules a fixture is never evidence for a requirement, but the fixtures are the best record we have of what each rule's author meant it to catch and to leave alone, so we list them. Every def in `cases.bend` has a dotted name, which is why none needs a comment or a law (see "Findings"). Line numbers are in `bolt/spec/cases.bend`.

| Fixture | Line | Rule | Flags | Stays quiet on | Laws |
| :---- | ----: | :---- | :---- | :---- | :---- |
| `rules.undocumented` | 65 | doc | `dec`, `T`, law `l` with no comment | documented `inc`, helper `dec.go`, `main`; the whole text at `x/PROOF.bend` and `x/tests/a.bend` | doc_undotted, doc_proof, doc_test, rules_graded |
| `rules.unused` | 88 | unused | parameter `x`, locals `b`, `g`, `h`, lambda binder `w` | used names, `_y`, erased `-A`, pattern binders `p` and `r`, foreign parameter `path`, law binder `ih` | unused_names, rules_graded |
| `rules.shadowed` | 109 | shadow | let `k` and pattern `k` below `def k` | let `k` above `def k`, parameter `k` | shadow_def |
| `rules.holes` | 127 | hole | one `?TODO` | the same text as `LAWS.bend` | hole_todo, hole_laws |
| `rules.spaced` | 130 | space | trailing space, a tab, a 121-wide comment | a 200-character string literal, a `#\|` trailer line | space_width |
| `rules.headers` | 134 | wrap | a one-line header over 120 | a one-liner that fits, a wrapped header, a header long only by a string literal | wrap_header |
| `rules.jammed` | 149 | wrap | seven multi-line headers with two parameters on a line, a parameter on the `def` line, a split return, or a parameter split across lines | `black`, `shut`, `trail`, and a one-liner | wrap_jammed |
| `rules.params` | 191 | param | parameter `n` | type parameters `A`, `T`; quantity `a`; local `x` | param_short, rules_sample |
| `rules.picked` | 206 | pick | `go` and `nested` recursing in both branches | `ok`, which binds the call above | pick_both |
| `rec.picked` | 733 | pick | `get` and `nested` in one branch, `two` in both | `ok` | pick_once |
| `rules.lawful` | 230 | law | `g`, `main`, type `O`, `h`, `shout`, `k`, `j`, `s` (eight gaps under `./p/`) | named `f` and `say`, helper `g.go`, `./p/tests/t.bend`, `./q/n.bend` outside any law directory | law_gaps |
| `rules.config` | 241 | config | `laws` set to the typo `wran`, graded error | | config_group, config_nearest, rules_graded |
| `proj.reached` | 261 | unsafe, imports | `spin` and `walk`, reached from `./p/PROOF.bend` | `loose`, unreached | imports_closure, unsafe_reached |
| `proj.unreached` | 269 | unsafe | | `loose`, reached by no law file | unsafe_quiet |
| `proj.lawless` | 274 | unsafe | | `spin` in a project with no law files | unsafe_lawless |
| `proj.foreigns` | 278 | foreign | `.c`-only `a.b`, `.js`-only `a.c` | `a.d` with both, plain `e` | foreign_lanes |
| `proj.native` | 297 | foreign | `.js`-only `a.c` | `.c`-only `a.b`, in a `# lanes: native` file | foreign_native |
| `proj.fuels` | 300 | fuel | `walk(1000n, ..)`, `spend(.., 10n)` | self-call `go(3n)`, derived fuel, `U32.to_nat`, qualified `M.walk`, unknown `other` | fuel_fixed |
| `proj.laws` | 328 | closed, quantify | | a closed equality, a one-line closed law, a `for` law, an `exs` law, and the same text outside LAWS.bend | closed_eq, closed_outside |
| `tok.put_src` | 349 | put | `Map.put(` | `Map.put(` in a comment and a string, `Map.put.bit` | put_call |
| `tok.put_own` | 358 | put | | a file that defines `Map.put` | put_own |
| `tok.escape_src` | 363 | escape | `\033`, `\012`, `\07`, `\09` | `\\033`, `\u{1B}`, `\0b`, a comment | escape_octal |
| `tok.nat_src` | 375 | nat | `1000n`, `4294967295n` | `999n`, `12n`, U32 `100000`, a comment, a string | nat_big |
| `tok.strings_src` | 954 | strings | one match over 79 characters of string arms | smaller matches | strings_long |
| `tok.chars_src` | 1022 | chars | one match over nine char arms | smaller matches, char literals in a comment | chars_many |
| `tok.twice_src` | 1064 | twice | two list patterns repeating a literal in a recursive def | a pattern that does not repeat | twice_lit |
| `tok.arms_src` | 1095 | arms | `2n+..` and `3n` under `1n+p`; `5n` under `Succ{p}` | well-ordered matches, a two-scrutinee match | arms_wide |
| `rec.stricted` | 384 | strict | self-calls under `&&`, `Bool.or`, `\|\|` | a call bound above; a self-call in a pick branch whose condition uses `&&`; the whole text at `x/PROOF.bend` | strict_and, strict_proof |
| `rec.eagered` | 422 | eager | `cost(xs)` in a pick branch | a bound call, a cheap condition, a self-call, a non-looping `flat`, a looping call in a nested pick's condition; the whole text at `x/PROOF.bend` | eager_cost, eager_proof |
| `rec.tailed` | 457 | tail | `len`, `up`, `count` | accumulator `sum`, tree `size`, `keep`; the whole text at `x/LAWS.bend` | tail_acc, tail_laws |
| `rec.concatted` | 502 | concat | `acc ++ ..`, `List.append(acc, [h])` | prepends `pre` and `back` | concat_acc |
| `rec.indexed` | 532 | index | `List.get` in `total`, `String.get` in `scan` | non-recursive `third`, a get on the walked element in `heads` | index_get |
| `rec.tabled` | 559 | table, index | fixed table read in `go`, set in `setgo`; data-dependent `dep` as `index` | `grow`, `once`, `slot`; the whole text at `x/PROOF.bend` | table_set |
| `rec.hoisted` | 603 | hoist | `go`, `uses`, `arr` rebuilding a table per step | `cold` (base case), `rowed` (built from the element), `tiny` (eight cells); `x/PROOF.bend` | hoist_table |
| `rec.ringed` | 653 | ring | `step`, `text` | `grow`, `eat`; `x/PROOF.bend` | ring_window |
| `rec.rewalked` | 675 | rewalk | `go`, `bound` | `both`, `full`, `split`; `x/PROOF.bend` | rewalk_twice |
| `rec.united` | 708 | unit | `* 1` in `hot`, `Nat.mul(p, 1n)` and `Nat.div(.., 1n)` in `nest` | `cold`, `base`, `minus`; `x/PROOF.bend` | unit_one |

The LSP has its own fixtures under `bolt/lsp/fixtures/`, read by the stay-list host tests in `bolt/lsp/tests/`: `effectful.bend` (a `main` the server must never run), `mistyped.bend` (the checker's one type error), `levels/bolt.bend` (a config for `levels.bend`), and the `proven/` and `unproven/` law pair. The canned LSP sessions (`refs`, `nav`, `lawhover`, `completion`, `session`, `lint` in `cases.bend`) are inboxes of JSON-RPC messages with a fake file service and a fake checker; each session law pins every byte the server prints.

## Findings

We checked each of these against the code at `a38e87a`. "Confirmed" means we reproduced it by running the binary built from this tree on a small scratch project; "by reading" means we did not. They are recorded, not resolved. The RFC carries a review item for each one a requirement depends on.

### The three we were asked to verify

**Most of bolt sits outside any law directory, so `law` never grades it.** Confirmed. `law_dirs` (`bolt/rules/laws/law.bend:50-56`) collects the directory of every file whose path ends in `LAWS.bend`, and `under` (`law.bend:59-64`) grades a file when its normalized path starts with one of them, so a law directory covers its subdirectories too. This repo has six: `lazy/`, `core/`, `bolt/spec/`, `syntax/spec/`, `bolt/lsp/fixtures/proven/` and `bolt/lsp/fixtures/unproven/`. Of the 94 source files that are neither exempt nor a `bolt.bend`, the rule grades 19: `lazy/lazy.bend`, the 17 files of `core/`, and `bolt/spec/cases.bend`, whose defs are all dotted and so out of scope. The other 76 are never graded: all 13 of `bolt/*.bend`, the 35 files of `bolt/rules/`, the 20 of `bolt/lsp/`, the 3 of `bolt/walk/`, and the 5 of `syntax/*.bend` (`syntax/spec/` holds only its LAWS.bend and PROOF.bend). The linter itself is entirely ungraded. The laws that describe it live in `bolt/spec/` and `syntax/spec/`, beside the code rather than above it, which is exactly the placement that keeps the code out of scope.

**The `tests/` exemption matches anywhere in a path.** Confirmed. `Digest.is_exempt` (`bolt/rules/digest.bend:115-117`) is `String.contains(pp, "tests/")`, so `p/contests/x.bend` beside `p/LAWS.bend` gets no L001 finding while `p/sub/x.bend` does. The same pattern holds for the law files: every `LAWS.bend` and `PROOF.bend` test in bolt is `String.ends_with`, so `p/OUTLAWS.bend` is exempt from `law`, makes its own directory a law directory, and is held to `closed` and `quantify`; `p/myPROOF.bend` is exempt from `law` and `param`, and `DISPROOF.bend` becomes a starting point for `unsafe`. The rules also disagree on the spelling: `doc` exempts `contains(path, "/tests/")` (`bolt/rules/style/doc.bend:50`), with the leading slash, so `bolt tests/t.bend` is not exempt from `doc` while the walked `./tests/t.bend` is, and `contests/` is exempt from `law` but not from `doc`.

**`main` has no ruleset or branch protection requiring CI.** Confirmed through the GitHub API on 2026-09-22: `repos/Emerging-Patterns/bolt/branches/main/protection` answers "Branch not protected", `repos/.../rulesets` is `[]`, and `repos/.../rules/branches/main`, which includes rulesets inherited from the organization, is `[]`. The repository also has `allow_auto_merge` on, so an auto-merge request on a pull request merges without waiting for `ci.yml`. The proof gate and bolt's self-lint therefore run on every pull request but bind nothing.

### Behavior the code guarantees that no law states

Every per-file rule's `check` is a pure function of the `Src` it is handed: it reads the path, the text and the three parsed readings, and nothing else (`bolt/src.bend:12-14`). None has IO, and none has a fuel limit that cuts findings short. The two project rules are pure functions of the list of digests, which means of the set of files in the run and their order.

With no files named, bolt lints every `.bend` file under `.`, skipping any directory whose name starts with `.` and `node_modules` (`bolt/glob.bend:10-11`), and sorts the result by `String.is_le` (`glob.bend:58-61`). Symbolic links are listed as files even when they point at directories, so the walk cannot loop (`bolt/walk/dir.c:1-5`). A file that cannot be read becomes a `read` finding, `Cannot read this file.`, which grades with correctness and so is an error by default (`bolt/lint.bend:35-40`, `bolt/rules.bend:92-94`). A `bolt.bend` in the file list is dropped before reading (`lint.bend:91-101`). The run prints `clean` or `N errors, M warnings` and exits 1 exactly when some graded finding is an error (`lint.bend:108-150`, `bolt/status.bend`). Findings print 1-based (`bolt/finding.bend:16-29`).

The output order is fixed but not sorted: the `read` findings first, then each file's per-file findings in file-list order, each file's findings in the rule order of `Rules.on` (`bolt/rules.bend:49-79`) and each rule's in its own traversal order, and the project rules `law` and `unsafe` last, over all files. Naming a file twice lints it twice.

A law anywhere counts as coverage, not only a law in a LAWS.bend: `law_mentions` reads every `law` statement of every file in the run (`digest.bend:87-95`), so the lemma laws in `core/PROOF.bend`, or a law in an ungraded file, cover the defs they mention.

### Behavior that looks accidental

The `law` rule's notion of "named" is a token match (`digest.bend:67-95`). Any name token in a law's header or body counts, so a closed law covers every def it mentions, the law's own name covers a def of the same name in the same file, and a type is covered by any mention of its module, including a name that does not exist (`M.zzz`). A bare name covers only a def in the law's own file. Taken together with bolt#10, this makes the cheapest way to satisfy `law` a closed law that calls each def once, which is the shape of the 63 `helper pin` laws in `syntax/spec/LAWS.bend`. Confirmed.

A dotted name is out of scope for both `doc` and `law` whether or not its parent exists (`doc.bend:24-25`, `law.bend:79`). Every def in `bolt/spec/cases.bend` is dotted (`src.sample`, `rules.lawful`), with no `src` or `rules` def to ride on, and none has a comment; bolt still reports the file clean. Confirmed by the self-lint.

The project rules see only the files in the run. Linting `p/m.bend` alone reports no L001 gap that linting `p/` does; an `unsafe` chain `PROOF.bend` to `mid.bend` to `lib/u.bend` is missed when `mid.bend` is not in the run; and mixing an absolute and a relative spelling of paths turns both rules off, since directory prefixes and resolved import paths no longer match. `Imports.norm` also drops the leading `/` of an absolute path (`bolt/rules/imports.bend:16-34`). Confirmed.

`quantify`'s `# toward` marker is the last line of the law's doc comment after `Outline.undoc` strips `# ` or a bare `#` (`bolt/rules/laws/quantify.bend:32-46`, `syntax/outline.bend:248-250`). `#toward R-1` exempts, while `#  toward`, `# Toward` and a bare `# toward` do not, and README's advice to list exemptions with `grep -rn '^# toward '` misses the `#toward` form. `closed` and `quantify` both accept a `for` binder that the statement never uses, and `closed` accepts any law with `==` anywhere inside it, so `{Bool.and(1 == 1, True{}) : Bool}` passes. Confirmed.

Config lookup stops at the current directory for relative paths. The candidates for `a/b/c.bend` are `a/b/bolt.bend`, `a/bolt.bend` and `bolt.bend` (`bolt/config.bend:127-140`), so running bolt from a subdirectory of a project never reads the project's root `bolt.bend`, and for `../x.bend` the second candidate is the current directory's `bolt.bend`, which is not a parent of the file. A setting whose name is no rule or group is silently ignored; the word `warning`, which is what bolt prints for a warn finding, grades as error; and the pseudo-rule `read` can be switched off with `def read()`. The first matching setting in a file wins, `"Error"`, `"OFF"` and `""` also grade as error, and only the nearest `bolt.bend` applies, with no merging of parents. Confirmed: from `p1/sub`, `bolt a.bend` grades by the defaults while `bolt sub/a.bend` from `p1` grades by `p1/bolt.bend`, and `../../p3/a.bend` was graded by a `bolt.bend` that is not an ancestor of the file. A directory given as an argument reads as empty and reports `clean`.

`bolt check` reports `clean` and exits 0 when `bend` is not on the PATH. Confirmed: `bolt/lsp/checker/exec.c` exits 127 with no output, and an empty report parses as no errors. It also places an error inside an imported module on the importing file's line, because `bolt/lsp/report.bend:80-82` looks for a `/` in bend's `Location:` line and bend 2.0.25 prints `Location: m.dbl`; the closed law `report_import` pins the older format. The LAWS.bend settling in `bolt/lsp/checker/bend.bend:38` needs a `/LAWS.bend` suffix, so `bolt check LAWS.bend` and `bolt check ./LAWS.bend` disagree. Confirmed.

The parser agrees with bend on most of what the rules rely on, and is total with no fuel. Lexing is lossless on every input we tried, including unclosed strings (`syntax/lex.bend:289-293`), and the tree drops no token whatever the brackets. It disagrees with bend in four places we confirmed. bend accepts a string literal that spans lines, and bolt splits it at the newline, so text inside the string can become a phantom def with findings of its own. A continuation line indented under an expression becomes a child statement. A `>` inside parentheses nested in `<..>` closes the angle group. A run of `>` characters is re-emitted as single-character tokens with synthesized positions (`syntax/tree.bend:271-276`), so the tree's leaves equal the significant tokens as text but not as a token list, and the closed law `tree_leaves` compares text only. Identifiers are ASCII-only (`Char.is_alpha`), and the outline reads column-0 prefixes line by line without the tree, so the two can disagree.

The LSP differs from the CLI on the same text. It runs only the per-file rules, never `law` or `unsafe` (`bolt/lsp/server.bend:93-98`), and it grades by the absolute path in the document URI where the CLI grades by the path as typed, so the two pick different `bolt.bend` files from a subdirectory. Columns are code points while LSP clients count UTF-16 units by default, and the server advertises no `positionEncoding`, so a finding after an astral character is off by one per such character. `Content-Length` is matched case-sensitively (`bolt/lsp/frame.bend:129-132`), so a lowercase header loses the message. Malformed JSON is ignored rather than answered with `-32700`, requests after `shutdown` are still answered, the exit code is 0 even on EOF without `shutdown`, and a surrogate-pair `\u` escape comes back as invalid UTF-8. The checker has no timeout, so a hung `bend` blocks the loop. Confirmed.

`wrap` flags every one-line def header that ends in a trailing comment (`def u(aa: U32) -> U32: # note`) as "not one parameter per line", because `Outline.ends_colon` looks at the last character of the line (`syntax/outline.bend:338`) and the header then swallows the body. It also accepts `)` on a parameter's line, which its header rules out. Confirmed.

The correctness rules each have at least one confirmed false positive or false negative against their header, except `escape`. `twice`, `strings` and `chars` look at the first column of a multi-scrutinee match only. `pick` and `twice` decide "recursive" by any leaf equal to the def's name, so a parameter named like the def makes them fire, and `pick` reports a nested both-branch pick twice though its header says it will not. `pick` does not call `Calls.exempt`, though `bolt/rules/calls.bend:1-5` names it among the rules that do. `hole` misses `? TODO`. `foreign`'s `# lanes: native` exemption matches that line anywhere in the file, not only in the header. `strings` reports 4294967295 characters for an unterminated string arm, from a U32 underflow. `arms` misses `Succ{_}`. `chars`'s header cites `bolt/lsp/frame.bend` as an example of a match it leaves alone, and that file no longer has one.

The suspicious rules are the same story: only `nat` does exactly what its header says, and each of the other eleven has at least one confirmed false positive or false negative. `unused` reports every parameter of a foreign def whose header is wrapped, since its exemption reads only the `def` line. `strict` fires on a self-call inside a lazy thunk under `||`. `eager`, `concat`, `fuel` and `ring` all miss the same pattern once it is bound by a let first. `concat` and `ring` never check which argument slot the grown or dropped value goes into. `fuel` flags any Nat literal passed to a parameter named `steps` or `fuel`, including an exact repeat count such as `3n`. `index` flags a `List.get` that sits only in the base arm. `table` collects let names across the whole body with no scoping, so a later rebinding to a growing list still counts as the table. `hoist` treats any user-def call with carried arguments as a wide table and never applies its 8-cell limit to it. `ring` takes only the first scrutinee as the matched list. `rewalk` compares arguments as text, so a rebinding between the two calls still counts as the same walk. `unit` skips an operator followed by `(`. Nine rules share `Calls.exempt` (`bolt/rules/calls.bend:201-202`), a suffix test, so `x/MYPROOF.bend` is exempt and `x/proof.bend` is not. Throughout, name matching is by raw token text, so a qualified or aliased call (`Base.Bool.or`, `Me.len`) is invisible to every recursion rule. Each finding in this paragraph was confirmed.

core/PROOF.bend states laws of its own (`Word.xor_zero` and three more). The gate checks them like any law, but no LAWS.bend states them, so nothing marks them as claims a change must keep.
