# RFC: A Behavioral Specification for bolt

Read at a38e87a on main ("chore(main): release 0.9.0 (#43)"), bolt 0.9.0, bend 2.0.25.

## Draft Status

**State:** Draft

This draft was written from the code at `a38e87a`, from the evidence in [bolt-law-inventory.md](bolt-law-inventory.md), and from the positions reached by the specification of ez, the project manager and proof-gate runner for Bend 2 that bolt is built with (Emerging-Patterns/ez), which went through this spec-to-proof process first ([ez-spec.md](https://github.com/Emerging-Patterns/ez/blob/master/docs/rfc/ez-spec.md)). Every verdict below was checked against the code, and most were confirmed by running a binary built from this tree. The items below are decisions this draft makes and asks a maintainer to confirm. Each one also appears inline where the decision lives. The first one comes first because every other decision depends on how it is resolved.

**Items for review:**

- [ ] <!-- REVIEW-1: bolt#10 made closed equalities first-class laws and moved 240 `#|` tests into closed laws; bolt#42 added `quantify` (L004) as an opt-in strict mode. That conflicts with ez's position that closed laws have no standing. The maintainer has given the direction: bolt is strict about closed laws too, and every closed law is deleted, not kept as a `# toward` trail. What remains is the mechanism. We propose that `closed` (L002) itself becomes strict and reports any law in a LAWS.bend with no binder; the `# toward` exemption goes away; `quantify` is retired and L004 is reserved, never reused; bolt's own bolt.bend sets `closed` to error. This is a behavior change for every project that runs bolt, and no compatibility path is kept. ez has agreed: it keeps its `# toward` trail laws only while its rollout lasts, stays pinned at bolt v0.9.0 until the last trail is deleted, and then bumps bolt, removes `def quantify()` from its bolt.bend and turns on strict `closed`. Other projects learn of the change from the release notes, and once BOLT-CFG-7 lands a leftover `def quantify()` is itself a finding. -->
- [ ] <!-- REVIEW-2: Each BOLT-RULE-<code> requirement is the rule's header comment rewritten precisely. Where the verdict is partly, we propose fixing the code where the header states the intent a user relies on (`pick` reporting nested picks twice, `wrap` flagging trailing comments, `strings` underflow), and narrowing the header where the code's behavior is a deliberate heuristic (`fuel` matching by parameter name, `eager` only counting looping defs). The per-rule list is in the inventory. -->
- [ ] <!-- REVIEW-3: The `law` rule grades 19 of 94 source files and none of the linter. We propose moving the law files up so their directories cover the code they describe (`bolt/LAWS.bend`, `syntax/LAWS.bend`), with `law` at warn in bolt's own bolt.bend until the quantified laws exist, as ez does. We also propose that coverage changes meaning (BOLT-LAW-1): a def or type is covered only when a quantified law in a LAWS.bend references it, where a reference is a use in the law's statement that the binder (BOLT-SYN-5) resolves to that def, through an import alias or in the same file. A law's own name, a token in a closed law, a law outside a LAWS.bend, and a nonexistent `M.zzz` stop counting. This is the fix that matters most to ez, which needs it before it turns `law` back to error. Behavior change. -->
- [ ] <!-- REVIEW-4: Exemptions are decided by suffix and substring tests. We propose one shared predicate module: a law file is a path whose basename is exactly `LAWS.bend` or `PROOF.bend`, and a test is a path with a segment exactly `tests`. Behavior change: `contests/`, `OUTLAWS.bend` and `myPROOF.bend` stop being exempt. -->
- [ ] <!-- REVIEW-5: Config lookup for a relative path stops at the current directory and handles `..` lexically. We propose resolving each path against the working directory before computing candidates, so BOLT-CFG-4 holds as README states it. Also proposed: an unknown setting name in a bolt.bend becomes a finding (BOLT-CFG-7), and `warning` is accepted as a synonym for `warn`. We also propose that the walk's silent truncation past 100000 directories becomes a finding (BOLT-SCOPE-1). Behavior change. -->
- [ ] <!-- REVIEW-6: `bolt check` reports `clean` and exits 0 when bend cannot be run. We propose that a spawn failure becomes an error diagnostic and exit 1, and that the report parser's import-location rule is corrected against bend 2.0.25's `Location:` format. Behavior change. -->
- [ ] <!-- REVIEW-7: The LSP and the CLI give different findings for the same text. We propose BOLT-LSP-2 states that the LSP's diagnostics for an open document equal the CLI's per-file findings for that file under the same bolt.bend, with project rules out of the LSP's scope by design. The path difference disappears once REVIEW-5 lands. We also propose advertising `positionEncoding: utf-32` when the client offers it, and converting to UTF-16 otherwise. -->
- [ ] <!-- REVIEW-8: `main` has no branch protection or ruleset, and auto-merge is on, so the gate binds nothing. We propose a repository ruleset on `main` that requires the `ci` check (the `nix flake check` job) and forbids force pushes. A maintainer applies it by hand; this RFC does not. BOLT-TRUST-7 holds only once it exists. -->
- [ ] <!-- REVIEW-9: The traceability rule (BOLT-LAW-5, requested in Emerging-Patterns/bolt#44) goes in bolt's `laws` group as a project rule, opt-in by name, and reads only the requirement and trust tables of the SPEC.md at the root of the linted tree. The SPEC.md format under "Tagging and traceability" is decided for bolt's own spec; ez adopts it as it stands. The rule needs discovery of one non-`.bend` file, a table-row parser, and a project-rule shape that receives the spec rows. -->
- [ ] <!-- REVIEW-10: Code stability across releases cannot be a law, since a law sees one version. We propose splitting it: BOLT-OUT-1, the one-to-one map between slugs and codes, is Proved, and BOLT-OUT-6, "a released code is never renumbered or reused", is Trusted, enforced by review of the SPEC row that lists the table. -->
- [ ] <!-- REVIEW-11: Output order is fixed but not sorted by line. We propose BOLT-OUT-3 states today's order rather than change it, because editors and the gate do not depend on sorting and a sort costs a pass over every finding. -->
- [ ] <!-- REVIEW-12: `core/` is a library the bolt binary does not import. We propose its quantified laws stay as untagged laws outside bolt's SPEC, its 17 closed laws are deleted with the rest, and whether `core/` moves to its own repository is left out of this RFC. -->
- [ ] <!-- REVIEW-13: Soundness laws for tree rules may cost more than they are worth. The escape hatch is explicit: a requirement that proves too expensive moves to Trusted with a written reason. We order the work so token rules come first. -->
- [ ] <!-- REVIEW-14: Splitting each command into a planner and an interpreter makes three interpreters' faithfulness assumptions that the trust table does not yet name. We propose three rows, each added in the same PR that introduces its interpreter and justified there as the refactoring contract requires: BOLT-TRUST-9, the lint interpreter lists, reads and prints what the plan says and exits with its status; BOLT-TRUST-10, the `bolt check` interpreter records bend's output or its spawn failure in the oracle unchanged; BOLT-TRUST-11, the LSP loop feeds each received message to `step`, performs its asks, and sends its replies in order. -->

## Abstract

bolt has 271 laws, and 257 of them are closed: each pins one call on one input, so the proof gate passing tells us that old examples still compute what they did, and nothing about whether a rule reports what its header describes. This RFC defines a behavioral specification for bolt, in the same shape as ez's, in which every requirement is either **Proved** by a tagged quantified law or **Trusted** as a named assumption. It deletes every closed law, makes the `closed` rule strict, models the lint run as a pure planner over a World value so that its IO behavior can be stated, and adds the traceability rule, which ez also adopts.

## Glossary

| Term | Meaning |
| :---- | :---- |
| ez | The project manager and proof-gate runner for Bend 2 that bolt is built with (Emerging-Patterns/ez), which went through this spec-to-proof process first. |
| Rule (per-file) | A function `check(Src) -> List<Finding>` that looks at one file. bolt has 29: the 27 with a BOLT-RULE row, plus the laws rules `closed` and `quantify`, which look only at LAWS.bend files. |
| Project rule | A rule that sees a digest of every file in the run at once. Today there are two, `law` and `unsafe`, which with the 29 per-file rules make 31. |
| Finding | A report of one rule at one place: path, line, column, length, rule slug, message. |
| Graded finding | A finding with the level its bolt.bend assigns to it attached. `off` findings are dropped. |
| Group | One of the five sets of rules (correctness, suspicious, style, laws, pedantic) that a single setting can grade together. |
| Level | `off`, `warn` or `error`. An error makes the run exit 1. |
| bolt.bend | A project's configuration: plain Bend, one def per setting, each body a level string. |
| Law directory | The directory of a LAWS.bend in the run. Files in or below it are graded by `law`. |
| Exemption | A path a rule skips by its header, such as a LAWS.bend for `hole` or a `tests/` file for `doc`. |
| `Src` | The parsed form every per-file rule receives: path, text, tokens, tree and binder, computed once (`bolt/src.bend`). |
| Digest | The per-file summary project rules read: the path and its normalized form, law-file flags, top-level items, law mentions, imports and `@unsafe` defs (`bolt/rules/digest.bend`). |
| `#\|` test | A test written as a `#\|` trailer comment beside the code, which a test runner evaluates. bolt#10 moved most of bolt's into closed laws. |
| Closed law | A law with no `for` or `exs` binder. It holds for one input, which makes it a unit test checked at compile time. |
| Quantified law | A law with at least one binder. It holds for every input of that type. |
| Proof gate | For every PROOF.bend, `bend PROOF.bend` prints exactly `All terms check.` as its first line. |
| Proved | A requirement backed by a quantified law tagged with its ID, passing the proof gate. |
| Trusted | A requirement that is assumed, listed in the trust boundary, and checked by nothing in bolt. |
| Pending | The status of a Proved requirement whose law has not landed. It is a status, not a level. |
| Requirement ID | A stable name such as `BOLT-CFG-4` for one row of `SPEC.md`. |
| Trust boundary | The table of every Trusted requirement, with the reason each is assumed. |
| World | A value that models everything a command can observe: the working directory, directory listings, file contents, and for `bolt check` the answers bend gives. |
| Planner | The pure part of a command. It reads a World and returns a plan of lines to print and an exit status. |
| Interpreter | The thin IO part of a command. It fills a World from the real system and performs the plan. |
| Helper | A def whose name contains a dot (`dec.go`), which rides on its parent's comment and laws and so is out of scope for `doc` and `law`. The parent need not exist, which the inventory records as accidental. |
| Stay list | AGENTS.md's list of the host and integration tests that Bend cannot state as laws: `tests/bare.bend`, `tests/flake.bend`, the LSP checker and levels tests, syntax's disk lex and tree tests, and `lazy/tests/lazy.bend`. |
| Header comment | A rule module's leading comment block. It is the only statement of what the rule is for, and so its de facto spec. |

## Background

### What bolt is

bolt is a linter, a checker (`bolt check`) and a language server (`bolt lsp`) for Bend 2, written in Bend and shipped as one binary built from `bolt/main.bend`. It has 31 rules in five groups: correctness (C001 to C010), suspicious (U001 to U012), style (S001 to S004), laws (L001 to L004) and pedantic (P001). Twenty-seven of them are per-file rules of type `check(Src) -> List<Finding>`, and each has a BOLT-RULE requirement below. Two more, the laws rules `closed` and `quantify`, also run per file but look only at LAWS.bend files, so BOLT-LAW-2 and BOLT-LAW-4 cover them rather than BOLT-RULE rows. The last two, `law` and `unsafe`, are project rules over the digests of every file in the run.

Each finding is graded by the nearest bolt.bend. bolt's own bolt.bend sets the correctness, suspicious, style and laws groups to error, leaving pedantic at its default of off, and the gate requires `bolt` run at the repository root to print `clean`. That makes bolt both a tool other projects run, ez among them, and a project that holds itself to its own rules, which is why a change to what a rule reports is a change in two places at once.

### How bolt proves things today

bolt uses Bend's LAWS/PROOF model, as ez does. Its laws live in six LAWS.bend files, and all five PROOF.bend files pass the gate: `bolt/spec/PROOF.bend` takes 84 s and `syntax/spec/PROOF.bend` 34 s, and the others finish in under a second. bolt then lints itself clean.

Both results mean less than they sound. The inventory counts 271 laws, of which 14 are quantified and 257 closed. All 240 laws about the linter itself (123 in `syntax/spec/`, 117 in `bolt/spec/`) are closed, each proved by `{==}`, and 46 of those pin the full text of a finding or an LSP message. The one real guarantee is in `lazy/`: three quantified laws prove that `Lazy.stop`, `Lazy.or_else` and `Lazy.and_then` agree with `Bool.pick`, `Bool.or` and `Bool.and` for every input, which matters because 79 call sites use them in place of the strict forms. The nine quantified laws in `core/` are about a dependency-injection library that the bolt binary does not import. The self-lint is clean only because `quantify` is off in bolt.bend, so none of the 257 closed laws is reported, and because `law` grades 19 of the 94 source files, none of them part of the linter.

These laws came from bolt#10, which made closed equalities first-class laws: the `closed` rule accepts `{lhs == rhs : T}` with no binder, `IO(T)` included, and 240 `#|` tests (Bend's inline test trailers, a `#|` comment line holding an expression the test runner evaluates and compares) were moved into `syntax/spec/` and `bolt/spec/` in that form. bolt#42 later added `quantify` (L004), a strict mode that flags every law without a binder, but made it opt in.

### How bolt and ez depend on each other

The two repositories check each other. bolt's gate is built with ez: `flake.nix` calls ez's `mkProofs`, the nix helper that builds a flake check running every PROOF.bend through ez's runner, and bolt pins shake (a Bend argv parser) and ezjson (a Bend JSON library) through `ez.toml`. In the other direction, ez runs bolt as a lint tool through `mkLint`, and ez's specification asks bolt for two things it cannot do itself: a `closed` rule strict enough to enforce "closed laws have no standing", and a traceability rule that reads `SPEC.md` and the tagged laws. So a decision in this RFC about closed laws or tagging is also a decision about how ez's own specification is enforced, which is why this RFC mirrors ez's shape and takes its positions as given.

ez is also the most useful case study we have of bolt in use. It is the largest Bend project bolt lints, and bolt v0.8.1 reported about 900 style, correctness and suspicious findings in it before ez's own cleanup. It shares bolt's foundations, including the bad assumptions we made about Bend early on: that a closed equality is a law, that a `#|` test moved into LAWS.bend becomes a guarantee, and that IO behavior can only be established by running it. Both projects closed the same gap the same way and ended up with the same pile of closed laws. And ez aims at the same thing bolt does, a tool written in Bend whose behavior is proved in Bend. So a finding in one repository usually holds in the other, and where ez met a problem first (refactor-equivalence laws, guarantees proved in a pinned dependency, the planner and interpreter split), this RFC takes ez's answer rather than rederiving it.

### Why closed laws are the wrong evidence

A closed law says `f(a) == b` for one `a`. That is too weak to protect behavior, because a refactor that breaks a rule on every input except its one fixture still passes the gate. It is also too strong to allow change, because the witness pins the whole output, so a wording change to one message breaks 46 proofs and nothing records which part of the output anyone depended on. ez reached the same conclusion from its own laws, and bolt's evidence is sharper in one respect.

The closed law `report_import` pins how `bolt check` places an error that bend locates inside an imported module. It encodes a `Location:` format with a `/` in it, and bend 2.0.25 no longer prints that format: it prints `Location: m.dbl`. The law still passes, because it runs the parser on the old text, while the real `bolt check` puts import errors on the wrong line (`bolt/lsp/report.bend:80-82`). The closed laws were made from tests built on assumptions about Bend, and this one shows what happens when an assumption goes stale: the gate stays green over a bug.

Closed laws also made `law` coverage cheap. `law` counts a def as covered when any token of any law in the run names it (`bolt/rules/digest.bend:67-95`), so a closed law that calls each def once satisfies it. The 63 helper-pin laws in `syntax/spec/LAWS.bend` have exactly that shape.

## Problem Statement

We need a specification that says, for every behavior bolt has, what exactly is guaranteed and whether that guarantee is proved for all inputs or assumed. When we change bolt's implementation, the answer must tell us mechanically which statements have to survive. Today the gate cannot answer either question, because nearly everything it checks is an example.

bolt has two jobs that make this harder than it is for ez. Its rules are heuristics over text, so "the rule reports exactly this pattern" has never been written down beyond a header comment, and several headers disagree with their code. And bolt is also the enforcement point for the spec model itself: ez's traceability check and ez's strictness about closed laws are both bolt rules, so bolt's position on closed laws has to be settled before ez's can be enforced.

The goals follow from that. We want one document, `SPEC.md` at the repository root, that lists every guaranteed behavior with a stable ID and exactly one of two levels. We want a model of the lint run's inputs so that its IO behavior can be stated as quantified laws. We want closed laws gone as a form of assurance, with the `closed` rule enforcing that in every project that runs bolt. And we want the same refactoring contract ez uses, so that an agent changing bolt knows which statements it must keep.

We are not proving bend, the host filesystem, git, or the pinned dependencies correct; those are trust assumptions and the spec names them. The host tests on AGENTS.md's stay list keep running and are outside the specification, so nothing in it depends on running a test. This RFC does not itself change bolt's behavior. Where the spec and the code disagree, a decision is recorded under "Decided behavior changes", and each lands as its own PR.

## Proposal

### Overview

The proposal has five parts, four of them carried over from ez. A **specification document** (`SPEC.md` at the repository root, which is the root of the linted tree) lists every requirement with an ID, a level, a status and, for proved requirements, the law. **Law tagging** links each quantified law to the requirement it proves. A **World model** gives the lint run a pure planner that laws can quantify over. A **refactoring contract** says which statements a change may touch. The fifth part is bolt's own: the **rules that enforce the model**, a strict `closed` and a new traceability rule, which ez then uses too.

|  |
|:---:|
| <pre>┌──────────┐     ┌───────────────┐          ┌────────────────┐     ┌────────────────┐<br>│ SPEC.md  │────▶│ Requirement   │──Proved─▶│ LAWS.bend      │────▶│ PROOF.bend     │<br>│ (IDs +   │     │ ID + level    │          │ (quantified,   │     │ (gate: "All    │<br>│  levels) │     │               │          │  # BOLT-X-N)   │     │  terms check.")│<br>└──────────┘     └───────┬───────┘          └────────────────┘     └────────────────┘<br>                         │                          ▲<br>                      Trusted                       │ checked by<br>                         ▼                          │<br>                 ┌───────────────┐          ┌────────────────┐<br>                 │ Trust boundary│          │ bolt: closed + │<br>                 │ (in SPEC.md)  │          │ traceability   │<br>                 └───────────────┘          └────────────────┘</pre> |
| Caption: Every requirement ends in a tagged quantified law the proof gate checks, or in a named assumption. bolt's own rules check that the tags and binders are there. |

### Two levels, and the positions carried over from ez

We take ez's positions as settled rather than re-argue them, since the two specifications have to agree for bolt to enforce ez's. Every requirement carries exactly one of two levels. A requirement is **Proved** when a quantified law (one with a `for` or `exs` binder) in a LAWS.bend is tagged with its ID in a comment directly above its `law` line and passes the proof gate, which means it holds for every input the law quantifies over. A requirement is **Trusted** when it is a named assumption in the trust boundary table, so a reader can see exactly where the gate stops looking. A Proved requirement whose law has not landed is **pending**, which is a status rather than a third level: the spec says plainly that a pending requirement is intended but not yet guaranteed.

The other positions follow from keeping only those two levels. Closed laws have no standing, because a law about one input is a test, and tests and fixtures are never evidence for a requirement for the same reason. Untagged quantified laws are allowed, but nothing protects them, so a change may edit or delete them freely. A guarantee proved in a pinned dependency is Trusted from bolt's side, because bolt's gate does not re-check the dependency's proofs.

The proof gate is the one mechanical check the spec depends on: every PROOF.bend's first output line is exactly `All terms check.`, which rules out the `All terms check, but N defs rely on unsafe or foreign code:` form bend exits 0 with. bolt does not run that gate itself. `flake.nix` calls ez's `mkProofs`, which runs `ez test --unit-only` today and `ez prove` once ez ships it, and that runner's faithfulness is BOLT-TRUST-6.

### Closed laws and the `closed` rule

Every closed law in bolt is deleted: 257 of them (123 in `syntax/spec/`, 117 in `bolt/spec/`, 17 in `core/`), together with the fixtures in `bolt/spec/cases.bend` that only those laws use. None is kept as a `# toward <ID>` trail. The inventory's Points toward column keeps the map of what each closed law was reaching for, so the quantified law that replaces it can be written against the right requirement without the wrong assumption sitting next to it.

The rule changes to match. `closed` (L002) itself becomes strict and reports any law in a LAWS.bend with no binder, equality or not. The `# toward` exemption goes away, since there is nothing left for it to exempt. `quantify` (L004) is retired, and its code is reserved and never reused. bolt's own bolt.bend sets the four groups it names to error today and names no rule. We propose it also names `closed` at error, so that a later change to the `laws` group line cannot quietly relax it.

<!-- REVIEW-1: bolt#10 made closed equalities first-class laws and moved 240 `#|` tests into closed laws; bolt#42 added `quantify` (L004) as an opt-in strict mode. That conflicts with ez's position that closed laws have no standing. The maintainer has given the direction: bolt is strict about closed laws too, and every closed law is deleted, not kept as a `# toward` trail. What remains is the mechanism. We propose that `closed` (L002) itself becomes strict and reports any law in a LAWS.bend with no binder; the `# toward` exemption goes away; `quantify` is retired and L004 is reserved, never reused; bolt's own bolt.bend sets `closed` to error. This is a behavior change for every project that runs bolt, and no compatibility path is kept. ez has agreed: it keeps its `# toward` trail laws only while its rollout lasts, stays pinned at bolt v0.9.0 until the last trail is deleted, and then bumps bolt, removes `def quantify()` from its bolt.bend and turns on strict `closed`. Other projects learn of the change from the release notes, and once BOLT-CFG-7 lands a leftover `def quantify()` is itself a finding. -->

We chose to change `closed` rather than flip `quantify` on by default because two rules for one property is the configuration surface that let bolt be clean while holding 257 closed laws. With one strict rule, a project that wants closed laws has to switch `closed` off by name, which is a visible decision in its bolt.bend. The cost is that every project running bolt sees new findings on upgrade. We keep no compatibility path for that, ez included, since ez has agreed to bump bolt only after its last `# toward` trail is gone; the release notes carry the change (see Risks).

The LSP fixtures under `bolt/lsp/fixtures/` stay, because host tests read them, and both of their laws are already quantified. AGENTS.md's hard rule ("If Bend can state it as a law (including an IO equality ...), it goes in LAWS.bend") and the `closed` entry in `bolt/README.md` both endorse closed equalities, so both change in the first phase. This RFC does not write their new text.

### Requirements

The tables below carry the first version of `SPEC.md`'s rows. SPEC.md keeps their ID, Requirement, Level and Status columns, drops Verdict and Evidence, and adds a Law column naming the law that proves each proved row. Each requirement is stated as behavior and was checked against the code. The Status column is `proved` only for BOLT-LIB-1, the one requirement with a tagged quantified law today; every other Proved requirement is `pending`, and Trusted rows have no status. The Verdict column says whether the code does what the requirement says today, and it is applied the same way in every group. **holds** means we found no counterexample, confirmed by running bolt or by reading the code in full. **partly** means it holds except on a confirmed class of inputs, and the Evidence cell names that class. **fails** means the stated behavior is violated on an ordinary input a user meets, such as running from a subdirectory, bend missing from the PATH, or an import error. One row uses a fourth marker, **unchecked**, meaning not yet checked against the code. Evidence is kept to a file and line and a phrase; the inventory has the long form. The Verdict and Evidence columns belong to this RFC only and never appear in SPEC.md.

#### Rules (BOLT-RULE)

Every per-file rule is already a pure function of its `Src` by type. There is no IO in `check`'s type and no fuel that cuts findings short, so rule requirements need no World model at all. The work is in stating each pattern precisely, and the header comment is where that statement starts.

<!-- REVIEW-2: Each BOLT-RULE-<code> requirement is the rule's header comment rewritten precisely. Where the verdict is partly, we propose fixing the code where the header states the intent a user relies on (`pick` reporting nested picks twice, `wrap` flagging trailing comments, `strings` underflow), and narrowing the header where the code's behavior is a deliberate heuristic (`fuel` matching by parameter name, `eager` only counting looping defs). The per-rule list is in the inventory. -->

| ID | Requirement | Level | Status | Verdict | Evidence |
| :---- | :---- | :---- | :---- | :---- | :---- |
| BOLT-RULE-C001 | `shadow` reports exactly a let, do-bind, lambda or pattern binder named like a top-level def above it in the file, and nothing else. | Proved | pending | partly | any top-level item counts, laws included (shadow.bend:27) |
| BOLT-RULE-C002 | `hole` reports exactly a `?TODO` outside a LAWS.bend, and nothing else. | Proved | pending | partly | `? TODO` missed (hole.bend:11-14); exemption is a suffix test (hole.bend:23) |
| BOLT-RULE-C003 | `pick` reports exactly a self-call in one or both branches of `Bool.pick`, and does not report again a nested pick in a branch it reported. | Proved | pending | partly | a parameter named like the def fires, recursion by mention (pick.bend:20); nested both-branch pick reported twice (pick.bend:33); not exempt though calls.bend:1-5 says so |
| BOLT-RULE-C004 | `put` reports exactly a `Map.put(` call, except in a file that defines `Map.put`. | Proved | pending | holds | put.bend |
| BOLT-RULE-C005 | `arms` reports exactly, in a single-scrutinee match, a Nat arm already covered by an earlier `kn+p` or `Succ{p}` arm. | Proved | pending | partly | `Succ{_}` not treated as `1n+p` (arms.bend:51) |
| BOLT-RULE-C006 | `escape` reports exactly a `\0` followed by a digit in a string or char literal. | Proved | pending | holds | escape.bend |
| BOLT-RULE-C007 | `twice` reports exactly, in a recursive def, a list pattern opening with the same literal twice. | Proved | pending | partly | recursion by mention (twice.bend:72); second match column never read |
| BOLT-RULE-C008 | `strings` reports exactly a match whose string-literal arms total over 64 characters. | Proved | pending | partly | unterminated arm underflows to 4294967295 (strings.bend:24-25); first column only |
| BOLT-RULE-C009 | `chars` reports exactly a match with more than eight char-literal arms. | Proved | pending | partly | first column only; `Con{'x', t}` arms not counted (chars.bend:26); header cites a frame.bend example that no longer exists |
| BOLT-RULE-C010 | `foreign` reports exactly a foreign def with a `.c` body and no `.js` or the reverse, where a `# lanes: native` file needs no `.js`. | Proved | pending | partly | the native marker matches anywhere in the file (foreign.bend:83) |
| BOLT-RULE-U001 | `unused` reports exactly an unused let, do-bind, lambda binder or parameter, with the header's exemptions. | Proved | pending | partly | a wrapped foreign def's parameters are reported (unused.bend:16-19, 31) |
| BOLT-RULE-U002 | `strict` reports exactly a self-call inside `Bool.and` or `Bool.or`, or on either side of `&&` or `\|\|`. | Proved | pending | partly | fires inside a lazy thunk; misses `Base.Bool.or` |
| BOLT-RULE-U003 | `eager` reports exactly a looping def of the file called in a `Bool.pick` branch. | Proved | pending | partly | a `=>` clears the branch for the rest of the chain (eager.bend:76-81) |
| BOLT-RULE-U004 | `concat` reports exactly a self-call argument that appends onto a parameter. | Proved | pending | partly | slot not checked; a parenthesized or let-bound append missed (concat.bend:30-37) |
| BOLT-RULE-U005 | `nat` reports exactly a Nat literal of 1000 or more. | Proved | pending | holds | nat.bend |
| BOLT-RULE-U006 | `fuel` reports exactly a Nat literal passed where a def of the file takes its fuel. | Proved | pending | partly | fuel recognized by parameter name only (fuel.bend:22-24); only a lone literal token counts |
| BOLT-RULE-U007 | `index` reports exactly a `List.get` or `String.get` at a non-literal index in a recursive def. | Proved | pending | holds | holds as worded; a get only in the base arm is reported, which README's wording does not allow |
| BOLT-RULE-U008 | `table` reports exactly a get or set at a computed index on a fixed table inside a recursive def. | Proved | pending | partly | let names collected without scoping (table.bend:150-160) |
| BOLT-RULE-U009 | `hoist` reports exactly a table of more than eight cells rebuilt per step from carried inputs. | Proved | pending | partly | a user-def call with carried arguments counts as wide regardless of size (hoist.bend:245-252) |
| BOLT-RULE-U010 | `ring` reports exactly a fixed window dropped and appended per step. | Proved | pending | partly | only the first scrutinee counts as matched (ring.bend:232-238); slot not checked |
| BOLT-RULE-U011 | `rewalk` reports exactly the same walk twice on the same argument, one result read for a single value. | Proved | pending | partly | arguments compared as text, so a rebinding between calls still matches (rewalk.bend:467) |
| BOLT-RULE-U012 | `unit` reports exactly a multiply or divide by one on a recursive step. | Proved | pending | partly | an operator followed by `(` is skipped (unit.bend:152) |
| BOLT-RULE-S001 | `doc` reports exactly a top-level def, type or law with no comment block right above it, with the header's exemptions. | Proved | pending | partly | test exemption needs a leading slash (doc.bend:50); a bare `#` line counts as no comment |
| BOLT-RULE-S002 | `space` reports exactly trailing whitespace, a tab, or a line over 120 columns with string literals counted as two. | Proved | pending | partly | the `#\|` exemption covers width only (space.bend:38) |
| BOLT-RULE-S003 | `wrap` reports exactly a def header whose shape breaks the header's rules. | Proved | pending | partly | a one-line header with a trailing comment is flagged (outline.bend:338); `)` placement never checked (wrap.bend:691) |
| BOLT-RULE-S004 | `param` reports exactly a parameter name shorter than two characters, with the header's exemptions. | Proved | pending | holds | param.bend |
| BOLT-RULE-P001 | `tail` reports exactly a non-tail self-call in a def whose first live parameter is a List or String. | Proved | pending | partly | a type test, never a shrink test (calls.bend:184) |
| BOLT-RULE-EXEMPT | For every text, a per-file rule's check on a path its header exempts returns no findings. | Proved | pending | holds | holds for the paths as coded; predicates per REVIEW-4 |
| BOLT-RULE-INERT | For every rule whose pattern is code (all but `escape`, `strings`, `chars`, `space`, `twice` and `nat`), changing the contents of a comment or string literal does not change the findings. | Proved | pending | unchecked | not established: seen on the fixtures for token rules only, never checked for tree rules |

Five rules hold and twenty-two hold partly, which is the honest summary of bolt as a linter today. Most partly verdicts come from three shared causes rather than twenty-two separate bugs: recursion decided by any leaf equal to the def's name, so a qualified call is invisible and a parameter named like the def fires; multi-scrutinee matches read at their first column only; and a pattern missed once it is bound by a let first. Fixing those in `bolt/rules/calls.bend` and the shared helpers moves several rows at once, which is why REVIEW-2 decides per rule but the fixes will land per helper.

The two cross-cutting rows cover the 27 rules above and not `closed`, whose scope BOLT-LAW-2 already states. They exist because they are the properties a user notices first. BOLT-RULE-EXEMPT makes a header's exemption list a guarantee rather than a hope, and it is cheap once REVIEW-4 gives every rule the same path predicates. BOLT-RULE-INERT is the property most token-based false positives would break: a rule that fires on `Map.put(` inside a comment is wrong in a way no fixture list can rule out, and a law quantified over the contents of comments and strings can. The six excluded rules look at literals or raw text on purpose, so for them the property would be false by design.

#### Laws rules (BOLT-LAW)

| ID | Requirement | Level | Status | Verdict | Evidence |
| :---- | :---- | :---- | :---- | :---- | :---- |
| BOLT-LAW-1 | In every file under a law directory, except helpers, law files and tests, every def and type is referenced by a quantified law in a LAWS.bend: a use in the law's statement that the binder (BOLT-SYN-5) resolves to that def, through an import alias or in the same file. | Proved | pending | fails | today any token of any law in the run counts, closed laws, the law's own name and a nonexistent `M.zzz` for types included (digest.bend:67-95); depends on the run set; mixing absolute and relative paths turns it off |
| BOLT-LAW-2 | `closed` reports any law in a LAWS.bend with no binder. | Proved | pending | fails | today's rule reports only a binderless law that is not an equality, and loosely at that: `==` anywhere counts, an unused binder counts (closed.bend:17, 27) |
| BOLT-LAW-3 | An `@unsafe def` reachable by relative imports from a law file in the run is a finding. | Proved | pending | partly | a chain through a file that is not in the run is missed |
| BOLT-LAW-5 | The traceability rule reports exactly the findings listed under "Tagging and traceability" for the SPEC.md format stated there. | Proved | pending | fails | no code exists (Emerging-Patterns/bolt#44) |

BOLT-LAW-2 is stated in its post-REVIEW-1 form, so it fails today: the current rule accepts every closed equality and reports a binderless law only when it is not an equality. Even that weaker check is loose: `{Bool.and(1 == 1, True{}) : Bool}` passes because `==` appears somewhere, and a `for` binder the statement never uses counts as a binder. Whether "has a binder" should mean "has a binder the statement uses" is a refinement we leave to the rule's law, since the strict form already closes the gap that matters.

BOLT-LAW-4 (`quantify`) is retired under REVIEW-1 and has no row. Its verdict is recorded here because the rule ships in 0.9.0: partly, since its `# toward` marker accepts `#toward` and rejects `# Toward` (quantify.bend:32-46), so README's `grep -rn '^# toward '` misses some exemptions. The ID is reserved, like the code L004.

BOLT-LAW-1 is stated in the form ez needs before it turns `law` back to error, and it fails today because coverage is a token match. Any name token in any law in the run counts, so a closed law that calls a def once covers it, a law's own name covers a def of the same name, a law in a PROOF.bend or an ungraded file counts, and a type is covered by any mention of its module, even `M.zzz`, which does not exist. The new wording counts only a reference the binder resolves, from a quantified law in a LAWS.bend, so neither a closed law nor a stray token can satisfy the rule. Its reach is the other problem.

<!-- REVIEW-3: The `law` rule grades 19 of 94 source files and none of the linter. We propose moving the law files up so their directories cover the code they describe (`bolt/LAWS.bend`, `syntax/LAWS.bend`), with `law` at warn in bolt's own bolt.bend until the quantified laws exist, as ez does. We also propose that coverage changes meaning (BOLT-LAW-1): a def or type is covered only when a quantified law in a LAWS.bend references it, where a reference is a use in the law's statement that the binder (BOLT-SYN-5) resolves to that def, through an import alias or in the same file. A law's own name, a token in a closed law, a law outside a LAWS.bend, and a nonexistent `M.zzz` stop counting. This is the fix that matters most to ez, which needs it before it turns `law` back to error. Behavior change. -->

The laws for the linter sit in `bolt/spec/` and `syntax/spec/`, beside the code rather than above it, so `law` never grades the 76 files of `bolt/` and `syntax/` outside them. Moving them to `bolt/LAWS.bend` and `syntax/LAWS.bend` puts the whole linter under law. It also puts it at hundreds of `law` findings, which is why `law` runs at warn in bolt's own bolt.bend until the quantified laws exist, exactly as ez does.

#### Grading and config (BOLT-CFG)

| ID | Requirement | Level | Status | Verdict | Evidence |
| :---- | :---- | :---- | :---- | :---- | :---- |
| BOLT-CFG-1 | A rule's level is its own setting, else its group's setting, else its group's default. | Proved | pending | holds | config.bend:174-183 |
| BOLT-CFG-2 | Grading drops a finding at `off` and attaches the level to every other. | Proved | pending | holds | rules.bend:98-106 |
| BOLT-CFG-3 | A level word that is not `off` or `warn` grades as error. | Proved | pending | holds | config.bend:72-73; `warning`, `Error`, `OFF` and `""` all grade as error |
| BOLT-CFG-4 | A finding is graded by the nearest readable bolt.bend in its file's directory, then each parent, and only that one applies. | Proved | proved | fixed | `fix(config)`: relative paths used to stop at the current directory (config.bend:127-140; seen from a subdirectory and with `../../p3/a.bend`); each path is now resolved against the working directory first |
| BOLT-CFG-5 | Group defaults are correctness at error, pedantic off, and the rest at warn. | Proved | pending | holds | config.bend:165-167 |
| BOLT-CFG-6 | An opt-in rule is off unless its own setting names it. | Proved | pending | holds | config.bend:171-178 |
| BOLT-CFG-7 | A setting in a bolt.bend whose name is no rule or group is a finding. | Proved | pending | fails | ignored today |

Every row here except CFG-4 is a property of pure functions in `bolt/config.bend` and `bolt/rules.bend`, so they are among the cheapest laws in the spec. CFG-3 is deliberately fail-closed: a typo such as `wran` makes a rule stricter, never silently off. With `quantify` retired, CFG-6 has no rule to apply to, and we keep it because BOLT-LAW-5 is the next opt-in rule and inherits it.

<!-- REVIEW-5: Config lookup for a relative path stops at the current directory and handles `..` lexically. We propose resolving each path against the working directory before computing candidates, so BOLT-CFG-4 holds as README states it. Also proposed: an unknown setting name in a bolt.bend becomes a finding (BOLT-CFG-7), and `warning` is accepted as a synonym for `warn`. We also propose that the walk's silent truncation past 100000 directories becomes a finding (BOLT-SCOPE-1). Behavior change. -->

CFG-4 failed because `Config.candidates` worked on the path as typed (fixed by `fix(config)`, which resolves each path against the working directory; the text below is the finding as it stood). For `a/b/c.bend` it tries `a/b/bolt.bend`, `a/bolt.bend` and `bolt.bend` and stops, so running bolt from a project's subdirectory never reads the project's root bolt.bend, and for `../x.bend` the second candidate is the current directory's bolt.bend, which is not a parent of the file. Resolving against the working directory first fixes both, and it needs the working directory as an input, which is one of the reasons the World model below carries `cwd`. Accepting `warning` is a small kindness with a reason behind it: bolt prints that word for a warn finding, so users copy it into their bolt.bend.

#### Scope (BOLT-SCOPE)

| ID | Requirement | Level | Status | Verdict | Evidence |
| :---- | :---- | :---- | :---- | :---- | :---- |
| BOLT-SCOPE-1 | With no files named, bolt lints every `.bend` file under `.` found within the first 100000 directories the walk reads, not descending into hidden directories or `node_modules`, sorted by code point; past that bound the walk stops silently. | Proved | pending | holds | glob.bend:10-11, 58-61; the bound is the walk's fuel (glob.bend:60) |
| BOLT-SCOPE-2 | A per-file rule sees one file's `Src`; a project rule sees the digests of every file in the run, and nothing else. | Proved | pending | holds | lint.bend:104-106, rules.bend:87-89 |
| BOLT-SCOPE-3 | A file is under law when its normalized path starts with the directory of some LAWS.bend in the run. | Proved | pending | holds | as coded; in this repo 19 of 94 files (REVIEW-3) |
| BOLT-SCOPE-4 | Exemptions are decided by the path alone, never by content. | Proved | pending | holds | predicates are loose (REVIEW-4) |
| BOLT-SCOPE-5 | A bolt.bend is read, never linted, even when named. | Proved | pending | holds | lint.bend:91-101 |

The scope rows hold, but two of them hold over loose definitions. SCOPE-1's walk has a fuel of 100000 directories and drops the rest without a finding, so the requirement states the bound and the silence rather than pretend the walk is unbounded. We propose that the truncation become a finding, as part of REVIEW-5's behavior changes, so that a tree too large to walk is reported rather than half linted. SCOPE-4 says exemptions depend on the path, and the paths are tested inconsistently, which REVIEW-4 addresses.

<!-- REVIEW-5: see Draft Status; this is the SCOPE-1 part of it, making the walk's truncation past 100000 directories a finding. -->

<!-- REVIEW-4: Exemptions are decided by suffix and substring tests. We propose one shared predicate module: a law file is a path whose basename is exactly `LAWS.bend` or `PROOF.bend`, and a test is a path with a segment exactly `tests`. Behavior change: `contests/`, `OUTLAWS.bend` and `myPROOF.bend` stop being exempt. -->

Today every LAWS.bend and PROOF.bend test is `String.ends_with`, the `law` rule's test exemption is `String.contains(pp, "tests/")`, and `doc`'s is `contains(path, "/tests/")` with the leading slash, so the same file can be exempt from one rule and not the other. One predicate module makes BOLT-RULE-EXEMPT and SCOPE-4 statable with a single definition of "law file" and "test", which the laws can then share.

#### Output and exit (BOLT-OUT)

| ID | Requirement | Level | Status | Verdict | Evidence |
| :---- | :---- | :---- | :---- | :---- | :---- |
| BOLT-OUT-1 | The code table maps each rule slug to exactly one code and each code to exactly one slug. | Proved | pending | holds | codes.bend, README and rules.bend agree on 31 entries |
| BOLT-OUT-6 | A released code is never renumbered or reused. | Trusted | | holds | see the trust boundary |
| BOLT-OUT-2 | A finding prints as `path:line:col: level: CODE: message`, 1-based. | Proved | pending | holds | finding.bend:26-29 |
| BOLT-OUT-3 | Output order is read failures, then per-file findings in file-list order and `Rules.on` order, then `law` and `unsafe`. | Proved | pending | holds | lint.bend:104-106; a file named twice is linted twice |
| BOLT-OUT-4 | The last line is `clean` or `N errors, M warnings`, and the exit status is 1 exactly when some graded finding is an error. | Proved | pending | holds | lint.bend:108-150 |
| BOLT-OUT-5 | A path that cannot be read is a `read` finding graded with correctness. | Proved | proved | fixed | `fix(lint)`: a directory given as an argument used to read as empty and report `clean`; it is now a `read` finding; `def read()` can switch it off |

OUT-1 and OUT-6 were one requirement, split because a law sees one version of the code. That the table is one-to-one (OUT-1) is a quantified law over slugs. That 0.10.0's table extends 0.9.0's without renumbering (OUT-6) is a property across versions, so review enforces it, with the SPEC row listing the table. Each half has its own ID because the SPEC.md format requires IDs to be unique.

<!-- REVIEW-10: Code stability across releases cannot be a law, since a law sees one version. We propose splitting it: BOLT-OUT-1, the one-to-one map between slugs and codes, is Proved, and BOLT-OUT-6, "a released code is never renumbered or reused", is Trusted, enforced by review of the SPEC row that lists the table. -->

OUT-3 states today's order rather than a sorted one, because editors place diagnostics by position and the gate reads only the last line and the exit status, so no consumer depends on sorting, and a sort would cost a pass over every finding on every run. What users do depend on is that the same inputs give the same output, and OUT-3 guarantees that either way. OUT-5 was partly because a directory named on the command line read as empty text rather than failing to read (fixed by `fix(lint)`: the World answers such a path `Directory`, which the planner reads as no text, so it is a `read` finding like a missing file).

<!-- REVIEW-11: Output order is fixed but not sorted by line. We propose BOLT-OUT-3 states today's order rather than change it, because editors and the gate do not depend on sorting and a sort costs a pass over every finding. -->

#### Command line (BOLT-CLI)

| ID | Requirement | Level | Status | Verdict | Evidence |
| :---- | :---- | :---- | :---- | :---- | :---- |
| BOLT-CLI-1 | bolt accepts `bolt [lint] [files]`, `bolt check files`, `bolt lsp`, `bolt help [cmd]` and `--`; an argv parse error exits 1, and `help` and `--version` exit 0. | Proved | pending | holds | args.bend, main.bend:49-60; `bolt version` is read as a file |
| BOLT-CLI-2 | `--version` prints the release and, when the build has one, the short commit in parentheses. | Proved | pending | holds | args.bend `version.at` |

Both rows are pure functions of argv and the build's constants, so they need no World. argv parsing itself is shake's, and its correctness is BOLT-TRUST-8; CLI-1 is stated over what bolt does with shake's answer.

#### Checker (BOLT-CHK)

| ID | Requirement | Level | Status | Verdict | Evidence |
| :---- | :---- | :---- | :---- | :---- | :---- |
| BOLT-CHK-1 | `bolt check` prints one `path:line:1: error:` line per error bend reports, on the line bend marks, then a count; it exits 1 when there is any, and treats a failure to run bend as an error. | Proved | pending | fails | bend missing gives `clean` and exit 0 (checker/exec.c, confirmed); import errors land on the wrong line (report.bend:80-82); the LAWS.bend settle (below) needs a `/LAWS.bend` suffix (checker/bend.bend:38) |

CHK-1 fails in three independent ways, and the first is the one that matters for a gate: when `bend` is not on the PATH, `exec.c` exits 127 with no output, an empty report parses as no errors, and `bolt check` says `clean`. The fix is to make spawn failure a distinct value rather than empty output, which is also what makes CHK-1 statable (see "`bolt check` and bend as an oracle" below).

The third failure is in the **LAWS.bend settle**. A LAWS.bend states its laws as open claims, so bend alone always reports TODOs for it. When bend reports only open TODOs for a LAWS.bend, `bolt check` runs bend on the PROOF.bend beside it and clears the TODOs if that file checks clean (checker/bend.bend:25-38). The settle only fires for a path ending in `/LAWS.bend`, so `bolt check LAWS.bend` and `bolt check ./LAWS.bend` disagree, which REVIEW-4's basename predicate fixes.

<!-- REVIEW-6: `bolt check` reports `clean` and exits 0 when bend cannot be run. We propose that a spawn failure becomes an error diagnostic and exit 1, and that the report parser's import-location rule is corrected against bend 2.0.25's `Location:` format. Behavior change. -->

#### Parser (BOLT-SYN)

| ID | Requirement | Level | Status | Verdict | Evidence |
| :---- | :---- | :---- | :---- | :---- | :---- |
| BOLT-SYN-1 | `Lex.text(Lex.tokens(s)) == s` for every `s`. | Proved | pending | holds | lex.bend:289-293 |
| BOLT-SYN-2 | A token's line and column are those of its first character, 0-based, in code points. | Proved | pending | holds | lex.bend |
| BOLT-SYN-3 | The tree drops no token, and its leaves are the significant tokens in order. | Proved | pending | partly | holds as text; a run of `>` is re-emitted as single-character tokens (tree.bend:271-276) |
| BOLT-SYN-4 | The outline lists every column-0 import, def, type, law and `@unsafe def`. | Proved | pending | partly | reads prefixes line by line; finds phantom items inside multi-line strings |
| BOLT-SYN-5 | The binder resolves a use to the innermost binder, then a file item, then an alias qualifier, else free. | Proved | pending | holds | no counterexample found; checked on the fixtures and by reading bind.bend:146-199 |
| BOLT-SYN-6 | Every function in `syntax/` terminates on every input without fuel. | Trusted | | holds | structural recursion throughout |

The parser rows are the foundation the rule laws stand on, so they come early in the rollout. SYN-1 and SYN-2 are what let a token rule be stated over `Lex.tokens` instead of raw text. SYN-3, SYN-4 and SYN-5 are the lemmas the tree rules need before their own laws can say anything for all inputs. SYN-3 is partly because the tree re-emits `>>` as two `>` tokens with synthesized positions; the leaves equal the tokens as text but not as a token list, and the old closed law `tree_leaves` compared text only, which is why it never noticed.

SYN-6 is Trusted rather than Proved because termination is exactly what the Bend checker's structural-recursion check establishes. It rests on BOLT-TRUST-1 and needs no law of its own, and writing one would restate the checker's work.

Agreement with bend's own parser is not a row in this group. It is BOLT-TRUST-2, with four confirmed divergences listed there: multi-line string literals, continuation lines indented under an expression becoming child statements, a `>` inside parentheses nested in `<..>` closing the angle group, and ASCII-only identifiers.

#### Language server (BOLT-LSP)

| ID | Requirement | Level | Status | Verdict | Evidence |
| :---- | :---- | :---- | :---- | :---- | :---- |
| BOLT-LSP-1 | `Content-Length` counts UTF-8 bytes; a partial header or body waits; `cut` of `wrap(s)` gives `s`. | Proved | pending | partly | header name matched case-sensitively (frame.bend:129-132) |
| BOLT-LSP-2 | Diagnostics for an open document equal the CLI's per-file findings for that file and text under the same bolt.bend. | Proved | pending | fails | the grading path differs |
| BOLT-LSP-3 | Each request gets exactly one response with the same id, in order; an unknown request gets -32601; an unknown notification gets nothing. | Proved | pending | holds | server.bend, confirmed |
| BOLT-LSP-4 | Open and save publish checker plus lint; change publishes lint plus the last checker result; close publishes an empty list; an open bolt.bend gets no lint. | Proved | pending | holds | server.bend |
| BOLT-LSP-5 | The checker never runs `main`. | Proved | pending | holds | `bend --check-only`, exec.c; depends on BOLT-TRUST-5 |
| BOLT-LSP-6 | Hover, definition, references and completion answer from the binder (BOLT-SYN-5) over the open text and its relative imports. | Proved | pending | holds | no counterexample found; checked on the fixtures and by reading bind.bend:146-199 |
| BOLT-LSP-7 | Positions are in the encoding the client negotiated. | Proved | pending | fails | code points; no `positionEncoding` advertised |

LSP-2 is the requirement editors care about, and it fails today for one reason: the LSP grades by the absolute path in the document URI while the CLI grades by the path as typed, so from a subdirectory the two pick different bolt.bend files. The LSP also runs only per-file rules, never `law` or `unsafe` (`bolt/lsp/server.bend:93-98`), but that is not a failure, because project rules are out of the LSP's scope by design and LSP-2 compares per-file findings only.

<!-- REVIEW-7: The LSP and the CLI give different findings for the same text. We propose BOLT-LSP-2 states that the LSP's diagnostics for an open document equal the CLI's per-file findings for that file under the same bolt.bend, with project rules out of the LSP's scope by design. The path difference disappears once REVIEW-5 lands. We also propose advertising `positionEncoding: utf-32` when the client offers it, and converting to UTF-16 otherwise. -->

We state LSP-2 over per-file findings because README already says `law` runs in bolt alone, and project rules over one open document would be wrong more often than right. Once REVIEW-5 resolves every path against the working directory, the CLI's path and the URI's path name the same file, and the grading difference goes away without an LSP-specific fix.

LSP-5 is Proved over bolt's side (the arguments it passes) and leans on BOLT-TRUST-5 for bend's side (that `--check-only` means what it says). Several behaviors are accidental and are not made requirements: malformed JSON is ignored rather than answered with -32700, requests after `shutdown` are still answered, the exit code is 0 on EOF without `shutdown`, and the checker has no timeout, so a hung bend blocks the loop. Any of them can be fixed without touching the spec.

#### Library (BOLT-LIB)

| ID | Requirement | Level | Status | Verdict | Evidence |
| :---- | :---- | :---- | :---- | :---- | :---- |
| BOLT-LIB-1 | `Lazy.stop(c, a, _ => b) == Bool.pick(c, a, b)`, `Lazy.or_else(a, _ => b) == Bool.or(a, b)` and `Lazy.and_then(a, _ => b) == Bool.and(a, b)` for all inputs. | Proved | proved | holds | lazy/LAWS.bend `stop_is_pick`, `or_else_is_or`, `and_then_is_and` |

This is bolt's one Proved requirement today, and it is real: 79 call sites in `bolt/` and `syntax/` rely on the lazy forms meaning the same as the strict ones. The three laws get the tag in the first phase. Each already has a doc comment directly above `law`, and the tag goes between them, so `doc` still sees a contiguous comment block and the traceability rule finds the tag in the comment block directly above `law`:

```
# LAW: a thunk that ignores its argument makes stop Bool.pick
# BOLT-LIB-1
law stop_is_pick:
  for c: Bool
  for a: U32
  for b: U32
  {Lazy.stop(U32, c, a, _u => b) == Bool.pick(U32, c, a, b) : U32}
```

`core/`'s nine quantified laws are not in any group. They are true and they pass the gate, but they describe a dependency-injection library that only the host tests use (as the reporter in `core/check`), so a bolt requirement about them would be a guarantee about something bolt does not ship.

<!-- REVIEW-12: `core/` is a library the bolt binary does not import. We propose its quantified laws stay as untagged laws outside bolt's SPEC, its 17 closed laws are deleted with the rest, and whether `core/` moves to its own repository is left out of this RFC. -->

### The World model, and how far each part is from a pure function

Laws quantify over values, and some of bolt's behavior is IO. bolt is in a better position than ez here, because most of it is already pure and the IO that remains sits at a few known points. We take each part in turn, from nearest to farthest.

#### Per-file rules

Per-file rules are pure already, with `check : Src -> List<Finding>` and no fuel, so the distance is only the statement. What decides the order of work is what each rule reads, since a rule's law can only speak for all inputs once the structure it reads has its own laws.

| Rule family | Reads | Needs first |
| :---- | :---- | :---- |
| Token rules: `put`, `nat`, `escape`, `hole`, `space` | The token list or the text | BOLT-SYN-1, BOLT-SYN-2 |
| Match and literal rules: `arms`, `strings`, `chars`, `twice` | The tree, match arms and literal tokens | BOLT-SYN-3 |
| Recursion rules: `pick`, `strict`, `eager`, `concat`, `index`, `table`, `hoist`, `ring`, `rewalk`, `unit`, `tail` | The tree and each def's self-calls | BOLT-SYN-3, BOLT-SYN-4 |
| Binding rules: `shadow`, `unused`, `param` | The binder | BOLT-SYN-5 |
| Layout rules: `doc`, `wrap`, `foreign` | The outline and the lines above each item | BOLT-SYN-4 |

Token rules come first because their patterns are nearly definitional once the lexer is proved: "`nat` reports exactly a Nat literal of 1000 or more" is a law over every token list. Tree rules come after their lemmas, and some may turn out not to be worth proving.

<!-- REVIEW-13: Soundness laws for tree rules may cost more than they are worth. The escape hatch is explicit: a requirement that proves too expensive moves to Trusted with a written reason. We order the work so token rules come first. -->

#### Project rules

`law` and `unsafe` are pure functions of `List<Digest>`, so their laws quantify over digest lists. What they cannot see is which files were in the run, and that is where BOLT-LAW-1 and BOLT-LAW-3 depend on the run set: linting `p/m.bend` alone reports no gap that linting `p/` does. That is the planner's job, and SCOPE-1 and SCOPE-2 together state it once the planner exists.

#### The lint run

`bolt/lint.bend`'s `run` has three IO points. The walk is already behind a service: `Glob.find` takes a `Walk` and a `FakeWalk` exists, but `run` hard-codes `WalkDisk`. The reads go through the `Files` service, hard-coded to `Disk`. And grading reads the bolt.bend candidates of every finding's directory, once per finding, through the same service. None of the decisions happen inside IO, which is the difference from ez: the logic is already in pure functions, and what is missing is a value to pass them.

We model the run's inputs as a World and split `run` into a planner and an interpreter. None of these types exists yet, and the names are proposals.

```
# New types. The planner decides everything; the interpreter fills the
# World by listing and reading, then prints `lines` and exits with `exit`.
type Entry:
  File{name: String}
  Dir{name: String}                              # listed with a trailing `/`

type World:
  cwd: String                                    # absolute working directory
  dirs: Map(Path, Maybe(List(Entry)))            # the listing effect's answers
  files: Map(Path, Maybe(String))                # the read effect's answers

type Plan:
  Plan{lines: List(String), exit: U32}

# normalizes each path against w.cwd, walks w.dirs as a pure fold with its
# fuel and sort, looks bolt.bend up in w.files, grades, and renders
def lint_plan(w: World, paths: List(String)) -> Plan
```

With that split, the requirements that need the file system become statable for every world. SCOPE-1 is a law about the walk fold over `dirs`. CFG-4 is a law about which key of `files` grades a finding, for every `cwd` and every path. OUT-3, OUT-4 and OUT-5 are laws about `lines` and `exit`. BOLT-LAW-1 and BOLT-LAW-3 become laws over the set of paths the planner chose, rather than over whatever a caller passed in.

|  |
|:---:|
| <pre>real system ──list/read──▶ World ──▶ lint_plan (pure, laws apply) ──▶ Plan ──▶ interpreter ──print/exit──▶ real system</pre> |
| Caption: All decisions live in the planner, where laws apply. The interpreter lists, reads, prints and exits, and is trusted. |

The World is a lazy value in spirit: the interpreter lists only the directories the walk reaches and reads only the files and bolt.bend candidates the planner asks for, so building it costs no more than today's run. Grading also improves in passing, since the candidates are looked up once per directory rather than once per finding.

<!-- REVIEW-14: Splitting each command into a planner and an interpreter makes three interpreters' faithfulness assumptions that the trust table does not yet name. We propose three rows, each added in the same PR that introduces its interpreter and justified there as the refactoring contract requires: BOLT-TRUST-9, the lint interpreter lists, reads and prints what the plan says and exits with its status; BOLT-TRUST-10, the `bolt check` interpreter records bend's output or its spawn failure in the oracle unchanged; BOLT-TRUST-11, the LSP loop feeds each received message to `step`, performs its asks, and sends its replies in order. -->

#### `bolt check` and bend as an oracle

`bolt check` cannot be made pure, because its answer is bend's output. We model bend as an oracle in the World, one answer per file, with spawn failure explicit:

```
type SpawnFailure:
  NotFound{}                                     # exec failed, e.g. exit 127
  Died{status: U32}

# added to World for `bolt check` and the LSP checker
check: Map(Path, Result(String, SpawnFailure))
```

CHK-1's bug is exactly the conflation this type rules out: today a missing bend and a clean check are both empty text. With the oracle, `Report.parse` and the LAWS.bend settle rule are proved over the oracle's text for every text, and CHK-1's "treats a failure to run bend as an error" is a law over the `Err` arm. Whether bend's text means what `Report.parse` thinks it means stays Trusted (BOLT-TRUST-5), and the `report_import` drift is the reason that row names the format.

#### The language server

`Server.serve` already injects its transport, checker and files as services, and the `Script` transport turns a whole session into one closed IO value. That is how the six session laws in `bolt/spec/` worked, and it is also why they were closed: each one fixed a single inbox. We propose splitting the loop body into a pure step,

```
def step(docs: Docs, msg: Msg) -> Step
# Step{replies: List(String), asks: List(Ask), docs: Docs}
# an Ask is a file read or a checker run; its answer comes back as a Msg
```

and a trusted loop that receives, calls `step`, performs the asks and sends the replies. Laws then quantify over inboxes and over files and checker models, which is what LSP-2, LSP-4 and LSP-6 need. LSP-1 (framing) and LSP-3 (id pairing) are statable today as pure laws over `bolt/lsp/frame.bend` and the dispatch table, so they do not wait for the split.

### Tagging and traceability

The traceability rule, BOLT-LAW-5, is the rule ez's specification asked bolt for, and it is requested in Emerging-Patterns/bolt#44. It checks that the tags on laws and the rows of SPEC.md agree. The format is decided for bolt's own SPEC.md, and ez adopts whatever bolt settles on. The table shape matches ez's because it already fits bolt's requirements, not because the format has to serve both repositories.

<!-- REVIEW-9: The traceability rule (BOLT-LAW-5, requested in Emerging-Patterns/bolt#44) goes in bolt's `laws` group as a project rule, opt-in by name, and reads only the requirement and trust tables of the SPEC.md at the root of the linted tree. The SPEC.md format under "Tagging and traceability" is decided for bolt's own spec; ez adopts it as it stands. The rule needs discovery of one non-`.bend` file, a table-row parser, and a project-rule shape that receives the spec rows. -->

#### The SPEC.md format

SPEC.md lives at the root of the linted tree, which is the directory holding the nearest bolt.bend. The rule reads two kinds of table in it and ignores every other line, so the rest of the file stays prose for people.

| Element | Format |
| :---- | :---- |
| Requirement table | Any Markdown table whose header row is exactly `\| ID \| Requirement \| Level \| Status \| Law \|`. This is the shape ez already uses, kept because it fits bolt's requirements. |
| Trust table | Any table whose header row is exactly `\| ID \| Assumption \| Why it is trusted \|`. |
| ID | Matches `[A-Z][A-Z0-9]*(-[A-Z0-9]+)+`: uppercase segments separated by hyphens, at least two segments. It is unique within the requirement tables and unique within the trust table, and never reused once released. A Trusted requirement's ID appears exactly twice, once in a requirement table and once in the trust table, and that pair is the link the rule checks. IDs such as `BOLT-TRUST-1` appear only in the trust table. `BOLT-CFG-1`, `EZ-HASH-1` and `BOLT-RULE-C001` all match. |
| Level | Exactly `Proved` or `Trusted`. |
| Status | `proved` or `pending` for a Proved row, and empty for a Trusted row. |
| Law | `<path> <law>` entries separated by `; `, with the path relative to SPEC.md, as in `lazy/LAWS.bend stop_is_pick`. A proved row names one or more. A pending row may name laws that each prove part of it, and stays pending until the requirement is proved in full. A Trusted row names none. |
| Tag | A comment line `# <ID>`, alone on its line, in the unbroken comment block directly above a `law` line in a LAWS.bend. A law may carry several tags, one per line. |

We chose a pattern with at least two segments and no required numeric tail because bolt's rule IDs end in a code (`BOLT-RULE-C001`), and a pattern ending in `-[0-9]+` would reject them. Tag lines are part of the law's doc comment block, so `doc` is satisfied without a second comment, as the BOLT-LIB-1 example shows. The Verdict and Evidence columns in this RFC's tables are RFC-only and never appear in SPEC.md. SPEC.md keeps the RFC's first four columns and adds Law, which is why its requirement table's header has five columns where the RFC's tables have six.

#### What the rule reports

The findings are the ones #44 asks for, with pending rows allowed to carry partial laws. The rule reports a proved row whose Law cell is empty, and a Trusted row whose Law cell is not. It checks every Law entry of a Proved row, proved or pending, alike, and reports one whose law is missing, has no `for` or `exs` binder, or lacks the row's tag. It reports a tag naming an ID that SPEC.md does not list, or lists as Trusted, since a tag is a claim that the law proves the row or part of it. A tag naming a pending row is allowed: a quantified law that proves part of a requirement is tagged and named in the pending row's Law cell, so the rule checks it, where an untagged law would be checked by nothing. What remains to prove is the row's own business, which a project may explain beside it. It reports a Trusted row with no trust-table row, a malformed row, and a duplicate ID, meaning the same ID in two requirement rows or in two trust rows. A Trusted requirement's ID appearing once in each kind of table is the expected link, not a duplicate. Every pending requirement is listed without failing, as one summary line, which is the honest answer to "what does this project prove right now".

It is a project rule because it compares one file against every LAWS.bend in the run. It is opt-in by name, under BOLT-CFG-6, because a project with no SPEC.md would otherwise get findings it never asked for, and bolt turns it on for itself in the fifth phase. It runs in the CLI only, like `law`, since the LSP runs per-file rules. The inventory's audit found four gaps between bolt today and this rule. Three need a change, which are the three pieces REVIEW-9 names, and the fourth needs none:

| Gap | Where | What changes |
| :---- | :---- | :---- |
| bolt discovers only `.bend` files and hands every path to `Src.of` | glob.bend:38, lint.bend:45-52 | SPEC.md gets its own discovery: the file beside the nearest bolt.bend, by convention, read once per run. |
| There is no Markdown parser | none | A table-row parser that recognizes the two header rows above and reads the cells of the rows under them, and nothing else. |
| Project rules are `check(List<Digest>)` | rules.bend:87-89 | The project-rule shape gains the spec rows, and the digest gains each law's name, binder flag and the tag lines of its comment block. |
| A bolt.bend maps names to levels only | config.bend:72-73 | Nothing: the spec path is fixed by convention, so no setting is needed. |

### Refactoring contract

This is the rule a contributor or an agent follows when changing bolt, and it is ez's contract with bolt's names. A change to implementation code must keep every tagged law passing the proof gate without editing its statement in LAWS.bend. The proof in PROOF.bend may be rewritten freely, and untagged laws may be changed or removed.

A change may not move a requirement from Proved to Trusted without going through review as a behavior change, because weakening a guarantee is one. A change that adds a Trusted row must justify it in the PR description, since every Trusted row is a place where the gate stops looking. A change to a requirement in SPEC.md is a behavior change, not a refactor, and it is the only way a tagged law's statement may change.

With that in place, "does this change keep bolt's guarantees?" has a mechanical answer: the gate passes, no tagged statement changed, and the trust boundary did not grow. No test run is needed to establish it. For bolt specifically, a change to a rule's header comment is a change to its BOLT-RULE requirement and goes through review the same way, since the header is where the requirement's wording comes from.

### Trust boundary

These assumptions sit outside the proofs. They are the complete list of Trusted requirements, and naming them keeps the spec honest about what a passing gate means. Three more rows, BOLT-TRUST-9 to BOLT-TRUST-11 for the lint, check and LSP interpreters, join the table as those interpreters are introduced (REVIEW-14).

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| BOLT-TRUST-1 | The Bend checker is sound. | It cannot be checked from inside Bend; this is EZ-TRUST-1. bolt pins bend through the flake. |
| BOLT-TRUST-2 | bolt's lexer, tree and outline read a file as the program bend reads, for the constructs the rules depend on. | bolt cannot call bend's parser from Bend. Four divergences are known (multi-line strings, indented continuation lines, `>` inside parentheses in `<..>`, ASCII-only identifiers); each is either fixed or narrows a rule's requirement. |
| BOLT-TRUST-3 | The directory listing effect (`bolt/walk/dir.c`, `dir.js`) returns a directory's entries, marking directories with `/`, and the file read effect returns a file's text. | The walk and the reads are foreign code; the planner takes their answers as given. |
| BOLT-TRUST-4 | The LSP transport (`bolt/lsp/transport/fd.c`, `fd.js`) delivers stdin bytes in order and writes stdout bytes whole. | Foreign code over descriptors 0 and 1. |
| BOLT-TRUST-5 | `bend <file> --check-only` never runs `main`, and prints its report in the shape `bolt/lsp/report.bend` parses. | bend is a separate program, and the report format has already drifted once (`report_import`). |
| BOLT-TRUST-6 | The proof gate runner runs bend on every PROOF.bend and accepts only an exact `All terms check.` first line. | It is ez code run by `mkProofs` (`ez test --unit-only` today, `ez prove` when ez ships it). CI builds from a clean tree. |
| BOLT-TRUST-7 | Every commit on `main` passed `ci.yml`. | Holds only once the ruleset in REVIEW-8 exists. Today it does not hold. |
| BOLT-TRUST-8 | shake v0.1.1 parses argv as its spec says, and ezjson v0.4.2 parses and prints JSON correctly. | Pinned dependencies, by ez.toml hash; bolt's gate does not re-check them. |
| BOLT-OUT-6 | A released code is never renumbered or reused. | A property across versions, enforced by review of the SPEC row that lists the table. |
| BOLT-SYN-6 | Every function in `syntax/` terminates on every input without fuel. | Termination is what the Bend checker's structural-recursion check establishes, so this rests on BOLT-TRUST-1 and needs no law of its own. |

BOLT-TRUST-7 is the row that currently fails, and it undermines every other row, because a gate nothing requires is a gate a merge can skip.

<!-- REVIEW-8: `main` has no branch protection or ruleset, and auto-merge is on, so the gate binds nothing. We propose a repository ruleset on `main` that requires the `ci` check (the `nix flake check` job) and forbids force pushes. A maintainer applies it by hand; this RFC does not. BOLT-TRUST-7 holds only once it exists. -->

The GitHub API confirmed on 2026-09-22 that `main` has no branch protection, no repository ruleset and no inherited ruleset, and the repository has `allow_auto_merge` on. So the proof gate and the self-lint run on every pull request and bind nothing. A ruleset requiring the `ci` check is an outward-facing setting a maintainer applies by hand, which is why it is a preliminary rollout phase rather than part of any PR.

### Decided behavior changes

Each review item that changes behavior lands as its own PR, separate from the spec's rollout, and a requirement stays pending until the change it depends on lands.

From REVIEW-1, every closed law is deleted, 257 in all (123 in `syntax/spec/`, 117 in `bolt/spec/`, 17 in `core/`), along with the `bolt/spec/cases.bend` fixtures only those laws use. The LSP fixtures under `bolt/lsp/fixtures/` stay because host tests read them. `closed` becomes strict, `quantify` is retired with L004 reserved, and bolt.bend names `closed` at error. AGENTS.md's hard rule and `bolt/README.md`'s `closed` entry are rewritten to stop endorsing closed equalities.

From REVIEW-2, per rule, either the code is fixed to match its header or the header is narrowed to match the code, following the inventory's per-rule list. From REVIEW-3, the law files move to `bolt/LAWS.bend` and `syntax/LAWS.bend`, with `law` at warn in bolt.bend, and `law`'s coverage changes to BOLT-LAW-1's new meaning: a def or type counts as covered only when a quantified law in a LAWS.bend references it through the binder. Of all the changes here, this is the one that matters most to ez, because without it `law` at error can be satisfied by a stray token. From REVIEW-4, one predicate module decides "law file" and "test" for every rule, by exact basename and exact path segment.

From REVIEW-5, config lookup resolves each path against the working directory, an unknown setting name becomes a finding, `warning` is accepted for `warn`, and the walk's truncation past 100000 directories becomes a finding. From REVIEW-6, a failure to run bend is an error diagnostic and exit 1, and the import-location rule follows bend 2.0.25's `Location:` line. From REVIEW-7, the LSP advertises `positionEncoding: utf-32` when offered and converts to UTF-16 otherwise. From REVIEW-8, a maintainer adds the ruleset on `main`.

The host tests on AGENTS.md's stay list (`tests/bare.bend`, `tests/flake.bend`, `bolt/lsp/tests/checker.bend`, `bolt/lsp/tests/levels.bend`, `syntax/tests/lex_files.bend`, `syntax/tests/tree_files.bend`, `lazy/tests/lazy.bend` and their companions) keep running. They are integration checks against bend, nix, node and the disk, and they are outside the specification.

### How we will know it worked

The first four rollout phases prove the BOLT-CFG, BOLT-SCOPE, BOLT-OUT, BOLT-CLI and BOLT-SYN groups and BOLT-LAW-1 to LAW-3, and the fifth brings the traceability rule that checks them. The rules are covered too. By the end of the third phase the token rules (C002, C004, C006, U005, S002) and BOLT-RULE-EXEMPT are proved, and each tree rule is either proved or has moved to Trusted with a written reason, under REVIEW-13. The spec has done its job when the traceability rule passes on bolt with none of those requirements pending. By then no LAWS.bend in the repository contains a closed law, and `law` is back at error with bolt's whole source under a law directory. The test that matters is a rewrite of a rule's internals merged on the strength of the proof gate alone, and that test applies to exactly the rules that are proved. ez then uses the same rule to answer the same question about itself.

## Abandoned Ideas

### Keep closed laws as `# toward` trails

This was bolt#42's design and ez's first-phase approach: a closed law that illustrates a pending requirement stays, marked `# toward <ID>` directly above its `law` line, until the quantified law lands, and `quantify` exempts it. The appeal is that it keeps a record of what someone meant a rule to do, costs nothing, and gives each pending requirement a visible trail. It also made a gradual migration possible, since no law had to be deleted before its replacement existed.

The maintainer rejected it for bolt, and the reason is specific to where bolt's closed laws came from. They were made from tests that encoded assumptions about Bend, and some of those assumptions were wrong. `report_import` is the concrete case: it pins a `Location:` format bend no longer prints, so as a trail it would sit next to BOLT-CHK-1 and point the next author at the wrong format. Keeping trails preserves the wrong assumptions right beside the requirement they claim to lead to. The inventory's Points toward column keeps the map, which is the useful part of a trail, without keeping the laws, which are the harmful part.

### Keep bolt#10's position that closed equalities are laws

bolt#10's argument had real merit. A closed equality is checked at compile time, it puts every check on one gate, and it works for IO values, where `{main() == IO.print("...") : IO(Unit)}` states something a `#|` test could only run. Moving 240 tests into that form was mechanical work well suited to agents, and it made the proof gate the only gate.

The result is still a test suite, checked at a different moment. As Background shows, closed laws are too weak to protect a rule (a refactor that breaks it everywhere except its fixture passes) and too strong to let it change (a wording edit breaks 46 proofs). They also made `law` coverage cheap, since one closed law that calls a def once satisfies the rule, which is how the 63 helper pins came to exist. Keeping this position would leave bolt unable to enforce ez's specification, which says closed laws have no standing, so the two repositories would disagree about the model bolt is meant to check.

### Check rules against a corpus of real Bend files

A snapshot of bolt's output over this repository, ez, and other public Bend projects would find regressions fast. Every rule change would show its diff across thousands of real lines, and a false positive introduced by a refactor would appear the moment it touched real code. That is a stronger signal than any fixture list, and it costs little to build.

We rejected it as evidence because it is a test, and a snapshot is a closed law on a bigger input: it says the output on these files is this output, and nothing about any other file. It would also carry the same brittleness, since a deliberate fix to a rule changes the snapshot exactly as a regression would, and the reviewer would be left to judge which is which. It may still be useful as a development tool outside the spec, where it helps an author see a change's reach without claiming to guarantee anything. Used that way, a corpus diff is a prompt to go and write the missing law, since any false positive it surfaces is a counterexample to some BOLT-RULE requirement, and a counterexample is exactly what a quantified law is for ruling out.

### Prove each rule equal to a simpler reference implementation

This would turn "the rule reports exactly the header's pattern" into one quantified equality per rule: `for s: Src, {Shadow.check(s) == Shadow.ref(s) : List<Finding>}`, where `Shadow.ref` is a slow, obvious implementation. It is attractive because the law is uniform across rules, the reference is easy to read, and the proof is a single induction per rule.

We rejected it as the primary form because the reference is a second implementation that can share the first one's misreading. If both decide recursion by any leaf equal to the def's name, the law proves they agree and says nothing about whether either is right. That is the refactor-equivalence pattern ez already deleted. We state patterns as properties over tokens and trees instead, such as "every finding of `nat` sits on a Nat literal token of 1000 or more, and every such token has a finding", and we use a reference only where the property is the definition, as it nearly is for the token rules. A property also documents the rule for its users in a way a reference cannot, since it reads as the sentence in the header rather than as a second program to trust.

### Reuse bend's parser instead of bolt's own

If bolt used bend's own parser, BOLT-TRUST-2 would disappear along with its four divergences, and every rule would see exactly the program bend sees. That would remove the widest trust row in the table and a whole class of false findings, such as phantom defs inside multi-line strings.

It is not possible from inside Bend today, because bend's parser is not a Bend library bolt can import. Calling bend as a subprocess and parsing its output would replace one trust row with another, weaker one, since bend has no stable machine-readable tree output. So agreement stays Trusted, with its divergences listed so that each is fixed in `syntax/` or written into the affected rules' requirements. If bend ever exposes its parser as a library, this becomes the right design and the row goes away. Until then, the practical middle ground is the host test `syntax/tests/tree_files.bend`, which already runs bolt's parser over real files; it stays outside the spec, but it is where a new divergence is most likely to be noticed first.

## Risks

### Proof effort for tree rules

Bend has no tactics, so a law over every tree is a long explicit proof, and the recursion rules read the tree in ways that resist induction. Some rule requirements may cost more than they are worth. The escape hatch is explicit: such a requirement moves to Trusted with a written reason, which is a visible weakening rather than a silent one. We order the work so the parser lemmas and token rules come first, which both proves the cheap rows and tells us early how expensive the tree rows really are.

### Deleting 257 laws removes a regression signal

The closed laws, however weak, did catch some regressions, and after the first phase a refactor of a rule has less standing between it and a broken release. We accept this because those laws were never guarantees, and the pending status in SPEC.md says plainly that nothing about the rules is proved yet. The host tests remain for integration, and the rollout proves the cheap rows next, so the gap is visible and shrinks with each phase.

### Strict `closed` breaks other projects on upgrade

Every project that runs bolt with the laws group at warn or error and holds closed equalities will see new findings on the release that makes `closed` strict, and no compatibility path is kept. ez is not at risk: it stays pinned at bolt v0.9.0 while its `# toward` trails exist, and when the last is deleted it bumps bolt, removes `def quantify()` from its bolt.bend and turns strict `closed` on in the same change. Other projects learn of it from the release notes, which must say what changed and how to switch `closed` off by name. Once BOLT-CFG-7 lands, a leftover `def quantify()` is itself a finding, which is how a project that missed the notes notices.

### Rule requirements may encode heuristics as guarantees

Writing "reports exactly this pattern" from a header risks promoting a heuristic into a promise. `fuel` recognizing fuel by parameter name is a heuristic, and stating the header's broader wording as a requirement would make it fail forever. REVIEW-2 handles this by narrowing such headers to what the code deliberately does, so the requirement states the heuristic honestly rather than an ideal no rule meets.

### Parser divergence from bend

Every rule inherits bolt's parser, so a divergence from bend (BOLT-TRUST-2) is a wrong finding in every rule that reads the affected construct. A proof over bolt's tree proves the rule correct over bolt's reading, not bend's. We list the four known divergences in the trust row and fix or scope each, and a new divergence found later is a new entry in that row, reviewed as a change to the trust boundary.

### Branch protection depends on a manual step

BOLT-TRUST-7 holds only once a maintainer adds the ruleset on `main`, and nothing in the repository can apply or check it. Until then, auto-merge can merge a pull request whose gate failed. We make it a preliminary phase so it lands first, and the SPEC row states plainly that the assumption does not hold until it does.

## Rollout

The rollout proceeds in phases, each of which leaves the repository consistent. The decided behavior changes land as their own PRs alongside it, and the only ordering between them is that a requirement cannot be proved before the change it depends on. The refactoring contract applies from the first phase, since it depends only on law statements and the trust boundary.

**Preliminary phase.** A maintainer adds the ruleset on `main` (REVIEW-8), requiring the `ci` check and forbidding force pushes. This is a repository setting, not a PR, and it comes first because every later phase relies on the gate binding.

**First phase.** SPEC.md lands at the repository root from this RFC, with every requirement's level and status. Lazy's three laws get the `# BOLT-LIB-1` tag. Every closed law is deleted with the fixtures only they use, `closed` becomes strict and is set to error in bolt.bend, `quantify` is retired, and AGENTS.md and `bolt/README.md` stop endorsing closed equalities. The law files move per REVIEW-3, with `law` at warn. Strict `closed` makes BOLT-LAW-2 true in this phase, though its law comes in the second. After this phase bolt proves one requirement and says so honestly, and the gate is 84 s plus 34 s faster.

**Second phase.** The cheap Proved requirements that need no World: BOLT-CFG-1, CFG-2, CFG-3, CFG-5 and CFG-6, BOLT-CFG-7 after REVIEW-5 lands, BOLT-LAW-2, BOLT-OUT-1, BOLT-OUT-2, BOLT-CLI-1 and CLI-2, BOLT-SYN-1 and SYN-2, BOLT-LSP-1 and LSP-3, and BOLT-RULE-EXEMPT with BOLT-SCOPE-4 once REVIEW-4's predicates land.

**Third phase.** The token rules (C002, C004, C006, U005, S002), then BOLT-SYN-3, SYN-4 and SYN-5 as lemmas, then the tree rules in order of how often they fire, with BOLT-RULE-INERT proved for each family as its rules land.

**Fourth phase.** The lint planner and World, with BOLT-TRUST-9 added in the same PR (REVIEW-14). Then BOLT-SCOPE-1, SCOPE-2, SCOPE-3 and SCOPE-5, BOLT-CFG-4 after REVIEW-5, BOLT-OUT-3, OUT-4 and OUT-5, and BOLT-LAW-1 and LAW-3 over the planner's chosen paths. `law` returns to error when the files it grades are covered.

**Fifth phase.** The BOLT-LAW-5 traceability rule, opt-in. bolt turns it on for itself at error, and ez adopts it in place of the check its own RFC planned.

**Later phases.** The `bolt check` oracle with BOLT-TRUST-10, proving BOLT-CHK-1 after REVIEW-6; then the LSP step function with BOLT-TRUST-11, proving BOLT-LSP-2, LSP-4, LSP-6 and LSP-7, and BOLT-LSP-5 over bolt's side of the checker call, with bend's side resting on BOLT-TRUST-5.

## Future Steps

ez's traceability rule comes from here: once BOLT-LAW-5 ships, ez's SPEC.md is checked by the same code as bolt's, and the sibling libraries (ezjson, eztoml, ezhttp) can adopt it with no new tooling. The lint planner makes a `bolt --fix` statable, since a fix is a plan of edits and "fixing never introduces a finding of the same rule" becomes a law over worlds. The LSP step function makes editor behavior provable in the same way, so that what an editor shows is a guarantee rather than a transcript of one session.
