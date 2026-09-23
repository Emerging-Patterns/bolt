# bolt specification

This is the list of every behavior bolt guarantees, each under a stable requirement ID. Every requirement has one of two levels. A **Proved** requirement holds for every input, and is backed by a quantified law (a `for` or `exs` binder) in a LAWS.bend that passes the proof gate. A **Trusted** requirement is an assumption bolt cannot check from inside its own gate, and it is listed in the trust boundary below. A Proved requirement whose law has not landed yet has status **pending**: we intend to prove it, and until then it is not guaranteed. The proof gate is this check: for every PROOF.bend in the tree, the first line `bend PROOF.bend` prints is exactly `All terms check.` Tests and fixtures are never evidence for a requirement.

The reasoning behind each requirement, the verdict of each against the code at `a38e87a`, and the decisions that shaped them are in [docs/rfc/bolt-spec.md](docs/rfc/bolt-spec.md). Every law as it stood then is in [docs/rfc/bolt-law-inventory.md](docs/rfc/bolt-law-inventory.md).

## Format

A requirement table is any table whose header row is exactly `| ID | Requirement | Level | Status | Law |`. An ID is uppercase segments joined by hyphens, at least two (`[A-Z][A-Z0-9]*(-[A-Z0-9]+)+`), unique within the requirement tables, and never reused once released. Level is `Proved` or `Trusted`. Status is `proved` or `pending` for a Proved row and empty for a Trusted row. The Law cell is empty unless the row is proved; then it holds one or more `<path> <law>` entries, paths relative to this file, separated by `; `.

A law proves a requirement when a comment line `# <ID>`, alone on its line, sits in the unbroken comment block directly above its `law` line. A law may carry several tags, one per line:

```
# LAW: a thunk that ignores its argument makes stop Bool.pick
# BOLT-LIB-1
law stop_is_pick:
```

A Trusted requirement's ID appears once in a requirement table and once in the trust boundary table. Untagged quantified laws are allowed; they pass the gate like any law, but nothing here protects them. A law with no binder is a `closed` finding.

## Requirements

### Rules (BOLT-RULE)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| BOLT-RULE-C001 | `shadow` reports exactly a let, do-bind, lambda or pattern binder named like a top-level def above it in the file, and nothing else. | Proved | pending |  |
| BOLT-RULE-C002 | `hole` reports exactly a TODO hole bend counts, a `?` then `TODO` with only spaces, newlines or comments between, outside a LAWS.bend, and nothing else. | Proved | pending |  |
| BOLT-RULE-C003 | `pick` reports exactly a self-call in one or both branches of `Bool.pick`, and does not report again a nested pick in a branch it reported. | Proved | pending |  |
| BOLT-RULE-C004 | `put` reports exactly a `Map.put(` call, except in a file that defines `Map.put`. | Proved | pending |  |
| BOLT-RULE-C005 | `arms` reports exactly, in a single-scrutinee match, a Nat arm already covered by an earlier `kn+p` or `Succ{p}` arm. | Proved | pending |  |
| BOLT-RULE-C006 | `escape` reports exactly one finding for each `\0` followed by a digit in a string or char literal, its escapes read as a backslash and the one char after it, and none for anything else. | Proved | proved | bolt/rules/LAWS.bend escape_counts; bolt/rules/LAWS.bend escape_scan_counts |
| BOLT-RULE-C007 | `twice` reports exactly, in a recursive def, a list pattern opening with the same literal twice. | Proved | pending |  |
| BOLT-RULE-C008 | `strings` reports exactly a match whose string-literal arms total over 64 characters. | Proved | pending |  |
| BOLT-RULE-C009 | `chars` reports exactly a match with more than eight char-literal arms. | Proved | pending |  |
| BOLT-RULE-C010 | `foreign` reports exactly a foreign def with a `.c` body and no `.js` or the reverse, where a `# lanes: native` file needs no `.js`. | Proved | pending |  |
| BOLT-RULE-U001 | `unused` reports exactly an unused let, do-bind, lambda binder or parameter, with the header's exemptions. | Proved | pending |  |
| BOLT-RULE-U002 | `strict` reports exactly a self-call inside `Bool.and` or `Bool.or`, or on either side of `&&` or `\|\|`, matched by that exact text, where a lambda body counts only by its own `&&` or `\|\|`. | Proved | pending |  |
| BOLT-RULE-U003 | `eager` reports exactly a looping def of the file called in a `Bool.pick` branch. | Proved | pending |  |
| BOLT-RULE-U004 | `concat` reports exactly a self-call argument that appends onto the parameter in its own position. | Proved | pending |  |
| BOLT-RULE-U005 | `nat` reports exactly one finding for each token the lexer reads as a Nat literal of 1000 or more (digits then `n`, four or more digits once leading zeros are dropped), and none for any other token. | Proved | proved | bolt/rules/LAWS.bend nat_counts |
| BOLT-RULE-U006 | `fuel` reports exactly an argument that is one Nat literal token alone, in a call (not a self-call) to a def of the file, at a parameter named `fuel`, `gas`, `steps` or `budget` or starting with `fuel`. | Proved | pending |  |
| BOLT-RULE-U007 | `index` reports exactly a `List.get` or `String.get` at a non-literal index in a recursive def. | Proved | pending |  |
| BOLT-RULE-U008 | `table` reports exactly a get or set at a computed index on a fixed table inside a recursive def. | Proved | pending |  |
| BOLT-RULE-U009 | `hoist` reports exactly a table of more than eight cells rebuilt per step from carried inputs. | Proved | pending |  |
| BOLT-RULE-U010 | `ring` reports exactly a fixed window dropped and appended per step and passed back in its own parameter position. | Proved | pending |  |
| BOLT-RULE-U011 | `rewalk` reports exactly the same walk twice on the same argument, one result read for a single value. | Proved | pending |  |
| BOLT-RULE-U012 | `unit` reports exactly a multiply or divide by one on a recursive step. | Proved | pending |  |
| BOLT-RULE-S001 | `doc` reports exactly a top-level def, type or law with no comment block right above it, with the header's exemptions. | Proved | pending |  |
| BOLT-RULE-S002 | `space` reports exactly trailing whitespace or a tab on any line, string literals and `#\|` lines included, or a line over 120 columns with string literals counted as two, comments at full width, and `#\|` lines not counted. | Proved | pending |  |
| BOLT-RULE-S003 | `wrap` reports exactly a def header whose shape breaks the header's rules. | Proved | pending |  |
| BOLT-RULE-S004 | `param` reports exactly a parameter name shorter than two characters, with the header's exemptions. | Proved | pending |  |
| BOLT-RULE-P001 | `tail` reports exactly a non-tail self-call outside any `Bool.pick(..)` in a def whose first live parameter's type is a List or String, whether or not the call shrinks it. | Proved | pending |  |
| BOLT-RULE-EXEMPT | For every text, a per-file rule's check on a path its header exempts returns no findings. | Proved | pending |  |
| BOLT-RULE-INERT | For every rule whose pattern is code (all but `escape`, `strings`, `chars`, `space`, `twice` and `nat`), changing the contents of a comment or string literal does not change the findings. | Proved | pending |  |

### Laws rules (BOLT-LAW)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| BOLT-LAW-1 | In every file under a law directory, except helpers, law files and tests, every def and type is referenced by a quantified law in a LAWS.bend: a use in the law's statement that the binder (BOLT-SYN-5) resolves to that def, through an import alias or in the same file. | Proved | pending |  |
| BOLT-LAW-2 | `closed` reports any law in a LAWS.bend with no binder. | Proved | pending |  |
| BOLT-LAW-3 | An `@unsafe def` reachable by relative imports from a law file in the run is a finding. | Proved | pending |  |
| BOLT-LAW-5 | The traceability rule reports exactly the findings listed under "Tagging and traceability" for the SPEC.md format stated there. | Proved | pending |  |

### Grading and config (BOLT-CFG)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| BOLT-CFG-1 | A rule's level is its own setting, else its group's setting, else its group's default. | Proved | pending |  |
| BOLT-CFG-2 | Grading drops a finding at `off` and attaches the level to every other. | Proved | pending |  |
| BOLT-CFG-3 | A level word that is not `off` or `warn` grades as error. | Proved | pending |  |
| BOLT-CFG-4 | A finding is graded by the nearest readable bolt.bend in its file's directory, then each parent, and only that one applies. | Proved | pending |  |
| BOLT-CFG-5 | Group defaults are correctness at error, pedantic off, and the rest at warn. | Proved | pending |  |
| BOLT-CFG-6 | An opt-in rule is off unless its own setting names it. | Proved | pending |  |
| BOLT-CFG-7 | A setting in a bolt.bend whose name is no rule or group is a finding. | Proved | pending |  |

### Scope (BOLT-SCOPE)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| BOLT-SCOPE-1 | With no files named, bolt lints every `.bend` file under `.` found within the first 100000 directories the walk reads, not descending into hidden directories or `node_modules`, sorted by code point; past that bound the walk stops silently. | Proved | pending |  |
| BOLT-SCOPE-2 | A per-file rule sees one file's `Src`; a project rule sees the digests of every file in the run, and nothing else. | Proved | pending |  |
| BOLT-SCOPE-3 | When the files in the run include a LAWS.bend, every file in the run that is not exempt is under law; otherwise none is. | Proved | pending |  |
| BOLT-SCOPE-4 | Exemptions are decided by the path alone, never by content. | Proved | pending |  |
| BOLT-SCOPE-5 | A bolt.bend is read, never linted, even when named. | Proved | pending |  |

### Output and exit (BOLT-OUT)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| BOLT-OUT-1 | The code table maps each rule slug to exactly one code and each code to exactly one slug. | Proved | pending |  |
| BOLT-OUT-6 | A released code is never renumbered or reused. | Trusted |  |  |
| BOLT-OUT-2 | A finding prints as `path:line:col: level: CODE: message`, 1-based. | Proved | pending |  |
| BOLT-OUT-3 | Output order is read failures, then per-file findings in file-list order and `Rules.on` order, then `coverage` and `unsafe`. | Proved | pending |  |
| BOLT-OUT-4 | The last line is `clean` or `N errors, M warnings`, and the exit status is 1 exactly when some graded finding is an error. | Proved | pending |  |
| BOLT-OUT-5 | A path that cannot be read is a `read` finding graded with correctness. | Proved | pending |  |

### Command line (BOLT-CLI)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| BOLT-CLI-1 | bolt accepts `bolt [lint] [files]`, `bolt check files`, `bolt lsp`, `bolt help [cmd]` and `--`; an argv parse error exits 1, and `help` and `--version` exit 0. | Proved | pending |  |
| BOLT-CLI-2 | `--version` prints the release and, when the build has one, the short commit in parentheses. | Proved | pending |  |

### Checker (BOLT-CHK)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| BOLT-CHK-1 | `bolt check` prints one `path:line:1: error:` line per error bend reports, on the line bend marks, then a count; it exits 1 when there is any, and treats a failure to run bend as an error. | Proved | pending |  |

### Parser (BOLT-SYN)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| BOLT-SYN-1 | `Lex.text(Lex.tokens(s)) == s` for every `s`. | Proved | pending |  |
| BOLT-SYN-2 | A token's line and column are those of its first character, 0-based, in code points. | Proved | pending |  |
| BOLT-SYN-3 | The tree drops no token, and its leaves are the significant tokens in order. | Proved | pending |  |
| BOLT-SYN-4 | The outline lists every column-0 import, def, type, law and `@unsafe def`. | Proved | pending |  |
| BOLT-SYN-5 | The binder resolves a use to the innermost binder, then a file item, then an alias qualifier, else free. | Proved | pending |  |
| BOLT-SYN-6 | Every function in `syntax/` terminates on every input without fuel. | Trusted |  |  |

### Language server (BOLT-LSP)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| BOLT-LSP-1 | `Content-Length` counts UTF-8 bytes; a partial header or body waits; `cut` of `wrap(s)` gives `s`. | Proved | pending |  |
| BOLT-LSP-2 | Diagnostics for an open document equal the CLI's per-file findings for that file and text under the same bolt.bend. | Proved | pending |  |
| BOLT-LSP-3 | Each request gets exactly one response with the same id, in order; an unknown request gets -32601; an unknown notification gets nothing. | Proved | pending |  |
| BOLT-LSP-4 | Open and save publish checker plus lint; change publishes lint plus the last checker result; close publishes an empty list; an open bolt.bend gets no lint. | Proved | pending |  |
| BOLT-LSP-5 | The checker never runs `main`. | Proved | pending |  |
| BOLT-LSP-6 | Hover, definition, references and completion answer from the binder (BOLT-SYN-5) over the open text and its relative imports. | Proved | pending |  |
| BOLT-LSP-7 | Positions are in the encoding the client negotiated. | Proved | pending |  |

### Library (BOLT-LIB)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| BOLT-LIB-1 | `Lazy.stop(c, a, _ => b) == Bool.pick(c, a, b)`, `Lazy.or_else(a, _ => b) == Bool.or(a, b)` and `Lazy.and_then(a, _ => b) == Bool.and(a, b)` for all inputs. | Proved | proved | lazy/LAWS.bend stop_is_pick; lazy/LAWS.bend or_else_is_or; lazy/LAWS.bend and_then_is_and |
| BOLT-LIB-2 | `Lazy.stop`, `Lazy.or_else` and `Lazy.and_then` apply their thunk only on the branch that needs it. | Trusted |  |  |

## Trust boundary

These assumptions sit outside the proofs. They are the complete list of Trusted requirements, and a passing proof gate says nothing about them.

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| BOLT-TRUST-1 | The Bend checker is sound. | It cannot be checked from inside Bend; this is EZ-TRUST-1. bolt pins bend through the flake. |
| BOLT-TRUST-2 | bolt's lexer, tree and outline read a file as the program bend reads, for the constructs the rules depend on. | bolt cannot call bend's parser from Bend. Four divergences are known (multi-line strings, indented continuation lines, `>` inside parentheses in `<..>`, ASCII-only identifiers); each is either fixed or narrows a rule's requirement. |
| BOLT-TRUST-3 | The directory listing effect (`bolt/walk/dir.c`, `dir.js`) returns a directory's entries, marking directories with `/`, and the file read effect returns a file's text. | The walk and the reads are foreign code; the planner takes their answers as given. |
| BOLT-TRUST-4 | The LSP transport (`bolt/lsp/transport/fd.c`, `fd.js`) delivers stdin bytes in order and writes stdout bytes whole. | Foreign code over descriptors 0 and 1. |
| BOLT-TRUST-5 | `bend <file> --check-only` never runs `main`, and prints its report in the shape `bolt/lsp/report.bend` parses. | bend is a separate program, and the report format has already drifted once (`report_import`). |
| BOLT-TRUST-6 | The proof gate runner runs bend on every PROOF.bend and accepts only an exact `All terms check.` first line. | It is ez code run by `mkProofs` (`ez test --unit-only` today, `ez prove` when ez ships it). CI builds from a clean tree. |
| BOLT-TRUST-7 | Every commit on `main` passed `ci.yml`. | The repository ruleset "main: require ci" requires the `check / check` job on `main` (since 2026-09-22). release-please PRs, which get no CI run, merge through an admin pull-request bypass. |
| BOLT-TRUST-8 | shake v0.1.1 parses argv as its spec says, and ezjson v0.1.0 parses and prints JSON correctly. | Pinned dependencies, by ez.toml hash; bolt's gate does not re-check them. The surrogate-pair bug sits here. |
| BOLT-OUT-6 | A released code is never renumbered or reused. | A property across versions, enforced by review of the SPEC row that lists the table. |
| BOLT-SYN-6 | Every function in `syntax/` terminates on every input without fuel. | Termination is what the Bend checker's structural-recursion check establishes, so this rests on BOLT-TRUST-1 and needs no law of its own. |
| BOLT-LIB-2 | The lazy branches apply their thunk only on the branch that needs it. | A law states what a term equals, not what evaluation skipped, so Bend cannot state it. `lazy/lazy.bend` matches on the Bool before it applies the thunk, and BOLT-LIB-1 proves the values agree with the strict forms. |
