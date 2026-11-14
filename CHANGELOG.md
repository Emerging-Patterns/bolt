# Changelog

## [1.56.0](https://github.com/Emerging-Patterns/bolt/compare/v1.55.0...v1.56.0) (2026-11-14)


### Features

* **fmt:** bolt fmt, a formatter for blank space, with --check ([#369](https://github.com/Emerging-Patterns/bolt/issues/369)) ([45b2087](https://github.com/Emerging-Patterns/bolt/commit/45b20874c00168d0215991f7cf620840d84e5c33))


### Bug Fixes

* **config:** setting (C011) reports a limit under a name no rule has ([#370](https://github.com/Emerging-Patterns/bolt/issues/370)) ([28dcf64](https://github.com/Emerging-Patterns/bolt/commit/28dcf6431fd9435483ed7c9f9e2831291580889b))

## [1.55.0](https://github.com/Emerging-Patterns/bolt/compare/v1.54.0...v1.55.0) (2026-11-14)


### Features

* **rules:** arity (S009), length (S010) and depth (S011), a def's size ([#366](https://github.com/Emerging-Patterns/bolt/issues/366)) ([da8c4f1](https://github.com/Emerging-Patterns/bolt/commit/da8c4f1bdcc9fcfc58025d44f0296b5601348157))

## [1.54.0](https://github.com/Emerging-Patterns/bolt/compare/v1.53.0...v1.54.0) (2026-11-14)


### Features

* **config:** a bolt.bend sets a rule's limit; reach reads reach_max ([#362](https://github.com/Emerging-Patterns/bolt/issues/362)) ([f67964b](https://github.com/Emerging-Patterns/bolt/commit/f67964b8212a80cd55bea6aa0ccf212f13091fa5))


### Bug Fixes

* **syntax:** read the lines under a let by what the let's line ends in ([#361](https://github.com/Emerging-Patterns/bolt/issues/361)) ([b82866f](https://github.com/Emerging-Patterns/bolt/commit/b82866f30659597aba12e9d065af776439bbdb33)), closes [#346](https://github.com/Emerging-Patterns/bolt/issues/346)

## [1.53.0](https://github.com/Emerging-Patterns/bolt/compare/v1.52.0...v1.53.0) (2026-11-14)


### ⚠ BREAKING CHANGES

* **rules:** `param` (S004) is removed and its code is not reused. A bolt.bend that still sets `def param()` gets a `setting` finding (C011): delete the def. A `# noqa: S004` comment is now a `noqa` finding (S005). `reach` (S008) is new and graded with `style`: a project with `style` at error gets an error for each one-character name read more than 20 lines below its binder.

### Features

* **rules:** reach (S008) replaces param (S004) ([#357](https://github.com/Emerging-Patterns/bolt/issues/357)) ([cfdc3c6](https://github.com/Emerging-Patterns/bolt/commit/cfdc3c6247d1cf581f676d54d78aac0d311b3f7a))

## [1.52.0](https://github.com/Emerging-Patterns/bolt/compare/v1.51.0...v1.52.0) (2026-11-13)


### Bug Fixes

* **cli:** exit non-zero without writing a blank line to stderr ([#352](https://github.com/Emerging-Patterns/bolt/issues/352)) ([7dcfbc6](https://github.com/Emerging-Patterns/bolt/commit/7dcfbc6152a44612c0a8cd6d6f491246ae531f01))

## [1.51.0](https://github.com/Emerging-Patterns/bolt/compare/v1.50.0...v1.51.0) (2026-11-13)


### Bug Fixes

* **syntax:** read the proof of a named rewrite `%h@e : P` as a use ([#350](https://github.com/Emerging-Patterns/bolt/issues/350)) ([736d76a](https://github.com/Emerging-Patterns/bolt/commit/736d76a1a6bc312a55038d8a96d8f07259ab63c7))

## [1.50.0](https://github.com/Emerging-Patterns/bolt/compare/v1.49.0...v1.50.0) (2026-11-13)


### Bug Fixes

* **foreign:** find a foreign def's lanes under a wrapped header ([#348](https://github.com/Emerging-Patterns/bolt/issues/348)) ([2c7bc35](https://github.com/Emerging-Patterns/bolt/commit/2c7bc3560d3e29c0509512ff82509a03685ecda5))
* **syntax:** read writes chained in one term, `(a[i] <- v)[j] <- w`, as a term ([#349](https://github.com/Emerging-Patterns/bolt/issues/349)) ([e721ea2](https://github.com/Emerging-Patterns/bolt/commit/e721ea22bb75b0108b9e0a7f2632776ea441b8b5))

## [1.49.0](https://github.com/Emerging-Patterns/bolt/compare/v1.48.0...v1.49.0) (2026-11-13)


### Bug Fixes

* **rules:** read a wrapped def header as the def's signature ([#345](https://github.com/Emerging-Patterns/bolt/issues/345)) ([46385dc](https://github.com/Emerging-Patterns/bolt/commit/46385dcfa6301f880840a4f6b94074ff5e580e39))

## [1.48.0](https://github.com/Emerging-Patterns/bolt/compare/v1.47.0...v1.48.0) (2026-11-13)


### Bug Fixes

* **syntax:** read an array write `a[i] <- v` as a term that uses a ([#342](https://github.com/Emerging-Patterns/bolt/issues/342)) ([4ea3d4f](https://github.com/Emerging-Patterns/bolt/commit/4ea3d4fe9ac37aca86c17654106f77f9f1ccd942))

## [1.47.0](https://github.com/Emerging-Patterns/bolt/compare/v1.46.0...v1.47.0) (2026-11-13)


### Bug Fixes

* **syntax:** read a typed step `Unit <- m` as a term, not a let ([#341](https://github.com/Emerging-Patterns/bolt/issues/341)) ([38ef66e](https://github.com/Emerging-Patterns/bolt/commit/38ef66ea122c1b70720ac6f254cb20d064eb403b))

## [1.46.0](https://github.com/Emerging-Patterns/bolt/compare/v1.45.0...v1.46.0) (2026-11-13)


### Bug Fixes

* **files:** read a file whole, so a broken UTF-8 char cannot swallow the next line ([#339](https://github.com/Emerging-Patterns/bolt/issues/339)) ([0c90d59](https://github.com/Emerging-Patterns/bolt/commit/0c90d599099feff918b85f54be86a080f28f7547))

## [1.45.0](https://github.com/Emerging-Patterns/bolt/compare/v1.44.0...v1.45.0) (2026-11-13)


### Performance Improvements

* **doc:** branch the line flags on 12 bits, not 20 ([#337](https://github.com/Emerging-Patterns/bolt/issues/337)) ([1f557c7](https://github.com/Emerging-Patterns/bolt/commit/1f557c7dd40857d7ea9c14957df7fdde8d5bb057))

## [1.44.0](https://github.com/Emerging-Patterns/bolt/compare/v1.43.0...v1.44.0) (2026-11-13)


### Performance Improvements

* **rules:** walk imports through indexes of the edges, the files seen and the files read ([#334](https://github.com/Emerging-Patterns/bolt/issues/334)) ([3cb25e5](https://github.com/Emerging-Patterns/bolt/commit/3cb25e517b2733dd61c68da692b085e7db6163ad))

## [1.43.0](https://github.com/Emerging-Patterns/bolt/compare/v1.42.0...v1.43.0) (2026-11-13)


### Performance Improvements

* **lint:** read grading's bolt.bend candidates off an index of the replies ([#332](https://github.com/Emerging-Patterns/bolt/issues/332)) ([da4a544](https://github.com/Emerging-Patterns/bolt/commit/da4a544c1e8c742cb885e100ea7af7ccaca66eab))

## [1.42.0](https://github.com/Emerging-Patterns/bolt/compare/v1.41.0...v1.42.0) (2026-11-13)


### Bug Fixes

* **lsp:** the server asks for what the message lacks, so it answers under bend 2.0.40 ([#312](https://github.com/Emerging-Patterns/bolt/issues/312)) ([9c0ef1e](https://github.com/Emerging-Patterns/bolt/commit/9c0ef1e8ecb28cb89f5a8b163902bbbfe77f7471))

## [1.41.0](https://github.com/Emerging-Patterns/bolt/compare/v1.40.0...v1.41.0) (2026-11-13)


### Performance Improvements

* **role:** the marks ask indexes of what the walks reach ([#308](https://github.com/Emerging-Patterns/bolt/issues/308)) ([0777d83](https://github.com/Emerging-Patterns/bolt/commit/0777d834f987788058c642ca162f4eee2eec1d66))

## [1.40.0](https://github.com/Emerging-Patterns/bolt/compare/v1.39.0...v1.40.0) (2026-11-13)


### Performance Improvements

* **lint:** wants asks indexes of the paths met and the questions answered ([#305](https://github.com/Emerging-Patterns/bolt/issues/305)) ([20207c6](https://github.com/Emerging-Patterns/bolt/commit/20207c64bbd5912f748c4ea067a2f209eedc3bbf))

## [1.39.0](https://github.com/Emerging-Patterns/bolt/compare/v1.38.0...v1.39.0) (2026-11-13)


### Performance Improvements

* **noqa:** a finding asks whether its file holds a mark before the marks are searched ([#302](https://github.com/Emerging-Patterns/bolt/issues/302)) ([fda7404](https://github.com/Emerging-Patterns/bolt/commit/fda740469ab7b49bf09d1cede4df389df80be443))

## [1.38.0](https://github.com/Emerging-Patterns/bolt/compare/v1.37.0...v1.38.0) (2026-11-13)


### Performance Improvements

* **rules:** eager and rewalk gather the looping defs with an index of their names ([#298](https://github.com/Emerging-Patterns/bolt/issues/298)) ([db3768b](https://github.com/Emerging-Patterns/bolt/commit/db3768b357f7ee1683ce91fdbb3d311bcb0215e4))

## [1.37.0](https://github.com/Emerging-Patterns/bolt/compare/v1.36.0...v1.37.0) (2026-11-13)


### Performance Improvements

* **rules:** the digest asks an index of the proofs' names, not the list ([#296](https://github.com/Emerging-Patterns/bolt/issues/296)) ([8c5b6b0](https://github.com/Emerging-Patterns/bolt/commit/8c5b6b0c492ccd7a1c9dfee49b161f5357f6878f))

## [1.36.0](https://github.com/Emerging-Patterns/bolt/compare/v1.35.0...v1.36.0) (2026-11-13)


### Performance Improvements

* **rules:** doc reads one-pass line flags ([#294](https://github.com/Emerging-Patterns/bolt/issues/294)) ([af14827](https://github.com/Emerging-Patterns/bolt/commit/af1482755b6ef1269a7b8d9f943c1eab791e9b78))

## [1.35.0](https://github.com/Emerging-Patterns/bolt/compare/v1.34.0...v1.35.0) (2026-11-11)


### Performance Improvements

* **lint:** a per-file rule its file's config sets off is not run ([#292](https://github.com/Emerging-Patterns/bolt/issues/292)) ([5c30d50](https://github.com/Emerging-Patterns/bolt/commit/5c30d50754f751b1955d6480b6c32e9004adabf6)), closes [#286](https://github.com/Emerging-Patterns/bolt/issues/286)

## [1.34.0](https://github.com/Emerging-Patterns/bolt/compare/v1.33.0...v1.34.0) (2026-11-11)


### Performance Improvements

* **rules:** param reads a binder's note only for a short parameter ([#290](https://github.com/Emerging-Patterns/bolt/issues/290)) ([cd46684](https://github.com/Emerging-Patterns/bolt/commit/cd4668428c09a51a5df1c58790c19e7cf4464728))

## [1.33.0](https://github.com/Emerging-Patterns/bolt/compare/v1.32.0...v1.33.0) (2026-11-11)


### Performance Improvements

* **rules:** unused's index of the uses is exact, so no binder scans them ([#288](https://github.com/Emerging-Patterns/bolt/issues/288)) ([caf696f](https://github.com/Emerging-Patterns/bolt/commit/caf696f97c2aca97c812e131ebc5309f7929ce26))

## [1.32.0](https://github.com/Emerging-Patterns/bolt/compare/v1.31.0...v1.32.0) (2026-11-11)


### Performance Improvements

* **bind:** an index of the file's items, proved to answer as the scan does ([#284](https://github.com/Emerging-Patterns/bolt/issues/284)) ([82a4fa8](https://github.com/Emerging-Patterns/bolt/commit/82a4fa8c107eb8a183c59ae4706f7cdfd6661061))

## [1.31.0](https://github.com/Emerging-Patterns/bolt/compare/v1.30.0...v1.31.0) (2026-11-11)


### ⚠ BREAKING CHANGES

* **rules:** `twice` is removed; a bolt.bend that still sets it gets a `setting` finding (C011). `chars` is off unless `pedantic` or `def chars()` is set: a project that relied on its warning must turn it on.

### Features

* **rules:** retire twice and demote chars, their premises re-measured on bend 2.0.40 ([#280](https://github.com/Emerging-Patterns/bolt/issues/280)) ([6167ff7](https://github.com/Emerging-Patterns/bolt/commit/6167ff77ea6274037a5b3c92938a0b969677f483))


### Performance Improvements

* **rules:** rewalk reads a call's arguments only when it is a site ([#282](https://github.com/Emerging-Patterns/bolt/issues/282)) ([1d0a345](https://github.com/Emerging-Patterns/bolt/commit/1d0a34558dbe0ad34c8653b579e6b87499700c1e))

## [1.30.0](https://github.com/Emerging-Patterns/bolt/compare/v1.29.0...v1.30.0) (2026-11-11)


### Features

* **rules:** blank (S007), a named String compared to "" is is_empty ([#278](https://github.com/Emerging-Patterns/bolt/issues/278)) ([e73cf47](https://github.com/Emerging-Patterns/bolt/commit/e73cf47a941d6640cf0221c35a545c263b3c7233))

## [1.29.0](https://github.com/Emerging-Patterns/bolt/compare/v1.28.0...v1.29.0) (2026-11-11)


### Features

* **rules:** arms reports an arm an earlier arm of its match covers ([#275](https://github.com/Emerging-Patterns/bolt/issues/275)) ([d3d2f02](https://github.com/Emerging-Patterns/bolt/commit/d3d2f02bf094864cc113ee565863e48692a46392))

## [1.28.0](https://github.com/Emerging-Patterns/bolt/compare/v1.27.0...v1.28.0) (2026-11-09)


### Bug Fixes

* **deps:** import ezjson, shake and snap by hub name ([#273](https://github.com/Emerging-Patterns/bolt/issues/273)) ([c42e41d](https://github.com/Emerging-Patterns/bolt/commit/c42e41dcd13f8a5f9fcc2bc4578690eb7b554a62))

## [1.27.0](https://github.com/Emerging-Patterns/bolt/compare/v1.26.0...v1.27.0) (2026-11-01)


### Features

* **rules:** empty (U018), a kept length compared to zero is is_empty ([22835b9](https://github.com/Emerging-Patterns/bolt/commit/22835b95370e594df901a1e038847d7be45eb03f))

## [1.26.0](https://github.com/Emerging-Patterns/bolt/compare/v1.25.0...v1.26.0) (2026-11-01)


### ⚠ BREAKING CHANGES

* **rules:** `table`, `hoist`, `ring`, `unit`, `scan` and `unsafe` are removed; a bolt.bend that still sets one gets a `setting` finding (C011). `strings`, `chars` and `foreign` are no longer errors by default, `strict`, `fuel`, `index`, `rewalk` and `foreign` are off unless `pedantic` (or the rule) is set, and `coverage` and `closed` are off unless set by name: a project that relied on them must add `def coverage()` / `def closed()`.

### Features

* **rules:** regroup, demote and retire rules after the audit ([#267](https://github.com/Emerging-Patterns/bolt/issues/267)) ([ca72d74](https://github.com/Emerging-Patterns/bolt/commit/ca72d74cc8c6e06234d839eacf6e4de4503a265c))

## [1.25.0](https://github.com/Emerging-Patterns/bolt/compare/v1.24.0...v1.25.0) (2026-11-01)


### Features

* **rules:** prefix (U017), a take compared to a literal is starts_with ([#265](https://github.com/Emerging-Patterns/bolt/issues/265)) ([20d9de9](https://github.com/Emerging-Patterns/bolt/commit/20d9de9b339887d4ef39b5ca882aeb6aa11a8dc5)), closes [#260](https://github.com/Emerging-Patterns/bolt/issues/260)

## [1.24.0](https://github.com/Emerging-Patterns/bolt/compare/v1.23.0...v1.24.0) (2026-11-01)


### Features

* **rules:** concat sees an append passed through a continuation ([#262](https://github.com/Emerging-Patterns/bolt/issues/262)) ([c1d1e17](https://github.com/Emerging-Patterns/bolt/commit/c1d1e171861c47724a1aed44b6884e5feeb31f7e))

## [1.23.0](https://github.com/Emerging-Patterns/bolt/compare/v1.22.0...v1.23.0) (2026-11-01)


### Features

* **rules:** pick reports a search bound above its pick ([#261](https://github.com/Emerging-Patterns/bolt/issues/261)) ([7ecc841](https://github.com/Emerging-Patterns/bolt/commit/7ecc841e88f490a2f873fbb1a35711b6d2f590a5)), closes [#199](https://github.com/Emerging-Patterns/bolt/issues/199)

## [1.22.0](https://github.com/Emerging-Patterns/bolt/compare/v1.21.0...v1.22.0) (2026-11-01)


### ⚠ BREAKING CHANGES

* the `trace` rule (L005) is removed and its code retired. A bolt.bend that still has `def trace()` gets a `setting` finding (C011) for an unknown setting; delete it.

### Features

* one guarantee per file under laws/ and proofs/; drop trace and SPEC.md ([#257](https://github.com/Emerging-Patterns/bolt/issues/257)) ([48c08fe](https://github.com/Emerging-Patterns/bolt/commit/48c08fef206caa15aeeeeca0ed68d32364dde790))

## [1.21.0](https://github.com/Emerging-Patterns/bolt/compare/v1.20.0...v1.21.0) (2026-10-29)


### Features

* **scope:** run coverage and trace per package ([#255](https://github.com/Emerging-Patterns/bolt/issues/255)) ([9374588](https://github.com/Emerging-Patterns/bolt/commit/9374588ee37d0cb54fa7662825827eff0ac77a6e))

## [1.20.0](https://github.com/Emerging-Patterns/bolt/compare/v1.19.0...v1.20.0) (2026-10-29)


### Features

* **rules:** transcong (S006, opt-in), an Equal.trans an Equal.cong feeds ([#253](https://github.com/Emerging-Patterns/bolt/issues/253)) ([786aaef](https://github.com/Emerging-Patterns/bolt/commit/786aaef0599568a3d0e0ef11c31787e91f5a3816))

## [1.19.0](https://github.com/Emerging-Patterns/bolt/compare/v1.18.0...v1.19.0) (2026-10-25)


### Features

* **nix:** build and check on x86_64-linux, aarch64-linux and aarch64-darwin ([#249](https://github.com/Emerging-Patterns/bolt/issues/249)) ([dcd0b1c](https://github.com/Emerging-Patterns/bolt/commit/dcd0b1c5fc01baf4e094a2322074c4c320151b61))

## [1.18.0](https://github.com/Emerging-Patterns/bolt/compare/v1.17.0...v1.18.0) (2026-10-23)


### Bug Fixes

* **deps:** ezjson v1.2.0 ([#245](https://github.com/Emerging-Patterns/bolt/issues/245)) ([25b1dba](https://github.com/Emerging-Patterns/bolt/commit/25b1dba44b13bff58a2daa3ac700a32e56ec4adc))

## [1.17.0](https://github.com/Emerging-Patterns/bolt/compare/v1.16.0...v1.17.0) (2026-10-23)


### Bug Fixes

* **flake:** expose ez as packages.ez ([#239](https://github.com/Emerging-Patterns/bolt/issues/239)) ([561b5b0](https://github.com/Emerging-Patterns/bolt/commit/561b5b07c2f891d0e3773fa519221b443743adb2))

## [1.16.0](https://github.com/Emerging-Patterns/bolt/compare/v1.15.0...v1.16.0) (2026-10-23)


### ⚠ BREAKING CHANGES

* bolt needs Bend 2.0.38. Runtime options go between +RTS and -RTS: `bolt --gpu off ...` is now an unknown option, write `bolt +RTS --gpu off -RTS ...`. A plain `--` reaches bolt as end-of-options.

### Bug Fixes

* port bolt to Bend 2.0.38, shake v0.6.0 and snap v1.3.0 ([#236](https://github.com/Emerging-Patterns/bolt/issues/236)) ([1e2a1eb](https://github.com/Emerging-Patterns/bolt/commit/1e2a1eb0e566fad3f12695f2b69dc37e6ea39b2d))

## [1.15.0](https://github.com/Emerging-Patterns/bolt/compare/v1.14.0...v1.15.0) (2026-09-30)


### Performance Improvements

* index once in rewalk, bind.refresh and digest.laws_of ([#231](https://github.com/Emerging-Patterns/bolt/issues/231)) ([9994646](https://github.com/Emerging-Patterns/bolt/commit/9994646fadf6294c3006b746cea2b64521bee94a))

## [1.14.0](https://github.com/Emerging-Patterns/bolt/compare/v1.13.0...v1.14.0) (2026-09-30)


### Features

* **rules:** fromrev (U016), fewer false positives in six rules, retire argv ([#229](https://github.com/Emerging-Patterns/bolt/issues/229)) ([35271b9](https://github.com/Emerging-Patterns/bolt/commit/35271b9a06517f0d9d035c309d160aaf50f54d85))

## [1.13.0](https://github.com/Emerging-Patterns/bolt/compare/v1.12.0...v1.13.0) (2026-09-30)


### Features

* **rules:** scan (U013), argv (U014), thunk (U015) and setting (C011) ([#226](https://github.com/Emerging-Patterns/bolt/issues/226)) ([b60e9cd](https://github.com/Emerging-Patterns/bolt/commit/b60e9cd9f3cb96302f235ccfe5f096f66a46e429))

## [1.12.0](https://github.com/Emerging-Patterns/bolt/compare/v1.11.0...v1.12.0) (2026-09-30)


### Features

* **rules:** unsafe reaches foreign defs, fuel sees U32.to_nat, bend 2.0.34 text ([#219](https://github.com/Emerging-Patterns/bolt/issues/219)) ([639d1fe](https://github.com/Emerging-Patterns/bolt/commit/639d1fe38bfa0a1c1876ac705a91ee2f02d9399b))

## [1.11.0](https://github.com/Emerging-Patterns/bolt/compare/v1.10.0...v1.11.0) (2026-09-30)


### Bug Fixes

* **deps:** shake v0.4.0 ([#215](https://github.com/Emerging-Patterns/bolt/issues/215)) ([f41f84c](https://github.com/Emerging-Patterns/bolt/commit/f41f84c90098ad18a68a81094882045af2df239f))

## [1.10.0](https://github.com/Emerging-Patterns/bolt/compare/v1.9.0...v1.10.0) (2026-09-30)


### Features

* build, run and prove under bend 2.0.34; --help prints the usage page ([#214](https://github.com/Emerging-Patterns/bolt/issues/214)) ([c9c967e](https://github.com/Emerging-Patterns/bolt/commit/c9c967e892b062db3cd32f80b7fd21cf15b8ab34))


### Performance Improvements

* **lsp:** semantic tokens up to 10x faster, symbols up to 2.8x on large files ([#211](https://github.com/Emerging-Patterns/bolt/issues/211)) ([85f175d](https://github.com/Emerging-Patterns/bolt/commit/85f175dc80c2d02cb77231d6b010d6c599991df0))

## [1.9.0](https://github.com/Emerging-Patterns/bolt/compare/v1.8.0...v1.9.0) (2026-09-25)


### Bug Fixes

* build and run under bend 2.0.28 ([e1c8b27](https://github.com/Emerging-Patterns/bolt/commit/e1c8b27fd3767c6da966dd67f4c24e231477b87e))

## [1.8.0](https://github.com/Emerging-Patterns/bolt/compare/v1.7.0...v1.8.0) (2026-09-25)


### ⚠ BREAKING CHANGES

* **deps:** shake 0.2.0's parse rules reach bolt's command line: `bolt lint --version` (a root flag after a subcommand) is an unknown argument, `bolt help <word>` for a word that names no subcommand is an error instead of the root page, and `--version` given twice is refused.

### Bug Fixes

* **deps:** shake 0.2.0, ezjson 1.1.0 and snap 1.0.0 from the hub ([#204](https://github.com/Emerging-Patterns/bolt/issues/204)) ([19a7fbf](https://github.com/Emerging-Patterns/bolt/commit/19a7fbf4b9753666ef26f5f0f3af4b040b6ba92a))


### Performance Improvements

* bolt lint 10x faster over its own tree (208 s to 20 s) ([#201](https://github.com/Emerging-Patterns/bolt/issues/201)) ([6b687b0](https://github.com/Emerging-Patterns/bolt/commit/6b687b098a205f6dfce9e06f0392fdd13f9e7dd4))

## [1.7.0](https://github.com/Emerging-Patterns/bolt/compare/v1.6.2...v1.7.0) (2026-09-24)


### Features

* **noqa:** # noqa: CODE silences a finding; rule noqa (S005) reports a noqa that silences nothing (BOLT-OUT-7, BOLT-RULE-S005) ([#189](https://github.com/Emerging-Patterns/bolt/issues/189)) ([814b518](https://github.com/Emerging-Patterns/bolt/commit/814b51872d059f91482599722f9647e9572d958e))
* **noqa:** `# noqa: CODE` silences a finding; rule noqa (S005) reports a noqa that silences nothing (BOLT-OUT-7, BOLT-RULE-S005) ([814b518](https://github.com/Emerging-Patterns/bolt/commit/814b51872d059f91482599722f9647e9572d958e))

## [1.6.2](https://github.com/Emerging-Patterns/bolt/compare/v1.6.1...v1.6.2) (2026-09-24)


### Bug Fixes

* **pick,eager:** advise match, not bolt's internal Lazy helpers ([#187](https://github.com/Emerging-Patterns/bolt/issues/187)) ([9f287bb](https://github.com/Emerging-Patterns/bolt/commit/9f287bb3c0528a9e88dc9ca1fcfa070ea78f3e23))

## [1.6.1](https://github.com/Emerging-Patterns/bolt/compare/v1.6.0...v1.6.1) (2026-09-24)


### Bug Fixes

* **wrap:** a comment has no width and a string's line break is not a header break; prove wrap inert (BOLT-RULE-INERT, BOLT-RULE-S003) ([#184](https://github.com/Emerging-Patterns/bolt/issues/184)) ([3136736](https://github.com/Emerging-Patterns/bolt/commit/313673655d41a85348f1404a0dca7646c409fe33))
* **wrap:** comments have no width and only a newline token breaks a header; prove wrap inert (BOLT-RULE-INERT) ([3136736](https://github.com/Emerging-Patterns/bolt/commit/313673655d41a85348f1404a0dca7646c409fe33))

## [1.6.0](https://github.com/Emerging-Patterns/bolt/compare/v1.5.0...v1.6.0) (2026-09-24)


### Features

* **coverage:** a def is covered when a law reaches it through calls (BOLT-LAW-1) ([#175](https://github.com/Emerging-Patterns/bolt/issues/175)) ([354bc01](https://github.com/Emerging-Patterns/bolt/commit/354bc01b8bb23aa971d3957aeb78f6c9c70926ef))
* **coverage:** count coverage by reach through calls (BOLT-LAW-1) ([354bc01](https://github.com/Emerging-Patterns/bolt/commit/354bc01b8bb23aa971d3957aeb78f6c9c70926ef))


### Bug Fixes

* **arms:** read kn+p as a from-k-up arm only for a binder; prove arms, unused and hoist inert (BOLT-RULE-INERT, partial) ([#179](https://github.com/Emerging-Patterns/bolt/issues/179)) ([829071b](https://github.com/Emerging-Patterns/bolt/commit/829071b0387f29ab78f44fac055304e148942ca5))

## [1.5.0](https://github.com/Emerging-Patterns/bolt/compare/v1.4.2...v1.5.0) (2026-09-24)


### Features

* **concat:** see an append through parentheses and a let (BOLT-RULE-U004) ([#168](https://github.com/Emerging-Patterns/bolt/issues/168)) ([58278e1](https://github.com/Emerging-Patterns/bolt/commit/58278e1f3e97f511cc33284b1ece626be1ecd010)), closes [#96](https://github.com/Emerging-Patterns/bolt/issues/96)


### Bug Fixes

* **check:** place an imported file's error by the checked file's own names (BOLT-CHK-1) ([#173](https://github.com/Emerging-Patterns/bolt/issues/173)) ([d6c34f2](https://github.com/Emerging-Patterns/bolt/commit/d6c34f2605235cc37d77d158e58de82f5808798f))
* **rules:** a def with no type is a proof, exempt from the cost rules ([#169](https://github.com/Emerging-Patterns/bolt/issues/169)) ([57fe3a5](https://github.com/Emerging-Patterns/bolt/commit/57fe3a5cc59779dce6eec65bd547ba678d6592ba))

## [1.4.2](https://github.com/Emerging-Patterns/bolt/compare/v1.4.1...v1.4.2) (2026-09-23)


### Bug Fixes

* **rules:** reword finding messages in plain English ([afa5e01](https://github.com/Emerging-Patterns/bolt/commit/afa5e013d1c8415c25a1daf6d45fe1e778c2e96f))

## [1.4.1](https://github.com/Emerging-Patterns/bolt/compare/v1.4.0...v1.4.1) (2026-09-23)


### Bug Fixes

* **rules:** doc and param ignore string contents; prove 7 rules inert (BOLT-RULE-INERT, partial) ([#161](https://github.com/Emerging-Patterns/bolt/issues/161)) ([370167d](https://github.com/Emerging-Patterns/bolt/commit/370167d6ff3899112b1062bad9c1855e27e54f74))

## [1.4.0](https://github.com/Emerging-Patterns/bolt/compare/v1.3.4...v1.4.0) (2026-09-23)


### Features

* **lsp:** checker flag as data, binder-first navigation, negotiated position encoding (BOLT-LSP-5, BOLT-LSP-6, BOLT-LSP-7) ([#160](https://github.com/Emerging-Patterns/bolt/issues/160)) ([929ce75](https://github.com/Emerging-Patterns/bolt/commit/929ce75313358840e95e8d040754615977895b47))

## [1.3.4](https://github.com/Emerging-Patterns/bolt/compare/v1.3.3...v1.3.4) (2026-09-23)


### Bug Fixes

* **check:** treat a failure to run bend as an error (BOLT-CHK-1, partial) ([#156](https://github.com/Emerging-Patterns/bolt/issues/156)) ([f233165](https://github.com/Emerging-Patterns/bolt/commit/f233165bb5647d3de4608986e8893c8bab25d68d))

## [1.3.3](https://github.com/Emerging-Patterns/bolt/compare/v1.3.2...v1.3.3) (2026-09-23)


### Bug Fixes

* **lint:** a directory named on the command line is a read finding (BOLT-OUT-5) ([#147](https://github.com/Emerging-Patterns/bolt/issues/147)) ([02e623f](https://github.com/Emerging-Patterns/bolt/commit/02e623f7d440e6393c8600f0e50f1b0f4c70ac78))

## [1.3.2](https://github.com/Emerging-Patterns/bolt/compare/v1.3.1...v1.3.2) (2026-09-23)


### Bug Fixes

* **coverage:** read law mentions from the binder, and prove coverage (BOLT-LAW-1) ([#149](https://github.com/Emerging-Patterns/bolt/issues/149)) ([3c1e3b4](https://github.com/Emerging-Patterns/bolt/commit/3c1e3b490ca89be446340a1057a13b6dee400342))

## [1.3.1](https://github.com/Emerging-Patterns/bolt/compare/v1.3.0...v1.3.1) (2026-09-23)


### Bug Fixes

* **config:** resolve paths against the working directory (BOLT-CFG-4) ([#144](https://github.com/Emerging-Patterns/bolt/issues/144)) ([d72fcad](https://github.com/Emerging-Patterns/bolt/commit/d72fcad80d60f8c67aea1fed2bd67d18febbcd1d))

## [1.3.0](https://github.com/Emerging-Patterns/bolt/compare/v1.2.5...v1.3.0) (2026-09-23)


### Features

* **wrap:** report a return type off the ) line and a split header with no parameters ([#137](https://github.com/Emerging-Patterns/bolt/issues/137)) ([10904e0](https://github.com/Emerging-Patterns/bolt/commit/10904e0eacb67441762c0a070cf5c230c676ffb6))

## [1.2.5](https://github.com/Emerging-Patterns/bolt/compare/v1.2.4...v1.2.5) (2026-09-23)


### Bug Fixes

* **hoist:** read [v : T^d] as 2^d slots, and prove hoist (BOLT-RULE-U009) ([#132](https://github.com/Emerging-Patterns/bolt/issues/132)) ([ae67935](https://github.com/Emerging-Patterns/bolt/commit/ae679356c45033c2e2901a7f10b9fa495dba74d1))

## [1.2.4](https://github.com/Emerging-Patterns/bolt/compare/v1.2.3...v1.2.4) (2026-09-23)


### Bug Fixes

* **coverage:** a type is covered only when a law names it or a constructor, and prove coverage and unsafe over digests (BOLT-LAW-1, LAW-3 part) ([#130](https://github.com/Emerging-Patterns/bolt/issues/130)) ([0f76ed0](https://github.com/Emerging-Patterns/bolt/commit/0f76ed0ab627468af1f2d729b45bf84f8802a1ea))

## [1.2.3](https://github.com/Emerging-Patterns/bolt/compare/v1.2.2...v1.2.3) (2026-09-23)


### Bug Fixes

* **rules:** fuel and unit report exactly their rows, and prove both (BOLT-RULE-U006, U012) ([#127](https://github.com/Emerging-Patterns/bolt/issues/127)) ([29d7504](https://github.com/Emerging-Patterns/bolt/commit/29d750416af858722b091d254f785aee45bffde7))
* **wrap:** note the header's `:` with a flag, and prove wrap (BOLT-RULE-S003) ([#129](https://github.com/Emerging-Patterns/bolt/issues/129)) ([7317e87](https://github.com/Emerging-Patterns/bolt/commit/7317e87a36b44c3676161a45ea0bf61f65327a1d))

## [1.2.2](https://github.com/Emerging-Patterns/bolt/compare/v1.2.1...v1.2.2) (2026-09-23)


### Bug Fixes

* **rules:** pick reports a pick in another's condition, strict stops at =&gt;, and prove both (BOLT-RULE-C003, U002) ([#120](https://github.com/Emerging-Patterns/bolt/issues/120)) ([75f9c23](https://github.com/Emerging-Patterns/bolt/commit/75f9c23087fdaf54f962b5a5d855b754c12c97ca))

## [1.2.1](https://github.com/Emerging-Patterns/bolt/compare/v1.2.0...v1.2.1) (2026-09-23)


### Bug Fixes

* **strings:** an escaped quote does not close a string arm, and prove chars and strings (BOLT-RULE-C008, C009) ([#116](https://github.com/Emerging-Patterns/bolt/issues/116)) ([d18ff0b](https://github.com/Emerging-Patterns/bolt/commit/d18ff0bfb98b9d3a9c406218afe79fdc98b6ed9c))

## [1.2.0](https://github.com/Emerging-Patterns/bolt/compare/v1.1.1...v1.2.0) (2026-09-23)


### Features

* **trace:** let a pending requirement carry partial tagged laws ([#106](https://github.com/Emerging-Patterns/bolt/issues/106)) ([acbdafb](https://github.com/Emerging-Patterns/bolt/commit/acbdafb9ba7ad58e11f3e3b5b403a5a9d2dc3cb3))


### Bug Fixes

* **foreign:** honour `# lanes: native` only in the file's header ([#92](https://github.com/Emerging-Patterns/bolt/issues/92)) ([9612d64](https://github.com/Emerging-Patterns/bolt/commit/9612d64a2cd2d0ce9d999c61e169d2df446c9280))
* **put:** exempt every file that defines Map.put, and prove put (BOLT-RULE-C004) ([#74](https://github.com/Emerging-Patterns/bolt/issues/74)) ([6d84313](https://github.com/Emerging-Patterns/bolt/commit/6d843139742c3578329908b50a8f35528e352e0e))
* **shadow:** retire the rule, whose failure bend no longer has ([#94](https://github.com/Emerging-Patterns/bolt/issues/94)) ([60f481b](https://github.com/Emerging-Patterns/bolt/commit/60f481bc76df1d8bc7f70eb1aff173f929fab5d5))
* **strings:** skip an unterminated string arm instead of underflowing ([#83](https://github.com/Emerging-Patterns/bolt/issues/83)) ([1a4eb6a](https://github.com/Emerging-Patterns/bolt/commit/1a4eb6af6bd1d9a3398230f01600436918056d73))
* **syntax:** a string literal runs across newlines, as bend reads it ([#72](https://github.com/Emerging-Patterns/bolt/issues/72)) ([d483dbf](https://github.com/Emerging-Patterns/bolt/commit/d483dbfe1ccc285db813bd27f862d41db42af8f2))
* **trace:** check SPEC.md only when bolt lints the whole tree ([#91](https://github.com/Emerging-Patterns/bolt/issues/91)) ([219c89f](https://github.com/Emerging-Patterns/bolt/commit/219c89ff1d755c0473787a16d66234a7b43cd976))

## [1.1.1](https://github.com/Emerging-Patterns/bolt/compare/v1.1.0...v1.1.1) (2026-09-23)


### Bug Fixes

* **arms:** count Succ{_} as 1n+p, as Succ{p} is ([#71](https://github.com/Emerging-Patterns/bolt/issues/71)) ([ec1cf42](https://github.com/Emerging-Patterns/bolt/commit/ec1cf424fa5ad8e97a98593eee4eb9e016d705a1))
* **concat:** report an append only in the parameter's own slot ([#75](https://github.com/Emerging-Patterns/bolt/issues/75)) ([43ea356](https://github.com/Emerging-Patterns/bolt/commit/43ea3561d4d4178aaff280ad5c62c4c6c7406daa))
* **doc:** a block of bare `#` lines counts as a comment block ([#80](https://github.com/Emerging-Patterns/bolt/issues/80)) ([d3f5d01](https://github.com/Emerging-Patterns/bolt/commit/d3f5d0120d0b583cad92d5bd4ca0c4700cbbd4cd))
* **eager:** a lambda clears the branch only for its own body ([#70](https://github.com/Emerging-Patterns/bolt/issues/70)) ([8eed03f](https://github.com/Emerging-Patterns/bolt/commit/8eed03f309d4b2dc5e3b20fee9b4ecac9918d559))
* **hoist:** a user-def build counts only when its body is a wide table ([#76](https://github.com/Emerging-Patterns/bolt/issues/76)) ([cbd8cc3](https://github.com/Emerging-Patterns/bolt/commit/cbd8cc34794933149b3c15a37960bba03dc8cb3f))
* **hole:** report every TODO hole bend counts, `? TODO` included ([#69](https://github.com/Emerging-Patterns/bolt/issues/69)) ([2e9fb33](https://github.com/Emerging-Patterns/bolt/commit/2e9fb33726e8d6a2db2b5cd8496c65b558843271))
* **law:** name the L001 rule coverage so a bolt.bend can set it ([#84](https://github.com/Emerging-Patterns/bolt/issues/84)) ([aba328e](https://github.com/Emerging-Patterns/bolt/commit/aba328e1b2a0d6c091aeeff3c2cb55d083e6decb))
* **pick:** report real self-calls once, outside laws and proofs ([#63](https://github.com/Emerging-Patterns/bolt/issues/63)) ([06e02ff](https://github.com/Emerging-Patterns/bolt/commit/06e02ff98e31084745a5daada44cac687135dc4e))
* **rewalk:** a let between two calls makes them different walks ([#86](https://github.com/Emerging-Patterns/bolt/issues/86)) ([18b6852](https://github.com/Emerging-Patterns/bolt/commit/18b68520c7738ce1e98d2dbe55904ebeabfd8381))
* **ring:** every scrutinee is input, and the window keeps its slot ([#82](https://github.com/Emerging-Patterns/bolt/issues/82)) ([76ce8b8](https://github.com/Emerging-Patterns/bolt/commit/76ce8b8e0874ab5b1cb78ec2ffdb24ec5fd73c8f))
* **strict:** a self-call in a lambda body is not an eager operand ([#65](https://github.com/Emerging-Patterns/bolt/issues/65)) ([52be422](https://github.com/Emerging-Patterns/bolt/commit/52be4227dd184b8ee30554323d5abb9adb377851))
* **syntax:** a `>` inside brackets within `<..>` does not close the angle group ([#79](https://github.com/Emerging-Patterns/bolt/issues/79)) ([f810b29](https://github.com/Emerging-Patterns/bolt/commit/f810b29c3f34fb59915743a34d77bc39f9bd65ff))
* **table:** a let is the table only where its binding is in scope ([#66](https://github.com/Emerging-Patterns/bolt/issues/66)) ([9abace6](https://github.com/Emerging-Patterns/bolt/commit/9abace65b965f3f5cddb7642d2d94ae9701b318d))
* **twice:** decide recursion by a real self-call ([#77](https://github.com/Emerging-Patterns/bolt/issues/77)) ([552f9e6](https://github.com/Emerging-Patterns/bolt/commit/552f9e617e41970e9ce848d76075ed403a907682))
* **unit:** an operator before `(` is checked, not taken for a call ([#90](https://github.com/Emerging-Patterns/bolt/issues/90)) ([9cfdd4d](https://github.com/Emerging-Patterns/bolt/commit/9cfdd4d11f066a6a8b952140bd83d3b5c7dc0e3a))
* **unused:** exempt every parameter of a wrapped foreign def ([#62](https://github.com/Emerging-Patterns/bolt/issues/62)) ([2f3b387](https://github.com/Emerging-Patterns/bolt/commit/2f3b387ec5f7b86ca178dccce42830e5502b603b))
* **wrap:** a header ends at its `:` before a comment, and `)` gets its own line ([#89](https://github.com/Emerging-Patterns/bolt/issues/89)) ([15fef36](https://github.com/Emerging-Patterns/bolt/commit/15fef3672735aa24a5d6c346474b278b7e9308d2))

## [1.1.0](https://github.com/Emerging-Patterns/bolt/compare/v1.0.3...v1.1.0) (2026-09-23)


### Features

* **trace:** SPEC.md and the laws agree (L005) ([#55](https://github.com/Emerging-Patterns/bolt/issues/55)) ([21f7e27](https://github.com/Emerging-Patterns/bolt/commit/21f7e271608e3b89dfcf28834e68f601383b1261))

## [1.0.3](https://github.com/Emerging-Patterns/bolt/compare/v1.0.2...v1.0.3) (2026-09-23)


### Bug Fixes

* **law:** grade every file of a run that states laws ([#54](https://github.com/Emerging-Patterns/bolt/issues/54)) ([e14c405](https://github.com/Emerging-Patterns/bolt/commit/e14c405ebb1249f2a3776f2afa6791dff7cf8e7e))

## [1.0.2](https://github.com/Emerging-Patterns/bolt/compare/v1.0.1...v1.0.2) (2026-09-23)


### Bug Fixes

* **law:** only a quantified law in a LAWS.bend covers a def ([#52](https://github.com/Emerging-Patterns/bolt/issues/52)) ([88895f0](https://github.com/Emerging-Patterns/bolt/commit/88895f03f81e7d1e88680b3604c5e60a4601910a))

## [1.0.1](https://github.com/Emerging-Patterns/bolt/compare/v1.0.0...v1.0.1) (2026-09-22)


### Bug Fixes

* **scope:** a test is a path with a tests segment, not a substring ([#50](https://github.com/Emerging-Patterns/bolt/issues/50)) ([300c28b](https://github.com/Emerging-Patterns/bolt/commit/300c28b4ac6ddecf82953c58ad035ab1b79a7d1d))

## [1.0.0](https://github.com/Emerging-Patterns/bolt/compare/v0.9.0...v1.0.0) (2026-09-22)


### ⚠ BREAKING CHANGES

* **closed:** `closed` reports closed equalities, IO included, and a `# toward` line no longer exempts a law. `quantify` is gone; a bolt.bend that names it sets nothing.

### Features

* **closed:** delete every closed law and make closed strict ([#48](https://github.com/Emerging-Patterns/bolt/issues/48)) ([66626db](https://github.com/Emerging-Patterns/bolt/commit/66626db257780ac4347ae4f83897dd8b95167ad8))

## [0.9.0](https://github.com/Emerging-Patterns/bolt/compare/v0.8.1...v0.9.0) (2026-09-22)


### Features

* **quantify:** opt-in strict mode of the closed rule (L004) ([#42](https://github.com/Emerging-Patterns/bolt/issues/42)) ([a5b21f7](https://github.com/Emerging-Patterns/bolt/commit/a5b21f74b5c8851d6b434105f8c15d40c04f9a80))

## [0.8.1](https://github.com/Emerging-Patterns/bolt/compare/v0.8.0...v0.8.1) (2026-09-22)


### Bug Fixes

* **law:** pin down that IO is no exemption, with fixtures ([#40](https://github.com/Emerging-Patterns/bolt/issues/40)) ([dfaf9a4](https://github.com/Emerging-Patterns/bolt/commit/dfaf9a4bd7d27771bd8d2539682ace1926947078))

## [0.8.0](https://github.com/Emerging-Patterns/bolt/compare/v0.7.0...v0.8.0) (2026-09-22)


### Features

* suspicious table, hoist, ring, rewalk, unit ([#38](https://github.com/Emerging-Patterns/bolt/issues/38)) ([381b6e5](https://github.com/Emerging-Patterns/bolt/commit/381b6e57b3d42b728f3900cd3c0ce6423152e681))

## [0.7.0](https://github.com/Emerging-Patterns/bolt/compare/v0.6.0...v0.7.0) (2026-09-22)


### Features

* numbered lint codes and clearer diagnostics ([#36](https://github.com/Emerging-Patterns/bolt/issues/36)) ([891f468](https://github.com/Emerging-Patterns/bolt/commit/891f468377221ee3a2a0e3839a01ab6a39a46cd3))

## [0.6.0](https://github.com/Emerging-Patterns/bolt/compare/v0.5.0...v0.6.0) (2026-09-22)


### Features

* flag jammed multi-line def header wraps ([#34](https://github.com/Emerging-Patterns/bolt/issues/34)) ([b9e1729](https://github.com/Emerging-Patterns/bolt/commit/b9e1729262558faf72812d1fcef616af7637f7c0))

## [0.5.0](https://github.com/Emerging-Patterns/bolt/compare/v0.4.0...v0.5.0) (2026-09-22)


### ⚠ Behavior changes

* `law` no longer exempts a file whose text contains "IO" ([#10](https://github.com/Emerging-Patterns/bolt/issues/10)). Up to v0.4.0 any mention of `IO` -- an IO def, or the word in a comment or a string -- took the whole module out of law coverage. Every def is now graded by its name and its file's path alone: IO-returning defs, the pure defs beside them, and pure modules that merely mention IO. A project that passed `law` on v0.4.0 can get new `law` (L001) findings; name those defs in a law, or set `law` (or `laws`) to `"warn"` or `"off"` in its `bolt.bend`.

### Features

* wrap def headers over 120 and ban one-letter params ([#30](https://github.com/Emerging-Patterns/bolt/issues/30)) ([a074e30](https://github.com/Emerging-Patterns/bolt/commit/a074e30d42c17c19e7e456a195cf91d765196e3d))
