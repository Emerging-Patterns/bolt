# Changelog

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
