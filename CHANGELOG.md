# Changelog

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
