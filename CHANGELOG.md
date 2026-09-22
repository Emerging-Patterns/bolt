# Changelog

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
