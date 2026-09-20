# run

One effect: a program run with its arguments.

`bolt` itself runs no program but the checker (`bolt/lsp/checker/exec.*`), and
nothing under `bolt/` imports this. It exists for the end-to-end tests in the
repo's top-level `tests/`, which have to drive the real `bend`, the real `node`
and the real `nix`, because those are the only things that can answer what
those tests ask: that bolt still builds with bare `bend`, that the server
survives being spawned by node over sockets, and that the packaged build and
its C toolchain still work.

`exec` takes the program and its arguments as a list, hands them to `execvp` as
a vector with no shell between, and answers the exit status on its own first
line followed by stdout and stderr together. `R.code(out)` reads the status back
and `R.text(out)` the output.

This is an effect, not pure: it forks and waits. It may not sit under a `!`
call, and it has no place on the GPU lane.
