#!/usr/bin/env bash
# Builds the binary people run (not the gate's): bin/bolt.bin, behind the
# bolt/bolt script, linked into ~/.local/bin as `bolt` (`bolt`, `bolt check`,
# `bolt lsp`). It has no `!` call, so the system clang (14+) will do.
set -eu
cd "$(dirname "$0")"
mkdir -p bin "$HOME/.local/bin"
bend bolt/main.bend -o bin/bolt.bin
ln -sfn "$PWD/bolt/bolt" "$HOME/.local/bin/bolt"
echo "built bin/bolt.bin -> ~/.local/bin/bolt"
