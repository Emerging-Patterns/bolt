#!/usr/bin/env bash
# Builds the binaries people run (not the gate's): bin/bend-lsp and
# bin/bolt.bin (behind the bolt/bolt script), linked into
# ~/.local/bin. Neither has a `!` call, so the system clang (14+) will do.
set -eu
cd "$(dirname "$0")"
mkdir -p bin "$HOME/.local/bin"
bend lsp/main.bend -o bin/bend-lsp
bend bolt/main.bend -o bin/bolt.bin
ln -sfn "$PWD/bin/bend-lsp" "$HOME/.local/bin/bend-lsp"
ln -sfn "$PWD/bolt/bolt" "$HOME/.local/bin/bolt"
echo "built bin/bend-lsp and bin/bolt.bin -> ~/.local/bin/{bend-lsp,bolt}"
