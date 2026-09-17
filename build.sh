#!/usr/bin/env bash
# Builds the binaries people run (not the gate's): bin/bend-lsp, linked into
# ~/.local/bin. The server has no `!` call, so the system clang (14+) will do.
set -eu
cd "$(dirname "$0")"
mkdir -p bin "$HOME/.local/bin"
bend lsp/main.bend -o bin/bend-lsp
ln -sfn "$PWD/bin/bend-lsp" "$HOME/.local/bin/bend-lsp"
echo "built bin/bend-lsp -> ~/.local/bin/bend-lsp"
