#!/usr/bin/env bash
# Builds the binaries people run (not the gate's): bin/bend-lsp and
# bin/bend-lint.bin (behind the lint/bend-lint script), linked into
# ~/.local/bin. Neither has a `!` call, so the system clang (14+) will do.
set -eu
cd "$(dirname "$0")"
mkdir -p bin "$HOME/.local/bin"
bend lsp/main.bend -o bin/bend-lsp
bend lint/main.bend -o bin/bend-lint.bin
ln -sfn "$PWD/bin/bend-lsp" "$HOME/.local/bin/bend-lsp"
ln -sfn "$PWD/lint/bend-lint" "$HOME/.local/bin/bend-lint"
echo "built bin/bend-lsp and bin/bend-lint.bin -> ~/.local/bin/{bend-lsp,bend-lint}"
