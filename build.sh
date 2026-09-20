#!/usr/bin/env bash
# Builds the binary people run (not the gate's): bin/bolt.bin, linked into
# ~/.local/bin as `bolt` (`bolt`, `bolt check file..`, `bolt lsp`). It has no
# `!` call, so the system clang (14+) will do.
#
# The compile peaks near 8 GB. bend prints "All terms
# check." before it emits any C, so a build the kernel kills for memory reads
# exactly like one that worked, minus the binary -- hence the check at the end.
set -eu
cd "$(dirname "$0")"
mkdir -p bin "$HOME/.local/bin"
rm -f bin/bolt.bin
st=0; bend bolt/main.bend -o bin/bolt.bin || st=$?
if [ ! -x bin/bolt.bin ]; then
  echo
  echo "build.sh: bend exited $st and left no bin/bolt.bin."
  if [ "$st" = 137 ] || [ "$st" = 139 ]; then
    have=$(awk '/MemAvailable/{printf "%.1f", $2/1048576}' /proc/meminfo 2>/dev/null || echo '?')
    echo "build.sh: that is the out-of-memory kill. Compiling bolt needs about"
    echo "build.sh: 8 GB; this machine has ${have} GB free."
  fi
  exit "${st:-1}"
fi
ln -sfn "$PWD/bin/bolt.bin" "$HOME/.local/bin/bolt"
echo "built bin/bolt.bin -> ~/.local/bin/bolt"
