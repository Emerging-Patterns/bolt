#!/bin/bash
# autoresearch Verify: build bolt from the committed tree and time `bolt`
# over that tree (minus autoresearch/). Prints seconds. Env: BEND_LIB, CC.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
work=${AR_WORK:-/tmp/ar-work}
rm -rf "${work:?}/tree"; mkdir -p "$work/tree"
git -C "$root" archive HEAD | tar -x -C "$work/tree"
rm -rf "${work:?}/tree/autoresearch"
cd "$work/tree"
bend bolt/main.bend -o "$work/bolt.bin" >"$work/build.log" 2>&1
s=$(date +%s.%N)
"$work/bolt.bin" --gpu off >"$work/findings.txt" 2>&1 || true
e=$(date +%s.%N)
echo "$e - $s" | bc
