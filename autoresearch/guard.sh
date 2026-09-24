#!/bin/bash
# autoresearch Guard: every PROOF.bend checks, and the findings of the last
# verify run equal the baseline's (same lines, same summary).
set -uo pipefail
root=$(git rev-parse --show-toplevel)
work=${AR_WORK:-/tmp/ar-work}
cd "$work/tree"
for p in $(find . -name PROOF.bend -not -path './.git/*' | sort); do
  r=$(bend "$p" --check-only 2>&1 | tail -1)
  [ "$r" = "All terms check." ] || { echo "FAIL proof $p: $r"; exit 1; }
done
# findings compare without line:col, so code moving down a file is no change
norm() { sed -E 's/^([^:]*):[0-9]+:[0-9]+:/\1:/' "$1"; }
diff <(norm "$root/autoresearch/loop-260924-2130/baseline-findings.txt") <(norm "$work/findings.txt") >/dev/null \
  || { echo "FAIL findings differ"; diff <(norm "$root/autoresearch/loop-260924-2130/baseline-findings.txt") <(norm "$work/findings.txt") | head; exit 1; }
echo pass
