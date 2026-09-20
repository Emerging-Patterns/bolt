#!/usr/bin/env bash
# Problem 1 matrix: split check / C-emit / clang, and localize by module.
# Every run is capped and sequential. Usage: matrix.sh [capGB]
cd "$(dirname "$0")/.."
cap=${1:-32}
M=.probe/meas.sh
T=$(mktemp -d)
echo "== phase split on the whole program (bolt/main.bend) =="
$M $cap "main -> .js  (check+JS)"  bend bolt/main.bend -o $T/m.js
$M $cap "main -> .c   (check+Cemit)" bend bolt/main.bend -o $T/m.c
$M $cap "main -> bin  (full native)" bend bolt/main.bend -o $T/m.bin
echo
echo "== the floor: Base only =="
$M $cap "floor -> .js" bend .probe/p_floor.bend -o $T/f.js
$M $cap "floor -> .c"  bend .probe/p_floor.bend -o $T/f.c
$M $cap "floor -> bin" bend .probe/p_floor.bend -o $T/f.bin
echo
echo "== main.bend's three arms, native =="
$M $cap "lint arm  -> bin"  bend .probe/p_lint.bend  -o $T/lint.bin
$M $cap "check arm -> bin"  bend .probe/p_check.bend -o $T/check.bin
$M $cap "lsp arm   -> bin"  bend .probe/p_lsp.bend   -o $T/lsp.bin
echo
echo "== C emitted, by entry point (capped) =="
for e in .probe/p_floor .probe/p_check .probe/p_lint .probe/p_lsp bolt/main; do
  n=$(basename $e)
  [ -f $T/$n.c ] || $M $cap "$n -> .c" bend $e.bend -o $T/$n.c
done
for f in $T/*.c; do
  printf '%-12s %12s bytes of C  %8s lines\n' "$(basename $f .c)" "$(stat -c%s $f)" "$(wc -l < $f)"
done
echo "artifacts in $T"
