#!/usr/bin/env bash
# The gate: every project's laws hold, and every test prints its `#|` lines on
# each lane: JS, native CPU, and (when the test has a `!` call) the GPU.
#   ./gate.sh            all lanes (native lanes run inside `nix develop`)
#   ./gate.sh --js-only  skip the native lanes
set -u
cd "$(dirname "$0")"
js_only=0; [ "${1:-}" = "--js-only" ] && js_only=1
if [ $js_only = 0 ] && ! command -v bend-cc >/dev/null; then
  exec nix develop -c "$0" "$@"
fi
export CC=bend-cc
pass=0; total=0
check() { # name, expected, observed
  total=$((total + 1))
  if [ "$2" = "$3" ]; then
    pass=$((pass + 1))
  else
    echo "FAIL: $1"; diff <(echo "$2") <(echo "$3") | sed 's/^/  /'
  fi
}
for proof in */PROOF.bend; do
  [ -f "$proof" ] || continue
  dir=$(dirname "$proof")
  check "$proof" "All terms check." "$(bend "$proof" 2>&1)"
  for t in "$dir"/tests/*.bend; do
    [ -f "$t" ] || continue
    want=$(sed -n 's/^#|//p' "$t")
    check "$t (js)" "$want" "$(bend "$t" 2>&1)"
    [ $js_only = 1 ] && continue
    bin="$dir/.gate/$(basename "$t" .bend)"
    mkdir -p "$dir/.gate"
    if ! built=$(bend "$t" -o "$bin" 2>&1); then
      check "$t (build)" "" "$built"; continue
    fi
    check "$t (cpu)" "$want" "$("$bin" --gpu off 2>&1)"
    if grep -q '!(' "$t"; then
      check "$t (gpu)" "$want" "$("$bin" --gpu 1GB 2>&1)"
    fi
  done
done
echo "PASS: $pass / $total"
[ "$pass" = "$total" ]
