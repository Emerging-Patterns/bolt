#!/usr/bin/env bash
# The gate: every project's laws hold, and every test prints its `#|` lines on
# each lane: JS and native (CPU; a GPU run is 2-5x slower and is not gated).
#   ./gate.sh            all lanes (native lanes run inside `nix develop`)
#   ./gate.sh --js-only  skip the native lanes (and the linter, a native binary)
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
# the C toolchain, built and run in the sandbox (flake.nix)
if [ $js_only = 0 ]; then
  check "nix flake check" "" "$(nix flake check 2>&1 | grep -v '^warning: Git tree' | grep -i 'error' || true)"
fi
for dir in */ */*/; do
  dir=${dir%/}
  [ -d "$dir/tests" ] || [ -f "$dir/PROOF.bend" ] || continue
  if [ -f "$dir/PROOF.bend" ]; then
    check "$dir/PROOF.bend" "All terms check." "$(bend "$dir/PROOF.bend" 2>&1)"
  fi
  for t in "$dir"/tests/*.bend; do
    [ -f "$t" ] || continue
    want=$(sed -n 's/^#|//p' "$t")
    # a test headed `# lanes: native` is too big for the JS lane's stack
    native_only=0; grep -q '^# lanes: native' "$t" && native_only=1
    if [ $native_only = 0 ]; then
      check "$t (js)" "$want" "$(bend "$t" 2>&1)"
    fi
    [ $js_only = 1 ] && continue
    bin="$dir/.gate/$(basename "$t" .bend)"
    mkdir -p "$dir/.gate"
    if ! built=$(bend "$t" -o "$bin" 2>&1); then
      check "$t (build)" "" "$built"; continue
    fi
    check "$t (cpu)" "$want" "$("$bin" --gpu off 2>&1)"
  done
done
# the one binary: the server as an editor runs it (spawned by node, over
# sockets), and bolt over the repo itself
if [ $js_only = 0 ]; then
  mkdir -p bin
  if built=$(bend bolt/main.bend -o bin/bolt.bin 2>&1); then
    if command -v node >/dev/null; then
      check "bolt/lsp/tests/spawn.js" "ok" "$(node bolt/lsp/tests/spawn.js bin/bolt.bin 2>&1)"
    fi
    check "bolt (repo)" "clean" "$(bolt/bolt 2>&1)"
  else
    check "bolt/main.bend (build)" "" "$built"
  fi
fi
echo "PASS: $pass / $total"
[ "$pass" = "$total" ]
