#!/usr/bin/env bash
# The gate: every project's laws hold, and every test prints its `#|` lines on
# each lane: JS and native (CPU; a GPU run is 2-5x slower and is not gated).
#   ./gate.sh            all lanes (native lanes run inside `nix develop`)
#   ./gate.sh --js-only  skip the native lanes (and the linter, a native binary)
#   ./gate.sh --full     run every unit, cached or not
#
# Three things keep it off the host's OOM killer and off the wall clock.
#
# One `bend` at a time, each capped. `bend` compiling to native costs
# gigabytes, and the peak follows the import closure, not the file: a project
# whose tests reach the whole program peaks near 8.4 GB here, where the same
# files on the JS lane peak near 2.5 GB. The concurrency comes from that
# measured peak against the free RAM, never from the core count, and at those
# sizes it is one. Every run sits in a memory-capped scope, so a job that runs
# away is killed as a job, with a legible message, rather than taking the host
# with it.
#
# One binary a project. `bend` has no incremental compile, so every build pays
# for the whole closure, and a project's tests import nearly the same set --
# bolt/lsp's ten tests each reach 54 to 57 of the same files. So the gate
# writes <project>/.gate/all.bend, which imports every test of the project and
# calls each `main` behind an `@@gate@@ <path>` line, and compiles that once.
# Each test is still its own check against its own `#|` trailer; only the
# compiling is shared.
#
# Nothing run twice. A lane's result is cached under .gate/cache against the
# content of every file it reads -- each test, everything those tests import,
# and the toolchain that would compile them. Touch a file and every lane whose
# closure holds it runs again; touch none and the gate re-does only what it
# cannot key, which is `nix flake check` and the repo lint.
set -u
cd "$(dirname "$0")"

js_only=0; full=0
for a in "$@"; do
  case $a in
    --js-only) js_only=1 ;;
    --full) full=1 ;;
    *) echo "gate: no such option: $a" >&2; exit 2 ;;
  esac
done
if [ $js_only = 0 ] && ! command -v bend-cc >/dev/null; then
  exec nix develop -c "$0" "$@"
fi
export CC=bend-cc
mark='@@gate@@ '
pass=0; total=0; skipped=0

check() { # name, expected, observed
  total=$((total + 1))
  if [ "$2" = "$3" ]; then
    pass=$((pass + 1))
  else
    echo "FAIL: $1"; diff <(echo "$2") <(echo "$3") | sed 's/^/  /'
  fi
}

# --- the caps --------------------------------------------------------------
# the measured peaks, rounded up: a whole-program native build peaks near
# 8.4 GB here, the same files on the JS lane near 2.5 GB
cap_js=${BOLT_GATE_CAP_JS:-6}
cap_native=${BOLT_GATE_CAP_NATIVE:-16}
capped=1
systemd-run --user --scope -q -p MemoryMax=1G true 2>/dev/null || capped=0
[ $capped = 0 ] && echo "gate: no systemd user scope here, so nothing caps a job; a build that runs away takes the host with it" >&2
# one command, inside a scope of <gb> GB, with swap off so the cap bites
cap_run() { local gb=$1; shift
  if [ $capped = 1 ]; then
    systemd-run --user --scope -q -p MemoryMax=${gb}G -p MemorySwapMax=0 nice -n 5 "$@"
  else
    nice -n 5 "$@"
  fi
}
run_raw() { local gb=$1; shift; local out st
  out=$(cap_run "$gb" "$@" 2>&1); st=$?
  # the scope kills at MemoryMax, and bend dies after printing "All terms
  # check.", so without this a build out of memory reads as one that worked
  [ $st = 137 ] && out="$out
gate: killed at the ${gb} GB cap; raise BOLT_GATE_CAP_NATIVE or BOLT_GATE_CAP_JS to retry"
  printf '%s\n' "$out"
  return $st
}
# bend 2.0.16 reports its unsafe annotations on stderr after the check; that is
# not the program's output, and a test's `#|` lines do not carry it. A
# PROOF.bend is the exception -- that line is its whole answer -- so it takes
# run_raw and normalises the count away itself.
run() { local out st; out=$(run_raw "$@"); st=$?
  printf '%s\n' "$out" | grep -v '^All terms check, with [0-9]* unsafe annotation'
  return $st
}

# --- what a lane reads, for its cache key ----------------------------------
# a .bend file reads itself, every .bend it reaches through a relative
# `import`, and the .c and .js bodies of its foreign defs. Memoised per file.
declare -A deps_of=()
deps() { local f=$1
  if [ -z "${deps_of[$f]+set}" ]; then
    local dir d seg segs out list=""
    dir=$(dirname "$f")
    while read -r d; do
      [ -z "$d" ] && continue
      out=(); IFS=/ read -ra segs <<<"$dir/$d"
      for seg in "${segs[@]}"; do
        case $seg in
          ''|.) ;;
          ..) [ ${#out[@]} -gt 0 ] && unset 'out[-1]' ;;
          *) out+=("$seg") ;;
        esac
      done
      list+="$( IFS=/; printf '%s' "${out[*]}" ) "
    done < <(sed -n 's/^[[:space:]]*import[[:space:]]*"\([^"]*\)".*/\1/p
                     s/^import[[:space:]]\{1,\}\(\.[^[:space:]]*\.bend\).*/\1/p' "$f")
    deps_of[$f]=$list
  fi
  printf '%s' "${deps_of[$f]}"
}
closure() { local -A seen=(); local queue=("$@") f d
  while [ ${#queue[@]} -gt 0 ]; do
    f=${queue[0]}; queue=("${queue[@]:1}")
    [ -n "${seen[$f]:-}" ] && continue
    [ -f "$f" ] || continue
    seen[$f]=1
    for d in $(deps "$f"); do queue+=("$d"); done
  done
  printf '%s\n' "${!seen[@]}" | sort
}
# a new bend, or a new clang, invalidates every key
tool_key=$( { bend --version; readlink -f "$(command -v bend-cc || echo -)"; } 2>/dev/null | sha256sum | cut -c1-16)
cache=.gate/cache; mkdir -p "$cache"
key() { local lane=$1; shift
  { echo "$lane $tool_key"; closure "$@" | tr '\n' '\0' | xargs -0 -r sha256sum; } | sha256sum | cut -c1-32
}

# --- one binary a project --------------------------------------------------
aggregate() { # file to write, project dir, tests..
  local out=$1 dir=$2; shift 2
  local t i
  { echo "# Written by gate.sh, and read by nothing else: every test of $dir in"
    echo "# one binary, so bend's whole-program compile is paid once for the"
    echo "# project instead of once a test. Each test still answers for its own"
    echo "# \`#|\` trailer; the gate splits this run's output on the marker lines."
    echo "import Base"
    i=0; for t in "$@"; do i=$((i + 1)); echo "import ../tests/$(basename "$t") as T$i"; done
    echo
    echo "def main() -> IO(Unit):"
    echo "  do IO<Unit>:"
    i=0; for t in "$@"; do i=$((i + 1))
      echo "    IO.print(\"$mark$t\")"
      echo "    T$i.main()"
    done
  } > "$out"
}
# each test's slice of an aggregate's output, against its own trailer
check_sections() { # lane, output, tests..
  local lane=$1 out=$2; shift 2
  local t want got
  for t in "$@"; do
    want=$(sed -n 's/^#|//p' "$t")
    got=$(printf '%s\n' "$out" | awk -v m="$mark$t" -v p="$mark" \
      'index($0, p) == 1 { on = ($0 == m); next } on { print }')
    check "$t ($lane)" "$want" "$got"
  done
}
# a project's tests, on one lane, as one compile
lane() { # lane(js|cpu), project dir, tests..
  local lane=$1 dir=$2; shift 2
  local src out st k t before
  [ $# -gt 0 ] || return 0
  case $lane in js) src=$dir/.gate/all.js.bend ;; *) src=$dir/.gate/all.bend ;; esac
  aggregate "$src" "$dir" "$@"
  k=$(key "$lane" "$@")
  if [ $full = 0 ] && [ -f "$cache/$k" ]; then
    for t in "$@"; do total=$((total + 1)); pass=$((pass + 1)); skipped=$((skipped + 1)); done
    return 0
  fi
  if [ "$lane" = js ]; then
    out=$(run $cap_js bend "$src"); st=$?
  else
    out=$(run $cap_native bend "$src" -o "$dir/.gate/all.bin"); st=$?
    if [ $st = 0 ] && [ -x "$dir/.gate/all.bin" ]; then out=$("$dir/.gate/all.bin" --gpu off 2>&1); fi
  fi
  # a file that runs as a main can still fail to import (AGENTS.md, the
  # binder-vs-def trap), and then no test of the project has been answered for
  if ! printf '%s\n' "$out" | grep -q "^$mark"; then
    for t in "$@"; do check "$t ($lane)" "$(sed -n 's/^#|//p' "$t")" ""; done
    echo "  $dir ($lane): the one binary did not build or did not start, so no test of it ran"
    printf '%s\n' "$out" | sed 's/^/    /' | head -12
    return 0
  fi
  before=$pass
  check_sections "$lane" "$out" "$@"
  [ $((pass - before)) = $# ] && : > "$cache/$k"
  return 0
}

# --- the gate --------------------------------------------------------------
started=$(date +%s)
# The C toolchain, built and run in the sandbox (flake.nix). This is the one
# job the gate cannot cap: with nix-daemon running, the build happens in
# nix-daemon.service, not in any scope this script can make, and it builds
# bolt the packaged way, so it is a ~19 GB compile of its own. Capping it is a
# machine-level fix (a MemoryMax drop-in on nix-daemon.service), not one this
# repo can make.
if [ $js_only = 0 ]; then
  check "nix flake check" "" "$(nix flake check 2>&1 | grep -v '^warning: Git tree' | grep -i 'error' || true)"
fi
for dir in */ */*/; do
  dir=${dir%/}
  [ -d "$dir/tests" ] || [ -f "$dir/PROOF.bend" ] || continue
  mkdir -p "$dir/.gate"
  if [ -f "$dir/PROOF.bend" ]; then
    k=$(key proof "$dir/PROOF.bend")
    if [ $full = 0 ] && [ -f "$cache/$k" ]; then
      total=$((total + 1)); pass=$((pass + 1)); skipped=$((skipped + 1))
    else
      before=$pass
      check "$dir/PROOF.bend" "All terms check." \
        "$(run_raw $cap_js bend "$dir/PROOF.bend" | sed 's/^All terms check, with [0-9]* unsafe annotations\{0,1\}\.$/All terms check./')"
      [ $pass -gt $before ] && : > "$cache/$k"
    fi
  fi
  [ -d "$dir/tests" ] || continue
  all=(); js=()
  for t in "$dir"/tests/*.bend; do
    [ -f "$t" ] || continue
    all+=("$t")
    # a test headed `# lanes: native` is too big for the JS lane's stack
    grep -q '^# lanes: native' "$t" || js+=("$t")
  done
  [ ${#all[@]} -gt 0 ] || continue
  lane js "$dir" ${js[@]+"${js[@]}"}
  [ $js_only = 1 ] && continue
  lane cpu "$dir" "${all[@]}"
done
# the one binary: the server as an editor runs it (spawned by node, over
# sockets), and bolt over the repo itself
if [ $js_only = 0 ]; then
  mkdir -p bin
  k=$(key binary bolt/main.bend)
  built=0
  if [ $full = 0 ] && [ -f "$cache/$k" ] && [ -x bin/bolt.bin ]; then
    built=1; skipped=$((skipped + 1))
  elif out=$(run $cap_native bend bolt/main.bend -o bin/bolt.bin) && [ -x bin/bolt.bin ]; then
    built=1; : > "$cache/$k"
  else
    check "bolt/main.bend (build)" "" "$out"
  fi
  if [ $built = 1 ]; then
    command -v node >/dev/null &&
      check "bolt/lsp/tests/spawn.js" "ok" "$(node bolt/lsp/tests/spawn.js bin/bolt.bin 2>&1)"
    check "bolt (repo)" "clean" "$(bolt/bolt 2>&1)"
  fi
fi
took=$(( $(date +%s) - started ))
echo "PASS: $pass / $total   (${took}s${skipped:+, $skipped cached})"
[ "$pass" = "$total" ]
