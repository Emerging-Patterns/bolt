#!/usr/bin/env bash
# The gate: every project's laws hold, and every test prints its `#|` lines on
# each lane: JS and native (CPU; a GPU run is 2-5x slower and is not gated).
#   ./gate.sh            all lanes (native lanes run inside `nix develop`)
#   ./gate.sh --js-only  skip the native lanes (and the linter, a native binary)
#   ./gate.sh --full     run every unit, cached or not
#
# Memory. `bend` compiling to native costs gigabytes, and the peak grows with
# the import closure: a test that reaches the whole program peaks around 16 GB
# here, where the same file on the JS lane peaks around 1.2 GB (README.md,
# "What the gate costs"). So every `bend` runs inside a memory-capped scope: a
# job that runs away is killed as a job, with a legible message, instead of
# taking the host's OOM killer with it. The native lane runs one job at a time;
# the JS lane runs as many as the free RAM affords, never more.
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

# --- memory caps -----------------------------------------------------------
# measured peaks, rounded up with room to spare (README.md)
cap_js=${BOLT_GATE_CAP_JS:-4}        # GB: the JS lane's heaviest test
cap_native=${BOLT_GATE_CAP_NATIVE:-24}  # GB: a whole-program native build
# how many JS jobs the machine can hold at once
avail_gb=$(awk '/MemAvailable/{printf "%d", $2/1048576}' /proc/meminfo)
jobs=${BOLT_GATE_JOBS:-$(( (avail_gb - 8) / cap_js ))}
[ "$jobs" -lt 1 ] 2>/dev/null && jobs=1
n_cpu=$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 4)
[ "$jobs" -gt "$n_cpu" ] && jobs=$n_cpu
[ "$jobs" -gt 8 ] && jobs=8
capped=1
systemd-run --user --scope -q -p MemoryMax=1G true 2>/dev/null || capped=0
if [ $capped = 0 ]; then
  echo "gate: no systemd user scope here; jobs run uncapped and a runaway one can take the host" >&2
  jobs=1
fi
# run one command inside a scope of <gb> GB, with swap off so the cap is real
cap_run() { local gb=$1; shift
  if [ $capped = 1 ]; then
    systemd-run --user --scope -q -p MemoryMax=${gb}G -p MemorySwapMax=0 nice -n 5 "$@"
  else
    nice -n 5 "$@"
  fi
}

# --- the import closure, for the cache key ---------------------------------
# a .bend file's inputs: itself, every .bend it reaches through a relative
# `import`, and the .c/.js bodies of its foreign defs. Memoised per file.
declare -A deps_of=() norm_of=()
norm() { local k=$1; local v=${norm_of[$k]:-}
  if [ -z "$v" ]; then
    local out=() seg segs; IFS=/ read -ra segs <<<"$k"
    for seg in "${segs[@]}"; do
      case $seg in ''|.) ;; ..) [ ${#out[@]} -gt 0 ] && unset 'out[-1]' ;; *) out+=("$seg") ;; esac
    done
    local IFS=/; v="${out[*]}"; norm_of[$k]=$v
  fi
  printf '%s' "$v"
}
deps() { local f=$1; local v=${deps_of[$f]:-}
  if [ -z "$v" ]; then
    local dir d line=()
    dir=$(dirname "$f")
    while read -r d; do [ -n "$d" ] && line+=("$(norm "$dir/$d")"); done < <(
      sed -n 's/^[[:space:]]*import[[:space:]]*"\([^"]*\)".*/\1/p
              s/^import[[:space:]]\{1,\}\(\.[^[:space:]]*\.bend\).*/\1/p' "$f" 2>/dev/null)
    v="${line[*]:-}"; deps_of[$f]=${v:- }
  fi
  printf '%s' "$v"
}
closure() { local -A seen=(); local queue=("$1") f d
  while [ ${#queue[@]} -gt 0 ]; do
    f=${queue[0]}; queue=("${queue[@]:1}")
    [ -n "${seen[$f]:-}" ] && continue
    [ -f "$f" ] || continue
    seen[$f]=1
    for d in $(deps "$f"); do queue+=("$d"); done
  done
  printf '%s\n' "${!seen[@]}" | sort
}
# the toolchain half of every key: a new bend or a new clang invalidates all
tool_key=$( { bend --version; command -v bend-cc >/dev/null && readlink -f "$(command -v bend-cc)"; } 2>/dev/null | sha256sum | cut -c1-16)
cache=.gate/cache; mkdir -p "$cache"
key() { # lane, file, expected output
  { echo "$1"; echo "$tool_key"; printf '%s' "$3"
    closure "$2" | tr '\n' '\0' | xargs -0 -r sha256sum
  } | sha256sum | cut -c1-32
}

# --- units -----------------------------------------------------------------
# each unit is a directory under .gate/jobs: cmd (what to run), want (what it
# must print), name. The JS ones run `jobs` wide, the native ones one at a time.
rm -rf .gate/jobs; mkdir -p .gate/jobs
n=0
unit() { # lane(js|native|host), name, want, key-or-empty, cmd...
  n=$((n + 1)); local d; d=$(printf '.gate/jobs/%03d' $n); mkdir -p "$d"
  echo "$1" > "$d/lane"; printf '%s' "$2" > "$d/name"; printf '%s' "$3" > "$d/want"
  printf '%s' "$4" > "$d/key"; shift 4
  printf '%s\0' "$@" > "$d/cmd"
}

# the C toolchain, built and run in the sandbox (flake.nix)
[ $js_only = 0 ] && unit host "nix flake check" "" "" nix-flake-check
for dir in */ */*/; do
  dir=${dir%/}
  [ -d "$dir/tests" ] || [ -f "$dir/PROOF.bend" ] || continue
  if [ -f "$dir/PROOF.bend" ]; then
    unit js "$dir/PROOF.bend" "All terms check." "$(key proof "$dir/PROOF.bend" 'All terms check.')" proof "$dir/PROOF.bend"
  fi
  for t in "$dir"/tests/*.bend; do
    [ -f "$t" ] || continue
    want=$(sed -n 's/^#|//p' "$t")
    # a test headed `# lanes: native` is too big for the JS lane's stack
    grep -q '^# lanes: native' "$t" || unit js "$t (js)" "$want" "$(key js "$t" "$want")" js "$t"
    [ $js_only = 1 ] && continue
    mkdir -p "$dir/.gate"
    unit native "$t (cpu)" "$want" "$(key cpu "$t" "$want")" cpu "$t" "$dir/.gate/$(basename "$t" .bend)"
  done
done
# the one binary: the server as an editor runs it (spawned by node, over
# sockets), and bolt over the repo itself
if [ $js_only = 0 ]; then
  mkdir -p bin
  unit native "bolt/main.bend (build)" "" "" binary
fi

# --- running ---------------------------------------------------------------
# bend 2.0.16 reports its unsafe annotations on stderr after the check; that
# is not the program's output, and a test's `#|` lines do not carry it
strip() { grep -v '^All terms check, with [0-9]* unsafe annotation'; }
# a scope that hits MemoryMax is killed with SIGKILL, and bend dies after it
# has printed "All terms check." -- say so, rather than leaving a silent stop
oom_note() { echo "killed: out of memory at the ${1} GB cap (README.md, \"What the gate costs\")"; }

# bend 2.0.16 reports its unsafe annotations on stderr after the check; that
# is not the program's output, and a test's `#|` lines do not carry it
run() { local out st; out=$(cap_run "$@" 2>&1); st=$?
  printf '%s\n' "$out" | grep -v '^All terms check, with [0-9]* unsafe annotation'
  return $st
}
work() { # the job in $1
  local d=$1 cmd gb out st
  mapfile -d '' -t cmd < "$d/cmd"
  case ${cmd[0]} in
    nix-flake-check)
      out=$(nix flake check 2>&1 | grep -v '^warning: Git tree' | grep -i 'error' || true) ;;
    proof)
      out=$(run $cap_js bend "${cmd[1]}" | sed 's/^All terms check, with [0-9]* unsafe annotations\{0,1\}\.$/All terms check./') ;;
    js)
      out=$(run $cap_js bend "${cmd[1]}"); st=$?
      [ $st = 137 ] && out="$out$(oom_note $cap_js)" ;;
    cpu)
      out=$(run $cap_native bend "${cmd[1]}" -o "${cmd[2]}"); st=$?
      if [ $st = 0 ] && [ -x "${cmd[2]}" ]; then
        out=$("${cmd[2]}" --gpu off 2>&1)
      else
        [ $st = 137 ] && out="$out$(oom_note $cap_native)"
        : > "$d/whatfailed"
      fi ;;
    binary)
      out=$(run $cap_native bend bolt/main.bend -o bin/bolt.bin); st=$?
      if [ $st != 0 ] || [ ! -x bin/bolt.bin ]; then
        [ $st = 137 ] && out="$out$(oom_note $cap_native)"
        : > "$d/whatfailed"
      else out=""; : > "$d/built"; fi ;;
  esac
  printf '%s' "$out" > "$d/got"
}

started=$(date +%s)
# the JS lane, `jobs` wide: each job is capped, so the pool's ceiling is
# jobs * cap_js, which is what `jobs` was chosen from
running=0
for d in .gate/jobs/*/; do
  d=${d%/}; [ "$(cat "$d/lane")" = js ] || continue
  k=$(cat "$d/key")
  if [ $full = 0 ] && [ -n "$k" ] && [ -f "$cache/$k" ]; then echo cached > "$d/cached"; continue; fi
  while [ $running -ge $jobs ]; do wait -n; running=$((running - 1)); done
  work "$d" & running=$((running + 1))
done
wait
# the native lane and the host checks, one at a time
for d in .gate/jobs/*/; do
  d=${d%/}; l=$(cat "$d/lane"); [ "$l" = js ] && continue
  k=$(cat "$d/key")
  if [ $full = 0 ] && [ -n "$k" ] && [ -f "$cache/$k" ]; then echo cached > "$d/cached"; continue; fi
  work "$d"
done

# --- the tally, in unit order so the output does not depend on timing -------
pass=0; total=0; cached=0
for d in .gate/jobs/*/; do
  d=${d%/}; name=$(cat "$d/name"); want=$(cat "$d/want"); k=$(cat "$d/key")
  if [ -f "$d/built" ]; then continue; fi
  total=$((total + 1))
  if [ -f "$d/cached" ]; then pass=$((pass + 1)); cached=$((cached + 1)); continue; fi
  got=$(cat "$d/got" 2>/dev/null || echo)
  if [ -f "$d/whatfailed" ]; then
    echo "FAIL: $name"; echo "$got" | sed 's/^/  /'
  elif [ "$want" = "$got" ]; then
    pass=$((pass + 1)); [ -n "$k" ] && : > "$cache/$k"
  else
    echo "FAIL: $name"; diff <(echo "$want") <(echo "$got") | sed 's/^/  /'
  fi
done
# the two checks that need the binary the native lane just built
if [ $js_only = 0 ] && [ -x bin/bolt.bin ]; then
  for c in spawn lint; do
    total=$((total + 1))
    case $c in
      spawn) command -v node >/dev/null || { total=$((total - 1)); continue; }
             got=$(node bolt/lsp/tests/spawn.js bin/bolt.bin 2>&1); want=ok; name=bolt/lsp/tests/spawn.js ;;
      lint)  got=$(bolt/bolt 2>&1); want=clean; name="bolt (repo)" ;;
    esac
    if [ "$want" = "$got" ]; then pass=$((pass + 1)); else echo "FAIL: $name"; diff <(echo "$want") <(echo "$got") | sed 's/^/  /'; fi
  done
fi
took=$(( $(date +%s) - started ))
echo "PASS: $pass / $total   (${took}s, ${cached} cached, ${jobs} js jobs at ${cap_js}G, native at ${cap_native}G)"
[ "$pass" = "$total" ]
