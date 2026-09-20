#!/usr/bin/env bash
# The gate: every project's laws hold, and every test prints its `#|` lines on
# each lane: JS and native (CPU; a GPU run is 2-5x slower and is not gated).
#   ./gate.sh            all lanes (native lanes run inside `nix develop`)
#   ./gate.sh --js-only  skip the native lanes (and the linter, a native binary)
#   ./gate.sh --full     run every unit, cached or not
#
# Two things keep it off the host's OOM killer and under ten minutes.
#
# Memory. `bend` compiling to native costs gigabytes, and the peak grows with
# the import closure, not with the file: a test that reaches the whole program
# peaks near 22 GB here, where the same file on the JS lane peaks near 1 GB
# (README.md, "What the gate costs"). Every `bend` therefore runs inside a
# memory-capped scope, so a job that runs away is killed as a job, with a
# legible message, instead of taking the host down. A native job is that big,
# so native jobs run one at a time: the measured peak, not the core count,
# sets the concurrency.
#
# One binary a project. `bend` has no incremental compile, so each build pays
# for the whole closure, and a project's tests import nearly the same set --
# bolt/lsp's ten tests reach 54 to 57 of the same files. The gate writes
# <project>/.gate/all.bend, importing every test of the project and calling
# each `main` in turn behind an `@@gate@@ <path>` marker, and builds that once.
# Each test is still its own check against its own `#|` trailer; only the
# compiling is shared.
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

# --- the caps --------------------------------------------------------------
# measured peaks rounded up (README.md, "What the gate costs")
cap_js=${BOLT_GATE_CAP_JS:-8}
cap_native=${BOLT_GATE_CAP_NATIVE:-28}
capped=1
systemd-run --user --scope -q -p MemoryMax=1G true 2>/dev/null || capped=0
[ $capped = 0 ] && echo "gate: no systemd user scope here; jobs run uncapped, and a runaway one can take the host with it" >&2
# run a command inside a scope of <gb> GB, with swap off so the cap is real
cap_run() { local gb=$1; shift
  if [ $capped = 1 ]; then
    systemd-run --user --scope -q -p MemoryMax=${gb}G -p MemorySwapMax=0 nice -n 5 "$@"
  else
    nice -n 5 "$@"
  fi
}
# bend 2.0.16 reports its unsafe annotations on stderr after the check; that
# is not the program's output, and a test's `#|` lines do not carry it
run() { local gb=$1; shift; local out st
  out=$(cap_run "$gb" "$@" 2>&1); st=$?
  # a scope that hits MemoryMax is SIGKILLed, and bend dies after it has
  # printed "All terms check." -- say so, rather than stopping in silence
  [ $st = 137 ] && out="$out
gate: killed at the ${gb} GB cap (README.md, \"What the gate costs\"); raise BOLT_GATE_CAP_NATIVE to retry"
  printf '%s\n' "$out" | grep -v '^All terms check, with [0-9]* unsafe annotation'
  return $st
}

# --- the import closure, for the cache key ---------------------------------
# a .bend file's inputs are itself, every .bend it reaches through a relative
# `import`, and the .c/.js bodies of its foreign defs. Memoised per file.
declare -A deps_of=()
deps() { local f=$1
  if [ -z "${deps_of[$f]+y}" ]; then
    local dir d out=() seg segs
    dir=$(dirname "$f")
    while read -r d; do
      [ -z "$d" ] && continue
      out=(); IFS=/ read -ra segs <<<"$dir/$d"
      for seg in "${segs[@]}"; do
        case $seg in ''|.) ;; ..) [ ${#out[@]} -gt 0 ] && unset 'out[-1]' ;; *) out+=("$seg") ;; esac
      done
      deps_of[$f]+="${out[*]-} "
    done < <(sed -n 's/^[[:space:]]*import[[:space:]]*"\([^"]*\)".*/\1/p
                     s/^import[[:space:]]\{1,\}\(\.[^[:space:]]*\.bend\).*/\1/p' "$f" 2>/dev/null | tr '/' '\n' | paste -sd/ - 2>/dev/null || true)
    deps_of[$f]=${deps_of[$f]:- }
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
# a new bend or a new clang invalidates every key
tool_key=$( { bend --version; command -v bend-cc >/dev/null && readlink -f "$(command -v bend-cc)"; } 2>/dev/null | sha256sum | cut -c1-16)
cache=.gate/cache; mkdir -p "$cache"
key() { # lane, then the files whose content the unit depends on
  local lane=$1; shift
  { echo "$lane"; echo "$tool_key"
    closure "$@" | tr '\n' '\0' | xargs -0 -r sha256sum
    for f in "$@"; do sed -n 's/^#|//p' "$f"; done
  } | sha256sum | cut -c1-32
}
