#!/usr/bin/env bash
# The import closure of a .bend file: itself, every .bend it reaches through a
# relative `import`, and the .c/.js bodies of its foreign defs. Paths are
# printed relative to the repo root, sorted.
set -u
norm() { # collapse a/b/../c without needing the file to exist
  local p=$1 out=() seg
  IFS=/ read -ra segs <<<"$p"
  for seg in "${segs[@]}"; do
    case $seg in
      ''|.) ;;
      ..) [ ${#out[@]} -gt 0 ] && unset 'out[-1]' ;;
      *) out+=("$seg") ;;
    esac
  done
  local IFS=/; echo "${out[*]}"
}
closure() {
  local -A seen=(); local queue=("$1")
  while [ ${#queue[@]} -gt 0 ]; do
    local f=${queue[0]}; queue=("${queue[@]:1}")
    [ -n "${seen[$f]:-}" ] && continue
    [ -f "$f" ] || continue
    seen[$f]=1
    local dir; dir=$(dirname "$f")
    local dep
    while read -r dep; do
      [ -z "$dep" ] && continue
      queue+=("$(norm "$dir/$dep")")
    done < <(sed -n 's/^[[:space:]]*import[[:space:]]*"\([^"]*\)".*/\1/p; s/^import[[:space:]]\{1,\}\(\.[^[:space:]]*\.bend\).*/\1/p' "$f")
  done
  printf '%s\n' "${!seen[@]}" | sort
}
closure "$1"
