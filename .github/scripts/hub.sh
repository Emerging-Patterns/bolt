#!/usr/bin/env bash
# Thin glue for bendhub: publish ENTRY, capture the 0x hash, write it
# into README, emit GitHub Actions outputs. Per-repo values live in
# .github/hub.env (NAME, ENTRY, VERSION_FILES).
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)

die() {
  echo "hub.sh: $*" >&2
  exit 1
}

load_cfg() {
  local cfg="$ROOT/.github/hub.env"
  [ -f "$cfg" ] || die "missing $cfg"
  # NAME, ENTRY, VERSION_FILES only
  NAME=""
  ENTRY=""
  VERSION_FILES=""
  while IFS= read -r line || [ -n "$line" ]; do
    case "$line" in
      ''|\#*) continue ;;
    esac
    local key=${line%%=*}
    local val=${line#*=}
    case "$key" in
      NAME) NAME=$val ;;
      ENTRY) ENTRY=$val ;;
      VERSION_FILES) VERSION_FILES=$val ;;
    esac
  done < "$cfg"
  [ -n "${NAME:-}" ] || die "NAME is empty in .github/hub.env"
  [ -n "${ENTRY:-}" ] || die "ENTRY is empty in .github/hub.env"
}

hash_ok() {
  echo "$1" | grep -qxE '0x[0-9a-fA-F]{8,}'
}

# First 0x token in the publish log (stdout prints the hash, then the import).
parse_hash() {
  local got
  got=$(printf '%s\n' "$1" | grep -oE '^0x[0-9a-fA-F]{8,}' | head -1)
  if [ -z "$got" ]; then
    got=$(printf '%s\n' "$1" | grep -oE '0x[0-9a-fA-F]{8,}' | head -1)
  fi
  [ -n "$got" ] || die "no 0x hash in publish output"
  printf '%s' "$got"
}

# `import 0xHASH/path/file.bend as Name` → path/file.bend
parse_entry() {
  local line path
  line=$(printf '%s\n' "$1" | grep -E '^import 0x' | head -1 || true)
  path=${line#import }
  path=${path%% as *}
  path=${path#*/}
  if [ -n "$path" ]; then
    printf '%s' "$path"
  else
    printf '%s' "$ENTRY"
  fi
}

emit() {
  local key="$1" val="$2"
  if [ -n "${GITHUB_OUTPUT:-}" ]; then
    printf '%s=%s\n' "$key" "$val" >> "$GITHUB_OUTPUT"
  fi
  printf '%s=%s\n' "$key" "$val"
}

# X.Y.Z from a version file we know how to read.
file_ver() {
  local f="$1" v=""
  [ -f "$f" ] || die "missing version file $f"
  case "$f" in
    *.nix)
      v=$(grep -oE 'version = "[0-9]+\.[0-9]+\.[0-9]+"' "$f" \
        | head -1 | grep -oE '[0-9]+\.[0-9]+\.[0-9]+' || true)
      ;;
    *.json)
      v=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1])).get("version",""))' "$f")
      ;;
    *)
      die "do not know how to read version from $f"
      ;;
  esac
  echo "$v" | grep -qxE '[0-9]+\.[0-9]+\.[0-9]+' || die "no X.Y.Z in $f"
  printf '%s' "$v"
}

write_ver() {
  local f="$1" ver="$2"
  case "$f" in
    *.nix)
      sed -i -E 's/version = "[0-9]+\.[0-9]+\.[0-9]+"/version = "'"$ver"'"/' "$f"
      grep -q "version = \"$ver\"" "$f" || die "failed to write $f version $ver"
      ;;
    *.json)
      sed -i -E 's/"version": "[0-9]+\.[0-9]+\.[0-9]+"/"version": "'"$ver"'"/' "$f"
      grep -q "\"version\": \"$ver\"" "$f" || die "failed to write $f version $ver"
      ;;
    *)
      die "do not know how to write version to $f"
      ;;
  esac
}

cmd_publish() {
  load_cfg
  command -v bend >/dev/null || die "bend is not on PATH"
  [ -f "$ENTRY" ] || die "missing $ENTRY"
  local log hash entry
  log=$(mktemp)
  if ! bend "$ENTRY" --publish >"$log" 2>&1; then
    cat "$log" >&2
    rm -f "$log"
    die "bend --publish failed"
  fi
  cat "$log" >&2
  hash=$(parse_hash "$(cat "$log")")
  entry=$(parse_entry "$(cat "$log")")
  rm -f "$log"
  emit hash "$hash"
  emit entry "$entry"
  emit identity "${hash}/${entry}"
}

cmd_readme() {
  load_cfg
  local hash="${1:-}" path="${2:-}"
  hash_ok "$hash" || die "hash must be 0x…, got: ${hash:-empty}"
  [ -f README.md ] || die "README.md missing"
  path=${path:-$ENTRY}
  python3 - "$hash" "$path" <<'PY'
import re
import sys
from pathlib import Path

h, path = sys.argv[1], sys.argv[2]
ident = h + "/" + path
esc = re.escape(path)
p = Path("README.md")
text = p.read_text()
new = re.sub(r"0x(?:…|[0-9a-fA-F]{8,64})/" + esc, ident, text)
if new == text and ident not in text:
    sys.exit("README.md: no hub identity (0x…/" + path + ") to replace")
p.write_text(new)
print("identity=" + ident)
PY
}

cmd_name() {
  load_cfg
  local ver="${1:-}" hash="${2:-}"
  [ -n "$ver" ] && hash_ok "$hash" || die "usage: hub.sh name X.Y.Z 0x…"
  emit name "${NAME} ${ver} (${hash})"
}

# Resolve X.Y.Z from VERSION_FILES. Env: VERSION_IN, BUMP (none|patch|minor|major).
cmd_version() {
  load_cfg
  [ -n "${VERSION_FILES:-}" ] || die "VERSION_FILES is empty in .github/hub.env"
  local f first="" v bump_files=0 ver
  for f in $VERSION_FILES; do
    v=$(file_ver "$f")
    if [ -z "$first" ]; then
      first="$v"
    elif [ "$v" != "$first" ]; then
      die "version mismatch: $f=$v (expected $first)"
    fi
  done

  ver=$(printf '%s' "${VERSION_IN:-}" | tr -d '[:space:]')
  ver="${ver#v}"
  if [ -n "$ver" ]; then
    :
  elif [ "${BUMP:-none}" != none ]; then
    local maj min pat
    IFS=. read -r maj min pat <<< "$first"
    case "$BUMP" in
      major) ver="$((maj + 1)).0.0" ;;
      minor) ver="$maj.$((min + 1)).0" ;;
      patch) ver="$maj.$min.$((pat + 1))" ;;
      *) die "unknown bump: $BUMP" ;;
    esac
    bump_files=1
  else
    ver="$first"
  fi

  echo "$ver" | grep -qxE '[0-9]+\.[0-9]+\.[0-9]+' || die "version must be X.Y.Z, got: $ver"
  if [ "$bump_files" -eq 0 ] && [ "$ver" != "$first" ]; then
    die "asked to tag v$ver but files are $first"
  fi
  if [ "$bump_files" -eq 1 ]; then
    for f in $VERSION_FILES; do
      write_ver "$f" "$ver"
    done
  fi
  emit version "$ver"
  emit bump_files "$bump_files"
  emit version_files "$VERSION_FILES"
}

cmd_selftest() {
  local h="0xdeadbeefcafebabe0123456789abcd"
  local out
  out=$(parse_hash $'publishing 3 files, 12 bytes, as '"$h"$'\n'"$h"$'\nimport '"$h"'/bolt/main.bend as Main\n')
  [ "$out" = "$h" ] || die "parse_hash: $out"
  ENTRY=bolt/main.bend
  out=$(parse_entry $'import '"$h"'/bolt/main.bend as Main\n')
  [ "$out" = "bolt/main.bend" ] || die "parse_entry: $out"
  tmp=$(mktemp -d)
  mkdir -p "$tmp/.github/scripts"
  printf '%s\n' 'NAME=bolt' 'ENTRY=bolt/main.bend' \
    'VERSION_FILES=flake.nix extra.json' > "$tmp/.github/hub.env"
  cp "$HERE/hub.sh" "$tmp/.github/scripts/hub.sh"
  chmod +x "$tmp/.github/scripts/hub.sh"
  printf '%s\n' 'bend 0x…/bolt/main.bend' > "$tmp/README.md"
  printf '%s\n' 'version = "0.3.0";' > "$tmp/flake.nix"
  printf '%s\n' '{"version": "0.3.0"}' > "$tmp/extra.json"
  (
    cd "$tmp"
    ./.github/scripts/hub.sh readme "$h"
    got=$(cat README.md)
    [ "$got" = "bend $h/bolt/main.bend" ] || die "readme: $got"
    GITHUB_OUTPUT="$tmp/out" ./.github/scripts/hub.sh version
    grep -qx 'version=0.3.0' "$tmp/out" || die "version: $(cat "$tmp/out")"
    GITHUB_OUTPUT="$tmp/out2" BUMP=patch ./.github/scripts/hub.sh version
    grep -qx 'version=0.3.1' "$tmp/out2" || die "bump: $(cat "$tmp/out2")"
    grep -q 'version = "0.3.1"' flake.nix || die "flake not bumped"
    grep -q '"version": "0.3.1"' extra.json || die "json not bumped"
  )
  rm -rf "$tmp"
  echo "hub.sh selftest ok"
}

case "${1:-}" in
  publish) cmd_publish ;;
  readme) cmd_readme "${2:-}" "${3:-}" ;;
  name) cmd_name "${2:-}" "${3:-}" ;;
  version) cmd_version ;;
  selftest) cmd_selftest ;;
  *) die "usage: hub.sh publish|readme HASH [ENTRY]|name VER HASH|version|selftest" ;;
esac
