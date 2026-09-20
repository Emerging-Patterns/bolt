#!/usr/bin/env bash
# Thin glue for bendhub: publish bolt/main.bend, capture the 0x hash,
# write it into README, emit GitHub Actions outputs.
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
# Users run this file from the hub: `bend 0x…/bolt/main.bend`.
ENTRY="bolt/main.bend"

die() {
  echo "hub.sh: $*" >&2
  exit 1
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

# `import 0xHASH/bolt/main.bend as Main` → bolt/main.bend
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

cmd_publish() {
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
  local hash="${1:-}"
  hash_ok "$hash" || die "hash must be 0x…, got: ${hash:-empty}"
  [ -f README.md ] || die "README.md missing"
  python3 - "$hash" <<'PY'
import re
import sys
from pathlib import Path

h = sys.argv[1]
p = Path("README.md")
text = p.read_text()
ident = h + "/bolt/main.bend"
new = re.sub(r"0x(?:…|[0-9a-fA-F]{8,64})/bolt/main\.bend", ident, text)
if new == text and ident not in text:
    sys.exit("README.md: no hub identity (0x…/bolt/main.bend) to replace")
p.write_text(new)
print("identity=" + ident)
PY
}

cmd_name() {
  local ver="${1:-}" hash="${2:-}"
  [ -n "$ver" ] && hash_ok "$hash" || die "usage: hub.sh name X.Y.Z 0x…"
  emit name "bolt ${ver} (${hash})"
}

cmd_selftest() {
  local h="0xdeadbeefcafebabe0123456789abcd"
  local out
  out=$(parse_hash $'publishing 3 files, 12 bytes, as '"$h"$'\n'"$h"$'\nimport '"$h"'/bolt/main.bend as Main\n')
  [ "$out" = "$h" ] || die "parse_hash: $out"
  out=$(parse_entry $'import '"$h"'/bolt/main.bend as Main\n')
  [ "$out" = "bolt/main.bend" ] || die "parse_entry: $out"
  tmp=$(mktemp -d)
  printf '%s\n' 'bend 0x…/bolt/main.bend' > "$tmp/README.md"
  (
    cd "$tmp"
    "$HERE/hub.sh" readme "$h"
    got=$(cat README.md)
    [ "$got" = "bend $h/bolt/main.bend" ] || die "readme: $got"
  )
  rm -rf "$tmp"
  echo "hub.sh selftest ok"
}

case "${1:-}" in
  publish) cmd_publish ;;
  readme) cmd_readme "${2:-}" ;;
  name) cmd_name "${2:-}" "${3:-}" ;;
  selftest) cmd_selftest ;;
  *) die "usage: hub.sh publish|readme HASH|name VER HASH|selftest" ;;
esac
