#!/usr/bin/env bash
# run an aggregate and check each section against its test's `#|` trailer
set -u
dir=$1; shift
out=$("$@" 2>&1 | grep -v '^All terms check, with [0-9]* unsafe annotation')
ok=0; bad=0
while IFS= read -r t; do
  want=$(sed -n 's/^#|//p' "$t")
  got=$(printf '%s\n' "$out" | awk -v m="@@gate@@ $t" '
    $0==m {on=1; next} /^@@gate@@ /{on=0} on {print}')
  if [ "$want" = "$got" ]; then ok=$((ok+1)); else bad=$((bad+1))
    echo "  MISMATCH $t"; diff <(echo "$want") <(echo "$got") | sed 's/^/    /' | head -8; fi
done < <(printf '%s\n' "$out" | sed -n 's/^@@gate@@ //p')
echo "$dir: $ok sections match, $bad differ"
