#!/usr/bin/env bash
# stage.sh <bin> <file>: per-stage seconds from the bench's stderr lines
"$1" +RTS --gpu off -RTS "$2" 2>&1 | { p=$(date +%s.%N); while read -r l; do n=$(date +%s.%N); printf '%8.2f  %s\n' "$(echo "$n - $p" | bc)" "$l"; p=$n; done; }
