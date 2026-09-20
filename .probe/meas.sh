#!/usr/bin/env bash
# measure one capped bend run: peak RSS (cgroup memory.peak), wall time, status
# usage: meas.sh <capGB> <label> <bend args...>
cap=$1; label=$2; shift 2
start=$(date +%s.%N)
out=$(systemd-run --user --scope -q -p MemoryMax=${cap}G -p MemorySwapMax=0 \
  bash -c 'nice -n 5 "$@" >/tmp/meas.out 2>/tmp/meas.err; st=$?;
           cg=$(awk -F: "/^0::/{print \$3}" /proc/self/cgroup);
           echo "PEAK=$(cat /sys/fs/cgroup${cg}/memory.peak 2>/dev/null || echo NA)";
           exit $st' _ "$@" 2>&1)
st=$?
end=$(date +%s.%N)
peak=$(printf '%s' "$out" | sed -n 's/^PEAK=//p' | tail -1)
secs=$(echo "$end - $start" | bc)
if [ -n "$peak" ] && [ "$peak" != NA ]; then gb=$(echo "scale=2; $peak/1073741824" | bc); else gb=NA; fi
printf '%-28s cap=%-3sG  peak=%-6s GB  %6.1f s  exit=%s\n' "$label" "$cap" "$gb" "$secs" "$st"
if [ $st != 0 ]; then echo "  stderr: $(tail -3 /tmp/meas.err 2>/dev/null | tr '\n' ' ')"; echo "  scope: $(printf '%s' "$out" | grep -iv '^PEAK=' | tail -2 | tr '\n' ' ')"; fi
