#!/usr/bin/env bash
# CPU vs GPU on the server's pure per-request work. For each batch of 2^d
# requests: the fold's own milliseconds (median of 3) on 1 core, on every
# core, and on the GPU, then the whole process's wall-clock on cores and GPU.
#   ./bolt/lsp/bench/run.sh [max-depth]        (run from the repo root)
set -u
cd "$(dirname "$0")/../../.."
if ! command -v bend-cc >/dev/null; then exec nix develop -c "$0" "$@"; fi
export CC=bend-cc
max=${1:-16}
bin=bolt/lsp/.gate/bench-request
mkdir -p bolt/lsp/.gate
bend bolt/lsp/bench/request.bend -o "$bin" >/dev/null 2>&1 || { echo "build failed"; exit 1; }
med() { sort -n | sed -n 2p; }
fold_ms() { for _ in 1 2 3; do DEPTH=$1 timeout 300 "$bin" "${@:2}" | sed -n 2p; done | med; }
wall_ms() { for _ in 1 2 3; do s=$(date +%s%N); DEPTH=$1 timeout 300 "$bin" "${@:2}" >/dev/null; echo $(( ($(date +%s%N) - s) / 1000000 )); done | med; }
echo "requests | fold ms: 1 core | all cores | GPU | wall ms: all cores | GPU"
for d in $(seq 0 2 "$max"); do
  echo "$((1 << d)) | $(fold_ms $d --gpu off --threads 1) | $(fold_ms $d --gpu off) | $(fold_ms $d --gpu 4GB) | $(wall_ms $d --gpu off) | $(wall_ms $d --gpu 4GB)"
done
