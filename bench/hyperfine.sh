#!/bin/sh
# Wall-clock comparison of `lake exe bench` via hyperfine. Build first so the
# measured command is the parse, not the build.
#
# Usage: sh bench/hyperfine.sh
# Requires: hyperfine (https://github.com/sharkdp/hyperfine).
set -eu

lake build bench

if ! command -v hyperfine >/dev/null 2>&1; then
  echo "hyperfine not found; running the self-timed harness instead:"
  lake exe bench
  exit 0
fi

hyperfine --warmup 3 --min-runs 10 'lake exe bench'
