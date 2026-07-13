#!/usr/bin/env bash
# JSONTestSuite parsers/ entry for grip.
# Protocol: exit 0 = valid JSON (accept), 1 = invalid (reject), other = crash.
# Usage: test_grip.sh <file>
set -euo pipefail
BIN="$(cd "$(dirname "$0")/.." && pwd)/.lake/build/bin/conformance"
if [ ! -x "$BIN" ]; then
  echo "grip binary not built; run: lake build conformance" >&2
  exit 2
fi
exec "$BIN" "$1"
