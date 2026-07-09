#!/usr/bin/env python3
"""Mechanical Lean style gate: 100-column limit (Unicode codepoints, matching
mathlib's linter), no trailing whitespace, no tabs. Run from the repo root:

    python3 scripts/style-check.py

Exits non-zero and lists every violation. Used by CI and runnable locally.
"""

import subprocess
import sys

MAX = 100
files = subprocess.check_output(["git", "ls-files", "*.lean"], text=True).split()
violations = []
for f in files:
    for i, line in enumerate(open(f, encoding="utf-8"), 1):
        line = line.rstrip("\n")
        if len(line) > MAX:
            violations.append(f"{f}:{i}: line is {len(line)} cols (>{MAX})")
        if line != line.rstrip():
            violations.append(f"{f}:{i}: trailing whitespace")
        if "\t" in line:
            violations.append(f"{f}:{i}: tab character")

for v in violations:
    print(v)
print(
    f"{'FAIL' if violations else 'OK'}: {len(files)} Lean files, {len(violations)} violations"
)
sys.exit(1 if violations else 0)
