#!/usr/bin/env python3
"""Sample a compiled Lean binary with Instruments and rank functions by time (macOS only).

    lake build bench && python3 tools/profile.py [--runs N] [--top K] [-- CMD ARGS...]

CMD defaults to the bench binary. Each run is recorded with the xctrace Time Profiler
(1 ms samples) and the samples of all runs are pooled. Symbols are demangled by the
toolchain's own `Lean.Name.Demangle.demangleSymbol` (tools/Demangle.lean) and folded to the
function they belong to, so every specialization of a combinator (`... spec at
Grip.Examples.Sexp.sexp`) and its lambdas count as that combinator.
"""

import argparse
import collections
import pathlib
import subprocess
import tempfile
import xml.etree.ElementTree as ET

ROOT = pathlib.Path(__file__).resolve().parent.parent
XPATH = '/trace-toc/run[@number="1"]/data/table[@schema="time-profile"]'


def record(cmd, out):
    subprocess.run(
        [
            "xctrace",
            "record",
            "--quiet",
            "--no-prompt",
            "--template",
            "Time Profiler",
            "--output",
            str(out),
            "--target-stdout",
            "-",
            "--launch",
            "--",
            *cmd,
        ],
        check=True,
        stdout=subprocess.DEVNULL,
    )


def stacks(trace):
    """Yield each sample's backtrace as symbol names, leaf first."""
    xml = subprocess.run(
        ["xctrace", "export", "--input", str(trace), "--xpath", XPATH],
        check=True,
        capture_output=True,
    ).stdout
    root = ET.fromstring(xml)
    # The export interns repeated elements: later occurrences are `ref=` to an earlier `id=`.
    ids = {e.get("id"): e for e in root.iter() if e.get("id")}

    def deref(e):
        return ids[e.get("ref")] if e.get("ref") else e

    for row in root.iter("row"):
        bt = row.find("backtrace")
        if bt is None:
            bt = row.find("tagged-backtrace")
        if bt is not None:
            frames = [deref(f).get("name") or "?" for f in deref(bt).findall("frame")]
            if frames:
                yield frames


def demangle(symbols):
    out = subprocess.run(
        ["lake", "env", "lean", "--run", "tools/Demangle.lean"],
        cwd=ROOT,
        input="\n".join(symbols) + "\n",
        check=True,
        capture_output=True,
        text=True,
    ).stdout.splitlines()
    # Keep the function, drop the `[λ, private] spec at ...` context. Symbols the demangler
    # left alone (C++ runtime, libc) contain spaces of their own, so keep them whole.
    return {s: d.split(" ")[0] if d != s else s for s, d in zip(symbols, out)}


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "--runs", type=int, default=10, help="recordings to pool (default 10)"
    )
    ap.add_argument("--top", type=int, default=30, help="rows per table (default 30)")
    ap.add_argument("cmd", nargs="*", default=[str(ROOT / ".lake/build/bin/bench")])
    args = ap.parse_args()

    samples = []
    with tempfile.TemporaryDirectory() as tmp:
        for i in range(args.runs):
            trace = pathlib.Path(tmp) / f"run{i}.trace"
            record(args.cmd, trace)
            samples.extend(stacks(trace))

    names = demangle(sorted({s for st in samples for s in st}))
    self_t, incl = collections.Counter(), collections.Counter()
    for st in samples:
        fs = [names[s] for s in st]
        self_t[fs[0]] += 1
        incl.update(set(fs))  # once per sample, however deep the recursion

    n = len(samples)
    print(f"{n} samples over {args.runs} runs of {' '.join(args.cmd)}")
    for title, c in (("self", self_t), ("inclusive", incl)):
        print(f"\n{title}:")
        for f, k in c.most_common(args.top):
            print(f"{100 * k / n:6.1f}%  {f}")


if __name__ == "__main__":
    main()
