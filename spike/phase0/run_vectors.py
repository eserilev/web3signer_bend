#!/usr/bin/env python3
"""Runs the spike binary on each bls12-381-tests sign vector.

A vector with an empty or null output must fail. All other vectors must print the exact
expected signature.

    ./run_vectors.py <path to bls12-381-tests/sign> [binary]
"""
import pathlib
import re
import subprocess
import sys

here = pathlib.Path(__file__).resolve().parent
vectors = pathlib.Path(sys.argv[1])
binary = sys.argv[2] if len(sys.argv) > 2 else str(here.parents[1] / "build/phase0/sign")

failures = 0
files = sorted(vectors.glob("*.yaml"))
for path in files:
    text = path.read_text()
    privkey = re.search(r"privkey: '(0x[0-9a-f]+)'", text).group(1)
    message = re.search(r"message: '(0x[0-9a-f]+)'", text).group(1)
    expected = re.search(r"output: *'(0x[0-9a-f]+)'", text)
    want = expected.group(1) if expected else None
    run = subprocess.run([binary, privkey, message], capture_output=True, text=True)
    got = run.stdout.strip()
    if want is None:
        ok = run.returncode != 0
        detail = f"exit {run.returncode}, stderr {run.stderr.strip()!r}"
    else:
        ok = run.returncode == 0 and got == want
        detail = f"exit {run.returncode}"
    print(f"{'PASS' if ok else 'FAIL'} {path.name} ({detail})")
    if not ok:
        failures += 1
        print(f"  want {want}\n  got  {got}")

print(f"{len(files) - failures}/{len(files)} passed")
sys.exit(1 if failures or not files else 0)
