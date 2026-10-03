#!/usr/bin/env python3
"""Runs the EIP-3076 interchange test vectors through src/interchange.bend.

    ./tests/run_interchange.py <tests/generated dir> [interchange_cli binary]

The vectors come from eth-clients/slashing-protection-interchange-tests.
web3signer_bend keeps every record (the complete strategy), so each check
uses should_succeed_complete. An import that fails is correct only when the
step expects a failure or holds slashable data; the vector README allows an
implementation to reject slashable data, and then the rest of the vector is
ignored.
"""
import json
import pathlib
import subprocess
import sys

here = pathlib.Path(__file__).resolve().parent
vectors = pathlib.Path(sys.argv[1])
cli = sys.argv[2] if len(sys.argv) > 2 else str(here.parent / "build/tests/interchange_cli")

passed = failed = rejected = 0


def run_vector(path):
    d = json.loads(path.read_text())
    ops = ["G", d["genesis_validators_root"]]
    plan = []
    for step in d["steps"]:
        ops += ["I", json.dumps(step["interchange"])]
        plan.append(("I", step))
        for b in step["blocks"]:
            ops += ["B", b["pubkey"], b["slot"], b.get("signing_root", "0x" + "00" * 32)]
            plan.append(("C", b))
        for a in step["attestations"]:
            ops += ["A", a["pubkey"], a["source_epoch"], a["target_epoch"], a.get("signing_root", "0x" + "00" * 32)]
            plan.append(("C", a))
    out = subprocess.run([cli, *ops], capture_output=True, text=True)
    if out.returncode != 0:
        return [f"exit {out.returncode}: {out.stderr.strip()}"], False
    lines = out.stdout.split("\n")
    if lines[0] != "G":
        return [f"bad output: {out.stdout!r}"], False
    lines = lines[1:]
    errors = []
    ignore = False
    for (kind, item), got in zip(plan, lines):
        if ignore:
            continue
        if kind == "I":
            ok = got.startswith("I OK")
            if ok and not item["should_succeed"]:
                errors.append("import passed, want fail")
            if not ok:
                if item["should_succeed"] and not item["contains_slashable_data"]:
                    errors.append(f"import failed ({got}), want pass")
                else:
                    ignore = True
            continue
        want = "S" if item["should_succeed_complete"] else "R"
        if got != want:
            errors.append(f"{json.dumps(item)}: got {got}, want {want}")
    if not errors and lines[len(plan)] != "LOG OK":
        errors.append(lines[len(plan)])
    return errors, ignore


for path in sorted(vectors.glob("*.json")):
    errors, ignored = run_vector(path)
    if errors:
        failed += 1
        print(f"FAIL {path.stem}")
        for e in errors[:5]:
            print(f"  {e}")
    else:
        passed += 1
        rejected += ignored

print(f"{passed} passed, {failed} failed ({rejected} rejected as slashable, checks skipped as the vectors allow)")
sys.exit(1 if failed else 0)
