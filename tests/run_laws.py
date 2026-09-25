#!/usr/bin/env python3
"""Runs the laws of LAWS.bend as checks on random operation sequences.

    ./tests/run_laws.py [sequences] [laws_cli binary]

For each request, the laws_cli binary evaluates each law with the
definitions of spec/safety.bend and prints R, P or S with any failed law.
This script also compares each decision with a separate Python model of the
slashing rules in docs/SPEC.md section 8. This is a test, not a proof.
"""
import pathlib
import random
import subprocess
import sys

here = pathlib.Path(__file__).resolve().parent
count = int(sys.argv[1]) if len(sys.argv) > 1 else 500
cli = sys.argv[2] if len(sys.argv) > 2 else str(here.parent / "build/tests/laws_cli")


class Model:
    def __init__(self):
        self.blocks = []  # (slot, root or None)
        self.atts = []  # (source, target, root or None)
        self.block_mark = None
        self.att_mark = None

    def block(self, slot, root):
        if self.block_mark is not None and slot < self.block_mark:
            return "R"
        again = False
        for s, r in self.blocks:
            if s == slot:
                if r == root:
                    again = True
                else:
                    return "R"
        if again:
            return "P"
        self.blocks.append((slot, root))
        return "S"

    def att(self, source, target, root):
        if source > target:
            return "R"
        if self.att_mark is not None and (source < self.att_mark[0] or target < self.att_mark[1]):
            return "R"
        again = False
        for s, t, r in self.atts:
            if t == target:
                if r != root:
                    return "R"
                if s == source:
                    again = True
            elif s < source and t > target:
                return "R"
            elif s > source and t < target:
                return "R"
        if again:
            return "P"
        self.atts.append((source, target, root))
        return "S"


def sequence(rng):
    model = Model()
    ops, want = [], []
    for _ in range(rng.randint(1, 25)):
        kind = rng.choices(["b", "a", "mb", "ma", "ub", "ua"], [30, 50, 3, 3, 3, 3])[0]
        if kind == "b":
            slot, root = rng.randint(0, 8), rng.randint(0, 2)
            ops += ["b", slot, root, 0]
            want.append(model.block(slot, root))
        elif kind == "a":
            source, target, root = rng.randint(0, 6), rng.randint(0, 6), rng.randint(0, 2)
            ops += ["a", source, target, root]
            want.append(model.att(source, target, root))
        elif kind == "mb":
            model.block_mark = rng.randint(0, 8)
            ops += ["mb", model.block_mark, 0, 0]
        elif kind == "ma":
            model.att_mark = (rng.randint(0, 6), rng.randint(0, 6))
            ops += ["ma", *model.att_mark, 0]
        elif kind == "ub":
            slot = rng.randint(0, 8)
            model.blocks.append((slot, None))
            ops += ["ub", slot, 0, 0]
        else:
            source, target = rng.randint(0, 6), rng.randint(0, 6)
            model.atts.append((source, target, None))
            ops += ["ua", source, target, 0]
    return ops, want


rng = random.Random(3076)
failures = 0
requests = 0
tally = {"R": 0, "P": 0, "S": 0}
for i in range(count):
    ops, want = sequence(rng)
    out = subprocess.run([cli, *map(str, ops)], capture_output=True, text=True)
    got = out.stdout.splitlines()
    tags = [line.split()[0] if line else "" for line in got]
    bad = [line for line in got if "FAIL" in line]
    if out.returncode != 0 or tags != want or bad:
        failures += 1
        if failures <= 5:
            print(f"FAIL sequence {i}: {' '.join(map(str, ops))}")
            print(f"  want {want}\n  got  {got}")
    requests += len(want)
    for t in want:
        tally[t] += 1

print(f"{count - failures}/{count} sequences passed, {requests} requests "
      f"(R {tally['R']}, P {tally['P']}, S {tally['S']})")
sys.exit(1 if failures else 0)
