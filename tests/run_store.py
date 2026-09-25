#!/usr/bin/env python3
"""Tests src/store.bend: decisions over many keys, the log format, and replay.

    ./tests/run_store.py [sequences] [store_cli binary]

1. Random request sequences over several keys and two genesis validators
   roots. Each outcome must match a Python model, and replaying the log that
   the run wrote must give the live state (REPLAY OK).
2. Log lines: each canonical line reads back to itself, and malformed lines
   fail.
3. Torn logs: a log cut at any byte reads as its complete lines. A complete
   line that does not parse makes the whole log fail.
"""
import pathlib
import random
import subprocess
import sys

here = pathlib.Path(__file__).resolve().parent
count = int(sys.argv[1]) if len(sys.argv) > 1 else 300
cli = sys.argv[2] if len(sys.argv) > 2 else str(here.parent / "build/tests/store_cli")

passed = 0
failed = 0


def run(*args):
    out = subprocess.run([cli, *map(str, args)], capture_output=True, text=True)
    if out.returncode != 0:
        return f"EXIT {out.returncode}: {out.stderr.strip()}"
    return out.stdout


def check(name, got, want):
    global passed, failed
    if got == want:
        passed += 1
    else:
        failed += 1
        if failed <= 10:
            print(f"FAIL {name}\n  want {want!r}\n  got  {got!r}")


class Key:
    def __init__(self):
        self.blocks = []
        self.atts = []

    def block(self, slot, root):
        again = False
        for s, r in reversed(self.blocks):  # newest first, as Bulkhead scans
            if s == slot:
                if r != root:
                    return "R 412 double block proposal"
                again = True
        if not again:
            self.blocks.append((slot, root))
            return "S", True
        return "S", False

    def att(self, source, target, root):
        if source > target:
            return "R 412 source epoch after target epoch"
        again = False
        for s, t, r in reversed(self.atts):  # newest first, as Bulkhead scans
            if t == target:
                if r != root:
                    return "R 412 double vote"
                if s == source:
                    again = True
            elif s < source and t > target:
                return "R 412 surrounded vote"
            elif s > source and t < target:
                return "R 412 surrounding vote"
        if not again:
            self.atts.append((source, target, root))
            return "S", True
        return "S", False


def w(n):
    return f"0x{n:08x}" + "0" * 56


def pk(n):
    return f"0x{n:08x}" + "0" * 88


# 1. Random sequences.
rng = random.Random(8282)
for i in range(count):
    keys, gvr, ops, want, log = {}, None, [], [], []
    for _ in range(rng.randint(1, 20)):
        kind = rng.choice("aaabbr")
        key, g = rng.randint(1, 3), rng.choice([7, 7, 7, 7, 8])
        if kind == "a":
            x, y, z = rng.randint(0, 5), rng.randint(0, 5), rng.randint(1, 3)
        elif kind == "b":
            x, y, z = rng.randint(0, 5), rng.randint(1, 3), 0
        else:
            x, y, z = rng.randint(0, 5), 0, 0
        ops += [kind, key, g, x, y, z]
        if gvr is not None and g != gvr:
            want.append("R 412 genesis validators root does not match the database")
            continue
        # A refused request writes no event, so only a signed request binds
        # the genesis validators root of the database.
        pre = [f"G {w(g)}"] if gvr is None else []
        k = keys.setdefault(key, Key())
        if kind == "r":
            want.append("S")
            log += pre
            gvr = g
            continue
        res = k.att(x, y, z) if kind == "a" else k.block(x, y)
        if isinstance(res, str):
            want.append(res)
            continue
        want.append("S")
        log += pre
        gvr = g
        if res[1]:
            log.append(f"A {pk(key)} {x} {y} {w(z)}" if kind == "a" else f"B {pk(key)} {x} {w(y)}")
    expected = "\n".join(want) + "\nLOG\n" + "".join(line + "\n" for line in log) + "REPLAY OK\n"
    check(f"sequence {i}: {' '.join(map(str, ops))}", run("run", *ops), expected)

# 2. Log lines.
MAX = 2**64 - 1


def rand_u64():
    return rng.choice([0, 1, 31, 32, 2**32 - 1, 2**32, MAX, rng.getrandbits(64)])


def rand_hex(n):
    return "0x" + "".join(rng.choice("0123456789abcdef") for _ in range(2 * n))


def rand_root():
    return rng.choice(["-", rand_hex(32)])


def rand_line():
    kind = rng.choice(["G", "B", "A", "WB", "WA"])
    if kind == "G":
        return f"G {rand_hex(32)}"
    if kind == "B":
        return f"B {rand_hex(48)} {rand_u64()} {rand_root()}"
    if kind == "A":
        return f"A {rand_hex(48)} {rand_u64()} {rand_u64()} {rand_root()}"
    if kind == "WB":
        return f"WB {rand_hex(48)} {rand_u64()}"
    return f"WA {rand_hex(48)} {rand_u64()} {rand_u64()}"


for i in range(300):
    line = rand_line()
    check(f"line round trip {line}", run("event", line), line + "\n")

key, root = rand_hex(48), rand_hex(32)
bad_lines = [
    "", "X", "G", f"G {root} extra", f"G  {root}", f"B {key} 1", f"B {key} 1 {root} x",
    f"B {key} {2**64} {root}", f"B {key} -1 {root}", f"B {key} 1a {root}", f"B {key[:-2]} 1 {root}",
    f"B {key}00 1 {root}", f"B {key} 1 {root[:-2]}", f"B {key} 1 --", f"A {key} 1 2", f"WB {key}",
    f"WA {key} 1", f"b {key} 1 {root}", f" B {key} 1 {root}", f"B {key} 1 {root} ",
    f"B {key}  1 {root}", f"B {key.replace('0x', '0y')} 1 {root}",
]
for line in bad_lines:
    check(f"rejects {line!r}", run("event", line), "ERR\n")

# 3. Torn logs.
for i in range(100):
    lines = [rand_line() for _ in range(rng.randint(0, 6))]
    text = "".join(line + "\n" for line in lines)
    cut = rng.randint(0, len(text))
    torn = text[:cut]
    check(f"torn log #{i} at {cut}", run("log", torn), f"{torn.count(chr(10))}\n")
    if lines:
        broken = list(lines)
        broken[rng.randrange(len(broken))] = "B not a key 1 -"
        check(f"corrupt log #{i}", run("log", "".join(line + "\n" for line in broken)), "ERR\n")
check("empty log", run("log", ""), "0\n")

print(f"{passed} passed, {failed} failed")
sys.exit(1 if failed else 0)
