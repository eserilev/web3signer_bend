#!/usr/bin/env python3
"""Tests src/json.bend through the json_cli binary, with Python's json as the reference.

    ./tests/run_json.py [json_cli binary]

Valid inputs must print the same compact JSON as json.dumps. Invalid
inputs must print ERR. The parser is stricter than Python's json in three
places, and the invalid cases test each one: duplicate keys, NaN and
Infinity, and nesting deeper than 32.
"""
import json
import pathlib
import random
import subprocess
import sys

here = pathlib.Path(__file__).resolve().parent
cli = sys.argv[1] if len(sys.argv) > 1 else str(here.parent / "build/tests/json_cli")

passed = 0
failed = 0


def run(*args):
    out = subprocess.run([cli, *args], capture_output=True, text=True)
    if out.returncode != 0:
        return f"EXIT {out.returncode}: {out.stderr.strip()}"
    return out.stdout.rstrip("\n")


def check(name, got, want):
    global passed, failed
    if got == want:
        passed += 1
    else:
        failed += 1
        print(f"FAIL {name}\n  want {want!r}\n  got  {got!r}")


def dumps(v):
    return json.dumps(v, separators=(",", ":"), ensure_ascii=False)


rng = random.Random(2335)
alphabet = "abcXYZ019 _-:/,{}[]\"\\\n\t\r\x01\x1f\x7fé"


def rand_str():
    return "".join(rng.choice(alphabet) for _ in range(rng.randint(0, 8)))


def rand_value(depth):
    kind = rng.randint(0, 6 if depth < 5 else 3)
    if kind == 0:
        return None
    if kind == 1:
        return rng.choice([True, False])
    if kind == 2:
        return rng.choice([0, 1, -1, 7, 2**64 - 1, -(2**63), rng.getrandbits(64)])
    if kind == 3:
        return rand_str()
    if kind == 4:
        return [rand_value(depth + 1) for _ in range(rng.randint(0, 4))]
    keys = list(dict.fromkeys(rand_str() for _ in range(rng.randint(0, 4))))
    return {k: rand_value(depth + 1) for k in keys}


def rand_ws():
    return rng.choice(["", "", " ", "\n", "\t", " \r\n "])


def spaced(v):
    """json.dumps with random white space between tokens."""
    if isinstance(v, list):
        inner = ("," + rand_ws()).join(spaced(x) for x in v)
        return "[" + rand_ws() + inner + rand_ws() + "]"
    if isinstance(v, dict):
        inner = ("," + rand_ws()).join(
            json.dumps(k) + rand_ws() + ":" + rand_ws() + spaced(x) for k, x in v.items())
        return "{" + rand_ws() + inner + rand_ws() + "}"
    return json.dumps(v)


# Valid inputs: random values, with random white space.
for i in range(300):
    v = rand_value(0)
    text = rand_ws() + spaced(v) + rand_ws()
    check(f"parse random #{i}: {text!r}", run("parse", text), dumps(v))

# Escapes, including \u escapes that Python decodes.
for text in [r'"Aé\u0000"', r'"\/\b\f\n\r\t\"\\"', r'"ÿ"', '"tab\\tnew\\nline"']:
    check(f"parse escapes {text}", run("parse", text), dumps(json.loads(text)))

# Numbers in every valid form keep their text.
for text in ["0", "-0", "12", "-12", "1.5", "-0.25", "1e5", "1E+5", "2e-3", "0.5E10", "18446744073709551615"]:
    check(f"number {text}", run("parse", text), text)

# Field lookup.
body = '{"type":"ATTESTATION","signingRoot":"0x12","fork_info":{"fork":{"epoch":"1"}}}'
check("get type", run("get", body, "type"), '"ATTESTATION"')
check("get object", run("get", body, "fork_info"), '{"fork":{"epoch":"1"}}')
check("get missing", run("get", body, "attestation"), "ERR")
check("get on array", run("get", "[1,2]", "type"), "ERR")

# Invalid inputs.
invalid = [
    "", " ", "{", "}", "[", "]", "[1,]", "[,1]", "{,}", '{"a":1,}', '{"a" 1}', '{"a":}',
    '{1:2}', '{"a":1 "b":2}', "[1 2]", '"abc', '"a\\x"', '"\\u12"', '"\\u12g4"', "tru", "nul",
    "True", "NaN", "Infinity", "-Infinity", "01", "1.", ".5", "-", "1e", "1e+", "--1", "+1",
    "1.2.3", "0x10", '"a"b', "1 2", "{} {}", "[] x", '{"a":1}}', "[[]]]",
    '{"a":1,"a":2}', '{"x":{"k":1,"k":1}}',
    '"line\nbreak"', '"tab\tinside"', '"\x01"',
    "[" * 33 + "]" * 33,
]
for text in invalid:
    check(f"reject {text!r}", run("parse", text), "ERR")

# Depth 32 is the limit: 32 nested arrays parse.
check("depth 32", run("parse", "[" * 32 + "]" * 32), "[" * 32 + "]" * 32)

print(f"{passed} passed, {failed} failed")
sys.exit(1 if failed else 0)
