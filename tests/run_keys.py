#!/usr/bin/env python3
"""Tests key loading (src/keys.bend and src/ffi/) with keys from Lighthouse.

    ./tests/run_keys.py [lighthouse dir] [keys_cli binary]

1. tests/vectors/keys/good: every key must load, with the public key and
   the signature of root 0x42..42 that Lighthouse gives (expected.jsonl).
   The keystores use scrypt and pbkdf2, ASCII and non-ASCII passwords, and a
   password with control characters.
2. tests/vectors/keys/bad_*: the program must stop with an error.
3. The two EIP-2335 keystores in Lighthouse's own tests
   (crypto/eth2_keystore/tests/eip2335_vectors.rs) must load. Bulkhead
   checks the decrypted key against the keystore pubkey field.
"""
import json
import pathlib
import re
import subprocess
import sys
import tempfile

here = pathlib.Path(__file__).resolve().parent
lighthouse = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else here.parents[1] / "lighthouse"
cli = sys.argv[2] if len(sys.argv) > 2 else str(here.parent / "build/tests/keys_cli")
vectors = here / "vectors" / "keys"

passed = 0
failed = 0


def check(name, ok, detail=""):
    global passed, failed
    if ok:
        passed += 1
    else:
        failed += 1
        print(f"FAIL {name} {detail}")


def run(d):
    return subprocess.run([cli, str(d)], capture_output=True, text=True, timeout=120)


# 1. Good keys.
want = {}
for line in (vectors / "expected.jsonl").read_text().splitlines():
    row = json.loads(line)
    want[row["pubkey"]] = (row["name"], row["signature"])
out = run(vectors / "good")
check("good dir exits 0", out.returncode == 0, out.stderr)
got = dict(line.split() for line in out.stdout.splitlines())
check("good dir loads every key", set(got) == set(want), f"got {sorted(got)}")
for pk, (name, sig) in want.items():
    check(f"good {name} signature", got.get(pk) == sig, f"got {got.get(pk)}")

# 2. Bad keys.
bad = {
    "bad_password": "wrong password",
    "bad_duplicate": "two key files name the key",
    "bad_raw": "privateKey is not 32 bytes of hex",
    "bad_type": "unsupported key type hashicorp",
}
for d, text in bad.items():
    out = run(vectors / d)
    msg = out.stdout + out.stderr
    check(f"{d} stops", out.returncode != 0, f"exit {out.returncode}")
    check(f"{d} says why", text in msg, repr(msg[-300:]))

# 3. EIP-2335 vectors from Lighthouse.
source = (lighthouse / "crypto/eth2_keystore/tests/eip2335_vectors.rs").read_text()
keystores = re.findall(r'let vector = r#"(.*?)"#;', source, re.S)
check("found the EIP-2335 vectors", len(keystores) == 2, str(len(keystores)))
# Both vectors hold the same secret key, so each goes in its own directory.
for i, ks in enumerate(keystores):
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        (tmp / "v.json").write_text(ks)
        (tmp / "v.yaml").write_text('type: "file-keystore"\nkeystoreFile: "v.json"\nkeystorePasswordFile: "pw.txt"\n')
        (tmp / "pw.txt").write_text("testpassword\n")
        out = run(tmp)
        check(f"EIP-2335 vector {i} loads", out.returncode == 0, out.stderr)
        check(f"EIP-2335 vector {i} public key", out.stdout.split()[:1] == ["0x" + json.loads(ks)["pubkey"]], out.stdout)
        (tmp / "pw.txt").write_text("not the password\n")
        out = run(tmp)
        check(f"EIP-2335 vector {i} wrong password stops", out.returncode != 0 and "wrong password" in out.stdout + out.stderr)

print(f"{passed} passed, {failed} failed")
sys.exit(1 if failed else 0)
