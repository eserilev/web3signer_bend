#!/usr/bin/env python3
"""Crash tests: Bulkhead killed with SIGKILL at random times.

    ./tests/run_crash.py [rounds] [seed]

Client threads send attestations and blocks for three keys. Their epochs
and slots are close together, so many requests conflict. Another thread
kills the server at random times and starts it again on the same log.

After all the rounds:

- No two messages that got a signature can be slashable together: no double
  vote, no surround vote, no double block. This holds across restarts only
  if Bulkhead writes each record before it replies.
- Each signed message has its record in the log.
- Bulkhead starts again after each kill, also when the kill cut a line.

SIGKILL keeps the data that write() gave to the kernel, so SIGKILL alone
does not test fsync. tests/crash_shim.c fixes that: it holds each write to
the log in memory until fsync, so a kill loses what no fsync covered, as a
power loss does. Each fsync also waits 20 ms (BULKHEAD_SHIM_FSYNC_US), so
most kills land between a write and its fsync. With this delay the test
finds a Bulkhead that replies before fsync; with no delay it does not.
"""
import http.client
import json
import os
import pathlib
import random
import signal
import socket
import subprocess
import sys
import tempfile
import threading
import time

here = pathlib.Path(__file__).resolve().parent
root = here.parent
bulkhead = os.environ.get("BULKHEAD_BIN", str(root / "build/bulkhead"))
request_cli = str(root / "build/tests/request_cli")
keys_dir = str(here / "vectors/keys/good")

rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 30
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 3076)

expected = [json.loads(line) for line in (here / "vectors/keys/expected.jsonl").read_text().splitlines()]
KEYS = sorted(row["pubkey"] for row in expected)[:3]
GVR = "0x" + "11" * 32
FORK = {"previous_version": "0x05000000", "current_version": "0x06000000", "epoch": "100"}
ROOTS = ["0x" + c * 64 for c in "abc"]

passed = 0
failed = 0


def check(name, ok, detail=""):
    global passed, failed
    if ok:
        passed += 1
    else:
        failed += 1
        print(f"FAIL {name} {detail}")


def att(source, target, broot):
    return json.dumps({
        "type": "ATTESTATION",
        "fork_info": {"fork": FORK, "genesis_validators_root": GVR},
        "attestation": {
            "slot": str(target * 32), "index": "0", "beacon_block_root": broot,
            "source": {"epoch": str(source), "root": "0x" + "01" * 32},
            "target": {"epoch": str(target), "root": "0x" + "02" * 32},
        },
    })


def block(slot, state_root):
    return json.dumps({
        "type": "BLOCK_V2",
        "fork_info": {"fork": FORK, "genesis_validators_root": GVR},
        "beacon_block": {"version": "FULU", "block_header": {
            "slot": str(slot), "proposer_index": "7", "parent_root": "0x" + "44" * 32,
            "state_root": state_root, "body_root": "0x" + "55" * 32}},
    })


def signing_root(body):
    out = subprocess.run([request_cli, body], capture_output=True, text=True).stdout.split()
    assert out[0] == "OK", out
    return out[2]


def free_port():
    s = socket.socket()
    s.bind(("127.0.0.1", 0))
    port = s.getsockname()[1]
    s.close()
    return port


tmp = pathlib.Path(tempfile.mkdtemp())
log = tmp / "slashing.log"
port = free_port()
shim = root / "build/crash_shim.so"
subprocess.run([os.environ.get("CC", "cc"), "-shared", "-fPIC", "-O2", "-o", str(shim),
                str(here / "crash_shim.c"), "-ldl", "-lpthread"], check=True)
env = {**os.environ, "LD_PRELOAD": str(shim), "BULKHEAD_SHIM_LOG": str(log),
       "BULKHEAD_SHIM_FSYNC_US": os.environ.get("BULKHEAD_SHIM_FSYNC_US", "20000")}


def start():
    proc = subprocess.Popen([bulkhead, "--key-config-path", keys_dir, "--slashing-log", str(log),
                             "--http-listen-port", str(port)],
                            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True, env=env)
    for _ in range(200):
        try:
            socket.create_connection(("127.0.0.1", port), timeout=0.2).close()
            return proc
        except OSError:
            if proc.poll() is not None:
                return proc
            time.sleep(0.02)
    return proc


def sign(pk, body):
    try:
        c = http.client.HTTPConnection("127.0.0.1", port, timeout=5)
        c.request("POST", f"/api/v1/eth2/sign/{pk}", body=body,
                  headers={"Content-Type": "application/json", "Accept": "application/json"})
        r = c.getresponse()
        status = r.status
        r.read()
        c.close()
        return status
    except (OSError, http.client.HTTPException):
        return None


# Each signed message: (key, "A", source, target, broot) or (key, "B", slot, state_root).
signed = []
signed_lock = threading.Lock()
stop = threading.Event()
window = {"epoch": 10, "slot": 1000}
counts = {"sent": 0, "signed": 0, "refused": 0, "no answer": 0}


def client(seed):
    r = random.Random(seed)
    while not stop.is_set():
        pk = r.choice(KEYS)
        if r.random() < 0.7:
            target = window["epoch"] + r.randrange(6)
            source = max(0, target - r.randrange(4))
            msg = (pk, "A", source, target, r.choice(ROOTS))
            body = att(source, target, msg[4])
        else:
            slot = window["slot"] + r.randrange(6)
            msg = (pk, "B", slot, r.choice(ROOTS))
            body = block(slot, msg[3])
        status = sign(pk, body)
        if status is None:
            time.sleep(0.005)
        with signed_lock:
            counts["sent"] += 1
            if status == 200:
                counts["signed"] += 1
                signed.append(msg)
            elif status is None:
                counts["no answer"] += 1
            else:
                counts["refused"] += 1


proc = start()
check("first start", proc.poll() is None)
threads = [threading.Thread(target=client, args=(i,)) for i in range(6)]
for t in threads:
    t.start()
for n in range(rounds):
    time.sleep(rng.uniform(0.02, 0.3))
    proc.send_signal(signal.SIGKILL)
    proc.wait()
    window["epoch"] += 1
    window["slot"] += 1
    proc = start()
    if proc.poll() is not None:
        check(f"restart after kill {n}", False, proc.stderr.read()[:300])
        break
stop.set()
for t in threads:
    t.join()
proc.send_signal(signal.SIGTERM)
proc.wait(timeout=10)
check(f"restarted after each of {rounds} kills", failed == 0)

# No slashable pair among the signed messages.
by_key = {}
for m in set(signed):
    by_key.setdefault(m[0], []).append(m)
slashable = []
for pk, ms in by_key.items():
    atts = [m for m in ms if m[1] == "A"]
    blocks = [m for m in ms if m[1] == "B"]
    for i, a in enumerate(atts):
        for b in atts[i + 1:]:
            (_, _, s1, t1, r1), (_, _, s2, t2, r2) = a, b
            if t1 == t2 and (s1, r1) != (s2, r2):
                slashable.append(("double vote", a, b))
            elif (s1 < s2 and t2 < t1) or (s2 < s1 and t1 < t2):
                slashable.append(("surround vote", a, b))
    for i, a in enumerate(blocks):
        for b in blocks[i + 1:]:
            if a[2] == b[2] and a[3] != b[3]:
                slashable.append(("double block", a, b))
check("no slashable pair was signed", not slashable, str(slashable[:3]))

# Each signed message has its record in the log.
log_lines = set(log.read_text().splitlines())
missing = []
for m in set(signed):
    if m[1] == "A":
        root = signing_root(att(m[2], m[3], m[4]))
        line = f"A {m[0]} {m[2]} {m[3]} {root}"
    else:
        root = signing_root(block(m[2], m[3]))
        line = f"B {m[0]} {m[2]} {root}"
    if line not in log_lines:
        missing.append(line)
check("each signed message is in the log", not missing, str(missing[:3]))

print(f"{counts['sent']} requests: {counts['signed']} signed, {counts['refused']} refused, "
      f"{counts['no answer']} without an answer; {rounds} kills")
print(f"{passed} passed, {failed} failed")
sys.exit(1 if failed else 0)
