#!/usr/bin/env python3
"""End-to-end tests of the Bulkhead server (main.bend).

    ./tests/run_server.py

Needs build/bulkhead, build/tests/request_cli and build/phase0/sign.

Oracles, each tested against Lighthouse elsewhere:
- request_cli computes the signing root of a body (tests/run_requests.py).
- build/phase0/sign signs a root with a secret key (spike/phase0).
The keys are tests/vectors/keys/good; their secrets follow from tools/lh-vectors.
"""
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
import http.client

here = pathlib.Path(__file__).resolve().parent
root = here.parent
bulkhead = str(root / "build/bulkhead")
request_cli = str(root / "build/tests/request_cli")
signer = str(root / "build/phase0/sign")
keys_dir = str(here / "vectors/keys/good")

passed = 0
failed = 0


def check(name, ok, detail=""):
    global passed, failed
    if ok:
        passed += 1
    else:
        failed += 1
        print(f"FAIL {name} {detail}")


# Keys: public key -> secret key hex (see tools/lh-vectors, mod keys).
def secret(i):
    return "0x" + bytes([0, 0x19] + [0] * 29 + [i + 1]).hex()


expected = [json.loads(line) for line in (here / "vectors/keys/expected.jsonl").read_text().splitlines()]
order = {"scrypt_ascii": 0, "pbkdf2_ascii": 1, "scrypt_nfkd": 2, "pbkdf2_nfkd": 3, "scrypt_control": 4,
         "scrypt_default": 5, "raw": 10}
secrets = {row["pubkey"]: secret(order[row["name"]]) for row in expected}
pubkeys = sorted(secrets)
PK = pubkeys[0]
PK2 = pubkeys[1]
GVR = "0x" + "11" * 32
FORK = {"previous_version": "0x05000000", "current_version": "0x06000000", "epoch": "100"}


def signing_root(body):
    out = subprocess.run([request_cli, body], capture_output=True, text=True).stdout.split()
    assert out[0] == "OK", out
    return out[2]


def oracle(pk, root_hex):
    return subprocess.run([signer, secrets[pk], root_hex], capture_output=True, text=True).stdout.strip()


def att(source, target, broot="0x" + "aa" * 32, gvr=GVR, slot=None):
    return json.dumps({
        "type": "ATTESTATION",
        "fork_info": {"fork": FORK, "genesis_validators_root": gvr},
        "attestation": {
            "slot": str(slot if slot is not None else target * 32), "index": "0",
            "beacon_block_root": broot,
            "source": {"epoch": str(source), "root": "0x" + "01" * 32},
            "target": {"epoch": str(target), "root": "0x" + "02" * 32},
        },
    })


def block(slot, state_root="0x" + "33" * 32, gvr=GVR):
    return json.dumps({
        "type": "BLOCK_V2",
        "fork_info": {"fork": FORK, "genesis_validators_root": gvr},
        "beacon_block": {"version": "FULU", "block_header": {
            "slot": str(slot), "proposer_index": "7", "parent_root": "0x" + "44" * 32,
            "state_root": state_root, "body_root": "0x" + "55" * 32}},
    })


def randao(epoch, gvr=GVR):
    return json.dumps({"type": "RANDAO_REVEAL", "fork_info": {"fork": FORK, "genesis_validators_root": gvr},
                       "randao_reveal": {"epoch": str(epoch)}})


class Server:
    def __init__(self, log, port, keys=keys_dir):
        self.port = port
        self.proc = subprocess.Popen(
            [bulkhead, "--key-config-path", keys, "--slashing-log", log, "--http-listen-port", str(port)],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        self.banner = self.proc.stdout.readline()
        for _ in range(100):
            try:
                socket.create_connection(("127.0.0.1", port), timeout=0.2).close()
                return
            except OSError:
                if self.proc.poll() is not None:
                    return
                time.sleep(0.05)

    def stop(self):
        if self.proc.poll() is None:
            self.proc.send_signal(signal.SIGTERM)
            self.proc.wait(timeout=10)

    def req(self, method, path, body=None, headers=None):
        c = http.client.HTTPConnection("127.0.0.1", self.port, timeout=30)
        c.request(method, path, body=body, headers=headers or {})
        r = c.getresponse()
        out = (r.status, r.getheader("Content-Type"), r.read().decode())
        c.close()
        return out

    def sign(self, pk, body, accept="application/json"):
        return self.req("POST", f"/api/v1/eth2/sign/{pk}", body,
                        {"Content-Type": "application/json", "Accept": accept})


def free_port():
    s = socket.socket()
    s.bind(("127.0.0.1", 0))
    port = s.getsockname()[1]
    s.close()
    return port


def expect_sig(name, resp, pk, body):
    status, ctype, text = resp
    want = oracle(pk, signing_root(body))
    ok = status == 200 and ctype.startswith("application/json") and json.loads(text).get("signature") == want
    check(name, ok, f"{resp} want {want}")


tmp = pathlib.Path(tempfile.mkdtemp())
log = str(tmp / "slashing.log")
port = free_port()
s = Server(log, port)
check("starts", s.proc.poll() is None and "7 keys" in s.banner, s.banner)

# Phase 2 bodies from Lighthouse (tests/vectors), with this test's gvr. A
# registration comes first: it has no gvr, so it must not set the gvr of the
# database (see "log has a G line first" below).
vector_rows = [json.loads(line) for line in (here / "vectors/lighthouse_requests.jsonl").read_text().splitlines()]
phase2_bodies = {}
for row in vector_rows:
    if row["kind"] in ("CONFIG", "ATTESTATION", "BLOCK_V2", "RANDAO_REVEAL", "AGGREGATION_SLOT"):
        continue
    d = json.loads(row["body"])
    d.pop("signingRoot", None)
    if "fork_info" in d:
        d["fork_info"]["genesis_validators_root"] = GVR
    phase2_bodies.setdefault(row["kind"], []).append(json.dumps(d))
reg = phase2_bodies["VALIDATOR_REGISTRATION"][0]
expect_sig("registration before any gvr", s.sign(PK, reg), PK, reg)
for kind, bodies in sorted(phase2_bodies.items()):
    for j, b in enumerate(bodies[:3]):
        expect_sig(f"{kind} #{j}", s.sign(PK, b), PK, b)
largest = max(phase2_bodies["AGGREGATE_AND_PROOF"], key=len)
t0 = time.time()
resp = s.sign(PK, largest)
elapsed = time.time() - t0
expect_sig(f"largest aggregate ({len(largest)} bytes)", resp, PK, largest)
check(f"largest aggregate in under 1 s ({elapsed:.2f} s)", elapsed < 1.0)

# Basic endpoints.
check("upcheck", s.req("GET", "/upcheck") == (200, "text/plain; charset=utf-8", "OK"))
status, ctype, text = s.req("GET", "/api/v1/eth2/publicKeys")
check("publicKeys", status == 200 and sorted(json.loads(text)) == pubkeys, text)
check("unknown path", s.req("GET", "/nope")[0] == 404)
check("wrong method", s.req("GET", f"/api/v1/eth2/sign/{PK}")[0] == 405)
check("unknown key", s.sign("0x" + "ab" * 48, att(1, 2))[0] == 404)
check("bad key hex", s.sign("0xzz", att(1, 2))[0] == 404)
check("invalid JSON", s.sign(PK, "{")[0] == 400)
bad_root = json.loads(att(1, 2))
bad_root["signingRoot"] = "0x" + "00" * 32
check("wrong signingRoot", s.sign(PK, json.dumps(bad_root))[0] == 400)

# Signing: attestation, block, randao, with the root and signature oracles.
expect_sig("attestation", s.sign(PK, att(10, 11)), PK, att(10, 11))
expect_sig("block", s.sign(PK, block(400)), PK, block(400))
expect_sig("randao", s.sign(PK, randao(12)), PK, randao(12))
expect_sig("other key", s.sign(PK2, att(10, 11)), PK2, att(10, 11))
good_root = json.loads(att(20, 21))
good_root["signingRoot"] = signing_root(att(20, 21))
expect_sig("right signingRoot", s.sign(PK, json.dumps(good_root)), PK, att(20, 21))
status, ctype, text = s.sign(PK, randao(13), accept="text/plain")
check("text/plain signature", status == 200 and ctype.startswith("text/plain") and text == oracle(PK, signing_root(randao(13))), text)
status, ctype, text = s.sign(PK.upper().replace("0X", "0x")[2:], randao(14))
check("key without 0x, upper case", status == 200, text)

# Slashing protection.
expect_sig("repeat attestation", s.sign(PK, att(10, 11)), PK, att(10, 11))
check("double vote", s.sign(PK, att(10, 11, broot="0x" + "bb" * 32)) == (412, "text/plain; charset=utf-8", "double vote"))
check("surrounding vote", s.sign(PK, att(9, 12))[2] == "surrounding vote")
expect_sig("attestation 30-40", s.sign(PK, att(30, 40)), PK, att(30, 40))
check("surrounded vote", s.sign(PK, att(31, 39))[2] == "surrounded vote")
check("source after target", s.sign(PK, att(5, 4))[2] == "source epoch after target epoch")
expect_sig("repeat block", s.sign(PK, block(400)), PK, block(400))
check("double block", s.sign(PK, block(400, state_root="0x" + "66" * 32))[2] == "double block proposal")
check("other key is separate", s.sign(PK2, block(400, state_root="0x" + "66" * 32))[0] == 200)
check("other gvr", s.sign(PK, att(50, 51, gvr="0x" + "22" * 32))[2] == "genesis validators root does not match the database")
check("other gvr, randao", s.sign(PK, randao(15, gvr="0x" + "22" * 32))[0] == 412)

# HTTP: keep-alive, pipelining, split writes, bad requests.
def raw(data_parts, read_until_close=True):
    c = socket.create_connection(("127.0.0.1", port), timeout=10)
    for part in data_parts:
        c.sendall(part)
        time.sleep(0.05)
    out = b""
    try:
        while True:
            d = c.recv(65536)
            if not d:
                break
            out += d
            if not read_until_close and out.count(b"HTTP/1.1") >= 2 and out.endswith(b"OK"):
                break
    except socket.timeout:
        pass
    c.close()
    return out

one = b"GET /upcheck HTTP/1.1\r\nHost: x\r\n\r\n"
out = raw([one + one + b"GET /upcheck HTTP/1.1\r\nConnection: close\r\n\r\n"])
check("pipelined requests", out.count(b"HTTP/1.1 200 OK") == 3, out[:200])
body = att(60, 61).encode()
req = (f"POST /api/v1/eth2/sign/{PK} HTTP/1.1\r\nContent-Type: application/json\r\nAccept: application/json\r\n"
       f"Content-Length: {len(body)}\r\nConnection: close\r\n\r\n").encode() + body
out = raw([req[:10], req[10:70], req[70:200], req[200:]])
check("request split over writes", b"200 OK" in out and oracle(PK, signing_root(att(60, 61))).encode() in out, out[:300])
out = raw(["POST /api/v1/eth2/sign/x HTTP/1.1\r\nContent-Length: 4\r\n\r\n{é}".encode()])
check("non-ASCII body", out.startswith(b"HTTP/1.1 400"), out[:100])
out = raw([b"POST /upcheck HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n"])
check("chunked body", out.startswith(b"HTTP/1.1 501"), out[:100])
out = raw([b"GARBAGE\r\n\r\n"])
check("bad request line", out.startswith(b"HTTP/1.1 400"), out[:100])
out = raw([b"GET /upcheck HTTP/1.1\r\nContent-Length: 99999999\r\n\r\n"])
check("huge Content-Length", out.startswith(b"HTTP/1.1 400"), out[:100])
c = http.client.HTTPConnection("127.0.0.1", port, timeout=10)
for i in range(5):
    c.request("GET", "/upcheck")
    r = c.getresponse()
    r.read()
check("keep-alive reuses one connection", r.status == 200)
c.close()

# Concurrency: many clients at once, one key, distinct targets.
results = {}
def worker(i):
    results[i] = s.sign(PK2, att(100 + i, 100 + i))
threads = [threading.Thread(target=worker, args=(i,)) for i in range(30)]
for t in threads:
    t.start()
for t in threads:
    t.join()
check("30 concurrent requests sign", all(results[i][0] == 200 for i in range(30)),
      str([results[i][:1] for i in range(30)]))

# Persistence: restart with the same log.
s.stop()
log_text = pathlib.Path(log).read_text()
check("log has a G line first", log_text.startswith("G " + GVR), log_text[:80])
s = Server(log, port)
check("restarts", s.proc.poll() is None, s.banner)
check("after restart: double block still refused", s.sign(PK, block(400, state_root="0x" + "77" * 32))[2] == "double block proposal")
check("after restart: surround still refused", s.sign(PK, att(29, 41))[2] == "surrounding vote")
expect_sig("after restart: repeat still signs", s.sign(PK, att(30, 40)), PK, att(30, 40))
check("after restart: gvr still bound", s.sign(PK, randao(16, gvr="0x" + "22" * 32))[0] == 412)
s.stop()

# A torn last line: Bulkhead starts, drops it, and appends on a new line.
with open(log, "a") as f:
    f.write("A 0x" + "ab" * 48 + " 1 2 0x12")
s = Server(log, port)
check("torn tail: starts", s.proc.poll() is None, s.banner)
check("torn tail: removed", pathlib.Path(log).read_text().endswith("\n"))
expect_sig("torn tail: signs", s.sign(PK, att(200, 201)), PK, att(200, 201))
s.stop()
check("torn tail: log still parses", all(line.split()[0] in "GBA" for line in pathlib.Path(log).read_text().splitlines()))

# A corrupt complete line: Bulkhead does not start.
with open(log, "a") as f:
    f.write("B not-a-key 1 -\n")
s = Server(log, port)
s.proc.wait(timeout=10)
check("corrupt log: refuses to start", s.proc.returncode != 0)

print(f"{passed} passed, {failed} failed")
sys.exit(1 if failed else 0)
