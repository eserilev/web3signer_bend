#!/usr/bin/env python3
"""Tests src/request.bend with request bodies and roots from Lighthouse.

    ./tests/run_requests.py [request_cli binary]

tests/vectors/lighthouse_requests.jsonl comes from tools/lh-vectors: the
bodies are serialized by Lighthouse's own types, and each root is the
signing root that Lighthouse computes. Bulkhead must accept each body with a
root and compute the same root, and reject each body without one.

The mutation cases check the rules in docs/SPEC.md section 6.
"""
import hashlib
import json
import pathlib
import random
import subprocess
import sys

here = pathlib.Path(__file__).resolve().parent
cli = sys.argv[1] if len(sys.argv) > 1 else str(here.parent / "build/tests/request_cli")
vectors = here / "vectors" / "lighthouse_requests.jsonl"

passed = 0
failed = 0


def run(body):
    out = subprocess.run([cli, body, config], capture_output=True, text=True)
    if out.returncode != 0:
        return f"EXIT {out.returncode}: {out.stderr.strip()}"
    return out.stdout.strip()


def check(name, got, want):
    global passed, failed
    ok = got.startswith(want) if want.startswith("ERR") else got == want
    if ok:
        passed += 1
    else:
        failed += 1
        print(f"FAIL {name}\n  want {want}\n  got  {got}")


rows = [json.loads(line) for line in vectors.read_text().splitlines()]
config = rows.pop(0)["body"] if rows and rows[0]["kind"] == "CONFIG" else ""
if not config:
    check("config line found", "none", "CONFIG")
if not rows:
    check("vectors found", "none", "some")

# Every Lighthouse body.
for i, row in enumerate(rows):
    want = f"OK {row['kind']} {row['root']}" if row["root"] else "ERR unsupported beacon_block version"
    check(f"lighthouse #{i} {row['kind']}", run(row["body"]), want)

# Mutations of accepted bodies.
rng = random.Random(42)
accepted = [r for r in rows if r["root"]]


def dump(d):
    return json.dumps(d, separators=(",", ":"))


def other_root(root):
    last = int(root[-1], 16) ^ 1
    return root[:-1] + format(last, "x")


def payload_key(d):
    for k in ["attestation", "beacon_block", "randao_reveal", "aggregation_slot",
              "aggregate_and_proof", "sync_committee_message", "sync_aggregator_selection_data",
              "contribution_and_proof", "voluntary_exit", "validator_registration"]:
        if k in d:
            return k
    raise KeyError("no payload")


by_kind = {}
for r in accepted:
    by_kind.setdefault(r["kind"], []).append(r)
sample = [r for k in sorted(by_kind) for r in rng.sample(by_kind[k], min(12, len(by_kind[k])))]
for i, row in enumerate(sample):
    kind, root = row["kind"], row["root"]
    reg = kind == "VALIDATOR_REGISTRATION"
    ok = f"OK {kind} {root}"
    base = json.loads(row["body"])

    d = dict(base); d["signingRoot"] = other_root(root)
    check(f"#{i} wrong root", run(dump(d)), "ERR signing root does not match")

    d = dict(base); del d["signingRoot"]
    check(f"#{i} no root", run(dump(d)), ok)

    d = dict(base); d["signingRoot"] = None
    check(f"#{i} null root", run(dump(d)), ok)

    d = dict(base); d["signing_root"] = d.pop("signingRoot")
    check(f"#{i} signing_root", run(dump(d)), ok)

    d = dict(base); d["signing_root"] = root
    check(f"#{i} both names, same", run(dump(d)), ok)

    d = dict(base); d["signing_root"] = other_root(root)
    check(f"#{i} both names, different", run(dump(d)), "ERR signingRoot and signing_root differ")

    d = dict(base); d["signingRoot"] = root.upper().replace("0X", "0x")
    check(f"#{i} upper-case root", run(dump(d)), ok)

    d = dict(base); d["type"] = kind.lower()
    check(f"#{i} lower-case type", run(dump(d)), ok)

    d = dict(base); d["extra"] = {"ignored": [1, 2, 3]}
    check(f"#{i} unknown field", run(dump(d)), ok)

    d = dict(base); d.pop("fork_info", None)
    check(f"#{i} no fork_info", run(dump(d)), ok if reg else "ERR missing fork_info")

    d = dict(base); del d["type"]
    check(f"#{i} no type", run(dump(d)), "ERR missing type")

    d = dict(base); d["type"] = "DEPOSIT"
    check(f"#{i} unsupported type", run(dump(d)), "ERR unsupported type")

    d = dict(base); del d[payload_key(d)]
    check(f"#{i} no payload", run(dump(d)), "ERR missing")

    if reg:
        d = dict(base); d["fork_info"] = {"fork": "ignored"}
        check(f"#{i} registration ignores fork_info", run(dump(d)), ok)
    else:
        d = json.loads(row["body"]); d["fork_info"]["fork"]["epoch"] = str(2**64)
        check(f"#{i} fork epoch overflow", run(dump(d)), "ERR invalid fork_info.fork")

        d = json.loads(row["body"]); d["fork_info"]["genesis_validators_root"] = "0x1234"
        check(f"#{i} short gvr", run(dump(d)), "ERR invalid fork_info.genesis_validators_root")

    body = row["body"]
    check(f"#{i} duplicate key", run(body[:-1] + ',"type":"' + kind + '"}'), "ERR invalid JSON")
    check(f"#{i} trailing text", run(body + "x"), "ERR invalid JSON")

    if kind == "BLOCK_V2":
        d = json.loads(row["body"]); d["beacon_block"]["version"] = d["beacon_block"]["version"].lower()
        check(f"#{i} lower-case version", run(dump(d)), ok)
        d = json.loads(row["body"]); d["beacon_block"]["version"] = "PHASE0"
        check(f"#{i} phase0 with header", run(dump(d)), "ERR unsupported beacon_block version")
        d = json.loads(row["body"]); del d["beacon_block"]["block_header"]["state_root"]
        check(f"#{i} header without state_root", run(dump(d)), "ERR invalid beacon_block.block_header")
    if kind == "ATTESTATION":
        d = json.loads(row["body"]); d["attestation"]["slot"] = int(d["attestation"]["slot"])
        check(f"#{i} bare integer slot", run(dump(d)), ok)
        d = json.loads(row["body"]); d["attestation"]["target"]["epoch"] = "-1"
        check(f"#{i} negative epoch", run(dump(d)), "ERR invalid attestation")

    if kind == "AGGREGATE_AND_PROOF":
        agg = json.loads(row["body"])["aggregate_and_proof"]
        d = json.loads(row["body"]); d["type"] = "AGGREGATE_AND_PROOF_V2"
        d["aggregate_and_proof"] = {"version": "ELECTRA", "data": agg}
        check(f"#{i} V2 wrapper", run(dump(d)), ok)
        d = json.loads(row["body"]); d["type"] = "AGGREGATE_AND_PROOF_V2"
        check(f"#{i} V2 type, bare object", run(dump(d)), ok)
        d = json.loads(row["body"]); a = d["aggregate_and_proof"]["aggregate"]
        if "committee_bits" in a:
            del a["committee_bits"]
        else:
            a["committee_bits"] = "0x" + "00" * 8
        check(f"#{i} committee_bits against the fork", run(dump(d)), "ERR invalid aggregate_and_proof")
        d = json.loads(row["body"]); d["aggregate_and_proof"]["aggregate"]["aggregation_bits"] += "00"
        check(f"#{i} bitlist without length bit", run(dump(d)), "ERR invalid aggregate_and_proof")
        d = json.loads(row["body"]); d["aggregate_and_proof"]["selection_proof"] = "0x" + "00" * 95
        check(f"#{i} short selection_proof", run(dump(d)), "ERR invalid aggregate_and_proof")
    if kind == "SYNC_COMMITTEE_CONTRIBUTION_AND_PROOF":
        d = json.loads(row["body"]); d["contribution_and_proof"]["contribution"]["aggregation_bits"] += "00"
        check(f"#{i} long contribution bits", run(dump(d)), "ERR invalid contribution_and_proof")
    if kind == "VALIDATOR_REGISTRATION":
        d = json.loads(row["body"]); d["validator_registration"]["fee_recipient"] = "0x" + "11" * 19
        check(f"#{i} short fee_recipient", run(dump(d)), "ERR invalid validator_registration")
        d = json.loads(row["body"]); d["validator_registration"]["pubkey"] = "0x" + "11" * 47
        check(f"#{i} short pubkey", run(dump(d)), "ERR invalid validator_registration")


# EIP-7044 as the spec and Web3Signer apply it: fork_info at Deneb or later
# selects the Capella version, even for an exit epoch before Deneb.
def sha(a, b):
    return hashlib.sha256(a + b).digest()


def u64(x):
    return x.to_bytes(8, "little") + bytes(24)


cfg = json.loads(config)
capella = bytes.fromhex(cfg["CAPELLA_FORK_VERSION"][2:])
deneb = int(cfg["DENEB_FORK_EPOCH"])
for i, (fork_epoch, exit_epoch) in enumerate([(deneb, 5), (deneb + 9, deneb - 1), (deneb - 1, 5),
                                              (deneb - 1, deneb + 3), (0, 0)]):
    prev, cur, gvr = bytes([1, 2, 3, 4]), bytes([5, 6, 7, 8]), bytes(range(32))
    if fork_epoch >= deneb:
        version = capella
    else:
        version = prev if exit_epoch < fork_epoch else cur
    domain = bytes([4, 0, 0, 0]) + sha(version + bytes(28), gvr)[:28]
    root = "0x" + sha(sha(u64(exit_epoch), u64(77)), domain).hex()
    body = {"type": "VOLUNTARY_EXIT", "voluntary_exit": {"epoch": str(exit_epoch), "validator_index": "77"},
            "fork_info": {"fork": {"previous_version": "0x" + prev.hex(), "current_version": "0x" + cur.hex(),
                                   "epoch": str(fork_epoch)}, "genesis_validators_root": "0x" + gvr.hex()}}
    check(f"exit rule #{i}", run(dump(body)), f"OK VOLUNTARY_EXIT {root}")

check("not JSON", run("not json"), "ERR invalid JSON")
check("empty", run(""), "ERR invalid JSON")
check("array", run("[]"), "ERR missing type")

print(f"{passed} passed, {failed} failed ({len(rows)} Lighthouse bodies)")
sys.exit(1 if failed else 0)
