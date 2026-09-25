#!/usr/bin/env python3
"""Tests src/ssz.bend through the ssz_cli binary.

    ./tests/run_ssz.py <consensus-spec-tests/tests dir> [ssz_cli binary]

Sources of truth:
- ssz_static vectors (mainnet and minimal) for the container roots: phase0
  for the phase 1 containers, and every fork for the phase 2 containers.
- A direct Python copy of the spec's merkleize, merkleize_progressive and
  bitlist roots, and of the builder spec's ValidatorRegistrationV1 root.
- hashlib for SHA-256.
- A direct Python copy of the spec's compute_domain for domains.
- Python integers for U64 parsing, printing, chunks and shifts.
"""
import hashlib
import pathlib
import random
import subprocess
import sys

import yaml

tests = pathlib.Path(sys.argv[1])
here = pathlib.Path(__file__).resolve().parent
cli = sys.argv[2] if len(sys.argv) > 2 else str(here.parent / "build/tests/ssz_cli")

passed = 0
failed = 0


def run(*args):
    out = subprocess.run([cli, *map(str, args)], capture_output=True, text=True)
    if out.returncode != 0:
        return f"EXIT {out.returncode}: {out.stderr.strip()}"
    return out.stdout.strip()


def check(name, got, want):
    global passed, failed
    if got == want:
        passed += 1
    else:
        failed += 1
        print(f"FAIL {name}\n  want {want}\n  got  {got}")


def h(b):
    return "0x" + b.hex()


rng = random.Random(7688)

# SHA-256 over two chunks.
for i in range(100):
    a, b = rng.randbytes(32), rng.randbytes(32)
    check(f"hash64 #{i}", run("hash64", h(a), h(b)), h(hashlib.sha256(a + b).digest()))
check("hash64 upper-case hex", run("hash64", "0x" + "AB" * 32, "0x" + "cd" * 32),
      h(hashlib.sha256(bytes([0xAB] * 32 + [0xCD] * 32)).digest()))
for bad in ["0x" + "00" * 31, "0x" + "00" * 33, "0x" + "0g" + "00" * 31, "", "0x"]:
    check(f"hash64 rejects {bad!r}", run("hash64", bad, "0x" + "00" * 32), "ERR")

# U64: decimal round trip, the SSZ chunk, and shifts.
edges = [0, 1, 9, 10, 2**32 - 1, 2**32, 2**48 - 1, 2**48, 2**63, 2**64 - 1,
         1844674407370955161, 1844674407370955165, 18446744073709551609]
values = edges + [rng.getrandbits(64) for _ in range(60)] + [rng.getrandbits(20) for _ in range(20)]
for v in values:
    chunk = h(v.to_bytes(8, "little") + bytes(24))
    check(f"u64 {v}", run("u64", v), f"{v} {chunk}")
    check(f"shr5 {v}", run("shr5", v), str(v >> 5))
    check(f"shr3 {v}", run("shr3", v), str(v >> 3))
check("u64 leading zeros", run("u64", "007"), f"7 {h((7).to_bytes(8, 'little') + bytes(24))}")
for bad in [str(2**64), "18446744073709551616", "99999999999999999999", "", "12a", "-1", " 1", "1.0"]:
    check(f"u64 rejects {bad!r}", run("u64", bad), "ERR")

# Container roots from ssz_static.
def u(x):
    return str(x)

commands = {
    "Checkpoint": lambda v: ["checkpoint", u(v["epoch"]), v["root"]],
    "AttestationData": lambda v: ["attdata", u(v["slot"]), u(v["index"]), v["beacon_block_root"],
                                  u(v["source"]["epoch"]), v["source"]["root"],
                                  u(v["target"]["epoch"]), v["target"]["root"]],
    "BeaconBlockHeader": lambda v: ["header", u(v["slot"]), u(v["proposer_index"]),
                                    v["parent_root"], v["state_root"], v["body_root"]],
    "Fork": lambda v: ["fork", v["previous_version"], v["current_version"], u(v["epoch"])],
    "ForkData": lambda v: ["forkdata", v["current_version"], v["genesis_validators_root"]],
    "SigningData": lambda v: ["signingdata", v["object_root"], v["domain"]],
}
cases = 0
for preset in ["mainnet", "minimal"]:
    for name, make in commands.items():
        base = tests / preset / "phase0" / "ssz_static" / name
        for case in sorted(base.glob("*/case_*")):
            value = yaml.safe_load((case / "value.yaml").read_text())
            root = yaml.safe_load((case / "roots.yaml").read_text())["root"]
            check(f"{preset} {name} {case.parent.name}/{case.name}", run(*make(value)), root)
            cases += 1
if cases == 0:
    check("ssz_static vectors found", "none", "some")

# Phase 2 containers, in every fork that has them. The preset values:
# Attestation kind, Base and Electra bitlist limits and depths,
# MAX_COMMITTEES_PER_SLOT, and the sync contribution bit count.
presets = {
    "mainnet": {"electra_limit": 131072, "electra_depth": 9, "cbits": 64, "sync_bits": 128},
    "minimal": {"electra_limit": 8192, "electra_depth": 5, "cbits": 4, "sync_bits": 8},
}
att_kind = {"phase0": "base", "altair": "base", "bellatrix": "base", "capella": "base",
            "deneb": "base", "electra": "electra", "fulu": "electra", "gloas": "gloas",
            "heze": "gloas"}


def data_args(d):
    return [u(d["slot"]), u(d["index"]), d["beacon_block_root"],
            u(d["source"]["epoch"]), d["source"]["root"],
            u(d["target"]["epoch"]), d["target"]["root"]]


def att_args(fork, p, a):
    kind = att_kind[fork]
    if kind == "base":
        head = ["base", 2048, 3, 0]
    elif kind == "electra":
        head = ["electra", p["electra_limit"], p["electra_depth"], p["cbits"]]
    else:
        head = ["gloas", 2**32 - 1, 0, p["cbits"]]
    return head + [a["aggregation_bits"]] + data_args(a["data"]) + [
        a["signature"], a.get("committee_bits", "-")]


def contribution_args(p, c):
    return [p["sync_bits"], u(c["slot"]), c["beacon_block_root"], u(c["subcommittee_index"]),
            c["aggregation_bits"], c["signature"]]


phase2 = {
    "VoluntaryExit": lambda f, p, v: ["exit", u(v["epoch"]), u(v["validator_index"])],
    "SyncAggregatorSelectionData": lambda f, p, v: ["syncsel", u(v["slot"]),
                                                    u(v["subcommittee_index"])],
    "SyncCommitteeContribution": lambda f, p, v: ["contribution", *contribution_args(p, v)],
    "ContributionAndProof": lambda f, p, v: ["contribproof", u(v["aggregator_index"]),
                                             *contribution_args(p, v["contribution"]),
                                             v["selection_proof"]],
    "Attestation": lambda f, p, v: ["att", *att_args(f, p, v)],
    "AggregateAndProof": lambda f, p, v: ["aggproof", u(v["aggregator_index"]),
                                          *att_args(f, p, v["aggregate"]), v["selection_proof"]],
}
phase2_cases = 0
for preset, p in presets.items():
    for fork in att_kind:
        for name, make in phase2.items():
            base = tests / preset / fork / "ssz_static" / name
            for case in sorted(base.glob("*/case_*")):
                value = yaml.safe_load((case / "value.yaml").read_text())
                root = yaml.safe_load((case / "roots.yaml").read_text())["root"]
                check(f"{preset} {fork} {name} {case.parent.name}/{case.name}",
                      run(*make(fork, p, value)), root)
                phase2_cases += 1
if phase2_cases < 1000:
    check("phase 2 ssz_static vectors found", phase2_cases, ">= 1000")
cases += phase2_cases


# The spec's merkleize, merkleize_progressive and bitlist roots.
def sha(a, b):
    return hashlib.sha256(a + b).digest()


def chunks_of(data):
    data = data + bytes(-len(data) % 32)
    return [data[i:i + 32] for i in range(0, len(data), 32)]


def merkleize(chunks, limit):
    size = 1
    while size < limit:
        size *= 2
    nodes = chunks + [bytes(32)] * (size - len(chunks))
    while len(nodes) > 1:
        nodes = [sha(nodes[i], nodes[i + 1]) for i in range(0, len(nodes), 2)]
    return nodes[0] if nodes else bytes(32)


def progressive(chunks, width=1):
    if not chunks:
        return bytes(32)
    return sha(merkleize(chunks[:width], width), progressive(chunks[width:], width * 4))


def mix_len(root, n):
    return sha(root, n.to_bytes(32, "little"))


def bitlist_hex(bits):
    n = len(bits)
    value = sum(1 << i for i, b in enumerate(bits) if b) | (1 << n)
    return value.to_bytes(n // 8 + 1, "little")


for n in [0, 1, 2, 5, 6, 21, 22, 85, 86, 200, 341, 342]:
    data = rng.randbytes(n * 32 - rng.randrange(0, 32) if n else 0)
    check(f"progressive {len(data)} bytes", run("progressive", h(data)),
          h(progressive(chunks_of(data))))

for n in [0, 1, 7, 8, 9, 255, 256, 257, 2047, 2048]:
    bits = [rng.random() < 0.5 for _ in range(n)]
    raw = bitlist_hex(bits)
    packed = sum(1 << i for i, b in enumerate(bits) if b).to_bytes((n + 7) // 8, "little")
    want = mix_len(merkleize(chunks_of(packed), 8), n)
    check(f"bitlist {n} bits", run("bitlist", h(raw), 2048, 3), h(want))
check("bitlist over the limit", run("bitlist", h(bitlist_hex([True] * 9)), 8, 0), "ERR")
for bad in ["0x", "0x00", "0x0100", "0x" + "ff" * 257]:
    check(f"bitlist rejects {bad}", run("bitlist", bad, 2048, 3), "ERR")

# ValidatorRegistrationV1 from the builder spec: fee_recipient (Bytes20),
# gas_limit, timestamp, pubkey (Bytes48).
for i in range(40):
    fee, pk = rng.randbytes(20), rng.randbytes(48)
    gas, ts = rng.getrandbits(64), rng.getrandbits(64)
    want = merkleize([fee + bytes(12), gas.to_bytes(32, "little"), ts.to_bytes(32, "little"),
                      merkleize(chunks_of(pk), 2)], 4)
    check(f"registration #{i}", run("registration", h(fee), gas, ts, h(pk)), h(want))
check("registration rejects a short address",
      run("registration", "0x" + "00" * 19, 1, 1, "0x" + "00" * 48), "ERR")

# compute_domain, as the spec writes it.
def fork_data_root(version, gvr):
    return hashlib.sha256(version + bytes(28) + gvr).digest()

def compute_domain(domain_type, version, gvr):
    return domain_type + fork_data_root(version, gvr)[:28]

for i in range(40):
    dt = rng.choice([bytes([d, 0, 0, 0]) for d in range(11)] + [bytes([0, 0, 0, 1])])
    prev, cur, gvr = rng.randbytes(4), rng.randbytes(4), rng.randbytes(32)
    fork_epoch = rng.getrandbits(rng.choice([8, 32, 64]))
    epoch = rng.choice([fork_epoch, max(fork_epoch - 1, 0), fork_epoch + 1, rng.getrandbits(64)])
    epoch = min(epoch, 2**64 - 1)
    want = compute_domain(dt, prev if epoch < fork_epoch else cur, gvr)
    check(f"domain #{i}", run("domain", h(dt), h(prev), h(cur), fork_epoch, epoch, h(gvr)), h(want))

print(f"{passed} passed, {failed} failed ({cases} ssz_static cases)")
sys.exit(1 if failed else 0)
