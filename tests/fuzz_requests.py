#!/usr/bin/env python3
"""Differential fuzzing of request decoding and signing roots.

    ./tests/fuzz_requests.py [iterations] [seed] [request_cli binary]

Each input is a mutation of a Lighthouse request body from
tests/vectors/lighthouse_requests.jsonl. request_cli decodes it and prints
its signing root, and a separate Python model of docs/SPEC.md does the same.
For each input:

- request_cli must exit, print one line, and finish within TIME_LIMIT.
- request_cli must accept the input if and only if the model accepts it.
- If both accept it, the two signing roots must be equal.

Before the fuzzing starts, the model must give Lighthouse's own root for each
of the Lighthouse bodies, so the model is checked against Lighthouse too.

Each failure is saved under build/fuzz/ as the input and the two results.
"""
import copy
import hashlib
import json
import pathlib
import random
import subprocess
import sys
import time

here = pathlib.Path(__file__).resolve().parent
root_dir = here.parent
iterations = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 7916
cli = sys.argv[3] if len(sys.argv) > 3 else str(root_dir / "build/tests/request_cli")
out_dir = root_dir / "build/fuzz"

TIME_LIMIT = 1.0
MAX_ARG = 120_000

rows = [json.loads(line) for line in (here / "vectors/lighthouse_requests.jsonl").read_text().splitlines()]
config_text = rows.pop(0)["body"]
config = json.loads(config_text)


# The network
# ===========

def config_word(k):
    return config[k].split()[0].strip("'\"")


GENESIS = bytes.fromhex(config_word("GENESIS_FORK_VERSION")[2:])
CAPELLA = bytes.fromhex(config_word("CAPELLA_FORK_VERSION")[2:])
DENEB = int(config_word("DENEB_FORK_EPOCH"))
ELECTRA = int(config_word("ELECTRA_FORK_EPOCH"))
GLOAS = int(config_word("GLOAS_FORK_EPOCH")) if "GLOAS_FORK_EPOCH" in config else 2**64 - 1
assert config_word("PRESET_BASE") == "mainnet"
LOG_SPE = 5
BASE_LIMIT, BASE_DEPTH = 2048, 3
ELECTRA_LIMIT, ELECTRA_DEPTH = 131072, 9
COMMITTEE_BITS = 64
SYNC_BITS = 128
U64_MAX = 2**64 - 1


class Reject(Exception):
    pass


def need(cond):
    if not cond:
        raise Reject()


# SSZ
# ===

def sha(a, b):
    return hashlib.sha256(a + b).digest()


def chunks(data):
    data = data + bytes(-len(data) % 32)
    return [data[i:i + 32] for i in range(0, len(data), 32)]


ZERO = [bytes(32)]
for _ in range(40):
    ZERO.append(sha(ZERO[-1], ZERO[-1]))


def merkleize(cs, depth):
    nodes = list(cs)
    for d in range(depth):
        if len(nodes) % 2:
            nodes.append(ZERO[d])
        nodes = [sha(nodes[i], nodes[i + 1]) for i in range(0, len(nodes), 2)]
    return nodes[0] if nodes else ZERO[depth]


def progressive(cs, width=1, depth=0):
    if not cs:
        return bytes(32)
    return sha(merkleize(cs[:width], depth), progressive(cs[width:], width * 4, depth + 2))


def u64(v):
    return v.to_bytes(8, "little") + bytes(24)


def mix_len(r, n):
    return sha(r, n.to_bytes(32, "little"))


def container(fields):
    depth = max(0, (len(fields) - 1).bit_length())
    return merkleize(fields, depth)


# A domain type is 4 bytes. DOMAIN_BEACON_ATTESTER is 01 00 00 00, so
# message domains are their number in the first byte.
def compute_domain(domain_type, version, gvr):
    if isinstance(domain_type, int):
        domain_type = bytes([domain_type, 0, 0, 0])
    return domain_type + sha(version + bytes(28), gvr)[:28]


DOMAIN_APPLICATION_BUILDER = bytes([0, 0, 0, 1])


def fork_version(fork, epoch):
    prev, cur, fork_epoch = fork
    return prev if epoch < fork_epoch else cur


# JSON, as Bulkhead reads it
# ==========================

class Num:
    def __init__(self, text):
        self.text = text


def no_dups(pairs):
    keys = [k for k, _ in pairs]
    need(len(keys) == len(set(keys)))
    return dict(pairs)


def reject_constant(_):
    raise Reject()


def text_depth(s):
    """The deepest nesting of arrays and objects in s, outside strings."""
    depth = best = 0
    in_str = esc = False
    for c in s:
        if in_str:
            if esc:
                esc = False
            elif c == "\\":
                esc = True
            elif c == '"':
                in_str = False
        elif c == '"':
            in_str = True
        elif c in "[{":
            depth += 1
            best = max(best, depth)
        elif c in "]}":
            depth -= 1
    return best


def parse_json(s):
    need(text_depth(s) <= 32)
    try:
        return json.loads(s, object_pairs_hook=no_dups, parse_int=Num, parse_float=Num,
                          parse_constant=reject_constant)
    except (ValueError, RecursionError):
        raise Reject()


def get(o, k):
    need(isinstance(o, dict) and k in o)
    return o[k]


def text(v):
    need(isinstance(v, str))
    return v


def dec_u64(v):
    s = v.text if isinstance(v, Num) else text(v)
    need(len(s) > 0 and all("0" <= c <= "9" for c in s))
    n = int(s)
    need(n <= U64_MAX)
    return n


def strip_hex(s):
    return s[2:] if s[:2] in ("0x", "0X") else s


HEXDIGITS = set("0123456789abcdefABCDEF")


def dec_bytes(v):
    s = strip_hex(text(v))
    need(len(s) % 2 == 0 and all(c in HEXDIGITS for c in s))
    return bytes.fromhex(s)


def dec_fixed(v, n):
    b = dec_bytes(v)
    need(len(b) == n)
    return b


def dec_b32(v):
    return dec_fixed(v, 32)


def dec_bytes4(v):
    return dec_fixed(v, 4)


def dec_sig_root(v):
    return merkleize(chunks(dec_fixed(v, 96)), 2)


def dec_bitlist(v, limit):
    b = dec_bytes(v)
    need(len(b) > 0 and b[-1] != 0)
    n = (len(b) - 1) * 8 + b[-1].bit_length() - 1
    need(n <= limit)
    value = int.from_bytes(b, "little") - (1 << n)
    return chunks(value.to_bytes((n + 7) // 8, "little")), n


def dec_bitvector(v, bits):
    b = dec_bytes(v)
    need(len(b) == (bits + 7) // 8)
    used = bits % 8 or 8
    need(b[-1] < (1 << used))
    return chunks(b)[0] if b else bytes(32)


def checkpoint(o):
    return sha(u64(dec_u64(get(o, "epoch"))), dec_b32(get(o, "root")))


def attestation_data(o):
    slot = dec_u64(get(o, "slot"))
    index = dec_u64(get(o, "index"))
    bbr = dec_b32(get(o, "beacon_block_root"))
    source = checkpoint(get(o, "source"))
    target_o = get(o, "target")
    target_epoch = dec_u64(get(target_o, "epoch"))
    target = checkpoint(target_o)
    r = container([u64(slot), u64(index), bbr, source, target])
    return r, slot, target_epoch


# Messages: (domain type, epoch or None, object root, special domain)
# ===================================================================

def m_attestation(body):
    r, slot, target_epoch = attestation_data(get(body, "attestation"))
    return 1, target_epoch, r


def m_block(body):
    bb = get(body, "beacon_block")
    version = text(get(bb, "version")).upper()
    need(version in ("BELLATRIX", "CAPELLA", "DENEB", "ELECTRA", "FULU", "GLOAS", "HEZE"))
    h = get(bb, "block_header")
    slot = dec_u64(get(h, "slot"))
    r = container([u64(slot), u64(dec_u64(get(h, "proposer_index"))), dec_b32(get(h, "parent_root")),
                   dec_b32(get(h, "state_root")), dec_b32(get(h, "body_root"))])
    return 0, slot >> LOG_SPE, r


def m_randao(body):
    e = dec_u64(get(get(body, "randao_reveal"), "epoch"))
    return 2, e, u64(e)


def m_agg_slot(body):
    s = dec_u64(get(get(body, "aggregation_slot"), "slot"))
    return 5, s >> LOG_SPE, u64(s)


def aggregate_attestation(a):
    data_root, slot, _ = attestation_data(get(a, "data"))
    sig = dec_sig_root(get(a, "signature"))
    epoch = slot >> LOG_SPE
    if epoch < ELECTRA:
        need("committee_bits" not in a)
        cs, n = dec_bitlist(get(a, "aggregation_bits"), BASE_LIMIT)
        r = container([mix_len(merkleize(cs, BASE_DEPTH), n), data_root, sig])
    elif epoch < GLOAS:
        cs, n = dec_bitlist(get(a, "aggregation_bits"), ELECTRA_LIMIT)
        cb = dec_bitvector(get(a, "committee_bits"), COMMITTEE_BITS)
        r = container([mix_len(merkleize(cs, ELECTRA_DEPTH), n), data_root, sig, cb])
    else:
        cs, n = dec_bitlist(get(a, "aggregation_bits"), ELECTRA_LIMIT)
        cb = dec_bitvector(get(a, "committee_bits"), COMMITTEE_BITS)
        r = sha(progressive([mix_len(progressive(cs), n), data_root, sig, cb]), bytes([15]) + bytes(31))
    return r, slot


def m_aggregate(body):
    o = get(body, "aggregate_and_proof")
    if isinstance(o, dict) and "version" in o and "data" in o:
        o = o["data"]
    ai = dec_u64(get(o, "aggregator_index"))
    att_root, slot = aggregate_attestation(get(o, "aggregate"))
    sel = dec_sig_root(get(o, "selection_proof"))
    return 6, slot >> LOG_SPE, container([u64(ai), att_root, sel])


def m_sync_msg(body):
    o = get(body, "sync_committee_message")
    slot = dec_u64(get(o, "slot"))
    return 7, slot >> LOG_SPE, dec_b32(get(o, "beacon_block_root"))


def m_sync_sel(body):
    o = get(body, "sync_aggregator_selection_data")
    slot = dec_u64(get(o, "slot"))
    sub = dec_u64(get(o, "subcommittee_index"))
    return 8, slot >> LOG_SPE, container([u64(slot), u64(sub)])


def m_contribution(body):
    o = get(body, "contribution_and_proof")
    ai = dec_u64(get(o, "aggregator_index"))
    c = get(o, "contribution")
    slot = dec_u64(get(c, "slot"))
    r = container([u64(slot), dec_b32(get(c, "beacon_block_root")), u64(dec_u64(get(c, "subcommittee_index"))),
                   dec_bitvector(get(c, "aggregation_bits"), SYNC_BITS), dec_sig_root(get(c, "signature"))])
    sel = dec_sig_root(get(o, "selection_proof"))
    return 9, slot >> LOG_SPE, container([u64(ai), r, sel])


def m_exit(body):
    o = get(body, "voluntary_exit")
    e = dec_u64(get(o, "epoch"))
    vi = dec_u64(get(o, "validator_index"))
    return "exit", e, container([u64(e), u64(vi)])


def m_registration(body):
    o = get(body, "validator_registration")
    fee = dec_fixed(get(o, "fee_recipient"), 20)
    gas = dec_u64(get(o, "gas_limit"))
    ts = dec_u64(get(o, "timestamp"))
    pk_text = strip_hex(text(get(o, "pubkey")))
    need(len(pk_text) == 96 and all(c in HEXDIGITS for c in pk_text))
    pk = bytes.fromhex(pk_text)
    r = container([fee + bytes(12), u64(gas), u64(ts), merkleize(chunks(pk), 1)])
    return "registration", None, r


MESSAGES = {
    "ATTESTATION": m_attestation,
    "BLOCK_V2": m_block,
    "RANDAO_REVEAL": m_randao,
    "AGGREGATION_SLOT": m_agg_slot,
    "AGGREGATE_AND_PROOF": m_aggregate,
    "AGGREGATE_AND_PROOF_V2": m_aggregate,
    "SYNC_COMMITTEE_MESSAGE": m_sync_msg,
    "SYNC_COMMITTEE_SELECTION_PROOF": m_sync_sel,
    "SYNC_COMMITTEE_CONTRIBUTION_AND_PROOF": m_contribution,
    "VOLUNTARY_EXIT": m_exit,
    "VALIDATOR_REGISTRATION": m_registration,
}


def claimed_root(body):
    found = []
    for k in ("signingRoot", "signing_root"):
        if k in body and body[k] is not None:
            found.append(dec_b32(body[k]))
    need(len(found) < 2 or found[0] == found[1])
    return found[0] if found else None


def model(s):
    """The signing root that docs/SPEC.md gives for body s, or Reject."""
    body = parse_json(s)
    need(isinstance(body, dict))
    kind = text(get(body, "type"))
    need(all(ord(c) < 128 for c in kind))
    m = MESSAGES.get(kind.upper())
    need(m is not None)
    domain_type, epoch, obj = m(body)
    if domain_type == "registration":
        domain = compute_domain(DOMAIN_APPLICATION_BUILDER, GENESIS, bytes(32))
    else:
        fi = get(body, "fork_info")
        f = get(fi, "fork")
        fork = (dec_bytes4(get(f, "previous_version")), dec_bytes4(get(f, "current_version")),
                dec_u64(get(f, "epoch")))
        gvr = dec_b32(get(fi, "genesis_validators_root"))
        if domain_type == "exit":
            if fork[2] < DENEB:
                domain = compute_domain(4, fork_version(fork, epoch), gvr)
            else:
                domain = compute_domain(4, CAPELLA, gvr)
        else:
            domain = compute_domain(domain_type, fork_version(fork, epoch), gvr)
    r = sha(obj, domain)
    claimed = claimed_root(body)
    need(claimed is None or claimed == r)
    return "0x" + r.hex()


# Running Bulkhead
# ================

def run(body):
    t = time.monotonic()
    try:
        out = subprocess.run([cli, body, config_text], capture_output=True, text=True, timeout=30)
        result = out.stdout.strip() if out.returncode == 0 else f"EXIT {out.returncode}: {out.stderr.strip()[:200]}"
    except subprocess.TimeoutExpired:
        result = "TIMEOUT"
    return result, time.monotonic() - t


def classify(result):
    parts = result.split()
    if len(parts) == 3 and parts[0] == "OK":
        return "OK", parts[2]
    if parts and parts[0] == "ERR" and "\n" not in result:
        return "ERR", None
    return "BAD", None


passed = 0
failed = 0
accepted_count = 0


def fail(name, body, detail):
    global failed
    failed += 1
    out_dir.mkdir(parents=True, exist_ok=True)
    path = out_dir / f"fail-{failed}.json"
    path.write_text(json.dumps({"name": name, "detail": detail, "body": body}))
    print(f"FAIL {name}: {detail} ({path})")


def compare(name, body):
    global passed, accepted_count
    if len(body) > MAX_ARG:
        return
    result, elapsed = run(body)
    try:
        want = ("OK", model(body))
    except Reject:
        want = ("ERR", None)
    got = classify(result)
    if got[0] == "BAD":
        fail(name, body, f"bad output: {result[:200]}")
    elif elapsed > TIME_LIMIT:
        fail(name, body, f"took {elapsed:.2f} s")
    elif got != want:
        fail(name, body, f"bulkhead {result[:120]}, model {want}")
    else:
        passed += 1
        if got[0] == "OK":
            accepted_count += 1


# Mutations
# =========

rng = random.Random(seed)

U64_EDGES = ["0", "1", "007", str(U64_MAX), str(U64_MAX + 1), "99999999999999999999999", "-1", "", " 1",
             "1 ", "1.0", "0x10", "+1"]
RAW_NUMBERS = ["0", "1", "18446744073709551615", "18446744073709551616", "-0", "-1", "1.0", "1e3", "0.5",
               "1E+2", "123456789012345678901234567890"]
OTHER_VALUES = [None, True, False, [], {}, [1], {"a": 1}]


def boundary_slots():
    out = []
    for e in (DENEB, ELECTRA, GLOAS):
        if e < 2**59:
            out += [(e << LOG_SPE) - 1, e << LOG_SPE, (e << LOG_SPE) + 31, (e << LOG_SPE) + 32]
    return [str(s) for s in out if 0 <= s <= U64_MAX]


def hex_variants(s):
    h = strip_hex(s)
    out = [h, "0X" + h, "0x" + h.upper(), "0x" + h[:-1], "0x" + h + "0", "0x" + h[:-2], "0x" + h + "00",
           "0x", "0", "0x" + "g" + h[1:], "0x" + h.replace(h[:1], "z", 1), "0x 0" + h[1:]]
    if h:
        last = int(h[-2:], 16) if len(h) >= 2 else 0
        for b in (0, 1, 0x80, 0xff, (last << 1) & 0xff, last >> 1):
            out.append("0x" + h[:-2] + f"{b:02x}")
    return out


def bitlist_values(limit):
    def encode(n, fill):
        value = (int.from_bytes(fill(n), "little") & ((1 << n) - 1)) | (1 << n)
        return "0x" + value.to_bytes(n // 8 + 1, "little").hex()
    ones = lambda n: b"\xff" * (n // 8 + 1)
    rand = lambda n: rng.randbytes(n // 8 + 1)
    out = []
    for n in (0, 1, 7, 8, 9, 255, 256, 2047, 2048, 2049, limit - 1, limit, limit + 1):
        if 0 <= n <= 140000:
            out.append(encode(n, rng.choice([ones, rand])))
    return out


def leaves(v, path=()):
    if isinstance(v, dict):
        for k, x in v.items():
            yield from leaves(x, path + (k,))
    elif isinstance(v, list):
        for i, x in enumerate(v):
            yield from leaves(x, path + (i,))
    else:
        yield path, v


def containers(v, path=()):
    if isinstance(v, dict):
        yield path, v
        for k, x in v.items():
            yield from containers(x, path + (k,))


def set_at(v, path, value):
    if not path:
        return value
    v[path[0]] = set_at(v[path[0]], path[1:], value)
    return v


class Raw:
    """A JSON number, written as its text."""

    def __init__(self, text):
        self.text = text


def dump(v, style):
    """JSON text for v. Raw values are written as they are. style picks the
    spacing, so the model and Bulkhead also see unusual whitespace."""
    sep, colon = style
    if isinstance(v, Raw):
        return v.text
    if isinstance(v, dict):
        return "{" + sep.join(json.dumps(k) + colon + dump(x, style) for k, x in v.items()) + "}"
    if isinstance(v, list):
        return "[" + sep.join(dump(x, style) for x in v) + "]"
    return json.dumps(v)


STYLES = [(",", ":"), (", ", ": "), (",\n  ", " :\t"), (" , ", ":")]


def mutate_leaf(body):
    path, value = rng.choice(list(leaves(body)))
    key = path[-1] if path else ""
    choice = rng.random()
    if key in ("slot",) and choice < 0.3:
        new = rng.choice(boundary_slots())
    elif isinstance(value, str) and value.startswith("0x") and choice < 0.6:
        if key == "aggregation_bits" and "aggregate" in path and rng.random() < 0.5:
            new = rng.choice(bitlist_values(ELECTRA_LIMIT))
        else:
            new = rng.choice(hex_variants(value))
    elif choice < 0.75:
        new = rng.choice(U64_EDGES)
    elif choice < 0.9:
        new = Raw(rng.choice(RAW_NUMBERS))
    else:
        new = copy.deepcopy(rng.choice(OTHER_VALUES))
    return set_at(body, path, new)


def mutate_key(body):
    path, obj = rng.choice(list(containers(body)))
    if not obj:
        return body
    k = rng.choice(list(obj))
    r = rng.random()
    if r < 0.4:
        del obj[k]
    elif r < 0.6:
        obj[k.upper() if rng.random() < 0.5 else k + "_"] = obj.pop(k)
    elif r < 0.8:
        obj["extra_" + str(rng.randrange(100))] = copy.deepcopy(rng.choice([1, "x", None, [], {"a": [1, 2]}]))
    else:
        obj[k] = {"version": "ELECTRA", "data": obj[k]}
    return body


def mutate_type(body):
    body["type"] = rng.choice(list(MESSAGES) + ["DEPOSIT", "BLOCK", "", "attestation", "Block_V2",
                                                 "AGGREGATE_AND_PROOF_V3"])
    return body


def mutate_root(body, true_root):
    r = rng.random()
    for k in ("signingRoot", "signing_root"):
        body.pop(k, None)
    if r < 0.3:
        body["signingRoot"] = true_root
    elif r < 0.5:
        body["signing_root"] = true_root.upper().replace("0X", "0x")
    elif r < 0.7:
        body["signingRoot"] = true_root[:-1] + ("0" if true_root[-1] != "0" else "1")
    elif r < 0.8:
        body["signingRoot"] = None
    else:
        body["signingRoot"] = true_root
        body["signing_root"] = rng.choice([true_root, None, "0x" + "00" * 32])
    return body


def raw_mutation(s):
    s = list(s)
    for _ in range(rng.randint(1, 4)):
        r = rng.random()
        i = rng.randrange(len(s) + 1)
        if r < 0.3 and s:
            del s[min(i, len(s) - 1)]
        elif r < 0.6:
            s.insert(i, rng.choice('{}[]:,"\\ \t\n0123456789abcdefxX-+.eE' + "\x01\x1f"))
        elif s:
            s[min(i, len(s) - 1)] = chr(rng.randrange(32, 127))
    return "".join(s)


def duplicate_key(s):
    body = json.loads(s)
    k = rng.choice(list(body))
    return s[:-1] + "," + json.dumps(k) + ":" + json.dumps(body[k]) + "}"


def nest(depth):
    return "[" * depth + "1" + "]" * depth


def big_inputs():
    """Inputs near the size limit: each must still finish within TIME_LIMIT."""
    base = json.loads(rng.choice(rows)["body"])
    yield "long type", json.dumps({**base, "type": "A" * 100_000})
    yield "long unknown string", json.dumps({**base, "x": "a" * 100_000})
    yield "long escaped string", json.dumps({**base, "x": "\\u0041" * 15_000})
    yield "long number", json.dumps(base)[:-1] + ',"x":' + "9" * 100_000 + "}"
    yield "many keys", json.dumps({**base, **{f"k{i}": i for i in range(8000)}})
    yield "long array", json.dumps({**base, "x": [0] * 40_000})
    yield "deep nesting 32", json.dumps(base)[:-1] + ',"x":' + nest(31) + "}"
    yield "deep nesting 33", json.dumps(base)[:-1] + ',"x":' + nest(32) + "}"
    yield "deep nesting 5000", json.dumps(base)[:-1] + ',"x":' + nest(5000) + "}"
    yield "whitespace", " " * 100_000 + json.dumps(base)
    yield "long hex root", json.dumps({**base, "signingRoot": "0x" + "0" * 100_000})
    agg = next(json.loads(r["body"]) for r in rows if r["kind"] == "AGGREGATE_AND_PROOF")
    for bits in bitlist_values(ELECTRA_LIMIT)[-3:]:
        a = json.loads(json.dumps(agg))
        a["aggregate_and_proof"]["aggregate"]["aggregation_bits"] = bits
        yield f"aggregate with {len(bits)} hex chars", json.dumps(a)


# Main
# ====

# 1. The model against Lighthouse.
model_failed = 0
for i, row in enumerate(rows):
    try:
        got = model(row["body"])
    except Reject:
        got = None
    if got != row["root"]:
        model_failed += 1
        print(f"MODEL FAIL #{i} {row['kind']}: model {got}, lighthouse {row['root']}")
if model_failed:
    print(f"the model disagrees with Lighthouse on {model_failed} bodies; fuzzing stopped")
    sys.exit(1)

# 2. Inputs near the size limit.
for name, body in big_inputs():
    compare(name, body)

# 3. Random mutations.
accepted = [r for r in rows if r["root"]]
for n in range(iterations):
    row = rng.choice(rows)
    body = json.loads(row["body"])
    ops = rng.randint(1, 3)
    for _ in range(ops):
        r = rng.random()
        if r < 0.5:
            body = mutate_leaf(body)
        elif r < 0.7:
            body = mutate_key(body)
        elif r < 0.8 and isinstance(body, dict):
            body = mutate_type(body)
        elif isinstance(body, dict) and row["root"]:
            body = mutate_root(body, row["root"])
    s = dump(body, rng.choice(STYLES))
    r = rng.random()
    if r < 0.15:
        s = raw_mutation(s)
    elif r < 0.2:
        try:
            s = duplicate_key(s)
        except (ValueError, IndexError, AttributeError, TypeError):
            pass
    compare(f"mutation #{n} of {row['kind']}", s)

print(f"{passed} passed, {failed} failed ({len(rows)} bodies checked against Lighthouse, "
      f"{iterations} mutations, {accepted_count} of them signed, seed {seed})")
sys.exit(1 if failed else 0)
