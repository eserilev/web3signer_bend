# What the proofs prove

This file tells you what the laws of web3signer_bend state, which laws have proofs, and what the proofs trust. The laws are in `LAWS.bend`. The proofs are in `PROOF.bend`.

## The main claim

Start from an empty slashing state. For each key, web3signer_bend never signs two messages that are slashable together. A decision on one key never changes the state of another key.

A slashable pair has the meaning of the consensus spec: two different blocks at one slot, a double vote, or a surround vote.

The proofs cover the decision logic in pure Bend. They do not cover the HTTP shell, the C code, or the log file encoding. The section "What the proofs do not cover" gives the full list.

## Status

23 laws are stated. 17 laws have proofs. 6 laws are open.

## The laws

In the tables below, "proved" means `PROOF.bend` has a proof that the Bend checker accepts. "Open" means the law is stated but has no proof yet.

### Signing root (L1, L2)

web3signer_bend signs a root that it computes from the request object and `fork_info`. It never signs the root that the client claims.

| Law | Status | What it states |
|---|---|---|
| `signs_computed_root` | proved | If the check passes, it gives the computed signing root and no other root. |
| `rejects_bad_root` | proved | If the body claims a root that is not the computed root, the check fails. |
| `accepts_own_root` | proved | If the body claims no other root, the check passes. |

`accepts_own_root` is necessary. Without it, a check that fails for every body satisfies the first two laws.

### Slashing safety (L3 to L5)

A key state holds the block records, the attestation records, and two watermarks. A state is "safe" when no two of its records are slashable together, and each attestation record has `source <= target`. `spec/safety.bend` defines "safe".

| Law | Status | What it states |
|---|---|---|
| `empty_safe` | proved | The empty state is safe. |
| `block_keeps_safe` | proved | If a state is safe, it stays safe after a block decision. |
| `att_keeps_safe` | proved | If a state is safe, it stays safe after an attestation decision. |
| `block_recorded` | proved | If the decision signs a block, the state after the decision has a record of that block. |
| `att_recorded` | proved | If the decision signs an attestation, the state after the decision has a record of that attestation. |
| `block_keeps_records` | proved | A block decision never removes a record and never changes a watermark. |
| `att_keeps_records` | proved | An attestation decision never removes a record and never changes a watermark. |

These laws together give the main claim for one key. The state starts safe. Each decision keeps it safe and keeps the old records. Each signed message gets a record. So a new message that clashes with an old signed message cannot get a signature: the record of the old message makes the state unsafe.

### Watermarks (L9)

| Law | Status | What it states |
|---|---|---|
| `block_respects_mark` | proved | web3signer_bend never signs a block with a slot below the block watermark. |
| `att_respects_mark` | proved | web3signer_bend never signs an attestation with a source or a target below the attestation watermark. |

### Liveness

A signer that refuses every request satisfies all the laws above. These two laws rule that out.

| Law | Status | What it states |
|---|---|---|
| `block_signs_when_clear` | proved | If a block clashes with no record and is not below the watermark, web3signer_bend signs it. |
| `att_signs_when_clear` | proved | If an attestation has `source <= target`, clashes with no record, and is not below the watermark, web3signer_bend signs it. |

### Store and log (L6)

The store holds the state of each key and the genesis validators root. Each decision writes events to a log file. After a restart, web3signer_bend reads the log and applies the same events.

| Law | Status | What it states |
|---|---|---|
| `store_att_is_key_decision` | proved | For its own key, a store decision on an attestation gives the same state as the decision for one key. |
| `store_block_is_key_decision` | proved | For its own key, a store decision on a block gives the same state as the decision for one key. |
| `store_other_keys` | proved | A decision on one key never changes the state of another key. |
| `event_roundtrip` | open | A log line reads back as the event that wrote it. |
| `log_roundtrip` | open | A log file reads back as its list of events. |

The first three laws carry the key-level laws to the full store. The two open laws give "the state after a restart is the state before it". Until they have proofs, the main claim across a restart depends on the tests (`tests/run_store.py`, `tests/run_crash.py`).

The two store decision laws need the genesis validators root check to pass. If the root of the request is not the root of the database, the store refuses the request.

### Numbers and encoding (L11 to L13)

`U64` is two `U32` values, because Bend has no native 64-bit number.

| Law | Status | What it states |
|---|---|---|
| `u64_cmp` | open | The `U64` order is the order of the numbers. |
| `u64_show_read` | open | Decimal printing and parsing of a `U64` are inverses. |
| `b32_hex` | open | Hex printing and parsing of a 32-byte value are inverses. |
| `u64_shrn` | open | A shift right by `n` divides by `2^n`. `epoch_of(slot)` uses this shift. |

These proofs need lemmas about `U32` division, multiplication, and bit operations. The Bend base library does not have these lemmas yet. The test suites cover these laws (`tests/run_ssz.py`, `tests/run_store.py`).

### Not yet stated

- **L10 `write_before_sign`**: web3signer_bend writes a record and runs `fsync` before it signs. `main.bend` keeps this order by its structure: the core task answers `Go` only after `Log.append_sync` returns, and a connection task signs only after `Go`. No law states it yet, because it is a law about `IO` terms.
- **L7 `import_keeps_safe`** and **L8 `import_monotone`**: these are for EIP-3076 import. The import code does not exist yet (phase 2).

## What the proofs trust

- **The definitions in `spec/`.** `spec/safety.bend` defines "slashable", "safe", and the watermark rules from the consensus spec. `spec/signing.bend` defines the signing-root terms. `spec/store.bend` defines the view of one key in the store. A proof shows that the code agrees with these definitions. If a definition is wrong, the proof does not find the error. A human reviews these files.
- **The laws in `LAWS.bend`.** A law that states the wrong property has a proof that means nothing. A human reviews this file too.
- **The Bend 2 checker.** It checks each proof.
- **The Bend 2 compiler.** The proofs are about the Bend terms. The compiler turns these terms into C, and clang turns the C into a binary.
- **The C code in `src/ffi/`.** BLS signing, keystore decryption, file reads, the log append with `fsync`, and the socket.
- **blst** for BLS signatures, and **OpenSSL** for keystore decryption.

## What the proofs do not cover

- SHA-256 and the SSZ hash tree roots. The `ssz_static` vectors of the consensus spec test them.
- The HTTP parser and the JSON parser. The fuzzer and the Lighthouse request bodies test them.
- The order "write, then sign" (L10). The code structure keeps it, and `tests/run_crash.py` tests it.
- The log file encoding and the restart (the open L6 laws).
- The numbers and encoding laws (L11 to L13).

## How to check the proofs

```sh
bend PROOF.bend
```

If a law has no proof, the command fails. When every law holds, it prints `All terms check.`

`tests/run_laws.py` also runs the laws as checks on random request sequences, and compares each decision with a Python model. That is a test, not a proof.

## Files

| File | Contents |
|---|---|
| `LAWS.bend` | The laws. The project owner writes and approves this file. |
| `spec/safety.bend` | The meaning of "slashable" and "safe", from the consensus spec. |
| `spec/signing.bend` | The terms for the signing-root laws. |
| `spec/store.bend` | The terms for the store laws. |
| `PROOF.bend` | A proof of each law. |
| `proof/lemmas.bend` | General lemmas about `Bool`, `Word`, `U32`, `U64`, `B32`, and `Pubkey`. |

The code and `PROOF.bend` must satisfy `LAWS.bend` and `spec/`. The code does not edit these files.
