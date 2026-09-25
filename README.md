# Bulkhead

Bulkhead is an Ethereum consensus-layer remote signer written in [Bend 2](https://github.com/bendlang/bend). It serves the eth2 signing API of Web3Signer. A validator client that works with Web3Signer works with Bulkhead with no change.

A bulkhead is a wall that keeps one flooded part of a ship from sinking the rest. Bulkhead keeps validator keys and slashing rules apart from the validator client.

## Status

Phase 1 is complete. Phase 2 is in progress.

- Phase 1: SSZ, JSON, the slashing store and log, the server, and the Lighthouse harness and devnet. 17 of the 23 laws have proofs.
- Milestone 2.1 (all message types up to Electra, and Gloas aggregates): complete.
- Milestone 2.2 (EIP-3076 interchange, pruning, `/healthcheck`): not started.
- Milestone 2.3 (laws L7 and L8): not started.

### What works with real clients

- `tools/lh-signer-tests` runs Lighthouse's `web3signer_tests`, adapted to Bulkhead. Lighthouse's `ValidatorStore` gives the same signatures through Bulkhead as with a local keystore, on mainnet and Sepolia. This is true for randao, attestations, selection proofs, blocks from Bellatrix on, Base and Electra aggregates, sync committee messages, sync selection proofs, contributions, registrations, and exits before and after Deneb.
- With Lighthouse's own slashing protection off, Bulkhead still refuses double votes, surround votes and double blocks, also after a restart.
- On a Kurtosis devnet (`devnet/`), a Lighthouse validator client and a Teku validator client sign through Bulkhead. They hold two thirds of the stake. The chain finalizes, and their validators get full source, target and head rewards and propose blocks. With the milestone 2.1 build, both clients also publish aggregates, sync committee messages and contributions through Bulkhead. The validators get all their sync committee rewards, and the clients log no signing errors.
- Bulkhead rejects blocks before Bellatrix, and the Gloas types of phase 3.

## Run

You need clang, OpenSSL (`libcrypto`) and ICU (`libicuuc`).

```sh
BEND=~/.bend/bin/bend scripts/build.sh main.bend build/bulkhead
./build/bulkhead --key-config-path <dir> --slashing-log <file> [--network-config <config.yaml>] \
  [--http-listen-host 127.0.0.1] [--http-listen-port 9000]
```

The key directory uses the Web3Signer key-config format (`file-keystore` and `file-raw`). Bulkhead listens on 127.0.0.1 by default. It has no TLS: put a TLS proxy in front of it for remote clients.

### Lighthouse harness and devnet

```sh
# Lighthouse's web3signer_tests against Bulkhead (needs ../lighthouse).
cd tools/lh-signer-tests && cargo test --release

# A devnet: build the image, patch ethereum-package, run Kurtosis.
docker build -f docker/Dockerfile -t bulkhead:local .
git -C <ethereum-package checkout> apply $PWD/devnet/ethereum-package-lighthouse-remote-signer.patch
kurtosis run --enclave bulkhead <ethereum-package checkout> --args-file devnet/kurtosis.yaml
```

The patch lets ethereum-package give the Lighthouse validator client a remote signer. It applies to ethereum-package commit `c0db06b`. The image entrypoint (`docker/entrypoint.sh`) accepts the Web3Signer command line that ethereum-package uses.

## Laws with proofs

| Group | Laws |
|---|---|
| Signing root | `signs_computed_root`, `rejects_bad_root`, `accepts_own_root` |
| Slashing safety | `empty_safe`, `block_keeps_safe`, `att_keeps_safe`, `block_recorded`, `att_recorded`, `block_keeps_records`, `att_keeps_records` |
| Watermarks | `block_respects_mark`, `att_respects_mark` |
| Liveness | `block_signs_when_clear`, `att_signs_when_clear` |
| Store | `store_att_is_key_decision`, `store_block_is_key_decision`, `store_other_keys` |

Together, these proofs give the main result: from an empty state, no two messages that one key signs are slashable together, and a store decision on one key acts as the key-level decision and does not change other keys.

### Open laws

`event_roundtrip`, `log_roundtrip`, `u64_cmp`, `u64_show_read`, `b32_hex` and `u64_shrn`. They are about numbers and text encoding. Their proofs need lemmas about `U32` division, multiplication and bit operations, which Base does not have. The test suites cover them (`run_ssz.py`, `run_store.py`).

## Development

You need Bend 2.0.27, clang, OpenSSL, ICU, and Python 3 with PyYAML. Set `BEND` if `bend` is not on your PATH. The key and server suites also need a Lighthouse checkout at `../lighthouse` (or set `LIGHTHOUSE`).

```sh
# Build each test binary and run each test suite.
BEND=~/.bend/bin/bend tests/run_all.sh <path to consensus-spec-tests/tests>
```

The suites:

| Suite | Checks |
|---|---|
| `tests/run_ssz.py` | SSZ roots against `ssz_static`, SHA-256 against `hashlib`, `U64` and domains against Python. |
| `tests/run_laws.py` | The laws of `LAWS.bend` as checks on random request sequences, and each decision against a Python model. A test, not a proof. |
| `tests/run_json.py` | The JSON parser against Python's `json`, with valid and invalid inputs. |
| `tests/run_requests.py` | Request decoding and signing roots against bodies and roots from Lighthouse's own code, plus mutations of those bodies. |
| `tests/run_store.py` | Store decisions over many keys against a Python model, replay of the written log, log line round trips, and torn logs. |
| `tests/run_keys.py` | Key loading: keystores and a raw key made by Lighthouse's own code, the EIP-2335 vectors, and bad key directories. |
| `tests/run_server.py` | The server end to end: signing against independent root and signature oracles, slashing refusals, restarts, torn and corrupt logs, and HTTP edge cases. |

`tools/lh-vectors` writes `tests/vectors/lighthouse_requests.jsonl`. It needs a Lighthouse checkout next to this one (`../lighthouse`).

## Lighthouse harness and devnet

```sh
# Lighthouse's web3signer_tests against Bulkhead (needs ../lighthouse).
cd tools/lh-signer-tests && cargo test --release

# A devnet: build the image, patch ethereum-package, run Kurtosis.
docker build -f docker/Dockerfile -t bulkhead:local .
git -C <ethereum-package checkout> apply $PWD/devnet/ethereum-package-lighthouse-remote-signer.patch
kurtosis run --enclave bulkhead <ethereum-package checkout> --args-file devnet/kurtosis.yaml
```

The patch lets ethereum-package give the Lighthouse validator client a remote signer. It applies to ethereum-package commit `c0db06b`. The image entrypoint (`docker/entrypoint.sh`) accepts the Web3Signer command line that ethereum-package uses.

## Laws

`LAWS.bend` and the files in `spec/` belong to the project owner. The code and `PROOF.bend` must satisfy them, and they do not edit them. `spec/safety.bend` defines "slashable" and "safe" from the consensus spec. `spec/signing.bend` holds the definitions for the signing-root laws. `LAWS.bend` states the laws with these definitions.

`bend PROOF.bend` checks every proof. It prints the number of open laws until all of them have proofs. `proof/lemmas.bend` holds the general lemmas about `Bool`, `Word`, `U32`, `U64`, `B32` and `Pubkey`.

## What is different

- The Bend checker proves the slashing rules (`LAWS.bend`).
- Bulkhead signs only a root that it computes itself from the request.
- Bulkhead writes each slashing record to disk, with `fsync`, before it returns the signature.

## Documents

- [docs/SPEC.md](docs/SPEC.md): the specification, the draft laws, and the phase plan.
