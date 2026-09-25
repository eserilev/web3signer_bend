# Bulkhead specification

Status: draft 0.1 (2026-09-23). Phases 0 and 1 are complete (2026-09-24). Lighthouse and Teku sign through Bulkhead on a devnet, and 17 of 23 laws have proofs.

Bulkhead is an Ethereum consensus-layer remote signer written in Bend 2. It serves the eth2 part of the Web3Signer HTTP API. A validator client that works with Web3Signer works with Bulkhead with no change.

The name comes from ship design. A bulkhead is a wall that keeps one flooded part of a ship from sinking the rest. Bulkhead keeps the validator keys and the slashing rules apart from the validator client. A fault in the client cannot make Bulkhead sign a slashable message.

## 1. Words in this document

| Word | Meaning |
|---|---|
| client | The validator client that sends signing requests (for example, Lighthouse). |
| request | One `POST /api/v1/eth2/sign/{pubkey}` call. |
| object | The consensus data inside a request (for example, `AttestationData`). |
| signing root | `hash_tree_root(SigningData{object_root, domain})`. The BLS key signs this value. |
| record | One entry in the slashing database: a signed block slot, or a signed attestation source and target. |
| slashing database | The durable history of records for each key. |
| law | A property in `LAWS.bend` that the Bend checker proves. |
| core | The pure Bend code: parse, compute roots, decide. It has no I/O. |
| shell | The I/O code: HTTP, files, and foreign C effects. |

In this document, "must" is a requirement. "Must not" is a prohibition. The document uses "verify" for every check that code does.

## 2. Goals

1. Bulkhead is a drop-in replacement for Web3Signer, for the eth2 sign API that consensus clients use.
2. Bulkhead never signs a slashable block or attestation, and the Bend checker proves this.
3. Bulkhead signs only the root that it computes itself from the object.
4. Bulkhead writes each record to durable storage before it returns the signature for that record.
5. The core is small enough for one person to read all of it.

## 3. Non-goals

These features are out of scope. A later version can add some of them.

- Eth1 signing, commit-boost, and the proof-of-validation extension.
- Key sources other than local files: no HashiCorp Vault, AWS, Azure, or YubiHSM.
- PostgreSQL, and a slashing database shared by more than one Bulkhead process.
- More than one genesis validators root in one slashing database.
- TLS inside Bulkhead in version 1. Section 11 gives the plan.
- A high watermark and the `watermark-repair` command.

## 4. Threat model

Bulkhead trusts these things:

- The machine and the operating system that run Bulkhead.
- The keystore files and the password files.
- The network configuration file (section 9).
- The Bend checker, the Bend compiler, clang, and the foreign C code (section 12 lists the risk).

Bulkhead does not trust the client. The client can be buggy, or an attacker can control it. For this reason, these rules apply:

- Bulkhead computes every signing root itself. It does not sign a root that the client sends.
- Bulkhead does its own slashing protection. It does not depend on the protection in the client.
- Bulkhead rejects a request that it cannot parse fully.

Lighthouse sends an attestation to the signer before its own slashing check runs (`lighthouse_validator_store/src/lib.rs`, `sign_attestations`). For this reason, the protection in Bulkhead is the only protection that runs before the key signs.

## 5. Architecture

```
            client (Lighthouse, Teku, ...)
                      |
                 HTTP (localhost)
                      |
  +-------------------v-------------------+
  | shell: HTTP server (Bend, on TCP)     |
  |   one task for each connection        |
  +-------------------+-------------------+
                      | Chan: parsed request + reply channel
  +-------------------v-------------------+
  | core: decision task (one owner)       |
  |   parse -> compute root -> decide     |
  |   slashing state lives here only      |
  +---------+---------------------+-------+
            |                     |
   append + fsync record    foreign BLS sign (blst)
   (foreign effect)          on a helper thread
```

### 5.1 One owner for the slashing state

One Bend task owns the slashing state. Each connection task sends its parsed request to this task on a channel. The decision task handles one request at a time. As a result, two requests for the same key cannot race.

Bend values are affine, so only one task can hold the state at a time. The design above follows from this rule.

### 5.2 Order of operations for one request

1. The shell reads the HTTP request and parses the JSON into a typed request.
2. The core computes the domain and the signing root from the object and `fork_info`.
3. If the request has `signingRoot` and the value is not equal to the computed root, the core rejects the request.
4. The core runs the slashing rules (section 8) on the current state.
5. If the rules reject the request, Bulkhead returns 412.
6. If the request adds a record, the shell appends the record to the log file. Then it calls `fsync`.
7. The shell calls the foreign BLS effect with the secret key and the computed root.
8. The shell returns the signature.

Web3Signer signs first and runs the slashing check after that. Bulkhead runs the check first. As a result, no signature for a rejected request ever exists in memory.

If step 7 fails after step 6, the record stays in the log, and no signature goes out. This result is safe: the record only blocks future requests.

If step 6 fails, Bulkhead stops. The state on disk is then not known, and a signer must not continue on a state that it cannot trust.

`main.bend` enforces the order of steps 6 and 7 by structure. The core task answers "go" only after the append and `fsync` return. The connection task calls the BLS effect only after it receives "go".

## 6. HTTP API

### 6.1 Endpoints

| Method and path | Version | Response |
|---|---|---|
| `POST /api/v1/eth2/sign/{identifier}` | 1 | Section 6.2. |
| `GET /api/v1/eth2/publicKeys` | 1 | 200, `application/json; charset=utf-8`, a JSON array of `0x` lowercase hex public keys. |
| `GET /upcheck` | 1 | 200, `text/plain; charset=utf-8`, body `OK`. |
| `GET /healthcheck` | 2 | 200 or 503, with JSON in the Web3Signer format. |
| `GET/POST/DELETE /eth/v1/keystores` | 3 | The Keymanager API. |

Lighthouse calls only the sign endpoint in production. The Lighthouse test harness also calls `/upcheck`.

### 6.2 Sign endpoint

The identifier is a BLS public key. Bulkhead makes it lowercase and adds `0x` if the prefix is missing.

The response format depends on the `Accept` header:

- If an `Accept` entry is `application/json` or `*/*`, the body is `{"signature":"0x..."}` with `application/json; charset=utf-8`.
- In all other cases, including no `Accept` header, the body is the bare `0x...` signature with `text/plain; charset=utf-8`.

Lighthouse sends `Accept: application/json`, and it parses `{"signature": ...}`.

### 6.3 Status codes

| Code | Cause |
|---|---|
| 200 | The request is valid, and Bulkhead signed it. |
| 400 | The JSON is malformed. A required field is missing. The `signingRoot` is not equal to the computed root. `fork_info` is missing for a type that needs it. The type or fork is not supported. |
| 404 | No loaded key has this public key. |
| 412 | A slashing rule rejected the request, or the genesis validators root is different from the one in the database. |
| 500 | An internal failure: a foreign effect failed, or the log write failed. |

Web3Signer returns 500 when `fork_info` is missing, because of a null pointer. Bulkhead returns 400. No client sends this request, so the difference is safe.

The error body is plain text with one line that gives the cause.

### 6.4 Request body

The body is one JSON object with these fields:

| Field | Required | Notes |
|---|---|---|
| `type` | yes | Section 7. Bulkhead ignores letter case, as Web3Signer does. |
| `fork_info` | for most types | `{fork: {previous_version, current_version, epoch}, genesis_validators_root}`. |
| `signingRoot` or `signing_root` | no | If present, it must equal the computed root. |
| one object field | yes | The field name depends on `type`. |

Bulkhead ignores unknown fields, as Web3Signer does.

These rules apply to the body:

- If the body has both `signingRoot` and `signing_root`, the two values must be equal.
- A `null` root is the same as no root.
- A `u64` field can also be a bare JSON integer.
- The JSON parser rejects duplicate keys, content after the value, and nesting deeper than 32 levels.

Numbers are JSON strings of decimal digits (`"123"`), and each is a `u64`. Hashes, keys, and fork versions are `0x` lowercase hex strings.

This example is the body for one attestation:

```json
{
  "type": "ATTESTATION",
  "fork_info": {
    "fork": {"previous_version": "0x05000000", "current_version": "0x06000000", "epoch": "411392"},
    "genesis_validators_root": "0x4b363db94e286120d76eb905340fdd4e54bfe9f06bf33ff6cf5ad27f511bfe95"
  },
  "signingRoot": "0x...",
  "attestation": {
    "slot": "13164544", "index": "0",
    "beacon_block_root": "0x...",
    "source": {"epoch": "411391", "root": "0x..."},
    "target": {"epoch": "411392", "root": "0x..."}
  }
}
```

## 7. Message types

### 7.1 Domains and signing roots

The fork version for the domain comes from `fork_info`. If `epoch < fork.epoch`, Bulkhead uses `previous_version`. In all other cases, it uses `current_version`. The domain is `compute_domain(domain_type, fork_version, genesis_validators_root)`.

The domain type is a 4-byte value. Bulkhead writes the domain number in little-endian order, so domain 11 becomes `0x0B000000`.

| `type` | Object field | Domain | Domain epoch | Object root | Version |
|---|---|---|---|---|---|
| `RANDAO_REVEAL` | `randao_reveal: {epoch}` | 2 | `epoch` | `Epoch` | 1 |
| `ATTESTATION` | `attestation` | 1 | `target.epoch` | `AttestationData` | 1 |
| `AGGREGATION_SLOT` | `aggregation_slot: {slot}` | 5 | epoch of `slot` | `Slot` | 1 |
| `BLOCK_V2` | `beacon_block: {version, block_header}` | 0 | epoch of `slot` | `BeaconBlockHeader` | 1 |
| `SYNC_COMMITTEE_MESSAGE` | `sync_committee_message: {beacon_block_root, slot}` | 7 | epoch of `slot` | `Root` | 2 |
| `SYNC_COMMITTEE_SELECTION_PROOF` | `sync_aggregator_selection_data` | 8 | epoch of `slot` | `SyncAggregatorSelectionData` | 2 |
| `SYNC_COMMITTEE_CONTRIBUTION_AND_PROOF` | `contribution_and_proof` | 9 | epoch of `contribution.slot` | `ContributionAndProof` | 2 |
| `AGGREGATE_AND_PROOF`, `AGGREGATE_AND_PROOF_V2` | `aggregate_and_proof` | 6 | epoch of `aggregate.data.slot` | `AggregateAndProof` for the fork | 2 |
| `VOLUNTARY_EXIT` | `voluntary_exit` | 4 | Section 7.3 | `VoluntaryExit` | 2 |
| `VALIDATOR_REGISTRATION` | `validator_registration` | `0x00000001` | Section 7.3 | `ValidatorRegistrationV1` | 2 |
| `PAYLOAD_ATTESTATION_MESSAGE` | `payload_attestation_message` | 12 | epoch of `slot` | `PayloadAttestationData` | 3 |
| `PROPOSER_PREFERENCES` | `proposer_preferences` | 13 | epoch of `proposal_slot` | `ProposerPreferences` | 3 |
| `EXECUTION_PAYLOAD_ENVELOPE` | `execution_payload_envelope` | 11 | epoch of envelope slot | `ExecutionPayloadEnvelope` | 3 |

Bulkhead does not support these types: `BLOCK` (deprecated), `DEPOSIT`, `EXECUTION_PAYLOAD_BID`, and `BUILDER_REQUEST_AUTH`. Lighthouse never sends `DEPOSIT` to a remote signer.

### 7.2 Blocks

For `BLOCK_V2`, Bulkhead accepts only `block_header`, for the forks from `BELLATRIX` on. Lighthouse sends only the header for these forks, and Web3Signer accepts only the header for them.

A header has five fields: `slot`, `proposer_index`, `parent_root`, `state_root`, `body_root`. The root of the header equals the root of the full block. As a result, Bulkhead does not need the SSZ types of any block body.

Bulkhead rejects `PHASE0` and `ALTAIR` blocks with 400. These forks need the full block, and no live network uses them.

### 7.3 Types with a fixed domain

Some domains do not come from `fork_info`. They come from the network configuration (section 9).

- `VALIDATOR_REGISTRATION`: the domain is `compute_domain(0x00000001, GENESIS_FORK_VERSION, zero_root)`. The request has no `fork_info`. Lighthouse returns an error if it builds this request with `fork_info`.
- `VOLUNTARY_EXIT`: if the Deneb fork is active at `fork_info.fork.epoch`, the fork version is `CAPELLA_FORK_VERSION` (EIP-7044). In all other cases, Bulkhead uses the normal rule of section 7.1. Web3Signer uses `fork_info.fork.epoch` for this decision. Lighthouse sends a synthetic fork for this case. Its `previous_version` and `current_version` are both the Capella version, and its `epoch` is the exit epoch.

### 7.4 Gloas: the two formats

Lighthouse and Web3Signer do not agree on the format of the Gloas types today:

| Message | Lighthouse sends | Web3Signer accepts |
|---|---|---|
| Payload attestation | `type: PAYLOAD_ATTESTATION`, field `payload_attestation_data`, bare object | `type: PAYLOAD_ATTESTATION_MESSAGE`, field `payload_attestation_message: {version, data}` |
| Envelope | field `execution_payload_envelope`, bare object | field `execution_payload_envelope: {version, data}` |
| Proposer preferences | field `proposer_preferences`, bare object | field `proposer_preferences: {version, data}` |

Lighthouse marks these types with `TODO(gloas) verify w/ web3signer specs` (`validator_client/signing_method/src/web3signer.rs`). So today, Lighthouse cannot sign these messages through Web3Signer.

Bulkhead accepts the Web3Signer format. Open question 1 (section 14) asks if it also accepts the Lighthouse format.

### 7.5 Aggregates and the fork

The JSON of an Electra aggregate and the JSON of a Gloas aggregate have the same fields. Their tree-hash rules are different, because Gloas uses a progressive container (EIP-7495) and a progressive bitlist (EIP-7916). Bulkhead selects the SSZ type from the network configuration and the slot of `aggregate.data`. It does not select the type from the JSON.

Web3Signer uses the same rule. It also accepts the object in two forms: bare, or wrapped as `{version, data}`. Bulkhead accepts both forms for both type names and ignores `version`. Lighthouse sends the bare form with `type: AGGREGATE_AND_PROOF` for all forks.

Bulkhead also makes sure that the JSON matches the selected type:

- A Base aggregate has no `committee_bits`. Its `aggregation_bits` has at most `MAX_VALIDATORS_PER_COMMITTEE` bits.
- An Electra aggregate must have `committee_bits` of `MAX_COMMITTEES_PER_SLOT` bits. Its `aggregation_bits` has at most `MAX_VALIDATORS_PER_COMMITTEE * MAX_COMMITTEES_PER_SLOT` bits.
- A Gloas aggregate has the Electra fields and limits. The progressive bitlist has no type limit, so Bulkhead uses the Electra limit.

If the JSON does not match, Bulkhead rejects the request with 400.

## 8. Slashing protection

### 8.1 Scope

Slashing protection covers `BLOCK_V2` and `ATTESTATION` only. Web3Signer has the same scope. The consensus spec has no slashing rule for the other types.

### 8.2 State

For each public key, the state holds:

- the block records: `(slot, signing_root)`.
- the attestation records: `(source_epoch, target_epoch, signing_root)`.
- a block low watermark: a slot, or none.
- an attestation low watermark: a source epoch and a target epoch, or none.
- an enabled flag.

The database also holds one genesis validators root (GVR). The first request or the first import sets it.

### 8.3 Block rule

Bulkhead rejects a block request if one of these conditions is true:

1. The block low watermark exists, and `slot < watermark.slot`.
2. A block record exists at `slot`, and its root is different or unknown.

If a block record exists at `slot` with the same root, Bulkhead signs again and adds no record. The same block always gives the same signature, so this result is safe.

### 8.4 Attestation rule

Bulkhead rejects an attestation request if one of these conditions is true:

1. `source > target`.
2. The attestation low watermark exists, and `source < watermark.source`.
3. The attestation low watermark exists, and `target < watermark.target`.
4. A record exists with the same `target`, and its root is different or unknown. This condition is a double vote.
5. A record `r` exists with `r.source < source` and `r.target > target`. The new attestation is inside `r`.
6. A record `r` exists with `r.source > source` and `r.target < target`. The new attestation surrounds `r`.

If a record exists with the same target and the same root, Bulkhead signs again and adds no record.

### 8.5 Genesis validators root

If the request GVR is not equal to the GVR in the database, Bulkhead rejects the request with 412. This rule applies to all message types that have `fork_info`.

`VALIDATOR_REGISTRATION` has no `fork_info` and no GVR. Bulkhead does not do the GVR check for it, and a registration does not set the GVR. If the body has a `fork_info`, Bulkhead ignores it.

The first request that Bulkhead signs sets the GVR: it writes a `G` event before its other events. A request that Bulkhead refuses writes no event, so it does not set the GVR.

### 8.6 Low watermarks

- The first record for a key does not set a watermark.
- An import raises a watermark to the lowest value in the imported data. It raises the watermark only if the new value is higher.
- Pruning raises a watermark (section 8.8).
- Nothing lowers a watermark.

### 8.7 Log file format

The slashing database is one append-only text file, `slashing.log`. Each line is one event:

```
G <genesis_validators_root>
B <pubkey> <slot> <signing_root|->
A <pubkey> <source> <target> <signing_root|->
WB <pubkey> <slot>
WA <pubkey> <source> <target>
D <pubkey>
E <pubkey>
```

`-` means the root is unknown. An EIP-3076 import can give records with no root. `D` disables a key. `E` enables a key again.

At start, Bulkhead reads the file from the first line to the last line. It builds the state with the same `apply` function that the decision task uses.

If the last line is not complete, Bulkhead ignores that line. A line that is not complete never had its `fsync` finish. For this reason, no signature went out for it. Bulkhead then cuts the file to its complete lines (`ftruncate` and `fsync`), so the next append starts on a new line.

If any line other than the last one cannot be parsed, Bulkhead stops and does not serve requests.

### 8.8 Pruning (version 2)

Pruning keeps the last 250 epochs of attestation records and the last 250 × 32 slots of block records, for each key. It raises the watermark first. Then it writes a new compacted file, calls `fsync` on it, and renames it over the old file.

### 8.9 EIP-3076 interchange (version 2)

Bulkhead imports and exports interchange format version `"5"`.

- An import with a GVR different from the database GVR fails, and nothing changes.
- An import skips each record that conflicts with the state. It logs a warning for each skipped record.
- An import never removes a record, and it never lowers a watermark.

## 9. Configuration

Bulkhead reads three inputs at start.

### 9.1 Network configuration

This is a consensus-spec `config.yaml` file. Bulkhead reads only simple `KEY: value` lines. It uses these keys:

- `PRESET_BASE` (`mainnet` or `minimal`). The preset sets `SLOTS_PER_EPOCH` and the SSZ list limits.
- `GENESIS_FORK_VERSION`, for registrations.
- `CAPELLA_FORK_VERSION` and `DENEB_FORK_EPOCH`, for exits.
- `ELECTRA_FORK_EPOCH` and `GLOAS_FORK_EPOCH`, for the aggregate type. If the file has no `GLOAS_FORK_EPOCH`, the Gloas fork is at `FAR_FUTURE_EPOCH`.

A value can have a comment after it, as in the built-in mainnet file. If a key is missing or its value does not parse, Bulkhead does not start. Without `--network-config`, Bulkhead uses the mainnet values.

Bulkhead uses the fork schedule to select SSZ types by slot, and to get the fixed domains of section 7.3. For all other domains, Bulkhead uses the fork versions in `fork_info`.

### 9.2 Keys

Bulkhead reads the Web3Signer key-configuration format. An operator can use one directory with both signers.

```yaml
type: "file-keystore"
keyType: "BLS"
keystoreFile: "/path/keystore.json"
keystorePasswordFile: "/path/password.txt"
```

```yaml
type: "file-raw"
keyType: "BLS"
privateKey: "0x<32 bytes hex>"
```

Bulkhead reads each `*.yaml` and `*.yml` file in the key directory. It skips hidden files. It reads only the first line of a password file, without a trailing carriage return. A blank password is an error.

Keystores follow EIP-2335. Bulkhead supports the `scrypt` and `pbkdf2` key derivation functions and the `aes-128-ctr` cipher. It normalizes the password to NFKD (ICU) and removes the control characters, as EIP-2335 requires. It verifies the checksum before it uses a key. If the keystore has a `pubkey` field, the decrypted key must match it.

If any key does not load, Bulkhead does not start. Two files for the same public key are also an error. Web3Signer loads the keys that it can and reports the errors. Bulkhead is stricter: a signer that silently misses a key is worse than one that does not start.

Secret keys stay in C memory (`src/ffi/bulkhead.h`). Bend code refers to a key by its index.

### 9.3 Command line

Version 1 has these flags:

| Flag | Meaning |
|---|---|
| `--network-config <file>` | The network configuration of section 9.1. |
| `--key-config-path <dir>` | The key directory of section 9.2. |
| `--slashing-log <file>` | The log file of section 8.7. |
| `--http-listen-host <ip>` | Default `127.0.0.1`. It must be an IPv4 address. |
| `--http-listen-port <port>` | Default `9000`. |

## 10. Laws

A human writes `LAWS.bend` and owns it. The AI writes `PROOF.bend` and the code, and it does not edit `LAWS.bend`. The laws below are drafts for the owner to review. They are English statements, not Bend syntax yet.

### 10.1 Signing root

- **L1 `signs_computed_root`**: For each request that `decide` accepts, the root that the shell signs equals `signing_root(object, domain)` from the parsed request.
- **L2 `rejects_bad_root`**: If a request has a `signingRoot` that is not equal to the computed root, `decide` rejects it.

### 10.2 Slashing safety

Let `safe(state)` mean that these statements are true for each key in `state`:

- No two block records have the same slot and different or unknown roots.
- No two attestation records have the same target and different or unknown roots.
- No record surrounds another record.
- In each attestation record, `source <= target`.

Then:

- **L3 `empty_safe`**: `safe(empty_state)`.
- **L4 `decide_keeps_safe`**: If `safe(s)` and `decide(s, req) = Accept(s2)`, then `safe(s2)`.
- **L5 `decide_records`**: If `decide(s, req) = Accept(s2)` for a block or an attestation, then `s2` holds a record for `req`.
- **L6 `replay_equals_state`**: For each log `l`, `replay(l)` equals the state that the decision task had after it wrote `l`.
- **L7 `import_keeps_safe`**: If `safe(s)`, then `safe(import(s, data))`.
- **L8 `import_monotone`**: `import` never removes a record and never lowers a watermark.
- **L9 `watermark_monotone`**: No operation lowers a low watermark.

L4, L5 and L6 together give the main result: no two signatures that Bulkhead returns for one key are slashable together. This result also holds across restarts.

### 10.3 Order of effects

- **L10 `write_before_sign`**: In the shell, the append-and-`fsync` effect for a record comes before the BLS sign effect for that request.

L10 is a law about an `IO` term, not about a pure function. The Bend guide shows laws on `IO` terms (`demos/io_hello_world`). If L10 is too hard to state in Bend, it becomes a reviewed rule, and section 12 lists it as not proved.

### 10.4 Numbers and encoding

- **L11 `u64_model`**: Each `U64` operation (compare, add, subtract, parse, and print) agrees with the same operation on `Nat` for values below 2^64.
- **L12 `hex_roundtrip`**: `parse_hex(show_hex(b)) = b` for each byte array `b`.
- **L13 `slot_epoch`**: `epoch_of(slot) = slot / SLOTS_PER_EPOCH`.

### 10.5 What the laws do not cover

- SHA-256 and SSZ roots. Test vectors cover them (section 13).
- BLS signing, keystore decryption, and `fsync`. These are foreign C code.
- The HTTP parser and the JSON parser. A law can state "parse after print gives the same value", but these parsers read input that the client controls. Fuzz tests cover them.

## 11. Bend 2 constraints and design answers

These facts come from the Bend 2 repository, version 2.0.27.

| Bend 2 limit | Design answer |
|---|---|
| No `U64`. `Nat` stops the program above 2^48 − 1. | A `U64` type made of two `U32` values, with law L11. Bulkhead never stores a `u64` in `Nat`. `FAR_FUTURE_EPOCH` (2^64 − 1) must parse. |
| No TLS. | Version 1 listens on localhost only. A TLS proxy (for example, stunnel) serves remote clients. Version 3 adds TLS through a single-file C library in a foreign effect. |
| No HTTP library. | An HTTP/1.1 request parser in Bend, on `TCP.recv`. It supports `Content-Length` and keep-alive. It does not support chunked request bodies. |
| No JSON library. | A JSON parser in Bend. It supports only what the request bodies need. It has a maximum size and a maximum depth. |
| Strings are linked lists. | Bulkhead reads request bodies as byte arrays where possible. The maximum body size is 1 MiB in versions 1 and 2. |
| No `fsync` and no `rename`. | A foreign effect: `File.append_sync(path, line)`, and a foreign effect for rename in version 2. |
| The linker flags are fixed. | The build runs `bend main.bend -o bulkhead.c`, then runs clang itself with Bend's flags plus `-I vendor/blst/bindings` and `libblst.a`. blst uses its normal assembly build. The phase 0 spike verified this method (`spike/phase0/README.md`). |
| Keystores need scrypt, PBKDF2, AES and NFKD. | Foreign C with OpenSSL (`libcrypto`) and ICU (`libicuuc`), linked by `scripts/build.sh`. |
| `TCP.listen` binds 0.0.0.0. | A foreign effect, `Net.listen`, binds the configured address. |
| `TCP.recv` decodes UTF-8, so a String length is not a byte length. | Bulkhead accepts only ASCII requests. A request with another character gets 400, and the connection closes. |
| The foreign C ABI has no stability promise. | Bulkhead pins one Bend version. Each Bend upgrade runs the full test suite before the version pin changes. |
| `tcp_connect` and the listener take IPv4 only. | `--http-listen-host` takes IPv4. |
| One event loop. | BLS signing runs in `io_work` on a helper thread, so the loop does not block. |
| `Bool.pick(c, a, b)` evaluates both `a` and `b`. | If a value costs more than a few steps, Bulkhead selects it with `match` on the `Bool`, or picks a function and calls only that function. Examples: the JSON lexer, the header splitter, and the dispatch on `type`. Before this rule, one 32 KB JSON string cost 22 s of CPU, and one 16 KB header line cost about 5 s. |
| No test framework. | The test runner is outside Bend: a script that starts Bulkhead and sends requests (section 13). |

## 12. Known risks

1. **The checker.** The Bend README says that the compiler is 99% AI-written and not fully audited. It also says that the Lean model and `bend.ts` do not match. A proof is as strong as the checker that verifies it.
2. **Foreign code.** BLS, keystore crypto, and `fsync` are C code that no law covers.
3. **The shell.** The HTTP server, the channel routing, and L10 (if L10 stays a reviewed rule) are not proved.
4. **Side channels.** The pure Bend code is not constant-time. Only foreign code touches secret keys. Keystore decryption must be in foreign code for this reason.
5. **Fork upgrades.** Each fork can add message types and SSZ types. Bulkhead must add them before the fork epoch.
6. **Throughput.** The core task calls `fsync` once for each signed record, one at a time. On one test machine, one request takes about 6.6 ms, and concurrent clients get about 290 signatures per second. Group commit (one `fsync` for several records) is the planned fix.

## 13. Test plan and phases

### 13.1 Test sources

- **SSZ and SHA-256**: The `ssz_static` consensus-spec test vectors give the root of each type. Bulkhead compares its roots with them.
- **BLS**: The `bls/sign` consensus-spec test vectors.
- **Keystores**: The EIP-2335 test vectors.
- **Interchange**: The EIP-3076 test vectors (`eth-clients/slashing-protection-interchange-tests`).
- **End to end**: Lighthouse `testing/web3signer_tests`. This harness compares the signatures of a local key and a remote signer for each message type. It needs two changes: an environment variable that sets the signer binary and its arguments, and a plain-HTTP mode. Today it downloads Web3Signer and connects with mutual TLS.
- **Devnet**: A Kurtosis devnet where Lighthouse uses Bulkhead for all its keys.

### 13.2 Phases

| Phase | Content | Exit condition |
|---|---|---|
| 0 | Spike: blst inside a foreign effect. Sign one root. | The signature equals the signature from Lighthouse for the same key and root. **Done 2026-09-23**: 10/10 EF vectors, 200/200 random cases identical to Lighthouse. |
| 1 | `U64`, SHA-256, SSZ for small containers, JSON, HTTP. Types: `RANDAO_REVEAL`, `ATTESTATION`, `AGGREGATION_SLOT`, `BLOCK_V2`. Slashing log. Laws L1 to L6, L9, and L11 to L13. | Lighthouse attests and proposes on a Kurtosis devnet through Bulkhead. The patched `web3signer_tests` pass for these types. **Done 2026-09-24**: Lighthouse and Teku validator clients attest and propose through Bulkhead on a Kurtosis devnet with two thirds of the stake, and the chain finalizes. The adapted `web3signer_tests` pass (`tools/lh-signer-tests`), with slashing tests that expect refusal. |
| 2 | Sync committee types, Electra aggregates, exits, registrations. Interchange import and export. Pruning. `/healthcheck`. Laws L7, L8, and L10. | All `web3signer_tests` pass. The EIP-3076 vectors pass. **Milestone 2.1 (message types) done 2026-09-24**: all types of section 7.1 up to version 2, and Gloas aggregates from phase 3. 7296 `ssz_static` cases pass. Lighthouse gives the same roots for 2100 request bodies. The adapted `web3signer_tests` pass for all these types on mainnet and Sepolia. On the devnet, the Lighthouse and Teku validator clients sign aggregates, sync committee messages and contributions through Bulkhead with no errors, and get full attestation and sync committee rewards. Next: milestone 2.2 (interchange, pruning, `/healthcheck`), then 2.3 (laws L7 and L8). |
| 3 | Gloas: progressive merkleization, Gloas aggregates, payload attestations, proposer preferences, envelopes. TLS. Keymanager API. | Lighthouse runs a Gloas devnet through Bulkhead. |

The envelope is the largest SSZ type in phase 3. It holds the full execution payload with its transactions, withdrawals, and execution requests.

## 14. Open questions

1. **The Gloas format.** Does Bulkhead also accept the format that Lighthouse sends today (section 7.4)? The alternative is to fix Lighthouse to send the Web3Signer format. The recommendation is to fix Lighthouse, and to accept both formats in Bulkhead until the fix ships.
2. **Test harness.** Does Bulkhead copy the Web3Signer command-line flags so that `web3signer_tests` can start it with no change? Or is a small patch to the harness better?
3. **Surround search.** Version 1 does a linear search over the attestation records of a key. With pruning at 250 epochs, a key has at most about 250 records. Is this fast enough in Bend, where lists are linked lists?
4. **Keystore crypto.** scrypt with n = 262144 needs 256 MiB. Is scrypt in foreign C acceptable, or must it be in Bend, where it is slower but side channels are a larger risk?
5. **The high watermark.** Web3Signer has a high watermark for recovery after a clock or database fault. Does version 2 need it?

## 15. References

- Web3Signer source: `Consensys/web3signer`, commit `8c5d2586`, especially `Eth2SignForIdentifierHandler.java` and `slashing-protection/`.
- Lighthouse client: `validator_client/signing_method/src/web3signer.rs`, `validator_client/lighthouse_validator_store/src/lib.rs`, `testing/web3signer_tests`.
- Bend 2: `bendlang/bend`, version 2.0.27: `README.md`, `guide/GUIDE.md`, `guide/EFFECTS.md`, `WONTFIX.txt`.
- EIP-2335 (keystores), EIP-3076 (slashing interchange), EIP-7044 (exit domain), EIP-7495 (progressive containers), EIP-7916 (progressive lists).
