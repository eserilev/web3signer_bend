//! Writes Web3Signer sign-request bodies as JSON lines, one per case.
//!
//! The object inside each body is serialized by Lighthouse's own
//! `Web3SignerObject`, and the signing root comes from Lighthouse's own
//! `SignableMessage::signing_root` and `ChainSpec::get_domain`. The outer
//! envelope (`type`, `fork_info`, `signingRoot`) is private in Lighthouse, so
//! it is rebuilt here with the same field names as
//! `validator_client/signing_method/src/web3signer.rs::SigningRequest`.
//!
//! Output: one JSON object per line, `{"kind", "body", "root"}`. `root` is
//! null when Bulkhead must reject the body. The first line has kind
//! `CONFIG`: its body is the network config of the phase 2 cases, as a JSON
//! object of config.yaml strings.
//!
//! Usage:
//!   `cargo run --release -- <cases per kind> <seed>`   request bodies, to stdout
//!   `cargo run --release -- keys <dir>`                a key directory, see `keys`

use serde_json::{Value, json};
use signing_method::{SignableMessage, Web3SignerObject};
use bls::{AggregateSignature, PublicKeyBytes, Signature};
use ssz::ProgressiveBitList;
use ssz_types::{BitList, BitVector};
use typenum::Unsigned;
use types::*;

type E = MainnetEthSpec;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    /// A u64 from a mix of ranges, so that small values, word boundaries and
    /// the maximum all appear.
    fn u64(&mut self) -> u64 {
        match self.next() % 6 {
            0 => self.next() % 100,
            1 => self.next() % (1 << 32),
            2 => (1 << 32) + self.next() % 1000,
            3 => u64::MAX - self.next() % 3,
            _ => self.next(),
        }
    }

    fn hash(&mut self) -> Hash256 {
        let mut bytes = [0u8; 32];
        for chunk in bytes.chunks_mut(8) {
            chunk.copy_from_slice(&self.next().to_le_bytes());
        }
        Hash256::from(bytes)
    }

    fn version(&mut self) -> [u8; 4] {
        (self.next() as u32).to_le_bytes()
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    /// A real signature, so that the object holds a valid curve point.
    fn signature(&mut self) -> Signature {
        let mut bytes = [0u8; 32];
        bytes[0] = 0x10;
        for b in bytes.iter_mut().skip(1) {
            *b = self.next() as u8;
        }
        let sk = bls::SecretKey::deserialize(&bytes).expect("valid secret");
        sk.sign(self.hash())
    }

    fn aggregate_signature(&mut self) -> AggregateSignature {
        let mut agg = AggregateSignature::infinity();
        agg.add_assign(&self.signature());
        agg
    }

    /// A bit count: often small, sometimes the limit or the limit minus one.
    fn bit_len(&mut self, limit: usize) -> usize {
        match self.next() % 5 {
            0 => limit,
            1 => limit - 1,
            2 => 0,
            _ => (self.next() % (limit as u64 + 1).min(3000)) as usize,
        }
    }
}

fn fork_info(fork: &Fork, gvr: Hash256) -> Value {
    json!({ "fork": fork, "genesis_validators_root": gvr })
}

/// The body as Lighthouse sends it: type, fork_info, signingRoot, then the
/// flattened object.
fn body(
    message_type: &str,
    fork: &Fork,
    gvr: Hash256,
    root: Hash256,
    object: &Web3SignerObject<E, FullPayload<E>>,
) -> Value {
    let mut out = json!({
        "type": message_type,
        "fork_info": fork_info(fork, gvr),
        "signingRoot": root,
    });
    let object = serde_json::to_value(object).expect("object serializes");
    for (k, v) in object.as_object().expect("object is a map") {
        out[k] = v.clone();
    }
    out
}

/// A body without fork_info, as Lighthouse sends a validator registration.
fn body_no_fork(message_type: &str, root: Hash256, object: &Web3SignerObject<E, FullPayload<E>>) -> Value {
    let mut out = json!({ "type": message_type, "signingRoot": root });
    let object = serde_json::to_value(object).expect("object serializes");
    for (k, v) in object.as_object().expect("object is a map") {
        out[k] = v.clone();
    }
    out
}

fn case(kind: &str, body: Value, root: Option<Hash256>) {
    let line = json!({
        "kind": kind,
        "body": serde_json::to_string(&body).expect("body serializes"),
        "root": root,
    });
    println!("{line}");
}

fn random_fork(rng: &mut Rng) -> Fork {
    Fork {
        previous_version: rng.version(),
        current_version: rng.version(),
        epoch: Epoch::new(rng.u64()),
    }
}

fn domain(spec: &ChainSpec, epoch: Epoch, d: Domain, fork: &Fork, gvr: Hash256) -> Hash256 {
    spec.get_domain(epoch, d, fork, gvr)
}

/// Mainnet with a Gloas fork epoch, so that all three Attestation shapes
/// appear.
fn phase2_spec() -> ChainSpec {
    let mut spec = E::default_spec();
    spec.gloas_fork_epoch = Some(Epoch::new(GLOAS_EPOCH));
    spec
}

const GLOAS_EPOCH: u64 = 400_000;

fn hex4(v: [u8; 4]) -> String {
    format!("0x{}", hex::encode(v))
}

fn config(spec: &ChainSpec) -> Value {
    json!({
        "PRESET_BASE": "'mainnet'",
        "GENESIS_FORK_VERSION": hex4(spec.genesis_fork_version),
        "CAPELLA_FORK_VERSION": hex4(spec.capella_fork_version),
        "DENEB_FORK_EPOCH": spec.deneb_fork_epoch.unwrap().to_string(),
        "ELECTRA_FORK_EPOCH": spec.electra_fork_epoch.unwrap().to_string(),
        "GLOAS_FORK_EPOCH": format!("{GLOAS_EPOCH}  # a comment, as config files have"),
    })
}

/// An epoch in [lo, hi), with the ends more likely.
fn epoch_in(rng: &mut Rng, lo: u64, hi: u64) -> Epoch {
    Epoch::new(match rng.below(4) {
        0 => lo,
        1 => hi - 1,
        _ => lo + rng.below(hi - lo),
    })
}

fn slot_in(rng: &mut Rng, lo: u64, hi: u64) -> Slot {
    epoch_in(rng, lo, hi).start_slot(E::slots_per_epoch()) + rng.below(E::slots_per_epoch())
}

/// The slot ranges before Electra, before Gloas, and after.
fn fork_ranges(spec: &ChainSpec) -> [(u64, u64); 3] {
    let electra = spec.electra_fork_epoch.unwrap().as_u64();
    [(0, electra), (electra, GLOAS_EPOCH), (GLOAS_EPOCH, u64::MAX >> 5)]
}

fn attestation_data(rng: &mut Rng, slot: Slot) -> AttestationData {
    AttestationData {
        slot,
        index: rng.u64(),
        beacon_block_root: rng.hash(),
        source: Checkpoint { epoch: Epoch::new(rng.u64()), root: rng.hash() },
        target: Checkpoint { epoch: Epoch::new(rng.u64()), root: rng.hash() },
    }
}

fn set_bits<F: FnMut(usize, bool)>(rng: &mut Rng, len: usize, mut set: F) {
    for i in 0..len {
        set(i, rng.below(3) == 0);
    }
}

fn aggregate(rng: &mut Rng, spec: &ChainSpec, range: usize) -> AggregateAndProof<E> {
    let (lo, hi) = fork_ranges(spec)[range];
    let slot = slot_in(rng, lo, hi);
    let data = attestation_data(rng, slot);
    let signature = rng.aggregate_signature();
    let mut committee_bits = BitVector::<<E as EthSpec>::MaxCommitteesPerSlot>::new();
    set_bits(rng, committee_bits.len(), |i, b| committee_bits.set(i, b).unwrap());
    let aggregate = match range {
        0 => {
            let len = rng.bit_len(<E as EthSpec>::MaxValidatorsPerCommittee::to_usize());
            let mut bits = BitList::with_capacity(len).unwrap();
            set_bits(rng, len, |i, b| bits.set(i, b).unwrap());
            Attestation::Base(AttestationBase { aggregation_bits: bits, data, signature })
        }
        1 => {
            let len = rng.bit_len(<E as EthSpec>::MaxValidatorsPerSlot::to_usize());
            let mut bits = BitList::with_capacity(len).unwrap();
            set_bits(rng, len, |i, b| bits.set(i, b).unwrap());
            Attestation::Electra(AttestationElectra { aggregation_bits: bits, data, signature, committee_bits })
        }
        _ => {
            let len = rng.bit_len(<E as EthSpec>::MaxValidatorsPerSlot::to_usize());
            let mut bits = ProgressiveBitList::with_capacity(len);
            set_bits(rng, len, |i, b| bits.set(i, b).unwrap());
            Attestation::Gloas(AttestationGloas { aggregation_bits: bits, data, signature, committee_bits })
        }
    };
    let aggregator_index = rng.u64();
    let selection_proof = rng.signature();
    match aggregate {
        Attestation::Base(aggregate) => AggregateAndProof::Base(AggregateAndProofBase { aggregator_index, aggregate, selection_proof }),
        Attestation::Electra(aggregate) => AggregateAndProof::Electra(AggregateAndProofElectra { aggregator_index, aggregate, selection_proof }),
        Attestation::Gloas(aggregate) => AggregateAndProof::Gloas(AggregateAndProofGloas { aggregator_index, aggregate, selection_proof }),
    }
}

fn contribution(rng: &mut Rng) -> ContributionAndProof<E> {
    let mut aggregation_bits = BitVector::<<E as EthSpec>::SyncSubcommitteeSize>::new();
    set_bits(rng, aggregation_bits.len(), |i, b| aggregation_bits.set(i, b).unwrap());
    ContributionAndProof {
        aggregator_index: rng.u64(),
        contribution: SyncCommitteeContribution {
            slot: Slot::new(rng.u64()),
            beacon_block_root: rng.hash(),
            subcommittee_index: rng.u64(),
            aggregation_bits,
            signature: rng.aggregate_signature(),
        },
        selection_proof: rng.signature(),
    }
}

/// The phase 2 message types, with the roots that Lighthouse signs.
fn phase2(rng: &mut Rng, spec: &ChainSpec) {
    // AGGREGATE_AND_PROOF, for each Attestation shape.
    for range in 0..3 {
        let agg = aggregate(rng, spec, range);
        let fork = random_fork(rng);
        let gvr = rng.hash();
        let epoch = agg.aggregate().data().slot.epoch(E::slots_per_epoch());
        let d = domain(spec, epoch, Domain::AggregateAndProof, &fork, gvr);
        let root = SignableMessage::<E>::SignedAggregateAndProof(agg.to_ref()).signing_root(d);
        case("AGGREGATE_AND_PROOF", body("AGGREGATE_AND_PROOF", &fork, gvr, root,
            &Web3SignerObject::AggregateAndProof(agg.to_ref())), Some(root));
    }

    // SYNC_COMMITTEE_MESSAGE
    let fork = random_fork(rng);
    let gvr = rng.hash();
    let (beacon_block_root, slot) = (rng.hash(), Slot::new(rng.u64()));
    let d = domain(spec, slot.epoch(E::slots_per_epoch()), Domain::SyncCommittee, &fork, gvr);
    let root = SignableMessage::<E>::SyncCommitteeSignature { beacon_block_root, slot }.signing_root(d);
    case("SYNC_COMMITTEE_MESSAGE", body("SYNC_COMMITTEE_MESSAGE", &fork, gvr, root,
        &Web3SignerObject::SyncCommitteeMessage { beacon_block_root, slot }), Some(root));

    // SYNC_COMMITTEE_SELECTION_PROOF
    let fork = random_fork(rng);
    let gvr = rng.hash();
    let sel = SyncAggregatorSelectionData { slot: Slot::new(rng.u64()), subcommittee_index: rng.u64() };
    let d = domain(spec, sel.slot.epoch(E::slots_per_epoch()), Domain::SyncCommitteeSelectionProof, &fork, gvr);
    let root = SignableMessage::<E>::SyncSelectionProof(&sel).signing_root(d);
    case("SYNC_COMMITTEE_SELECTION_PROOF", body("SYNC_COMMITTEE_SELECTION_PROOF", &fork, gvr, root,
        &Web3SignerObject::SyncAggregatorSelectionData(&sel)), Some(root));

    // SYNC_COMMITTEE_CONTRIBUTION_AND_PROOF
    let fork = random_fork(rng);
    let gvr = rng.hash();
    let cp = contribution(rng);
    let d = domain(spec, cp.contribution.slot.epoch(E::slots_per_epoch()), Domain::ContributionAndProof, &fork, gvr);
    let root = SignableMessage::<E>::SignedContributionAndProof(&cp).signing_root(d);
    case("SYNC_COMMITTEE_CONTRIBUTION_AND_PROOF", body("SYNC_COMMITTEE_CONTRIBUTION_AND_PROOF", &fork, gvr, root,
        &Web3SignerObject::ContributionAndProof(&cp)), Some(root));

    // VOLUNTARY_EXIT, before and after Deneb. fork_info is the fork at the
    // exit's epoch, as the Lighthouse VC sends it.
    let deneb = spec.deneb_fork_epoch.unwrap().as_u64();
    for (lo, hi) in [(0, deneb), (deneb, u64::MAX >> 5)] {
        let exit = VoluntaryExit { epoch: epoch_in(rng, lo, hi), validator_index: rng.u64() };
        let fork = spec.fork_at_epoch(exit.epoch);
        let gvr = rng.hash();
        let root = SignableMessage::<E>::VoluntaryExit(&exit).signing_root(exit.get_domain(gvr, spec));
        case("VOLUNTARY_EXIT", body("VOLUNTARY_EXIT", &fork, gvr, root,
            &Web3SignerObject::VoluntaryExit(&exit)), Some(root));
    }

    // VALIDATOR_REGISTRATION, without fork_info.
    let mut pubkey = [0u8; 48];
    for b in pubkey.iter_mut() {
        *b = rng.next() as u8;
    }
    let mut fee_recipient = Address::ZERO;
    for b in fee_recipient.0.iter_mut() {
        *b = rng.next() as u8;
    }
    let reg = ValidatorRegistrationData {
        fee_recipient,
        gas_limit: rng.u64(),
        timestamp: rng.u64(),
        pubkey: PublicKeyBytes::deserialize(&pubkey).expect("48 bytes"),
    };
    let root = SignableMessage::<E>::ValidatorRegistration(&reg).signing_root(spec.get_builder_application_domain());
    case("VALIDATOR_REGISTRATION", body_no_fork("VALIDATOR_REGISTRATION", root,
        &Web3SignerObject::ValidatorRegistration(&reg)), Some(root));
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).map(String::as_str) == Some("keys") {
        keys::write(std::path::Path::new(&args[2]));
        return;
    }
    let count: usize = args.get(1).map(|s| s.parse().unwrap()).unwrap_or(50);
    let seed: u64 = args.get(2).map(|s| s.parse().unwrap()).unwrap_or(7688);
    let mut rng = Rng(seed | 1);
    let spec = E::default_spec();
    let spec2 = phase2_spec();
    case("CONFIG", config(&spec2), None);

    for _ in 0..count {
        phase2(&mut rng, &spec2);

        // ATTESTATION
        let fork = random_fork(&mut rng);
        let gvr = rng.hash();
        let data = AttestationData {
            slot: Slot::new(rng.u64()),
            index: rng.u64(),
            beacon_block_root: rng.hash(),
            source: Checkpoint { epoch: Epoch::new(rng.u64()), root: rng.hash() },
            target: Checkpoint { epoch: Epoch::new(rng.u64()), root: rng.hash() },
        };
        let d = domain(&spec, data.target.epoch, Domain::BeaconAttester, &fork, gvr);
        let root = SignableMessage::<E>::AttestationData(&data).signing_root(d);
        case("ATTESTATION", body("ATTESTATION", &fork, gvr, root,
            &Web3SignerObject::Attestation(&data)), Some(root));

        // RANDAO_REVEAL
        let fork = random_fork(&mut rng);
        let gvr = rng.hash();
        let epoch = Epoch::new(rng.u64());
        let d = domain(&spec, epoch, Domain::Randao, &fork, gvr);
        let root = SignableMessage::<E>::RandaoReveal(epoch).signing_root(d);
        case("RANDAO_REVEAL", body("RANDAO_REVEAL", &fork, gvr, root,
            &Web3SignerObject::RandaoReveal { epoch }), Some(root));

        // AGGREGATION_SLOT
        let fork = random_fork(&mut rng);
        let gvr = rng.hash();
        let slot = Slot::new(rng.u64());
        let d = domain(&spec, slot.epoch(E::slots_per_epoch()), Domain::SelectionProof, &fork, gvr);
        let root = SignableMessage::<E>::SelectionProof(slot).signing_root(d);
        case("AGGREGATION_SLOT", body("AGGREGATION_SLOT", &fork, gvr, root,
            &Web3SignerObject::AggregationSlot { slot }), Some(root));

        // BLOCK_V2, for each fork. Phase0 and Altair send the full block,
        // which Bulkhead rejects.
        for fork_name in ForkName::list_all() {
            let block_spec = fork_name.make_genesis_spec(E::default_spec());
            let mut block = BeaconBlock::<E, FullPayload<E>>::empty(&block_spec);
            *block.slot_mut() = Slot::new(rng.u64());
            *block.proposer_index_mut() = rng.u64();
            *block.parent_root_mut() = rng.hash();
            *block.state_root_mut() = rng.hash();
            let fork = random_fork(&mut rng);
            let gvr = rng.hash();
            let d = domain(&spec, block.epoch(), Domain::BeaconProposer, &fork, gvr);
            let root = SignableMessage::<E>::BeaconBlock(&block).signing_root(d);
            let object = Web3SignerObject::beacon_block(&block).expect("block object");
            let accepted = !matches!(fork_name, ForkName::Base | ForkName::Altair);
            case("BLOCK_V2", body("BLOCK_V2", &fork, gvr, root, &object),
                accepted.then_some(root));
        }
    }
}

/// Key directories in the Web3Signer key-config format, made with
/// Lighthouse's own keystore code.
///
/// `<dir>/good` holds keystores (scrypt and pbkdf2, with ASCII and non-ASCII
/// passwords) and a raw key. `expected.jsonl` has one line per key: its
/// public key, and its signature of the root `ROOT`. Each directory under
/// `<dir>/bad_*` holds one key that Bulkhead must refuse to load.
mod keys {
    use bls::SecretKey;
    use eth2_keystore::json_keystore::{HexBytes, Kdf, Pbkdf2, Prf, Scrypt};
    use eth2_keystore::KeystoreBuilder;
    use serde_json::json;
    use std::fs;
    use std::path::Path;
    use types::Hash256;

    pub const ROOT: [u8; 32] = [0x42; 32];

    fn secret(i: u8) -> SecretKey {
        let mut bytes = [0u8; 32];
        bytes[1] = 0x19;
        bytes[31] = i + 1;
        SecretKey::deserialize(&bytes).expect("valid secret")
    }

    fn keystore(dir: &Path, name: &str, i: u8, password: &str, kdf: Kdf) -> String {
        let sk = secret(i);
        let keypair = bls::Keypair::from_components(sk.public_key(), sk);
        let ks = KeystoreBuilder::new(&keypair, password.as_bytes(), String::new())
            .expect("builder")
            .kdf(kdf)
            .build()
            .expect("keystore");
        fs::write(dir.join(format!("{name}.json")), ks.to_json_string().unwrap()).unwrap();
        fs::write(dir.join(format!("{name}.password")), format!("{password}\n")).unwrap();
        fs::write(
            dir.join(format!("{name}.yaml")),
            format!(
                "type: \"file-keystore\"\nkeyType: \"BLS\"\nkeystoreFile: \"{name}.json\"\nkeystorePasswordFile: \"{name}.password\"\n"
            ),
        )
        .unwrap();
        keypair.pk.as_hex_string()
    }

    fn scrypt(n: u32) -> Kdf {
        Kdf::Scrypt(Scrypt { dklen: 32, n, r: 8, p: 1, salt: HexBytes::from(vec![7u8; 32]) })
    }

    fn pbkdf2(c: u32) -> Kdf {
        Kdf::Pbkdf2(Pbkdf2 { c, dklen: 32, prf: Prf::HmacSha256, salt: HexBytes::from(vec![9u8; 32]) })
    }

    fn line(out: &mut String, name: &str, i: u8) {
        let sk = secret(i);
        let sig = sk.sign(Hash256::from(ROOT));
        out.push_str(&json!({"name": name, "pubkey": sk.public_key().as_hex_string(), "signature": sig.to_string()}).to_string());
        out.push('\n');
    }

    pub fn write(dir: &Path) {
        let good = dir.join("good");
        fs::create_dir_all(&good).unwrap();
        let mut expected = String::new();
        let cases: [(&str, &str, Kdf); 6] = [
            ("scrypt_ascii", "hi mum", scrypt(1024)),
            ("pbkdf2_ascii", "testpassword", pbkdf2(1024)),
            ("scrypt_nfkd", "\u{1D531}\u{1D522}\u{1D530}\u{1D531}\u{1D52D}\u{1D51E}\u{1D530}\u{1D530}\u{1D534}\u{1D52C}\u{1D52F}\u{1D521}\u{1F511}", scrypt(1024)),
            ("pbkdf2_nfkd", "caf\u{E9} \u{FB01}", pbkdf2(2048)),
            ("scrypt_control", "tab\tpass\u{7F}word\u{85}", scrypt(2048)),
            ("scrypt_default", "a much longer password with spaces", scrypt(262144)),
        ];
        for (i, (name, password, kdf)) in cases.into_iter().enumerate() {
            keystore(&good, name, i as u8, password, kdf);
            line(&mut expected, name, i as u8);
        }
        let raw = secret(10);
        fs::write(
            good.join("raw.yaml"),
            format!("type: \"file-raw\"\nprivateKey: \"0x{}\"\n", hex::encode(raw.serialize().as_bytes())),
        )
        .unwrap();
        line(&mut expected, "raw", 10);
        fs::write(good.join("notes.txt"), "not a key config\n").unwrap();
        fs::write(dir.join("expected.jsonl"), expected).unwrap();

        let bad = dir.join("bad_password");
        fs::create_dir_all(&bad).unwrap();
        keystore(&bad, "key", 20, "right password", pbkdf2(1024));
        fs::write(bad.join("key.password"), "wrong password\n").unwrap();

        let dup = dir.join("bad_duplicate");
        fs::create_dir_all(&dup).unwrap();
        keystore(&dup, "a", 21, "pw", pbkdf2(1024));
        fs::write(dup.join("b.yaml"), format!("type: \"file-raw\"\nprivateKey: \"0x{}\"\n", hex::encode(secret(21).serialize().as_bytes()))).unwrap();

        let raw_bad = dir.join("bad_raw");
        fs::create_dir_all(&raw_bad).unwrap();
        fs::write(raw_bad.join("k.yaml"), "type: \"file-raw\"\nprivateKey: \"0x00\"\n").unwrap();

        let unknown = dir.join("bad_type");
        fs::create_dir_all(&unknown).unwrap();
        fs::write(unknown.join("k.yaml"), "type: \"hashicorp\"\n").unwrap();
    }
}
