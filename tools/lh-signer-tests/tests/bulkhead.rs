//! Lighthouse's `testing/web3signer_tests`, adapted to Bulkhead.
//!
//! Each test runs two Lighthouse `ValidatorStore`s on one key: one with a
//! local keystore, and one with Bulkhead as its Web3Signer. The two must give
//! the same signed objects.
//!
//! The differences from the Lighthouse harness:
//! - The rig starts Bulkhead (`BULKHEAD_BIN`, or `build/bulkhead`) over plain
//!   HTTP. Bulkhead has no TLS.
//! - Bulkhead supports all the types that the Lighthouse VC signs through a
//!   Web3Signer, except blocks before Bellatrix. Those must fail, not sign.
//!   The phase 2 test adds Electra aggregates and voluntary exits before and
//!   after Deneb, which the Lighthouse harness does not test.
//! - Bulkhead gets the network's own config.yaml, as its fork versions and
//!   epochs select the aggregate shape and the exit domain.
//! - Bulkhead always does slashing protection. The Lighthouse harness runs
//!   Web3Signer without it, so there a slashable message is signed when
//!   Lighthouse's own protection is off. Here it must never be signed.
//!
//! Run: `cargo test --release` (the Lighthouse types need a release build to
//! be fast).

use account_utils::validator_definitions::{
    SigningDefinition, ValidatorDefinition, ValidatorDefinitions, Web3SignerDefinition,
};
use bls::{AggregateSignature, Keypair, PublicKeyBytes, SecretKey, Signature};
use eth2::types::FullBlockContents;
use eth2_keystore::KeystoreBuilder;
use eth2_network_config::Eth2NetworkConfig;
use fixed_bytes::FixedBytesExtended;
use futures::StreamExt;
use initialized_validators::InitializedValidators;
use lighthouse_validator_store::LighthouseValidatorStore;
use slashing_protection::{SLASHING_PROTECTION_FILENAME, SlashingDatabase};
use slot_clock::{SlotClock, TestingSlotClock};
use ssz_types::{BitList, BitVector};
use std::fmt::Debug;
use std::fs::{self, File};
use std::future::Future;
use std::net::TcpListener;
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::Arc;
use std::time::{Duration, Instant};
use task_executor::TaskExecutor;
use tempfile::TempDir;
use tokio::time::sleep;
use types::{attestation::AttestationBase, *};
use url::Url;
use validator_store::{AttestationToSign, SignedBlock, UnsignedBlock, ValidatorStore};

type E = MainnetEthSpec;

trait SignedObject: PartialEq + Debug {}

impl SignedObject for Signature {}
impl SignedObject for SingleAttestation {}
impl SignedObject for SignedBlock<E> {}
impl SignedObject for SelectionProof {}
impl SignedObject for SignedAggregateAndProof<E> {}
impl SignedObject for SyncSelectionProof {}
impl SignedObject for SyncCommitteeMessage {}
impl SignedObject for SignedContributionAndProof<E> {}
impl SignedObject for SignedValidatorRegistrationData {}
impl SignedObject for SignedVoluntaryExit {}

const KEYSTORE_PASSWORD: &str = "hi mum";
const LISTEN_ADDRESS: &str = "127.0.0.1";

/// The same arbitrary key as the Lighthouse harness.
fn testing_keypair() -> Keypair {
    let sk = SecretKey::deserialize(&[
        85, 40, 245, 17, 84, 193, 234, 155, 24, 234, 181, 58, 171, 193, 209, 164, 120, 147, 10, 174,
        189, 228, 119, 48, 181, 19, 117, 223, 2, 240, 7, 108,
    ])
    .unwrap();
    let pk = sk.public_key();
    Keypair::from_components(pk, sk)
}

fn bulkhead_binary() -> PathBuf {
    std::env::var("BULKHEAD_BIN").map(PathBuf::from).unwrap_or_else(|_| {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../build/bulkhead")
    })
}

fn free_port() -> u16 {
    TcpListener::bind((LISTEN_ADDRESS, 0)).unwrap().local_addr().unwrap().port()
}

/// A live Bulkhead process with one keystore.
struct BulkheadRig {
    keystore_path: PathBuf,
    dir: TempDir,
    port: u16,
    child: Child,
    url: Url,
}

impl Drop for BulkheadRig {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

impl BulkheadRig {
    async fn new(network: &str) -> Self {
        let dir = TempDir::new().unwrap();
        let keys = dir.path().join("keys");
        fs::create_dir(&keys).unwrap();
        let keystore = KeystoreBuilder::new(&testing_keypair(), KEYSTORE_PASSWORD.as_bytes(), String::new())
            .unwrap()
            .build()
            .unwrap();
        let keystore_path = keys.join("keystore.json");
        keystore.to_json_writer(File::create(&keystore_path).unwrap()).unwrap();
        fs::write(keys.join("password.txt"), KEYSTORE_PASSWORD).unwrap();
        fs::write(
            keys.join("key-config.yaml"),
            "type: \"file-keystore\"\nkeyType: \"BLS\"\nkeystoreFile: \"keystore.json\"\nkeystorePasswordFile: \"password.txt\"\n",
        )
        .unwrap();
        let config = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../../lighthouse/common/eth2_network_config/built_in_network_configs")
            .join(network)
            .join("config.yaml");
        fs::copy(&config, dir.path().join("config.yaml")).expect("network config.yaml in the Lighthouse checkout");
        Self::start(dir, keystore_path, free_port()).await
    }

    async fn start(dir: TempDir, keystore_path: PathBuf, port: u16) -> Self {
        let child = Command::new(bulkhead_binary())
            .arg("--key-config-path")
            .arg(dir.path().join("keys"))
            .arg("--slashing-log")
            .arg(dir.path().join("slashing.log"))
            .arg("--network-config")
            .arg(dir.path().join("config.yaml"))
            .arg("--http-listen-host")
            .arg(LISTEN_ADDRESS)
            .arg("--http-listen-port")
            .arg(port.to_string())
            .stdout(Stdio::null())
            .stderr(Stdio::inherit())
            .spawn()
            .expect("start bulkhead: build it with scripts/build.sh, or set BULKHEAD_BIN");
        let url = Url::parse(&format!("http://{LISTEN_ADDRESS}:{port}")).unwrap();
        let rig = Self { keystore_path, dir, port, child, url };
        rig.wait_until_up().await;
        rig
    }

    /// Stops Bulkhead and starts it again on the same key and log.
    async fn restart(mut self) -> Self {
        let _ = self.child.kill();
        let _ = self.child.wait();
        let dir = std::mem::replace(&mut self.dir, TempDir::new().unwrap());
        let keystore_path = self.keystore_path.clone();
        let port = self.port;
        drop(self);
        Self::start(dir, keystore_path, port).await
    }

    async fn wait_until_up(&self) {
        let start = Instant::now();
        let client = reqwest::Client::new();
        loop {
            let up = client.get(self.url.join("upcheck").unwrap()).send().await;
            if matches!(up, Ok(r) if r.status().is_success()) {
                return;
            }
            assert!(start.elapsed() < Duration::from_secs(30), "bulkhead did not start");
            sleep(Duration::from_millis(100)).await;
        }
    }

    fn log(&self) -> String {
        fs::read_to_string(self.dir.path().join("slashing.log")).unwrap_or_default()
    }
}

/// A `ValidatorStore`, as in the Lighthouse harness.
struct ValidatorStoreRig {
    validator_store: Arc<LighthouseValidatorStore<TestingSlotClock, E>>,
    _validator_dir: TempDir,
    runtime: Arc<tokio::runtime::Runtime>,
    _runtime_shutdown: async_channel::Sender<()>,
}

impl ValidatorStoreRig {
    async fn new(definition: ValidatorDefinition, local_protection: bool, spec: Arc<ChainSpec>) -> Self {
        let validator_dir = TempDir::new().unwrap();
        let initialized_validators = InitializedValidators::from_definitions(
            ValidatorDefinitions::from(vec![definition]),
            validator_dir.path().into(),
            initialized_validators::Config::default(),
        )
        .await
        .unwrap();
        let voting_pubkeys: Vec<_> = initialized_validators.iter_voting_pubkeys().collect();
        let runtime = Arc::new(tokio::runtime::Builder::new_multi_thread().enable_all().build().unwrap());
        let (runtime_shutdown, exit) = async_channel::bounded(1);
        let (shutdown_tx, _) = futures::channel::mpsc::channel(1);
        let executor = TaskExecutor::new(Arc::downgrade(&runtime), exit, shutdown_tx);
        let slashing_protection =
            SlashingDatabase::open_or_create(&validator_dir.path().join(SLASHING_PROTECTION_FILENAME)).unwrap();
        slashing_protection.register_validators(voting_pubkeys.iter().copied()).unwrap();
        let slot_clock = TestingSlotClock::new(Slot::new(0), Duration::from_secs(0), Duration::from_secs(1));
        let config = lighthouse_validator_store::Config {
            enable_web3signer_slashing_protection: local_protection,
            ..Default::default()
        };
        let validator_store = LighthouseValidatorStore::<_, E>::new(
            initialized_validators,
            slashing_protection,
            Hash256::repeat_byte(42),
            spec,
            None,
            slot_clock,
            &config,
            executor,
        );
        Self {
            validator_store: Arc::new(validator_store),
            _validator_dir: validator_dir,
            runtime,
            _runtime_shutdown: runtime_shutdown,
        }
    }

    fn shutdown(self) {
        Arc::try_unwrap(self.runtime).unwrap().shutdown_background()
    }
}

fn definition(signing_definition: SigningDefinition) -> ValidatorDefinition {
    ValidatorDefinition {
        enabled: true,
        voting_public_key: testing_keypair().pk,
        graffiti: None,
        suggested_fee_recipient: None,
        gas_limit: None,
        builder_proposals: None,
        builder_boost_factor: None,
        prefer_builder_proposals: None,
        description: String::default(),
        signing_definition,
    }
}

/// A local store and a Bulkhead store for the same key.
struct TestingRig {
    bulkhead: BulkheadRig,
    local: ValidatorStoreRig,
    remote: ValidatorStoreRig,
    pubkey: PublicKeyBytes,
}

type Store = Arc<LighthouseValidatorStore<TestingSlotClock, E>>;

impl TestingRig {
    async fn new(network: &str, local_protection: bool) -> (Self, Arc<ChainSpec>) {
        let spec = Arc::new(Eth2NetworkConfig::constant(network).unwrap().unwrap().chain_spec::<E>().unwrap());
        let bulkhead = BulkheadRig::new(network).await;
        let rig = Self::with(bulkhead, local_protection, spec.clone()).await;
        (rig, spec)
    }

    async fn with(bulkhead: BulkheadRig, local_protection: bool, spec: Arc<ChainSpec>) -> Self {
        let local = ValidatorStoreRig::new(
            definition(SigningDefinition::LocalKeystore {
                voting_keystore_path: bulkhead.keystore_path.clone(),
                voting_keystore_password_path: None,
                voting_keystore_password: Some(KEYSTORE_PASSWORD.to_string().into()),
            }),
            local_protection,
            spec.clone(),
        )
        .await;
        let remote = ValidatorStoreRig::new(
            definition(SigningDefinition::Web3Signer(Web3SignerDefinition {
                url: bulkhead.url.to_string(),
                root_certificate_path: None,
                request_timeout_ms: None,
                client_identity_path: None,
                client_identity_password: None,
            })),
            local_protection,
            spec,
        )
        .await;
        Self { bulkhead, local, remote, pubkey: PublicKeyBytes::from(&testing_keypair().pk) }
    }

    fn close(self) -> BulkheadRig {
        self.local.shutdown();
        self.remote.shutdown();
        self.bulkhead
    }

    /// Both stores must give the same signed object.
    async fn assert_match<F, R, S>(self, case: &str, f: F) -> Self
    where
        F: Fn(PublicKeyBytes, Store) -> R,
        R: Future<Output = S>,
        S: SignedObject,
    {
        let a = f(self.pubkey, self.local.validator_store.clone()).await;
        let b = f(self.pubkey, self.remote.validator_store.clone()).await;
        assert_eq!(a, b, "signature mismatch for {case}");
        self
    }

    /// The local store signs, and the Bulkhead store fails: Bulkhead does
    /// not support this type yet.
    async fn assert_unsupported<F, R, T>(self, case: &str, f: F) -> Self
    where
        F: Fn(PublicKeyBytes, Store) -> R,
        R: Future<Output = Result<T, lighthouse_validator_store::Error>>,
        T: Debug,
    {
        let a = f(self.pubkey, self.local.validator_store.clone()).await;
        let b = f(self.pubkey, self.remote.validator_store.clone()).await;
        assert!(a.is_ok(), "local store must sign {case}: {a:?}");
        assert!(b.is_err(), "bulkhead must not sign unsupported {case}: {b:?}");
        self
    }

    /// Neither store signs the slashable attestation.
    async fn assert_attestation_refused(self, case: &str, data: AttestationData) -> Self {
        for store in [&self.local.validator_store, &self.remote.validator_store] {
            let stream = store.sign_attestations(vec![AttestationToSign {
                attester_index: 0,
                pubkey: self.pubkey,
                committee_index: 0,
                data: data.clone(),
            }]);
            tokio::pin!(stream);
            match stream.next().await.unwrap() {
                Ok(signed) => assert!(signed.is_empty(), "{case} must not be signed"),
                Err(_) => {}
            }
        }
        self
    }

    /// Neither store signs the slashable block.
    async fn assert_block_refused(self, case: &str, block: BeaconBlock<E>) -> Self {
        for store in [&self.local.validator_store, &self.remote.validator_store] {
            let slot = block.slot();
            let unsigned = UnsignedBlock::Full(FullBlockContents::Block(block.clone()));
            let result = store.sign_block(self.pubkey, unsigned, slot).await;
            assert!(result.is_err(), "{case} must not be signed");
        }
        self
    }
}

fn attestation_data(source: u64, target: u64, block_root: u64) -> AttestationData {
    AttestationData {
        slot: Slot::new(target * E::slots_per_epoch()),
        index: 0,
        beacon_block_root: Hash256::from_low_u64_be(block_root),
        source: Checkpoint { epoch: Epoch::new(source), root: Hash256::zero() },
        target: Checkpoint { epoch: Epoch::new(target), root: Hash256::zero() },
    }
}

async fn sign_attestation(pubkey: PublicKeyBytes, store: Store, data: AttestationData) -> SingleAttestation {
    let stream = store.sign_attestations(vec![AttestationToSign { attester_index: 0, pubkey, committee_index: 0, data }]);
    tokio::pin!(stream);
    stream.next().await.unwrap().unwrap().pop().unwrap()
}

async fn sign_block(pubkey: PublicKeyBytes, store: Store, block: BeaconBlock<E>) -> SignedBlock<E> {
    let slot = block.slot();
    store.sign_block(pubkey, UnsignedBlock::Full(FullBlockContents::Block(block)), slot).await.unwrap()
}

/// A block of each fork from Bellatrix on, at its fork's first slot.
fn fork_blocks(spec: &ChainSpec) -> Vec<(String, BeaconBlock<E>)> {
    let mut out = vec![];
    for fork in ForkName::list_all() {
        if !fork.bellatrix_enabled() {
            continue;
        }
        let Some(epoch) = spec.fork_epoch(fork) else { continue };
        if epoch == spec.far_future_epoch {
            continue;
        }
        let fork_spec = fork.make_genesis_spec(spec.clone());
        let mut block = BeaconBlock::<E>::empty(&fork_spec);
        *block.slot_mut() = epoch.start_slot(E::slots_per_epoch());
        out.push((fork.to_string(), block));
    }
    out
}

async fn supported_types(network: &str) {
    let (mut rig, spec) = TestingRig::new(network, true).await;
    rig = rig
        .assert_match("randao_reveal", |pk, s| async move { s.randao_reveal(pk, Epoch::new(0)).await.unwrap() })
        .await
        .assert_match("attestation", |pk, s| sign_attestation(pk, s, attestation_data(0, 0, 0)))
        .await
        .assert_match("selection_proof", |pk, s| async move {
            s.produce_selection_proof(pk, Slot::new(0)).await.unwrap()
        })
        .await;
    let blocks = fork_blocks(&spec);
    assert!(blocks.len() >= 4, "want at least Bellatrix to Electra on {network}");
    for (fork, block) in blocks {
        rig = rig.assert_match(&format!("beacon_block_{fork}"), |pk, s| sign_block(pk, s, block.clone())).await;
    }
    rig.close();
}

fn aggregate_base(data: AttestationData) -> Attestation<E> {
    Attestation::Base(AttestationBase {
        aggregation_bits: BitList::with_capacity(1).unwrap(),
        data,
        signature: AggregateSignature::empty(),
    })
}

fn aggregate_electra(data: AttestationData) -> Attestation<E> {
    let mut committee_bits = BitVector::new();
    committee_bits.set(0, true).unwrap();
    let mut aggregation_bits = BitList::with_capacity(3).unwrap();
    aggregation_bits.set(1, true).unwrap();
    Attestation::Electra(AttestationElectra {
        aggregation_bits,
        data,
        signature: AggregateSignature::empty(),
        committee_bits,
    })
}

/// Attestation data at the first slot of epoch, with target epoch.
fn data_at(epoch: Epoch) -> AttestationData {
    AttestationData {
        slot: epoch.start_slot(E::slots_per_epoch()),
        target: Checkpoint { epoch, root: Hash256::zero() },
        ..attestation_data(0, 0, 0)
    }
}

async fn phase2_types(network: &str) {
    let (rig, spec) = TestingRig::new(network, true).await;
    let altair_slot = spec.altair_fork_epoch.unwrap().start_slot(E::slots_per_epoch());
    let electra_epoch = spec.electra_fork_epoch.unwrap();
    let capella_epoch = spec.capella_fork_epoch.unwrap();
    let deneb_epoch = spec.deneb_fork_epoch.unwrap();
    rig.assert_match("aggregate_and_proof_base", |pk, s| async move {
        s.produce_signed_aggregate_and_proof(pk, 0, aggregate_base(attestation_data(0, 0, 0)), SelectionProof::from(Signature::empty()))
            .await
            .unwrap()
    })
    .await
    .assert_match("aggregate_and_proof_electra", move |pk, s| async move {
        s.produce_signed_aggregate_and_proof(pk, 9, aggregate_electra(data_at(electra_epoch)), SelectionProof::from(Signature::empty()))
            .await
            .unwrap()
    })
    .await
    .assert_match("validator_registration", |pk, s| async move {
        s.sign_validator_registration_data(ValidatorRegistrationData {
            fee_recipient: Address::repeat_byte(42),
            gas_limit: 30_000_000,
            timestamp: 100,
            pubkey: pk,
        })
        .await
        .unwrap()
    })
    .await
    .assert_match("sync_committee_signature", move |pk, s| async move {
        s.produce_sync_committee_signature(altair_slot, Hash256::repeat_byte(3), 0, &pk).await.unwrap()
    })
    .await
    .assert_match("sync_selection_proof", move |pk, s| async move {
        s.produce_sync_selection_proof(&pk, altair_slot, SyncSubnetId::from(2)).await.unwrap()
    })
    .await
    .assert_match("signed_contribution_and_proof", move |pk, s| async move {
        let mut aggregation_bits = BitVector::new();
        aggregation_bits.set(5, true).unwrap();
        let contribution = SyncCommitteeContribution {
            slot: altair_slot,
            beacon_block_root: Hash256::repeat_byte(4),
            subcommittee_index: 1,
            aggregation_bits,
            signature: AggregateSignature::empty(),
        };
        s.produce_signed_contribution_and_proof(0, pk, contribution, SyncSelectionProof::from(Signature::empty()))
            .await
            .unwrap()
    })
    .await
    .assert_match("voluntary_exit_capella", move |pk, s| async move {
        s.sign_voluntary_exit(pk, VoluntaryExit { epoch: capella_epoch, validator_index: 7 }).await.unwrap()
    })
    .await
    .assert_match("voluntary_exit_deneb", move |pk, s| async move {
        s.sign_voluntary_exit(pk, VoluntaryExit { epoch: deneb_epoch + 1, validator_index: 7 }).await.unwrap()
    })
    .await
    .assert_unsupported("phase0_block", |pk, s| {
        let spec = spec.clone();
        async move {
            let block = BeaconBlock::<E>::Base(BeaconBlockBase::empty(&spec));
            s.sign_block(pk, UnsignedBlock::Full(FullBlockContents::Block(block)), Slot::new(0)).await
        }
    })
    .await
    .close();
}

/// Slashable messages are refused, whether or not Lighthouse's own
/// protection is on. Web3Signer with its protection off signs them.
async fn slashing_protection(local_protection: bool) {
    let (rig, spec) = TestingRig::new("mainnet", local_protection).await;
    let bellatrix_slot = spec.bellatrix_fork_epoch.unwrap().start_slot(E::slots_per_epoch());
    let first_block = {
        let mut b = BeaconBlockBellatrix::<E>::empty(&spec);
        b.slot = bellatrix_slot;
        BeaconBlock::Bellatrix(b)
    };
    let mut double_block = first_block.clone();
    *double_block.state_root_mut() = Hash256::repeat_byte(0xff);

    let rig = rig
        .assert_match("first_attestation", |pk, s| sign_attestation(pk, s, attestation_data(1, 4, 0)))
        .await
        .assert_attestation_refused("double_vote", attestation_data(1, 4, 1))
        .await
        .assert_attestation_refused("surrounding", attestation_data(0, 5, 0))
        .await
        .assert_attestation_refused("surrounded", attestation_data(2, 3, 0))
        .await
        .assert_match("first_block", |pk, s| sign_block(pk, s, first_block.clone()))
        .await
        .assert_block_refused("double_block", double_block.clone())
        .await;
    let bulkhead = rig.close();
    let log = bulkhead.log();
    assert_eq!(log.lines().filter(|l| l.starts_with("A ")).count(), 1, "one attestation record:\n{log}");
    assert_eq!(log.lines().filter(|l| l.starts_with("B ")).count(), 1, "one block record:\n{log}");

    // After a restart, with fresh Lighthouse stores that have no history of
    // their own, Bulkhead still refuses the double block.
    let bulkhead = bulkhead.restart().await;
    let rig = TestingRig::with(bulkhead, false, spec).await;
    let unsigned = UnsignedBlock::Full(FullBlockContents::Block(double_block.clone()));
    let result = rig.remote.validator_store.sign_block(rig.pubkey, unsigned, double_block.slot()).await;
    assert!(result.is_err(), "double block after restart must not be signed");
    rig.close();
}

#[tokio::test]
async fn mainnet_supported_types() {
    supported_types("mainnet").await
}

#[tokio::test]
async fn sepolia_supported_types() {
    supported_types("sepolia").await
}

#[tokio::test]
async fn mainnet_phase2_types() {
    phase2_types("mainnet").await
}

#[tokio::test]
async fn sepolia_phase2_types() {
    phase2_types("sepolia").await
}

#[tokio::test]
async fn slashing_protection_disabled_locally() {
    slashing_protection(false).await
}

#[tokio::test]
async fn slashing_protection_enabled_locally() {
    slashing_protection(true).await
}
