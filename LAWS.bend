# The laws of web3signer_bend. DRAFT for review: the owner of this file writes and
# approves it, and the code and PROOF.bend must satisfy it. The code does not
# edit this file or spec/safety.bend.
#
# spec/safety.bend defines what "safe" means, from the consensus spec. The
# laws below state that the code in src/ keeps to it.
import Base
import ./src/ssz.bend as S
import ./src/slashing.bend as Slash
import ./spec/safety.bend as Spec
import ./src/request.bend as R
import ./spec/signing.bend as Sig
import ./src/store.bend as St
import ./spec/store.bend as Sto
import ./src/interchange.bend as I
import ./spec/import.bend as Imp
import ./src/core.bend as Co
import ./spec/core.bend as Core

# L1-L2: the signing root
# =======================
#
# The root that web3signer_bend signs comes from the request object and fork_info,
# never from the root that the client claims. n is log2(SLOTS_PER_EPOCH).

# L1: a check that passes gives the computed root and no other.
law signs_computed_root:
  for +r: R.Request
  for +n: Nat
  {Sig.gives_only(R.Request.check(r, n), R.Request.signing_root(r, n)) == True{} : Bool}

# L2: a body that claims another root fails the check.
law rejects_bad_root:
  for +r: R.Request
  for +n: Nat
  for h: {Sig.claims_other(r, R.Request.signing_root(r, n)) == True{} : Bool}
  {Sig.fails(R.Request.check(r, n)) == True{} : Bool}

# L2: a body that claims no other root passes the check. Without this law, a
# check that fails for every body satisfies L1 and L2.
law accepts_own_root:
  for +r: R.Request
  for +n: Nat
  for h: {Sig.claims_other(r, R.Request.signing_root(r, n)) == False{} : Bool}
  {Sig.fails(R.Request.check(r, n)) == False{} : Bool}

# L3-L5, L9: slashing safety
# ==========================
#
# Together, these laws give the main result. Start from a safe state. Each
# decision keeps the state safe, keeps the old records, and records what it
# signs. So no two messages that one key signs are slashable together.

# L3: the empty state is safe.
law empty_safe:
  {Spec.safe(Slash.KeyState.empty()) == True{} : Bool}

# L4: a block decision keeps a safe state safe.
law block_keeps_safe:
  for +ks: Slash.KeyState
  for +slot: S.U64
  for +root: S.B32
  for h: {Spec.safe(ks) == True{} : Bool}
  {Spec.safe(Slash.KeyState.after(ks, Slash.Block.decide(ks, slot, root))) == True{} : Bool}

# L4: an attestation decision keeps a safe state safe.
law att_keeps_safe:
  for +ks: Slash.KeyState
  for +source: S.U64
  for +target: S.U64
  for +root: S.B32
  for h: {Spec.safe(ks) == True{} : Bool}
  {Spec.safe(Slash.KeyState.after(ks, Slash.Att.decide(ks, source, target, root))) == True{} : Bool}

# L5: a block that the decision signs has a record afterwards.
law block_recorded:
  for +ks: Slash.KeyState
  for +slot: S.U64
  for +root: S.B32
  {Spec.signs_block_recorded(Slash.Block.decide(ks, slot, root), ks,
    Slash.BlockRec{slot, Some{root}}) == True{} : Bool}

# L5: an attestation that the decision signs has a record afterwards.
law att_recorded:
  for +ks: Slash.KeyState
  for +source: S.U64
  for +target: S.U64
  for +root: S.B32
  {Spec.signs_att_recorded(Slash.Att.decide(ks, source, target, root), ks,
    Slash.AttRec{source, target, Some{root}}) == True{} : Bool}

# L5: a block decision never drops a record or moves a watermark.
law block_keeps_records:
  for +ks: Slash.KeyState
  for +slot: S.U64
  for +root: S.B32
  {Spec.keeps(ks, Slash.KeyState.after(ks, Slash.Block.decide(ks, slot, root))) == True{} : Bool}

# L5: an attestation decision never drops a record or moves a watermark.
law att_keeps_records:
  for +ks: Slash.KeyState
  for +source: S.U64
  for +target: S.U64
  for +root: S.B32
  {Spec.keeps(ks, Slash.KeyState.after(ks, Slash.Att.decide(ks, source, target, root))) == True{} : Bool}

# L9: no block below the watermark is signed.
law block_respects_mark:
  for +ks: Slash.KeyState
  for +slot: S.U64
  for +root: S.B32
  for h: {Spec.signs(Slash.Block.decide(ks, slot, root)) == True{} : Bool}
  {Spec.block_above_mark(slot, Spec.block_mark(ks)) == True{} : Bool}

# L9: no attestation below the watermark is signed.
law att_respects_mark:
  for +ks: Slash.KeyState
  for +source: S.U64
  for +target: S.U64
  for +root: S.B32
  for h: {Spec.signs(Slash.Att.decide(ks, source, target, root)) == True{} : Bool}
  {Spec.att_above_mark(source, target, Spec.att_mark(ks)) == True{} : Bool}

# Liveness: the laws above hold for a signer that refuses everything. These
# two laws rule that out. A request that clashes with no record and is not
# below a watermark gets a signature.

law block_signs_when_clear:
  for +ks: Slash.KeyState
  for +slot: S.U64
  for +root: S.B32
  for h: {Spec.block_clear(ks, slot, root) == True{} : Bool}
  {Spec.signs(Slash.Block.decide(ks, slot, root)) == True{} : Bool}

law att_signs_when_clear:
  for +ks: Slash.KeyState
  for +source: S.U64
  for +target: S.U64
  for +root: S.B32
  for h: {Spec.att_clear(ks, source, target, root) == True{} : Bool}
  {Spec.signs(Slash.Att.decide(ks, source, target, root)) == True{} : Bool}

# L6: the store and its log
# =========================
#
# The store applies the events of a decision to get its next state, and
# replay applies the same events from the log file. So these laws give: the
# state after a restart is the state before it, and the laws for one key
# above hold for the store.

# L6: a log line reads back as the event that wrote it.
law event_roundtrip:
  for +e: St.LogEvent
  {St.LogEvent.read(St.LogEvent.show(e)) == Some{e} : Maybe<&2, St.LogEvent>}

# L6: a log reads back as its events.
law log_roundtrip:
  for +es: List<&2, St.LogEvent>
  {St.Log.read(St.Log.show(es)) == Some{es} : Maybe<&2, List<&2, St.LogEvent>>}

# L6: for its own key, a store decision on an attestation does what the
# decision for one key does.
law store_att_is_key_decision:
  for +s: St.Store
  for +key: S.Pubkey
  for +d: S.AttestationData
  for +fork: S.Fork
  for +gvr: S.B32
  for +claimed: Maybe<&2, S.B32>
  for +root: S.B32
  for h: {Sto.gvr_ok(s, gvr) == True{} : Bool}
  {Sto.key_state(Sto.after(s, key, R.Request{R.MAttestation{d}, fork, gvr, claimed}, root), key)
    == Slash.KeyState.after(Sto.key_state(s, key),
         Slash.Att.decide(Sto.key_state(s, key), Sto.source(d), Sto.target(d), root)) : Slash.KeyState}

# L6: the same for a block.
law store_block_is_key_decision:
  for +s: St.Store
  for +key: S.Pubkey
  for +hd: S.BeaconBlockHeader
  for +fork: S.Fork
  for +gvr: S.B32
  for +claimed: Maybe<&2, S.B32>
  for +root: S.B32
  for h: {Sto.gvr_ok(s, gvr) == True{} : Bool}
  {Sto.key_state(Sto.after(s, key, R.Request{R.MBlock{hd}, fork, gvr, claimed}, root), key)
    == Slash.KeyState.after(Sto.key_state(s, key),
         Slash.Block.decide(Sto.key_state(s, key), Sto.slot(hd), root)) : Slash.KeyState}

# L6: a decision on one key never changes another key.
law store_other_keys:
  for +s: St.Store
  for +key: S.Pubkey
  for +other: S.Pubkey
  for +r: R.Request
  for +root: S.B32
  for h: {S.Pubkey.is_eq(other, key) == False{} : Bool}
  {Sto.key_state(Sto.after(s, key, r, root), other) == Sto.key_state(s, other) : Slash.KeyState}

# L11-L13: numbers and encoding
# =============================

# L11: U64 order is the order of the numbers.
law u64_cmp:
  for a: S.U64
  for b: S.U64
  {S.U64.cmp(a, b) == Nat.cmp(S.U64.to_nat(a), S.U64.to_nat(b)) : Cmp}

# L11: decimal printing and parsing are inverses.
law u64_show_read:
  for +a: S.U64
  {S.U64.read(S.U64.show(a)) == Some{a} : Maybe<&2, S.U64>}

# L12: hex printing and parsing are inverses.
law b32_hex:
  for +x: S.B32
  {S.Hex.read_b32(S.Hex.b32(x)) == Some{x} : Maybe<&2, S.B32>}

# L13: a shift right by n divides by 2^n. epoch_of(slot) is a shift by
# log2(SLOTS_PER_EPOCH).
law u64_shrn:
  for n: Nat
  for +a: S.U64
  {S.U64.to_nat(S.U64.shrn(n, a)) == Nat.div(S.U64.to_nat(a), Nat.pow(2n, n)) : Nat}

# L7-L8: EIP-3076 import
# =======================
#
# An import gives log events, and the store after it is Imp.after: apply_all
# of the events, or the same store if the import fails (src/interchange.bend).

# L7: an import keeps a safe key safe.
law import_keeps_safe:
  for +s: St.Store
  for +ix: I.Interchange
  for +key: S.Pubkey
  for h: {Spec.safe(Sto.key_state(s, key)) == True{} : Bool}
  {Spec.safe(Sto.key_state(I.Imp.after(s, ix), key)) == True{} : Bool}

# L8: an import never removes a record and never lowers a watermark.
law import_monotone:
  for +s: St.Store
  for +ix: I.Interchange
  for +key: S.Pubkey
  {Imp.keeps_up(Sto.key_state(s, key), Sto.key_state(I.Imp.after(s, ix), key)) == True{} : Bool}

# L10: write before sign
# ======================
#
# The core task runs the plan of src/core.bend in order: a write is an
# append with fsync, and a grant answers Go, after which a connection task
# signs. These laws are about the plan. The loop that runs it (main.bend) and
# the rule that a connection task signs only after Go are reviewed code.

# L10: the plan writes at most once, and only before its reply.
law write_before_sign:
  for +s: St.Store
  for +key: S.Pubkey
  for +r: R.Request
  for +root: S.B32
  {Core.write_first(Co.Core.plan(s, key, r, root)) == True{} : Bool}

# L10: the state after a request is the state before it with the written
# events applied. So the state in memory is the replay of the log.
law log_is_state:
  for +s: St.Store
  for +key: S.Pubkey
  for +r: R.Request
  for +root: S.B32
  {Co.Core.next(s, key, r, root) == St.Store.apply_all(Co.Plan.writes(Co.Core.plan(s, key, r, root)), s) : St.Store}
