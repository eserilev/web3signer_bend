# Sign requests: the JSON body of POST /api/v1/eth2/sign/{pubkey}, decoded
# into a typed request, and the signing root that Bulkhead computes for it.
#
# Bulkhead supports ATTESTATION, BLOCK_V2 (Bellatrix and later, header only),
# RANDAO_REVEAL, AGGREGATION_SLOT, AGGREGATE_AND_PROOF(_V2),
# SYNC_COMMITTEE_MESSAGE, SYNC_COMMITTEE_SELECTION_PROOF,
# SYNC_COMMITTEE_CONTRIBUTION_AND_PROOF, VOLUNTARY_EXIT and
# VALIDATOR_REGISTRATION. docs/SPEC.md sections 6 and 7 give the rules.
import Base
import ./ssz.bend as S
import ./json.bend as J

type Msg is Data:
  MAttestation{data: S.AttestationData}
  MBlock{header: S.BeaconBlockHeader}
  MRandao{epoch: S.U64}
  MAggSlot{slot: S.U64}
  MAggregate{agg: S.AggregateAndProof}
  MSyncMsg{slot: S.U64, beacon_block_root: S.B32}
  MSyncSel{data: S.SyncSelection}
  MContribution{cp: S.ContributionAndProof}
  # capella and deneb are CAPELLA_FORK_VERSION and DENEB_FORK_EPOCH of the
  # network: EIP-7044 fixes the exit domain to the Capella version.
  MExit{exit: S.VoluntaryExit, capella: U32, deneb: S.U64}
  # genesis is GENESIS_FORK_VERSION of the network.
  MRegistration{reg: S.Registration, genesis: U32}

# fork and gvr come from fork_info. claimed is the signingRoot of the body,
# if it has one.
type Request is Data:
  Request{msg: Msg, fork: S.Fork, gvr: S.B32, claimed: Maybe<&2, S.B32>}

# A decode or check result: the value, or the cause for a 400 response.
def Req.need(-A: Data, m: Maybe<&2, A>, why: String) -> Result<&2, &2, String, A>:
  match m:
    case None{}:
      Fail{why}
    case Some{x}:
      Done{x}

# The network
# ===========
#
# The values of the network config and its preset that decoding and
# signing need. log_spe is log2(SLOTS_PER_EPOCH). committee_bits is
# MAX_COMMITTEES_PER_SLOT. electra_limit is the Electra aggregation_bits
# limit, MAX_VALIDATORS_PER_COMMITTEE * MAX_COMMITTEES_PER_SLOT, and
# electra_depth is log2 of its chunk count. sync_bits is
# SYNC_COMMITTEE_SIZE / SYNC_COMMITTEE_SUBNET_COUNT.
type Net is Data:
  Net{log_spe: Nat, genesis_version: U32, capella_version: U32, deneb_epoch: S.U64,
    electra_epoch: S.U64, gloas_epoch: S.U64, committee_bits: U32, electra_limit: U32,
    electra_depth: Nat, sync_bits: U32}

def Net.far_future() -> S.U64:
  S.U64{4294967295, 4294967295}

# The preset values: log_spe, committee_bits, electra_limit, electra_depth
# and sync_bits.
type Preset is Data:
  Preset{log_spe: Nat, committee_bits: U32, electra_limit: U32, electra_depth: Nat, sync_bits: U32}

def Preset.mainnet() -> Preset:
  Preset{5n, 64, 131072, 9n, 128}

def Preset.minimal() -> Preset:
  Preset{3n, 4, 8192, 5n, 8}

def Preset.of(+name: String) -> Maybe<&2, Preset>:
  Bool.pick(Maybe<&2, Preset>, String.eq(name, "mainnet"), Some{Preset.mainnet()},
  Bool.pick(Maybe<&2, Preset>, String.eq(name, "minimal"), Some{Preset.minimal()}, None{}))

def Net.make(p: Preset, g: U32, c: U32, d: S.U64, e: S.U64, gl: S.U64) -> Net:
  match p:
    case Preset{spe, cb, el, ed, sb}:
      Net{spe, g, c, d, e, gl, cb, el, ed, sb}

# Mainnet, for a server started without --network-config.
def Net.mainnet() -> Net:
  Net.make(Preset.mainnet(), 0, 50331648, S.U64{0, 269568}, S.U64{0, 364032}, Net.far_future())

# The first word of a config value: YAML values can have a comment after
# them.
def Net.word.go(s: String, +acc: String) -> String:
  match s:
    case SNil{}:
      String.reverse(acc)
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          Bool.pick(String, U32.is_eq(x, 32) || U32.is_eq(x, 9), String.reverse(acc),
            Net.word.go(t, SCon{Chr{x}, acc}))

def Net.word(+o: J.Json, k: String) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    j : J.Json <- J.Json.get(o, k)
    s : String <- J.Json.str(j)
    return Net.word.go(s, "")

def Net.unquote(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          Bool.pick(String, U32.is_eq(x, 39) || U32.is_eq(x, 34),
            String.reverse(String.drop(String.reverse(t), 1n)), SCon{Chr{x}, t})

def Net.need(-A: Data, k: String, m: Maybe<&2, A>) -> Result<&2, &2, String, A>:
  match m:
    case None{}:
      Fail{"missing or invalid " ++ k}
    case Some{x}:
      Done{x}

def Net.version(+o: J.Json, +k: String) -> Result<&2, &2, String, U32>:
  do Result<&2, &2, String, U32>:
    w : String <- Net.need(String, k, Net.word(o, k))
    Net.need(U32, k, S.Hex.read_bytes4(w))

def Net.epoch(+o: J.Json, +k: String) -> Result<&2, &2, String, S.U64>:
  do Result<&2, &2, String, S.U64>:
    w : String <- Net.need(String, k, Net.word(o, k))
    Net.need(S.U64, k, S.U64.read(w))

# An epoch that the config can leave out: a missing fork is far in the
# future.
def Net.epoch_or_far(+o: J.Json, +k: String) -> Result<&2, &2, String, S.U64>:
  Bool.pick(Result<&2, &2, String, S.U64>, Maybe.is_none(&2, J.Json, J.Json.get(o, k)),
    Done{Net.far_future()}, Net.epoch(o, k))

# Reads a network config. o is the config.yaml file as a JSON object of
# strings.
def Net.read(+o: J.Json) -> Result<&2, &2, String, Net>:
  do Result<&2, &2, String, Net>:
    b : String <- Net.need(String, "PRESET_BASE", Net.word(o, "PRESET_BASE"))
    p : Preset <- Net.need(Preset, "PRESET_BASE (mainnet or minimal)", Preset.of(Net.unquote(b)))
    g : U32 <- Net.version(o, "GENESIS_FORK_VERSION")
    c : U32 <- Net.version(o, "CAPELLA_FORK_VERSION")
    d : S.U64 <- Net.epoch(o, "DENEB_FORK_EPOCH")
    e : S.U64 <- Net.epoch(o, "ELECTRA_FORK_EPOCH")
    gl : S.U64 <- Net.epoch_or_far(o, "GLOAS_FORK_EPOCH")
    return Net.make(p, g, c, d, e, gl)

def Net.log_spe(n: Net) -> Nat:
  match n:
    case Net{spe, g, c, d, e, gl, cb, el, ed, sb}:
      spe

def Net.genesis_version(n: Net) -> U32:
  match n:
    case Net{spe, g, c, d, e, gl, cb, el, ed, sb}:
      g

def Net.capella_version(n: Net) -> U32:
  match n:
    case Net{spe, g, c, d, e, gl, cb, el, ed, sb}:
      c

def Net.deneb_epoch(n: Net) -> S.U64:
  match n:
    case Net{spe, g, c, d, e, gl, cb, el, ed, sb}:
      d

def Net.sync_bits(n: Net) -> U32:
  match n:
    case Net{spe, g, c, d, e, gl, cb, el, ed, sb}:
      sb

# The Attestation shape of a slot: Base before Electra, Electra before
# Gloas, and Gloas after.
type AttKind is Data:
  KBase{}
  KElectra{limit: U32, depth: Nat, committee_bits: U32}
  KGloas{limit: U32, committee_bits: U32}

def AttKind.pick(+epoch: S.U64, +electra: S.U64, gloas: S.U64, +limit: U32, depth: Nat, +cb: U32) -> AttKind:
  Bool.pick(AttKind, S.U64.is_lt(epoch, electra), KBase{},
    Bool.pick(AttKind, S.U64.is_lt(epoch, gloas), KElectra{limit, depth, cb}, KGloas{limit, cb}))

def Net.att_kind(n: Net, slot: S.U64) -> AttKind:
  match n:
    case Net{spe, g, c, d, e, gl, cb, el, ed, sb}:
      AttKind.pick(S.U64.shrn(spe, slot), e, gl, el, ed, cb)

# Fields
# ======

# A u64 is a decimal string. A bare JSON integer is accepted too.
def Dec.u64(j: J.Json) -> Maybe<&2, S.U64>:
  match j:
    case J.JStr{s}:
      S.U64.read(s)
    case J.JNum{s}:
      S.U64.read(s)
    case J.JNull{}:
      None{}
    case J.JBool{b}:
      None{}
    case J.JArr{xs}:
      None{}
    case J.JObj{fs}:
      None{}

def Dec.b32(j: J.Json) -> Maybe<&2, S.B32>:
  do Maybe<&2, S.B32>:
    s : String <- J.Json.str(j)
    S.Hex.read_b32(s)

def Dec.bytes4(j: J.Json) -> Maybe<&2, U32>:
  do Maybe<&2, U32>:
    s : String <- J.Json.str(j)
    S.Hex.read_bytes4(s)

def Get.u64(+o: J.Json, k: String) -> Maybe<&2, S.U64>:
  do Maybe<&2, S.U64>:
    j : J.Json <- J.Json.get(o, k)
    Dec.u64(j)

def Get.b32(+o: J.Json, k: String) -> Maybe<&2, S.B32>:
  do Maybe<&2, S.B32>:
    j : J.Json <- J.Json.get(o, k)
    Dec.b32(j)

def Get.bytes4(+o: J.Json, k: String) -> Maybe<&2, U32>:
  do Maybe<&2, U32>:
    j : J.Json <- J.Json.get(o, k)
    Dec.bytes4(j)

# Objects
# =======

def Dec.checkpoint(+o: J.Json) -> Maybe<&2, S.Checkpoint>:
  do Maybe<&2, S.Checkpoint>:
    e : S.U64 <- Get.u64(o, "epoch")
    r : S.B32 <- Get.b32(o, "root")
    return S.Checkpoint{e, r}

def Dec.attestation_data(+o: J.Json) -> Maybe<&2, S.AttestationData>:
  do Maybe<&2, S.AttestationData>:
    slot : S.U64 <- Get.u64(o, "slot")
    index : S.U64 <- Get.u64(o, "index")
    bbr : S.B32 <- Get.b32(o, "beacon_block_root")
    sj : J.Json <- J.Json.get(o, "source")
    source : S.Checkpoint <- Dec.checkpoint(sj)
    tj : J.Json <- J.Json.get(o, "target")
    target : S.Checkpoint <- Dec.checkpoint(tj)
    return S.AttestationData{slot, index, bbr, source, target}

def Dec.header(+o: J.Json) -> Maybe<&2, S.BeaconBlockHeader>:
  do Maybe<&2, S.BeaconBlockHeader>:
    slot : S.U64 <- Get.u64(o, "slot")
    pi : S.U64 <- Get.u64(o, "proposer_index")
    pr : S.B32 <- Get.b32(o, "parent_root")
    sr : S.B32 <- Get.b32(o, "state_root")
    br : S.B32 <- Get.b32(o, "body_root")
    return S.BeaconBlockHeader{slot, pi, pr, sr, br}

def Dec.fork(+o: J.Json) -> Maybe<&2, S.Fork>:
  do Maybe<&2, S.Fork>:
    p : U32 <- Get.bytes4(o, "previous_version")
    c : U32 <- Get.bytes4(o, "current_version")
    e : S.U64 <- Get.u64(o, "epoch")
    return S.Fork{p, c, e}

# Letter case
# ===========

def Str.upper(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      SCon{Char.to_upper(c), Str.upper(t)}

def Str.is(+s: String, name: String) -> Bool:
  String.eq(Str.upper(s), name)

# Messages
# ========

# The block versions that send only block_header. Phase0 and Altair send the
# full block, which Bulkhead does not support.
def Dec.header_version(+v: String) -> Bool:
  Str.is(v, "BELLATRIX") || Str.is(v, "CAPELLA") || Str.is(v, "DENEB") || Str.is(v, "ELECTRA")
    || Str.is(v, "FULU") || Str.is(v, "GLOAS") || Str.is(v, "HEZE")

def Dec.block_version(ok: Bool, +bb: J.Json) -> Result<&2, &2, String, Msg>:
  match ok:
    case False{}:
      Fail{"unsupported beacon_block version: only BELLATRIX and later are supported"}
    case True{}:
      do Result<&2, &2, String, Msg>:
        hj : J.Json <- Req.need(J.Json, J.Json.get(bb, "block_header"), "missing beacon_block.block_header")
        h : S.BeaconBlockHeader <- Req.need(S.BeaconBlockHeader, Dec.header(hj), "invalid beacon_block.block_header")
        return MBlock{h}

def Dec.block(+body: J.Json) -> Result<&2, &2, String, Msg>:
  do Result<&2, &2, String, Msg>:
    +bb : J.Json <- Req.need(J.Json, J.Json.get(body, "beacon_block"), "missing beacon_block")
    vj : J.Json <- Req.need(J.Json, J.Json.get(bb, "version"), "missing beacon_block.version")
    +v : String <- Req.need(String, J.Json.str(vj), "invalid beacon_block.version")
    Dec.block_version(Dec.header_version(v), bb)

def Dec.attestation(+body: J.Json) -> Result<&2, &2, String, Msg>:
  do Result<&2, &2, String, Msg>:
    aj : J.Json <- Req.need(J.Json, J.Json.get(body, "attestation"), "missing attestation")
    a : S.AttestationData <- Req.need(S.AttestationData, Dec.attestation_data(aj), "invalid attestation")
    return MAttestation{a}

def Dec.randao(+body: J.Json) -> Result<&2, &2, String, Msg>:
  do Result<&2, &2, String, Msg>:
    rj : J.Json <- Req.need(J.Json, J.Json.get(body, "randao_reveal"), "missing randao_reveal")
    e : S.U64 <- Req.need(S.U64, Get.u64(rj, "epoch"), "invalid randao_reveal")
    return MRandao{e}

def Dec.agg_slot(+body: J.Json) -> Result<&2, &2, String, Msg>:
  do Result<&2, &2, String, Msg>:
    sj : J.Json <- Req.need(J.Json, J.Json.get(body, "aggregation_slot"), "missing aggregation_slot")
    s : S.U64 <- Req.need(S.U64, Get.u64(sj, "slot"), "invalid aggregation_slot")
    return MAggSlot{s}

def Get.str(+o: J.Json, k: String) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    j : J.Json <- J.Json.get(o, k)
    J.Json.str(j)

def Get.sig(+o: J.Json, k: String) -> Maybe<&2, S.B32>:
  do Maybe<&2, S.B32>:
    s : String <- Get.str(o, k)
    S.Hex.signature_root(s)

def Get.bitvector(+o: J.Json, k: String, +bits: U32) -> Maybe<&2, S.B32>:
  do Maybe<&2, S.B32>:
    s : String <- Get.str(o, k)
    S.Hex.bitvector(s, bits)

def Get.bitlist(+o: J.Json, limit: U32) -> Maybe<&2, S.Bitlist>:
  do Maybe<&2, S.Bitlist>:
    s : String <- Get.str(o, "aggregation_bits")
    S.Hex.bitlist(s, limit)

def Dec.att_slot(d: S.AttestationData) -> S.U64:
  match d:
    case S.AttestationData{slot, index, bbr, source, target}:
      slot

# Base attestations have no committee_bits.
def Dec.att.base(no_cb: Bool, +a: J.Json, d: S.AttestationData, sig: S.B32) -> Maybe<&2, S.Attestation>:
  match no_cb:
    case False{}:
      None{}
    case True{}:
      do Maybe<&2, S.Attestation>:
        bits : S.Bitlist <- Get.bitlist(a, 2048)
        return S.AttBase{bits, d, sig}

def Dec.att.kind(k: AttKind, +a: J.Json, d: S.AttestationData, sig: S.B32) -> Maybe<&2, S.Attestation>:
  match k:
    case KBase{}:
      Dec.att.base(Maybe.is_none(&2, J.Json, J.Json.get(a, "committee_bits")), a, d, sig)
    case KElectra{limit, depth, cbits}:
      do Maybe<&2, S.Attestation>:
        bits : S.Bitlist <- Get.bitlist(a, limit)
        cb : S.B32 <- Get.bitvector(a, "committee_bits", cbits)
        return S.AttElectra{bits, depth, d, sig, cb}
    case KGloas{limit, cbits}:
      do Maybe<&2, S.Attestation>:
        bits : S.Bitlist <- Get.bitlist(a, limit)
        cb : S.B32 <- Get.bitvector(a, "committee_bits", cbits)
        return S.AttGloas{bits, d, sig, cb}

# The shape of an aggregate comes from the fork at its slot, as in
# Web3Signer. The request's version field is not used.
def Dec.aggregate_att(+a: J.Json, +net: Net) -> Maybe<&2, S.Attestation>:
  do Maybe<&2, S.Attestation>:
    dj : J.Json <- J.Json.get(a, "data")
    +d : S.AttestationData <- Dec.attestation_data(dj)
    sig : S.B32 <- Get.sig(a, "signature")
    Dec.att.kind(Net.att_kind(net, Dec.att_slot(d)), a, d, sig)

def Dec.aggregate_and_proof(+o: J.Json, +net: Net) -> Maybe<&2, S.AggregateAndProof>:
  do Maybe<&2, S.AggregateAndProof>:
    ai : S.U64 <- Get.u64(o, "aggregator_index")
    aj : J.Json <- J.Json.get(o, "aggregate")
    a : S.Attestation <- Dec.aggregate_att(aj, net)
    sel : S.B32 <- Get.sig(o, "selection_proof")
    return S.AggregateAndProof{ai, a, sel}

# AGGREGATE_AND_PROOF_V2 wraps the object as {version, data}. Lighthouse
# sends the object without the wrapper for all forks.
def Dec.unwrap.data(m: Maybe<&2, J.Json>, o: J.Json) -> J.Json:
  match m:
    case None{}:
      o
    case Some{d}:
      d

def Dec.unwrap(+o: J.Json) -> J.Json:
  Dec.unwrap.data(Bool.pick(Maybe<&2, J.Json>, Maybe.is_none(&2, J.Json, J.Json.get(o, "version")),
    None{}, J.Json.get(o, "data")), o)

def Dec.aggregate(+body: J.Json, +net: Net) -> Result<&2, &2, String, Msg>:
  do Result<&2, &2, String, Msg>:
    oj : J.Json <- Req.need(J.Json, J.Json.get(body, "aggregate_and_proof"), "missing aggregate_and_proof")
    a : S.AggregateAndProof <- Req.need(S.AggregateAndProof, Dec.aggregate_and_proof(Dec.unwrap(oj), net), "invalid aggregate_and_proof")
    return MAggregate{a}

def Dec.sync_msg(+body: J.Json) -> Result<&2, &2, String, Msg>:
  do Result<&2, &2, String, Msg>:
    +oj : J.Json <- Req.need(J.Json, J.Json.get(body, "sync_committee_message"), "missing sync_committee_message")
    slot : S.U64 <- Req.need(S.U64, Get.u64(oj, "slot"), "invalid sync_committee_message")
    r : S.B32 <- Req.need(S.B32, Get.b32(oj, "beacon_block_root"), "invalid sync_committee_message")
    return MSyncMsg{slot, r}

def Dec.sync_sel(+body: J.Json) -> Result<&2, &2, String, Msg>:
  do Result<&2, &2, String, Msg>:
    +oj : J.Json <- Req.need(J.Json, J.Json.get(body, "sync_aggregator_selection_data"), "missing sync_aggregator_selection_data")
    slot : S.U64 <- Req.need(S.U64, Get.u64(oj, "slot"), "invalid sync_aggregator_selection_data")
    sub : S.U64 <- Req.need(S.U64, Get.u64(oj, "subcommittee_index"), "invalid sync_aggregator_selection_data")
    return MSyncSel{S.SyncSelection{slot, sub}}

def Dec.contribution(+o: J.Json, +bits: U32) -> Maybe<&2, S.Contribution>:
  do Maybe<&2, S.Contribution>:
    slot : S.U64 <- Get.u64(o, "slot")
    bbr : S.B32 <- Get.b32(o, "beacon_block_root")
    sub : S.U64 <- Get.u64(o, "subcommittee_index")
    ab : S.B32 <- Get.bitvector(o, "aggregation_bits", bits)
    sig : S.B32 <- Get.sig(o, "signature")
    return S.Contribution{slot, bbr, sub, ab, sig}

def Dec.contribution_and_proof(+o: J.Json, +bits: U32) -> Maybe<&2, S.ContributionAndProof>:
  do Maybe<&2, S.ContributionAndProof>:
    ai : S.U64 <- Get.u64(o, "aggregator_index")
    cj : J.Json <- J.Json.get(o, "contribution")
    c : S.Contribution <- Dec.contribution(cj, bits)
    sel : S.B32 <- Get.sig(o, "selection_proof")
    return S.ContributionAndProof{ai, c, sel}

def Dec.contribution_msg(+body: J.Json, +net: Net) -> Result<&2, &2, String, Msg>:
  do Result<&2, &2, String, Msg>:
    oj : J.Json <- Req.need(J.Json, J.Json.get(body, "contribution_and_proof"), "missing contribution_and_proof")
    c : S.ContributionAndProof <- Req.need(S.ContributionAndProof, Dec.contribution_and_proof(oj, Net.sync_bits(net)), "invalid contribution_and_proof")
    return MContribution{c}

def Dec.exit(+body: J.Json, +net: Net) -> Result<&2, &2, String, Msg>:
  do Result<&2, &2, String, Msg>:
    +oj : J.Json <- Req.need(J.Json, J.Json.get(body, "voluntary_exit"), "missing voluntary_exit")
    e : S.U64 <- Req.need(S.U64, Get.u64(oj, "epoch"), "invalid voluntary_exit")
    vi : S.U64 <- Req.need(S.U64, Get.u64(oj, "validator_index"), "invalid voluntary_exit")
    return MExit{S.VoluntaryExit{e, vi}, Net.capella_version(net), Net.deneb_epoch(net)}

def Dec.registration_of(+o: J.Json) -> Maybe<&2, S.Registration>:
  do Maybe<&2, S.Registration>:
    fs : String <- Get.str(o, "fee_recipient")
    fee : S.B32 <- S.Hex.bytes20_root(fs)
    gas : S.U64 <- Get.u64(o, "gas_limit")
    ts : S.U64 <- Get.u64(o, "timestamp")
    ps : String <- Get.str(o, "pubkey")
    pk : S.Pubkey <- S.Hex.read_pubkey(ps)
    return S.Registration{fee, gas, ts, pk}

def Dec.registration(+body: J.Json, +net: Net) -> Result<&2, &2, String, Msg>:
  do Result<&2, &2, String, Msg>:
    oj : J.Json <- Req.need(J.Json, J.Json.get(body, "validator_registration"), "missing validator_registration")
    r : S.Registration <- Req.need(S.Registration, Dec.registration_of(oj), "invalid validator_registration")
    return MRegistration{r, Net.genesis_version(net)}

# u is the type in upper case. Each decoder compares it with String.eq, so
# the type is upper-cased once, not once for each name.
def Dec.is_registration(+u: String) -> Bool:
  String.eq(u, "VALIDATOR_REGISTRATION")

# Picks the decoder as a function, so that only the decoder for the type
# runs: Bool.pick evaluates both of its values.
def Dec.msg(+u: String) -> (J.Json -> Net -> Result<&2, &2, String, Msg>):
  Bool.pick(J.Json -> Net -> Result<&2, &2, String, Msg>, String.eq(u, "ATTESTATION"), b => n => Dec.attestation(b),
  Bool.pick(J.Json -> Net -> Result<&2, &2, String, Msg>, String.eq(u, "BLOCK_V2"), b => n => Dec.block(b),
  Bool.pick(J.Json -> Net -> Result<&2, &2, String, Msg>, String.eq(u, "RANDAO_REVEAL"), b => n => Dec.randao(b),
  Bool.pick(J.Json -> Net -> Result<&2, &2, String, Msg>, String.eq(u, "AGGREGATION_SLOT"), b => n => Dec.agg_slot(b),
  Bool.pick(J.Json -> Net -> Result<&2, &2, String, Msg>, String.eq(u, "AGGREGATE_AND_PROOF") || String.eq(u, "AGGREGATE_AND_PROOF_V2"), b => n => Dec.aggregate(b, n),
  Bool.pick(J.Json -> Net -> Result<&2, &2, String, Msg>, String.eq(u, "SYNC_COMMITTEE_MESSAGE"), b => n => Dec.sync_msg(b),
  Bool.pick(J.Json -> Net -> Result<&2, &2, String, Msg>, String.eq(u, "SYNC_COMMITTEE_SELECTION_PROOF"), b => n => Dec.sync_sel(b),
  Bool.pick(J.Json -> Net -> Result<&2, &2, String, Msg>, String.eq(u, "SYNC_COMMITTEE_CONTRIBUTION_AND_PROOF"), b => n => Dec.contribution_msg(b, n),
  Bool.pick(J.Json -> Net -> Result<&2, &2, String, Msg>, String.eq(u, "VOLUNTARY_EXIT"), b => n => Dec.exit(b, n),
  Bool.pick(J.Json -> Net -> Result<&2, &2, String, Msg>, Dec.is_registration(u), b => n => Dec.registration(b, n),
  b => n => Fail{"unsupported type"}))))))))))

# signingRoot
# ===========

def Dec.root_field.value(null: Bool, j: J.Json) -> Result<&2, &2, String, Maybe<&2, S.B32>>:
  match null:
    case True{}:
      Done{None{}}
    case False{}:
      do Result<&2, &2, String, Maybe<&2, S.B32>>:
        r : S.B32 <- Req.need(S.B32, Dec.b32(j), "invalid signingRoot")
        return Some{r}

# The body can name the root signingRoot or signing_root. A null value is
# the same as no value.
def Dec.root_field(m: Maybe<&2, J.Json>) -> Result<&2, &2, String, Maybe<&2, S.B32>>:
  match m:
    case None{}:
      Done{None{}}
    case Some{+j}:
      Dec.root_field.value(J.Json.is_null(j), j)

def Dec.root_pair.same(+a: S.B32, b: S.B32, same: Bool) -> Result<&2, &2, String, Maybe<&2, S.B32>>:
  match same:
    case True{}:
      Done{Some{a}}
    case False{}:
      Fail{"signingRoot and signing_root differ"}

# If the body has both names, both must hold the same root.
def Dec.root_pair(a: Maybe<&2, S.B32>, b: Maybe<&2, S.B32>) -> Result<&2, &2, String, Maybe<&2, S.B32>>:
  match a:
    case None{}:
      Done{b}
    case Some{+x}:
      match b:
        case None{}:
          Done{Some{x}}
        case Some{+y}:
          Dec.root_pair.same(x, y, S.B32.is_eq(x, y))

def Dec.claimed(+body: J.Json) -> Result<&2, &2, String, Maybe<&2, S.B32>>:
  do Result<&2, &2, String, Maybe<&2, S.B32>>:
    a : Maybe<&2, S.B32> <- Dec.root_field(J.Json.get(body, "signingRoot"))
    b : Maybe<&2, S.B32> <- Dec.root_field(J.Json.get(body, "signing_root"))
    Dec.root_pair(a, b)

# The request
# ===========

type ForkInfo is Data:
  ForkInfo{fork: S.Fork, gvr: S.B32}

def Dec.fork_info(+body: J.Json) -> Result<&2, &2, String, ForkInfo>:
  do Result<&2, &2, String, ForkInfo>:
    +fi : J.Json <- Req.need(J.Json, J.Json.get(body, "fork_info"), "missing fork_info")
    fj : J.Json <- Req.need(J.Json, J.Json.get(fi, "fork"), "missing fork_info.fork")
    fork : S.Fork <- Req.need(S.Fork, Dec.fork(fj), "invalid fork_info.fork")
    gvr : S.B32 <- Req.need(S.B32, Get.b32(fi, "genesis_validators_root"), "invalid fork_info.genesis_validators_root")
    return ForkInfo{fork, gvr}

# A validator registration has no fork_info: its domain uses the genesis
# fork version and a zero root. Bulkhead ignores fork_info if the body has
# one.
def Dec.fork_info_for(reg: Bool, +body: J.Json) -> Result<&2, &2, String, ForkInfo>:
  match reg:
    case True{}:
      Done{ForkInfo{S.Fork{0, 0, S.U64.zero()}, S.B32.zero()}}
    case False{}:
      Dec.fork_info(body)

def Request.make(msg: Msg, fg: ForkInfo, claimed: Maybe<&2, S.B32>) -> Request:
  match fg:
    case ForkInfo{fork, gvr}:
      Request{msg, fork, gvr, claimed}

def Request.decode_json(+body: J.Json, +net: Net) -> Result<&2, &2, String, Request>:
  do Result<&2, &2, String, Request>:
    tj : J.Json <- Req.need(J.Json, J.Json.get(body, "type"), "missing type")
    t : String <- Req.need(String, J.Json.str(tj), "invalid type")
    +u : String = Str.upper(t)
    msg : Msg <- Dec.msg(u)(body)(net)
    fg : ForkInfo <- Dec.fork_info_for(Dec.is_registration(u), body)
    claimed : Maybe<&2, S.B32> <- Dec.claimed(body)
    return Request.make(msg, fg, claimed)

def Request.decode(s: String, +net: Net) -> Result<&2, &2, String, Request>:
  do Result<&2, &2, String, Request>:
    +body : J.Json <- Req.need(J.Json, J.Json.parse(s), "invalid JSON")
    Request.decode_json(body, net)

# Signing roots
# =============

def Msg.name(m: Msg) -> String:
  match m:
    case MAttestation{a}:
      "ATTESTATION"
    case MBlock{h}:
      "BLOCK_V2"
    case MRandao{e}:
      "RANDAO_REVEAL"
    case MAggSlot{s}:
      "AGGREGATION_SLOT"
    case MAggregate{a}:
      "AGGREGATE_AND_PROOF"
    case MSyncMsg{s, r}:
      "SYNC_COMMITTEE_MESSAGE"
    case MSyncSel{d}:
      "SYNC_COMMITTEE_SELECTION_PROOF"
    case MContribution{c}:
      "SYNC_COMMITTEE_CONTRIBUTION_AND_PROOF"
    case MExit{e, c, d}:
      "VOLUNTARY_EXIT"
    case MRegistration{r, g}:
      "VALIDATOR_REGISTRATION"

def Msg.slot_epoch(+slot: S.U64, log_spe: Nat) -> S.U64:
  S.U64.shrn(log_spe, slot)

# The domain from fork_info: domain_type at the fork version of epoch.
def Msg.std(domain_type: U32, fork: S.Fork, epoch: S.U64, gvr: S.B32) -> S.B32:
  S.Domain.compute(domain_type, S.Domain.fork_version(fork, epoch), gvr)

# EIP-7044: if fork_info is at Deneb or later, an exit signs with the
# Capella fork version. Otherwise the exit's epoch selects the version. This
# is the rule of the spec and of Web3Signer.
def Msg.exit_domain(e: S.VoluntaryExit, +capella: U32, deneb: S.U64, fork: S.Fork, +gvr: S.B32) -> S.B32:
  match e:
    case S.VoluntaryExit{epoch, vi}:
      match fork:
        case S.Fork{p, c, +fe}:
          Bool.pick(S.B32, S.U64.is_lt(fe, deneb),
            Msg.std(S.Domain.voluntary_exit(), S.Fork{p, c, fe}, epoch, gvr),
            S.Domain.compute(S.Domain.voluntary_exit(), capella, gvr))

def Msg.domain(m: Msg, fork: S.Fork, gvr: S.B32, log_spe: Nat) -> S.B32:
  match m:
    case MAttestation{a}:
      match a:
        case S.AttestationData{slot, index, bbr, source, target}:
          match target:
            case S.Checkpoint{e, r}:
              Msg.std(S.Domain.beacon_attester(), fork, e, gvr)
    case MBlock{h}:
      match h:
        case S.BeaconBlockHeader{slot, pi, pr, sr, br}:
          Msg.std(S.Domain.beacon_proposer(), fork, Msg.slot_epoch(slot, log_spe), gvr)
    case MRandao{e}:
      Msg.std(S.Domain.randao(), fork, e, gvr)
    case MAggSlot{s}:
      Msg.std(S.Domain.selection_proof(), fork, Msg.slot_epoch(s, log_spe), gvr)
    case MAggregate{a}:
      match a:
        case S.AggregateAndProof{ai, att, sel}:
          Msg.std(S.Domain.aggregate_and_proof(), fork, Msg.slot_epoch(S.Attestation.slot(att), log_spe), gvr)
    case MSyncMsg{s, r}:
      Msg.std(S.Domain.sync_committee(), fork, Msg.slot_epoch(s, log_spe), gvr)
    case MSyncSel{d}:
      match d:
        case S.SyncSelection{s, sub}:
          Msg.std(S.Domain.sync_committee_selection_proof(), fork, Msg.slot_epoch(s, log_spe), gvr)
    case MContribution{cp}:
      match cp:
        case S.ContributionAndProof{ai, c, sel}:
          match c:
            case S.Contribution{s, bbr, sub, bits, sig}:
              Msg.std(S.Domain.contribution_and_proof(), fork, Msg.slot_epoch(s, log_spe), gvr)
    case MExit{e, c, d}:
      Msg.exit_domain(e, c, d, fork, gvr)
    case MRegistration{r, g}:
      S.Domain.compute(S.Domain.application_builder(), g, S.B32.zero())

def Msg.object_root(m: Msg) -> S.B32:
  match m:
    case MAttestation{a}:
      S.AttestationData.root(a)
    case MBlock{h}:
      S.BeaconBlockHeader.root(h)
    case MRandao{e}:
      S.Ssz.u64(e)
    case MAggSlot{s}:
      S.Ssz.u64(s)
    case MAggregate{a}:
      S.AggregateAndProof.root(a)
    case MSyncMsg{s, r}:
      r
    case MSyncSel{d}:
      S.SyncSelection.root(d)
    case MContribution{c}:
      S.ContributionAndProof.root(c)
    case MExit{e, c, d}:
      S.VoluntaryExit.root(e)
    case MRegistration{r, g}:
      S.Registration.root(r)

# The root that Bulkhead signs. It depends only on the request, never on
# the claimed signingRoot.
def Request.signing_root(r: Request, log_spe: Nat) -> S.B32:
  match r:
    case Request{+msg, fork, gvr, claimed}:
      S.SigningData.root(Msg.object_root(msg), Msg.domain(msg, fork, gvr, log_spe))

def Request.check.claim(+root: S.B32, claimed: Maybe<&2, S.B32>) -> Result<&2, &2, String, S.B32>:
  match claimed:
    case None{}:
      Done{root}
    case Some{c}:
      Bool.pick(Result<&2, &2, String, S.B32>, S.B32.is_eq(c, root), Done{root},
        Fail{"signing root does not match the request"})

# The computed signing root, or a failure if the body claims another root.
def Request.check(+r: Request, log_spe: Nat) -> Result<&2, &2, String, S.B32>:
  match r:
    case Request{msg, fork, gvr, claimed}:
      Request.check.claim(Request.signing_root(Request{msg, fork, gvr, claimed}, log_spe), claimed)
