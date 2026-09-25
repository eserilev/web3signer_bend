# Test CLI for src/ssz.bend. tests/run_ssz.py calls it once for each case.
#
#   ssz_cli <command> <args...>
#
# It prints the result, or ERR if an argument does not parse.
import Base
import ../src/ssz.bend as S

def Args.data(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{h, Args.data(t)}

def Args.nth(xs: List<&2, String>, n: Nat) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      match n:
        case 0n:
          h
        case 1n+p:
          Args.nth(t, p)

def Arg.b32(+xs: List<&2, String>, n: Nat) -> Maybe<&2, S.B32>:
  S.Hex.read_b32(Args.nth(xs, n))

def Arg.u64(+xs: List<&2, String>, n: Nat) -> Maybe<&2, S.U64>:
  S.U64.read(Args.nth(xs, n))

def Arg.bytes4(+xs: List<&2, String>, n: Nat) -> Maybe<&2, U32>:
  S.Hex.read_bytes4(Args.nth(xs, n))

def Cli.hash64(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    a : S.B32 <- Arg.b32(xs, 1n)
    b : S.B32 <- Arg.b32(xs, 2n)
    return S.Hex.b32(S.Sha.hash64(a, b))

def Cli.u64(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    +a : S.U64 <- Arg.u64(xs, 1n)
    return S.U64.show(a) ++ " " ++ S.Hex.b32(S.Ssz.u64(a))

def Cli.shr(+xs: List<&2, String>, n: Nat) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    a : S.U64 <- Arg.u64(xs, 1n)
    return S.U64.show(S.U64.shrn(n, a))

def Cli.checkpoint(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    e : S.U64 <- Arg.u64(xs, 1n)
    r : S.B32 <- Arg.b32(xs, 2n)
    return S.Hex.b32(S.Checkpoint.root(S.Checkpoint{e, r}))

def Cli.attdata(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    slot : S.U64 <- Arg.u64(xs, 1n)
    index : S.U64 <- Arg.u64(xs, 2n)
    bbr : S.B32 <- Arg.b32(xs, 3n)
    se : S.U64 <- Arg.u64(xs, 4n)
    sr : S.B32 <- Arg.b32(xs, 5n)
    te : S.U64 <- Arg.u64(xs, 6n)
    tr : S.B32 <- Arg.b32(xs, 7n)
    return S.Hex.b32(S.AttestationData.root(
      S.AttestationData{slot, index, bbr, S.Checkpoint{se, sr}, S.Checkpoint{te, tr}}))

def Cli.header(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    slot : S.U64 <- Arg.u64(xs, 1n)
    pi : S.U64 <- Arg.u64(xs, 2n)
    pr : S.B32 <- Arg.b32(xs, 3n)
    sr : S.B32 <- Arg.b32(xs, 4n)
    br : S.B32 <- Arg.b32(xs, 5n)
    return S.Hex.b32(S.BeaconBlockHeader.root(S.BeaconBlockHeader{slot, pi, pr, sr, br}))

def Cli.fork(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    p : U32 <- Arg.bytes4(xs, 1n)
    c : U32 <- Arg.bytes4(xs, 2n)
    e : S.U64 <- Arg.u64(xs, 3n)
    return S.Hex.b32(S.Fork.root(S.Fork{p, c, e}))

def Cli.forkdata(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    c : U32 <- Arg.bytes4(xs, 1n)
    g : S.B32 <- Arg.b32(xs, 2n)
    return S.Hex.b32(S.ForkData.root(c, g))

def Cli.signingdata(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    o : S.B32 <- Arg.b32(xs, 1n)
    d : S.B32 <- Arg.b32(xs, 2n)
    return S.Hex.b32(S.SigningData.root(o, d))

# domain <domain_type> <previous_version> <current_version> <fork_epoch> <epoch> <gvr>
def Cli.domain(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    t : U32 <- Arg.bytes4(xs, 1n)
    p : U32 <- Arg.bytes4(xs, 2n)
    c : U32 <- Arg.bytes4(xs, 3n)
    fe : S.U64 <- Arg.u64(xs, 4n)
    e : S.U64 <- Arg.u64(xs, 5n)
    g : S.B32 <- Arg.b32(xs, 6n)
    return S.Hex.b32(S.Domain.compute(t, S.Domain.fork_version(S.Fork{p, c, fe}, e), g))

def Cli.lo(v: S.U64) -> U32:
  match v:
    case S.U64{h, l}:
      l

def Arg.u32(+xs: List<&2, String>, n: Nat) -> Maybe<&2, U32>:
  do Maybe<&2, U32>:
    v : S.U64 <- Arg.u64(xs, n)
    return Cli.lo(v)

def Arg.sig(+xs: List<&2, String>, n: Nat) -> Maybe<&2, S.B32>:
  S.Hex.signature_root(Args.nth(xs, n))

def Cli.exit(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    e : S.U64 <- Arg.u64(xs, 1n)
    v : S.U64 <- Arg.u64(xs, 2n)
    return S.Hex.b32(S.VoluntaryExit.root(S.VoluntaryExit{e, v}))

def Cli.syncsel(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    slot : S.U64 <- Arg.u64(xs, 1n)
    sub : S.U64 <- Arg.u64(xs, 2n)
    return S.Hex.b32(S.SyncSelection.root(S.SyncSelection{slot, sub}))

# Contribution args from index k: <nbits> <slot> <bbr> <sub> <bits> <sig>
def Arg.contribution(+xs: List<&2, String>, +k: Nat) -> Maybe<&2, S.Contribution>:
  do Maybe<&2, S.Contribution>:
    n : U32 <- Arg.u32(xs, k)
    slot : S.U64 <- Arg.u64(xs, Nat.add(k, 1n))
    bbr : S.B32 <- Arg.b32(xs, Nat.add(k, 2n))
    sub : S.U64 <- Arg.u64(xs, Nat.add(k, 3n))
    bits : S.B32 <- S.Hex.bitvector(Args.nth(xs, Nat.add(k, 4n)), n)
    sig : S.B32 <- Arg.sig(xs, Nat.add(k, 5n))
    return S.Contribution{slot, bbr, sub, bits, sig}

def Cli.contribution(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    c : S.Contribution <- Arg.contribution(xs, 1n)
    return S.Hex.b32(S.Contribution.root(c))

# contribproof <ai> <contribution args> <selection_proof>
def Cli.contribproof(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    ai : S.U64 <- Arg.u64(xs, 1n)
    c : S.Contribution <- Arg.contribution(xs, 2n)
    sel : S.B32 <- Arg.sig(xs, 8n)
    return S.Hex.b32(S.ContributionAndProof.root(S.ContributionAndProof{ai, c, sel}))

# registration <fee_recipient> <gas_limit> <timestamp> <pubkey>
def Cli.registration(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    fee : S.B32 <- S.Hex.bytes20_root(Args.nth(xs, 1n))
    gas : S.U64 <- Arg.u64(xs, 2n)
    ts : S.U64 <- Arg.u64(xs, 3n)
    pk : S.Pubkey <- S.Hex.read_pubkey(Args.nth(xs, 4n))
    return S.Hex.b32(S.Registration.root(S.Registration{fee, gas, ts, pk}))

def Arg.attdata(+xs: List<&2, String>, +k: Nat) -> Maybe<&2, S.AttestationData>:
  do Maybe<&2, S.AttestationData>:
    slot : S.U64 <- Arg.u64(xs, k)
    index : S.U64 <- Arg.u64(xs, Nat.add(k, 1n))
    bbr : S.B32 <- Arg.b32(xs, Nat.add(k, 2n))
    se : S.U64 <- Arg.u64(xs, Nat.add(k, 3n))
    sr : S.B32 <- Arg.b32(xs, Nat.add(k, 4n))
    te : S.U64 <- Arg.u64(xs, Nat.add(k, 5n))
    tr : S.B32 <- Arg.b32(xs, Nat.add(k, 6n))
    return S.AttestationData{slot, index, bbr, S.Checkpoint{se, sr}, S.Checkpoint{te, tr}}

# Attestation args from index k: <kind> <limit> <depth> <cbits> <bits>
# <7 attestation data fields> <sig> <committee_bits>. kind is base,
# electra or gloas. base ignores depth, cbits and committee_bits.
def Arg.att.base(+xs: List<&2, String>, +k: Nat) -> Maybe<&2, S.Attestation>:
  do Maybe<&2, S.Attestation>:
    limit : U32 <- Arg.u32(xs, Nat.add(k, 1n))
    bits : S.Bitlist <- S.Hex.bitlist(Args.nth(xs, Nat.add(k, 4n)), limit)
    d : S.AttestationData <- Arg.attdata(xs, Nat.add(k, 5n))
    sig : S.B32 <- Arg.sig(xs, Nat.add(k, 12n))
    return S.AttBase{bits, d, sig}

def Arg.att.electra(+xs: List<&2, String>, +k: Nat) -> Maybe<&2, S.Attestation>:
  do Maybe<&2, S.Attestation>:
    limit : U32 <- Arg.u32(xs, Nat.add(k, 1n))
    depth : U32 <- Arg.u32(xs, Nat.add(k, 2n))
    cbits : U32 <- Arg.u32(xs, Nat.add(k, 3n))
    bits : S.Bitlist <- S.Hex.bitlist(Args.nth(xs, Nat.add(k, 4n)), limit)
    d : S.AttestationData <- Arg.attdata(xs, Nat.add(k, 5n))
    sig : S.B32 <- Arg.sig(xs, Nat.add(k, 12n))
    cb : S.B32 <- S.Hex.bitvector(Args.nth(xs, Nat.add(k, 13n)), cbits)
    return S.AttElectra{bits, U32.to_nat(depth), d, sig, cb}

def Arg.att.gloas(+xs: List<&2, String>, +k: Nat) -> Maybe<&2, S.Attestation>:
  do Maybe<&2, S.Attestation>:
    limit : U32 <- Arg.u32(xs, Nat.add(k, 1n))
    cbits : U32 <- Arg.u32(xs, Nat.add(k, 3n))
    bits : S.Bitlist <- S.Hex.bitlist(Args.nth(xs, Nat.add(k, 4n)), limit)
    d : S.AttestationData <- Arg.attdata(xs, Nat.add(k, 5n))
    sig : S.B32 <- Arg.sig(xs, Nat.add(k, 12n))
    cb : S.B32 <- S.Hex.bitvector(Args.nth(xs, Nat.add(k, 13n)), cbits)
    return S.AttGloas{bits, d, sig, cb}

def Arg.att(+xs: List<&2, String>, +k: Nat) -> Maybe<&2, S.Attestation>:
  Bool.pick(Maybe<&2, S.Attestation>, String.eq(Args.nth(xs, k), "base"), Arg.att.base(xs, k),
  Bool.pick(Maybe<&2, S.Attestation>, String.eq(Args.nth(xs, k), "electra"), Arg.att.electra(xs, k),
  Bool.pick(Maybe<&2, S.Attestation>, String.eq(Args.nth(xs, k), "gloas"), Arg.att.gloas(xs, k),
  None{})))

def Cli.att(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    a : S.Attestation <- Arg.att(xs, 1n)
    return S.Hex.b32(S.Attestation.root(a))

# aggproof <ai> <attestation args> <selection_proof>
def Cli.aggproof(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    ai : S.U64 <- Arg.u64(xs, 1n)
    a : S.Attestation <- Arg.att(xs, 2n)
    sel : S.B32 <- Arg.sig(xs, 16n)
    return S.Hex.b32(S.AggregateAndProof.root(S.AggregateAndProof{ai, a, sel}))

# chunks <hex>: the root of a byte list under merkleize_progressive, and
# bitlist <hex> <limit> <depth>: its root, both for the unit tests.
def Cli.progressive(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    bs : List<&2, U32> <- S.Hex.bytes(Args.nth(xs, 1n))
    return S.Hex.b32(S.Ssz.progressive(S.Ssz.chunks(bs)))

def Cli.bitlist(+xs: List<&2, String>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    limit : U32 <- Arg.u32(xs, 2n)
    depth : U32 <- Arg.u32(xs, 3n)
    b : S.Bitlist <- S.Hex.bitlist(Args.nth(xs, 1n), limit)
    return S.Hex.b32(S.Bitlist.root(b, U32.to_nat(depth)))

def Cli.out(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      "ERR"
    case Some{s}:
      s

def Cli.is(+cmd: String, name: String) -> Bool:
  String.eq(cmd, name)

# Picks the command as a function, so that only the chosen command runs:
# Bool.pick evaluates both of its values.
def Cli.run(+cmd: String) -> (List<&2, String> -> Maybe<&2, String>):
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "hash64"), xs => Cli.hash64(xs),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "u64"), xs => Cli.u64(xs),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "shr3"), xs => Cli.shr(xs, 3n),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "shr5"), xs => Cli.shr(xs, 5n),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "checkpoint"), xs => Cli.checkpoint(xs),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "attdata"), xs => Cli.attdata(xs),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "header"), xs => Cli.header(xs),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "fork"), xs => Cli.fork(xs),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "forkdata"), xs => Cli.forkdata(xs),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "signingdata"), xs => Cli.signingdata(xs),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "domain"), xs => Cli.domain(xs),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "exit"), xs => Cli.exit(xs),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "syncsel"), xs => Cli.syncsel(xs),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "contribution"), xs => Cli.contribution(xs),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "contribproof"), xs => Cli.contribproof(xs),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "registration"), xs => Cli.registration(xs),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "att"), xs => Cli.att(xs),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "aggproof"), xs => Cli.aggproof(xs),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "progressive"), xs => Cli.progressive(xs),
  Bool.pick(List<&2, String> -> Maybe<&2, String>, Cli.is(cmd, "bitlist"), xs => Cli.bitlist(xs),
  xs => None{}))))))))))))))))))))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +xs : List<&2, String> = Args.data(args)
    IO.print(Cli.out(Cli.run(Args.nth(xs, 0n))(xs)))
