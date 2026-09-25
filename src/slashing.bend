# Slashing protection for one key: the records, the low watermarks, and the
# decision for a block or an attestation request. LAWS.bend states what these
# decisions must guarantee; this file is one implementation of them.
import Base
import ./ssz.bend as S

# A signed block: its slot and its signing root. The root is None when it is
# not known: an EIP-3076 import can give records with no root.
type BlockRec is Data:
  BlockRec{slot: S.U64, root: Maybe<&2, S.B32>}

type AttRec is Data:
  AttRec{source: S.U64, target: S.U64, root: Maybe<&2, S.B32>}

type AttMark is Data:
  AttMark{source: S.U64, target: S.U64}

type KeyState is Data:
  KeyState{blocks: List<&2, BlockRec>, atts: List<&2, AttRec>,
           block_mark: Maybe<&2, S.U64>, att_mark: Maybe<&2, AttMark>}

type Reason is Data:
  BelowWatermark{}
  DoubleBlock{}
  SourceAfterTarget{}
  DoubleVote{}
  Surrounded{}
  Surrounds{}

# Reject: do not sign. Repeat: this exact message has a record already, so
# sign it again and keep the state. Record: sign it and keep the new state.
type Decision is Data:
  Reject{reason: Reason}
  Repeat{}
  Record{state: KeyState}

def KeyState.empty() -> KeyState:
  KeyState{[], [], None{}, None{}}

# The state after a decision.
def KeyState.after(ks: KeyState, d: Decision) -> KeyState:
  match d:
    case Reject{r}:
      ks
    case Repeat{}:
      ks
    case Record{s}:
      s

# True when r is the known root k.
def Root.is(k: S.B32, r: Maybe<&2, S.B32>) -> Bool:
  match r:
    case None{}:
      False{}
    case Some{x}:
      S.B32.is_eq(k, x)

# The result of comparing a request with the records.
type Scan is Data:
  Clear{}
  Again{}
  Clash{reason: Reason}

# Clash wins over Again, and Again wins over Clear.
def Scan.join(a: Scan, b: Scan) -> Scan:
  match a:
    case Clash{r}:
      Clash{r}
    case Again{}:
      match b:
        case Clash{r}:
          Clash{r}
        case Again{}:
          Again{}
        case Clear{}:
          Again{}
    case Clear{}:
      b

def Scan.same_or(same: Bool, other: Reason) -> Scan:
  match same:
    case True{}:
      Again{}
    case False{}:
      Clash{other}

# Blocks
# ======

def Block.scan.one(+slot: S.U64, +root: S.B32, r: BlockRec) -> Scan:
  match r:
    case BlockRec{rs, rr}:
      Bool.pick(Scan, S.U64.is_eq(slot, rs), Scan.same_or(Root.is(root, rr), DoubleBlock{}), Clear{})

def Block.scan(xs: List<&2, BlockRec>, +slot: S.U64, +root: S.B32) -> Scan:
  match xs:
    case Nil{}:
      Clear{}
    case Con{x, t}:
      Scan.join(Block.scan.one(slot, root, x), Block.scan(t, slot, root))

def Block.below(+slot: S.U64, m: Maybe<&2, S.U64>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{w}:
      S.U64.is_lt(slot, w)

def Block.finish(s: Scan, ks: KeyState, +slot: S.U64, +root: S.B32) -> Decision:
  match s:
    case Clash{r}:
      Reject{r}
    case Again{}:
      Repeat{}
    case Clear{}:
      match ks:
        case KeyState{bs, as, bm, am}:
          Record{KeyState{Con{BlockRec{slot, Some{root}}, bs}, as, bm, am}}

def Block.decide.go(below: Bool, +ks: KeyState, +slot: S.U64, +root: S.B32) -> Decision:
  match below:
    case True{}:
      Reject{BelowWatermark{}}
    case False{}:
      match ks:
        case KeyState{+bs, as, bm, am}:
          Block.finish(Block.scan(bs, slot, root), KeyState{bs, as, bm, am}, slot, root)

def Block.decide(+ks: KeyState, +slot: S.U64, +root: S.B32) -> Decision:
  match ks:
    case KeyState{bs, as, +bm, am}:
      Block.decide.go(Block.below(slot, bm), KeyState{bs, as, bm, am}, slot, root)

# Attestations
# ============

# A record with the same target. The same root and source is this message
# again. The same root with another source is not a double vote: a root
# names one message, so real requests never do this, but the scan must not
# call it a repeat, because no record of it exists.
def Att.same_target(same_root: Bool, same_source: Bool) -> Scan:
  match same_root:
    case True{}:
      match same_source:
        case True{}:
          Again{}
        case False{}:
          Clear{}
    case False{}:
      Clash{DoubleVote{}}

# The comparisons use is_lt in the order that spec/safety.bend uses, so the
# proofs need no lemma about swapping them.
def Att.scan.one(+source: S.U64, +target: S.U64, +root: S.B32, r: AttRec) -> Scan:
  match r:
    case AttRec{+rs, +rt, rr}:
      Bool.pick(Scan, S.U64.is_eq(target, rt), Att.same_target(Root.is(root, rr), S.U64.is_eq(source, rs)),
      Bool.pick(Scan, S.U64.is_lt(rs, source) && S.U64.is_lt(target, rt), Clash{Surrounded{}},
      Bool.pick(Scan, S.U64.is_lt(source, rs) && S.U64.is_lt(rt, target), Clash{Surrounds{}},
      Clear{})))

def Att.scan(xs: List<&2, AttRec>, +source: S.U64, +target: S.U64, +root: S.B32) -> Scan:
  match xs:
    case Nil{}:
      Clear{}
    case Con{x, t}:
      Scan.join(Att.scan.one(source, target, root, x), Att.scan(t, source, target, root))

def Att.below(+source: S.U64, +target: S.U64, m: Maybe<&2, AttMark>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{w}:
      match w:
        case AttMark{ms, mt}:
          S.U64.is_lt(source, ms) || S.U64.is_lt(target, mt)

def Att.finish(s: Scan, ks: KeyState, +source: S.U64, +target: S.U64, +root: S.B32) -> Decision:
  match s:
    case Clash{r}:
      Reject{r}
    case Again{}:
      Repeat{}
    case Clear{}:
      match ks:
        case KeyState{bs, as, bm, am}:
          Record{KeyState{bs, Con{AttRec{source, target, Some{root}}, as}, bm, am}}

def Att.decide.scan(below: Bool, +ks: KeyState, +source: S.U64, +target: S.U64, +root: S.B32) -> Decision:
  match below:
    case True{}:
      Reject{BelowWatermark{}}
    case False{}:
      match ks:
        case KeyState{bs, +as, bm, am}:
          Att.finish(Att.scan(as, source, target, root), KeyState{bs, as, bm, am}, source, target, root)

def Att.decide.go(order: Bool, +ks: KeyState, +source: S.U64, +target: S.U64, +root: S.B32) -> Decision:
  match order:
    case False{}:
      Reject{SourceAfterTarget{}}
    case True{}:
      match ks:
        case KeyState{bs, as, bm, +am}:
          Att.decide.scan(Att.below(source, target, am), KeyState{bs, as, bm, am}, source, target, root)

def Att.decide(+ks: KeyState, +source: S.U64, +target: S.U64, +root: S.B32) -> Decision:
  Att.decide.go(Bool.not(S.U64.is_lt(target, source)), ks, source, target, root)
