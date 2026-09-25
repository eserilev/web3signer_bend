# The definition of slashing safety for Bulkhead. DRAFT for review: the owner
# of LAWS.bend owns this file too, and the code does not edit it.
#
# These definitions come from the consensus spec (is_slashable_attestation_data,
# and the proposer slashing condition), not from src/. The code can change
# freely; it cannot change what "safe" means. LAWS.bend states the laws with
# these definitions. Tests import this file to run the laws as checks.
import Base
import ../src/ssz.bend as S
import ../src/slashing.bend as Slash

# Spec: slashable pairs
# =====================

def eq(a: S.U64, b: S.U64) -> Bool:
  S.U64.is_eq(a, b)

def lt(a: S.U64, b: S.U64) -> Bool:
  S.U64.is_lt(a, b)

# Two roots are the same only when both are known and equal. An unknown root
# can hide any message, so it counts as different.
def differ(a: Maybe<&2, S.B32>, b: Maybe<&2, S.B32>) -> Bool:
  match a:
    case None{}:
      True{}
    case Some{x}:
      match b:
        case None{}:
          True{}
        case Some{y}:
          Bool.not(S.B32.is_eq(x, y))

# Two different blocks at one slot.
def blocks_clash(a: Slash.BlockRec, b: Slash.BlockRec) -> Bool:
  match a b:
    case Slash.BlockRec{sa, ra} Slash.BlockRec{sb, rb}:
      eq(sa, sb) && differ(ra, rb)

# a surrounds b: a.source < b.source and b.target < a.target.
def surrounds(sa: S.U64, ta: S.U64, sb: S.U64, tb: S.U64) -> Bool:
  lt(sa, sb) && lt(tb, ta)

# A double vote, or a surround vote in either direction.
def atts_clash(a: Slash.AttRec, b: Slash.AttRec) -> Bool:
  match a b:
    case Slash.AttRec{+sa, +ta, ra} Slash.AttRec{+sb, +tb, rb}:
      (eq(ta, tb) && differ(ra, rb))
        || surrounds(sa, ta, sb, tb) || surrounds(sb, tb, sa, ta)

# Spec: safe states
# =================

def block_clashes_any(+a: Slash.BlockRec, xs: List<&2, Slash.BlockRec>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      blocks_clash(a, x) || block_clashes_any(a, t)

def blocks_safe(xs: List<&2, Slash.BlockRec>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, +t}:
      Bool.not(block_clashes_any(x, t)) && blocks_safe(t)

def att_clashes_any(+a: Slash.AttRec, xs: List<&2, Slash.AttRec>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      atts_clash(a, x) || att_clashes_any(a, t)

# No attestation record has source > target.
def att_ordered(a: Slash.AttRec) -> Bool:
  match a:
    case Slash.AttRec{s, t, r}:
      Bool.not(lt(t, s))

def atts_safe(xs: List<&2, Slash.AttRec>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +t}:
      att_ordered(x) && Bool.not(att_clashes_any(x, t)) && atts_safe(t)

# No two records of one key are slashable together.
def safe(ks: Slash.KeyState) -> Bool:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      blocks_safe(bs) && atts_safe(as)

# Spec: what a decision must keep
# ===============================

def root_eq(a: Maybe<&2, S.B32>, b: Maybe<&2, S.B32>) -> Bool:
  match a:
    case None{}:
      Maybe.is_none(&2, S.B32, b)
    case Some{x}:
      match b:
        case None{}:
          False{}
        case Some{y}:
          S.B32.is_eq(x, y)

def block_eq(a: Slash.BlockRec, b: Slash.BlockRec) -> Bool:
  match a b:
    case Slash.BlockRec{sa, ra} Slash.BlockRec{sb, rb}:
      eq(sa, sb) && root_eq(ra, rb)

def att_eq(a: Slash.AttRec, b: Slash.AttRec) -> Bool:
  match a b:
    case Slash.AttRec{sa, ta, ra} Slash.AttRec{sb, tb, rb}:
      eq(sa, sb) && eq(ta, tb) && root_eq(ra, rb)

def has_block(+a: Slash.BlockRec, xs: List<&2, Slash.BlockRec>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      block_eq(a, x) || has_block(a, t)

def has_att(+a: Slash.AttRec, xs: List<&2, Slash.AttRec>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      att_eq(a, x) || has_att(a, t)

def blocks_within(xs: List<&2, Slash.BlockRec>, +ys: List<&2, Slash.BlockRec>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      has_block(x, ys) && blocks_within(t, ys)

def atts_within(xs: List<&2, Slash.AttRec>, +ys: List<&2, Slash.AttRec>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      has_att(x, ys) && atts_within(t, ys)

def mark_eq(a: Maybe<&2, S.U64>, b: Maybe<&2, S.U64>) -> Bool:
  match a:
    case None{}:
      Maybe.is_none(&2, S.U64, b)
    case Some{x}:
      match b:
        case None{}:
          False{}
        case Some{y}:
          eq(x, y)

def att_mark_same(a: Slash.AttMark, b: Slash.AttMark) -> Bool:
  match a b:
    case Slash.AttMark{xs, xt} Slash.AttMark{ys, yt}:
      eq(xs, ys) && eq(xt, yt)

def att_mark_eq(a: Maybe<&2, Slash.AttMark>, b: Maybe<&2, Slash.AttMark>) -> Bool:
  match a:
    case None{}:
      Maybe.is_none(&2, Slash.AttMark, b)
    case Some{x}:
      match b:
        case None{}:
          False{}
        case Some{y}:
          att_mark_same(x, y)

# The new state keeps every record and both watermarks of the old state.
def keeps(a: Slash.KeyState, b: Slash.KeyState) -> Bool:
  match a b:
    case Slash.KeyState{abs, aas, abm, aam} Slash.KeyState{bbs, bas, bbm, bam}:
      blocks_within(abs, bbs) && atts_within(aas, bas)
        && mark_eq(abm, bbm) && att_mark_eq(aam, bam)

# A decision to sign leaves a record of the message in the state it leaves.
def signs_block_recorded(d: Slash.Decision, +ks: Slash.KeyState, +r: Slash.BlockRec) -> Bool:
  match d:
    case Slash.Reject{x}:
      True{}
    case Slash.Repeat{}:
      match ks:
        case Slash.KeyState{bs, as, bm, am}:
          has_block(r, bs)
    case Slash.Record{s}:
      match s:
        case Slash.KeyState{bs, as, bm, am}:
          has_block(r, bs)

def signs_att_recorded(d: Slash.Decision, +ks: Slash.KeyState, +r: Slash.AttRec) -> Bool:
  match d:
    case Slash.Reject{x}:
      True{}
    case Slash.Repeat{}:
      match ks:
        case Slash.KeyState{bs, as, bm, am}:
          has_att(r, as)
    case Slash.Record{s}:
      match s:
        case Slash.KeyState{bs, as, bm, am}:
          has_att(r, as)

def signs(d: Slash.Decision) -> Bool:
  match d:
    case Slash.Reject{x}:
      False{}
    case Slash.Repeat{}:
      True{}
    case Slash.Record{s}:
      True{}

def block_above_mark(+slot: S.U64, m: Maybe<&2, S.U64>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{w}:
      Bool.not(lt(slot, w))

def att_above_mark(+source: S.U64, +target: S.U64, m: Maybe<&2, Slash.AttMark>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{w}:
      match w:
        case Slash.AttMark{ms, mt}:
          Bool.not(lt(source, ms)) && Bool.not(lt(target, mt))

def block_mark(ks: Slash.KeyState) -> Maybe<&2, S.U64>:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      bm

def att_mark(ks: Slash.KeyState) -> Maybe<&2, Slash.AttMark>:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      am

# Spec: liveness
# ==============

def block_clear(+ks: Slash.KeyState, +slot: S.U64, root: S.B32) -> Bool:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      block_above_mark(slot, bm)
        && Bool.not(block_clashes_any(Slash.BlockRec{slot, Some{root}}, bs))

def att_clear(+ks: Slash.KeyState, +source: S.U64, +target: S.U64, root: S.B32) -> Bool:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      Bool.not(lt(target, source)) && att_above_mark(source, target, am)
        && Bool.not(att_clashes_any(Slash.AttRec{source, target, Some{root}}, as))
