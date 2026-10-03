# Definitions for the import laws of web3signer_bend (L7, L8). DRAFT for
# review: the owner of LAWS.bend owns this file too, and the code does not
# edit it.
import Base
import ../src/ssz.bend as S
import ../src/slashing.bend as Slash
import ./safety.bend as Spec

# A watermark that exists still exists, and it is not lower.
def mark_up(a: Maybe<&2, S.U64>, b: Maybe<&2, S.U64>) -> Bool:
  match a:
    case None{}:
      True{}
    case Some{x}:
      match b:
        case None{}:
          False{}
        case Some{y}:
          Bool.not(S.U64.is_lt(y, x))

def att_mark_ge(x: Slash.AttMark, y: Slash.AttMark) -> Bool:
  match x y:
    case Slash.AttMark{xs, xt} Slash.AttMark{ys, yt}:
      Bool.not(S.U64.is_lt(ys, xs)) && Bool.not(S.U64.is_lt(yt, xt))

def att_mark_up(a: Maybe<&2, Slash.AttMark>, b: Maybe<&2, Slash.AttMark>) -> Bool:
  match a:
    case None{}:
      True{}
    case Some{x}:
      match b:
        case None{}:
          False{}
        case Some{y}:
          att_mark_ge(x, y)

# The new state b keeps every record of the old state a, and no watermark of
# a is lower in b.
def keeps_up(a: Slash.KeyState, b: Slash.KeyState) -> Bool:
  match a b:
    case Slash.KeyState{abs, aas, abm, aam} Slash.KeyState{bbs, bas, bbm, bam}:
      Spec.blocks_within(abs, bbs) && Spec.atts_within(aas, bas)
        && mark_up(abm, bbm) && att_mark_up(aam, bam)
