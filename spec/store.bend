# Definitions for the store laws of Bulkhead. DRAFT for review: the owner of
# LAWS.bend owns this file too, and the code does not edit it.
import Base
import ../src/ssz.bend as S
import ../src/slashing.bend as Slash
import ../src/request.bend as R
import ../src/store.bend as St

# The state of one key in the store.
def key_state(s: St.Store, +key: S.Pubkey) -> Slash.KeyState:
  match s:
    case St.Store{g, es}:
      St.Store.get(es, key)

# The request passes the genesis validators root check: the database has no
# root yet, or it has the same root.
def gvr_ok(s: St.Store, +g: S.B32) -> Bool:
  match s:
    case St.Store{have, es}:
      match have:
        case None{}:
          True{}
        case Some{x}:
          S.B32.is_eq(g, x)

def source(d: S.AttestationData) -> S.U64:
  match d:
    case S.AttestationData{slot, index, bbr, src, tgt}:
      match src:
        case S.Checkpoint{e, r}:
          e

def target(d: S.AttestationData) -> S.U64:
  match d:
    case S.AttestationData{slot, index, bbr, src, tgt}:
      match tgt:
        case S.Checkpoint{e, r}:
          e

def slot(h: S.BeaconBlockHeader) -> S.U64:
  match h:
    case S.BeaconBlockHeader{s, pi, pr, sr, br}:
      s

# The store after the decision for request r on key.
def after(+s: St.Store, +key: S.Pubkey, r: R.Request, +root: S.B32) -> St.Store:
  St.Store.after(s, St.Store.decide(s, key, r, root))
