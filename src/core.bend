# The pure step of the core task (main.bend): what it does for one request.
#
# A plan is a refusal, a grant, or a log write followed by the rest of the
# plan. main.bend runs a plan in order: a write is an append with fsync, and
# a grant answers Go, after which the connection task signs. The state after
# the step is the written events applied to the state before it, so the
# state in memory is always the replay of the log. LAWS.bend states L10 on
# Core.plan and Core.next.
import Base
import ./ssz.bend as S
import ./request.bend as R
import ./store.bend as St

type Plan is Data:
  PRefuse{status: U32, reason: String}
  PGrant{}
  PWrite{events: List<&2, St.LogEvent>, next: Plan}

def Plan.sign(es: List<&2, St.LogEvent>) -> Plan:
  match es:
    case Nil{}:
      PGrant{}
    case Con{e, rest}:
      PWrite{Con{e, rest}, PGrant{}}

def Plan.of(o: St.Outcome) -> Plan:
  match o:
    case St.Refuse{c, why}:
      PRefuse{c, why}
    case St.Sign{es}:
      Plan.sign(es)

# The events that a plan writes, in order.
def Plan.writes(p: Plan) -> List<&2, St.LogEvent>:
  match p:
    case PRefuse{c, why}:
      []
    case PGrant{}:
      []
    case PWrite{es, n}:
      List.append(&2, St.LogEvent, es, Plan.writes(n))

def Core.plan(+s: St.Store, +key: S.Pubkey, r: R.Request, +root: S.B32) -> Plan:
  Plan.of(St.Store.decide(s, key, r, root))

# The state after the request, by the decision rules of src/store.bend.
def Core.next(+s: St.Store, +key: S.Pubkey, r: R.Request, +root: S.B32) -> St.Store:
  St.Store.after(s, St.Store.decide(s, key, r, root))
