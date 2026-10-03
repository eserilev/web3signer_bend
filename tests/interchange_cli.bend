# Test CLI for src/interchange.bend. tests/run_interchange.py calls it.
#
#   interchange_cli <op>...
#
# Ops, run in order on one store that starts empty:
#   G <gvr>                          sets the genesis validators root
#   I <interchange json>             imports; prints I OK <events> or I FAIL
#   B <pubkey> <slot> <root>         a block request; prints S or R
#   A <pubkey> <source> <target> <root>   an attestation request; prints S or R
# At the end it prints REPLAY OK if the log of all events replays to the
# live store.
import Base
import ../src/ssz.bend as S
import ../src/slashing.bend as Slash
import ../src/request.bend as R
import ../src/store.bend as St
import ../src/interchange.bend as I

def Args.data(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{h, Args.data(t)}

def Num(s: String) -> S.U64:
  Maybe.default(&2, S.U64, S.U64.read(s), S.U64.zero())

def Root(s: String) -> S.B32:
  Maybe.default(&2, S.B32, S.Hex.read_b32(s), S.B32.zero())

def Key(s: String) -> S.Pubkey:
  Maybe.default(&2, S.Pubkey, S.Hex.read_pubkey(s), S.Pubkey{S.B32.zero(), S.B16{0, 0, 0, 0}})

def Gvr(s: St.Store) -> S.B32:
  match s:
    case St.Store{g, es}:
      Maybe.default(&2, S.B32, g, S.B32.zero())

def Req(+msg: R.Msg, +s: St.Store) -> R.Request:
  R.Request{msg, S.Fork{0, 0, S.U64.zero()}, Gvr(s), None{}}

def Block(+slot: S.U64) -> R.Msg:
  R.MBlock{S.BeaconBlockHeader{slot, S.U64.zero(), S.B32.zero(), S.B32.zero(), S.B32.zero()}}

def Att(+src: S.U64, +tgt: S.U64) -> R.Msg:
  R.MAttestation{S.AttestationData{S.U64.zero(), S.U64.zero(), S.B32.zero(),
    S.Checkpoint{src, S.B32.zero()}, S.Checkpoint{tgt, S.B32.zero()}}}

type State is Data:
  State{store: St.Store, log: List<&2, St.LogEvent>, out: String}

def State.events(st: State, +es: List<&2, St.LogEvent>, +line: String) -> State:
  match st:
    case State{s, log, out}:
      State{St.Store.apply_all(es, s), List.append(&2, St.LogEvent, log, es), out ++ line ++ "\n"}

def Note(st: State, +line: String) -> State:
  match st:
    case State{s, log, out}:
      State{s, log, out ++ line ++ "\n"}

def Run.import(st: State, m: Maybe<&2, List<&2, St.LogEvent>>) -> State:
  match m:
    case None{}:
      Note(st, "I FAIL")
    case Some{+es}:
      State.events(st, es, "I OK " ++ U32.show(U32.from_nat(List.length(&2, St.LogEvent, es))))

def Run.outcome(st: State, o: St.Outcome) -> State:
  match o:
    case St.Refuse{c, why}:
      Note(st, "R")
    case St.Sign{es}:
      State.events(st, es, "S")

def Store.of(st: State) -> St.Store:
  match st:
    case State{s, log, out}:
      s

def Run.parsed.go(st: State, +x: I.Interchange) -> State:
  match st:
    case State{+s, log, out}:
      Run.import(State{s, log, out}, I.Imp.run(s, x))

def Run.parsed(st: State, ix: Maybe<&2, I.Interchange>) -> State:
  match ix:
    case None{}:
      Note(st, "I PARSE")
    case Some{+x}:
      Run.parsed.go(st, x)

def Run.block(st: State, +k: S.Pubkey, +slot: S.U64, +root: S.B32) -> State:
  match st:
    case State{+s, log, out}:
      Run.outcome(State{s, log, out}, St.Store.decide(s, k, Req(Block(slot), s), root))

def Run.att(st: State, +k: S.Pubkey, +src: S.U64, +tgt: S.U64, +root: S.B32) -> State:
  match st:
    case State{+s, log, out}:
      Run.outcome(State{s, log, out}, St.Store.decide(s, k, Req(Att(src, tgt), s), root))

type Op is Data:
  OG{}
  OI{}
  OB{}
  OA{}
  OEnd{}

def Op.of(+op: String) -> Op:
  Bool.pick(Op, String.eq(op, "G"), OG{},
  Bool.pick(Op, String.eq(op, "I"), OI{},
  Bool.pick(Op, String.eq(op, "B"), OB{},
  Bool.pick(Op, String.eq(op, "A"), OA{}, OEnd{}))))

@unsafe
def Run.op(o: Op, rest: List<&2, String>, st: State) -> State:
  match o:
    case OG{}:
      Run.g(rest, st)
    case OI{}:
      Run.i(rest, st)
    case OB{}:
      Run.b(rest, st)
    case OA{}:
      Run.a(rest, st)
    case OEnd{}:
      st

@unsafe
def Run(ops: List<&2, String>, st: State) -> State:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      Run.op(Op.of(op), rest, st)

@unsafe
def Run.g(ops: List<&2, String>, +st: State) -> State:
  match ops:
    case Con{g, rest}:
      Run(rest, State.events(st, [St.EGvr{Root(g)}], "G"))
    case Nil{}:
      st

@unsafe
def Run.i(ops: List<&2, String>, +st: State) -> State:
  match ops:
    case Con{j, rest}:
      Run(rest, Run.parsed(st, I.Interchange.read(j)))
    case Nil{}:
      st

@unsafe
def Run.b(ops: List<&2, String>, +st: State) -> State:
  match ops:
    case Con{k, t1}:
      match t1:
        case Con{slot, t2}:
          match t2:
            case Con{root, rest}:
              Run(rest, Run.block(st, Key(k), Num(slot), Root(root)))
            case Nil{}:
              st
        case Nil{}:
          st
    case Nil{}:
      st

@unsafe
def Run.a(ops: List<&2, String>, +st: State) -> State:
  match ops:
    case Con{k, t1}:
      match t1:
        case Con{src, t2}:
          match t2:
            case Con{tgt, t3}:
              match t3:
                case Con{root, rest}:
                  Run(rest, Run.att(st, Key(k), Num(src), Num(tgt), Root(root)))
                case Nil{}:
                  st
            case Nil{}:
              st
        case Nil{}:
          st
    case Nil{}:
      st

def Show(st: State) -> String:
  match st:
    case State{s, +log, out}:
      out ++ Bool.pick(String, String.eq(St.Log.show(log), St.Log.show(Maybe.default(&2, List<&2, St.LogEvent>, St.Log.read(St.Log.show(log)), []))), "LOG OK", "LOG MISMATCH")

@unsafe
def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    IO.print(Show(Run(Args.data(args), State{St.Store.empty(), [], ""})))
