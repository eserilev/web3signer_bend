# Test CLI for src/store.bend. tests/run_store.py calls it.
#
#   store_cli run <op>...     runs requests, then replays the log
#   store_cli event <line>    prints show(read(line)), or ERR
#   store_cli log <text>      prints the number of events in a log text, or ERR
#
# run: each operation is six tokens, the kind and five numbers:
#   a <key> <gvr> <source> <target> <root>   an attestation request
#   b <key> <gvr> <slot> <root> 0            a block request
#   r <key> <gvr> <epoch> 0 0                a randao request
# A key, gvr or root is a small number n; it stands for a value with n in its
# first word. For each request, run prints S (sign) or R <status> <reason>.
# Then it prints the log, then REPLAY OK if the replayed state equals the
# live state, or REPLAY MISMATCH and both states.
import Base
import ../src/ssz.bend as S
import ../src/slashing.bend as Slash
import ../src/request.bend as R
import ../src/store.bend as St

def Args.data(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{h, Args.data(t)}

def Num(s: String) -> S.U64:
  Maybe.default(&2, S.U64, S.U64.read(s), S.U64.zero())

def Word.of(n: S.U64) -> U32:
  match n:
    case S.U64{h, l}:
      l

def B32.of(s: String) -> S.B32:
  S.B32{Word.of(Num(s)), 0, 0, 0, 0, 0, 0, 0}

def Key.of(s: String) -> S.Pubkey:
  S.Pubkey{B32.of(s), S.B16{0, 0, 0, 0}}

def Fork() -> S.Fork:
  S.Fork{0, 0, S.U64.zero()}

def Req(msg: R.Msg, gvr: String) -> R.Request:
  R.Request{msg, Fork(), B32.of(gvr), None{}}

def Msg.of(+k: String, +x: String, +y: String, +z: String) -> R.Msg:
  Bool.pick(R.Msg, String.eq(k, "a"),
    R.MAttestation{S.AttestationData{S.U64.zero(), S.U64.zero(), S.B32.zero(),
      S.Checkpoint{Num(x), S.B32.zero()}, S.Checkpoint{Num(y), S.B32.zero()}}},
  Bool.pick(R.Msg, String.eq(k, "b"),
    R.MBlock{S.BeaconBlockHeader{Num(x), S.U64.zero(), S.B32.zero(), S.B32.zero(), S.B32.zero()}},
    R.MRandao{Num(x)}))

# The root of the request: the last number for attestations, the one after
# the slot for blocks.
def Root.of(+k: String, +y: String, +z: String) -> S.B32:
  Bool.pick(S.B32, String.eq(k, "a"), B32.of(z), B32.of(y))

def Show.outcome(o: St.Outcome) -> String:
  match o:
    case St.Refuse{c, why}:
      "R " ++ U32.show(c) ++ " " ++ why
    case St.Sign{es}:
      "S"

def Show.events(o: St.Outcome) -> String:
  match o:
    case St.Refuse{c, why}:
      ""
    case St.Sign{es}:
      St.Log.show(es)

def Show.root(r: Maybe<&2, S.B32>) -> String:
  match r:
    case None{}:
      "-"
    case Some{x}:
      S.Hex.b32(x)

def Show.blocks(xs: List<&2, Slash.BlockRec>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      match x:
        case Slash.BlockRec{s, r}:
          S.U64.show(s) ++ ":" ++ Show.root(r) ++ " " ++ Show.blocks(t)

def Show.atts(xs: List<&2, Slash.AttRec>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      match x:
        case Slash.AttRec{s, u, r}:
          S.U64.show(s) ++ ":" ++ S.U64.show(u) ++ ":" ++ Show.root(r) ++ " " ++ Show.atts(t)

def Show.mark(m: Maybe<&2, S.U64>) -> String:
  match m:
    case None{}:
      "-"
    case Some{x}:
      S.U64.show(x)

def Show.att_mark(m: Maybe<&2, Slash.AttMark>) -> String:
  match m:
    case None{}:
      "-"
    case Some{x}:
      match x:
        case Slash.AttMark{s, t}:
          S.U64.show(s) ++ ":" ++ S.U64.show(t)

def Show.entries(es: List<&2, St.Entry>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{e, t}:
      match e:
        case St.Entry{k, ks}:
          match ks:
            case Slash.KeyState{bs, as, bm, am}:
              S.Hex.pubkey(k) ++ " blocks[" ++ Show.blocks(bs) ++ "] atts[" ++ Show.atts(as)
                ++ "] marks " ++ Show.mark(bm) ++ " " ++ Show.att_mark(am) ++ "\n" ++ Show.entries(t)

def Show.store(s: St.Store) -> String:
  match s:
    case St.Store{g, es}:
      "gvr " ++ Show.root(g) ++ "\n" ++ Show.entries(es)

def Replay.same(+live: String, +again: String) -> String:
  Bool.pick(String, String.eq(live, again), "REPLAY OK\n",
    "REPLAY MISMATCH\nlive:\n" ++ live ++ "replayed:\n" ++ again)

def Replay.check(+live: String, replayed: Maybe<&2, List<&2, St.LogEvent>>) -> String:
  match replayed:
    case None{}:
      "REPLAY MISMATCH: the log does not parse\n"
    case Some{es}:
      Replay.same(live, Show.store(St.Store.replay(es)))

def Run.finish(+s: St.Store, out: String, +log: String) -> String:
  out ++ "LOG\n" ++ log ++ Replay.check(Show.store(s), St.Log.read(log))

# out holds the report lines; log holds the log text.
def Run(xs: List<&2, String>, +s: St.Store, out: String, +log: String) -> String:
  match xs:
    case Nil{}:
      Run.finish(s, out, log)
    case Con{+k, x1}:
      match x1:
        case Nil{}:
          Run.finish(s, out, log)
        case Con{+key, x2}:
          match x2:
            case Nil{}:
              Run.finish(s, out, log)
            case Con{+gvr, x3}:
              match x3:
                case Nil{}:
                  Run.finish(s, out, log)
                case Con{+x, x4}:
                  match x4:
                    case Nil{}:
                      Run.finish(s, out, log)
                    case Con{+y, x5}:
                      match x5:
                        case Nil{}:
                          Run.finish(s, out, log)
                        case Con{+z, rest}:
                          +o = St.Store.decide(s, Key.of(key), Req(Msg.of(k, x, y, z), gvr), Root.of(k, y, z))
                          Run(rest, St.Store.after(s, o), out ++ Show.outcome(o) ++ "\n", log ++ Show.events(o))

def Is(+s: String, name: String) -> Bool:
  String.eq(s, name)

def Nth(xs: List<&2, String>, n: Nat) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      match n:
        case 0n:
          h
        case 1n+p:
          Nth(t, p)

def Event.cmd(m: Maybe<&2, St.LogEvent>) -> String:
  match m:
    case None{}:
      "ERR"
    case Some{e}:
      St.LogEvent.show(e)

def Log.cmd(m: Maybe<&2, List<&2, St.LogEvent>>) -> String:
  match m:
    case None{}:
      "ERR"
    case Some{es}:
      Nat.show(List.length(&2, St.LogEvent, es))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +xs : List<&2, String> = Args.data(args)
    +cmd : String = Nth(xs, 0n)
    IO.write(
      Bool.pick(String, Is(cmd, "run"), Run(List.drop(&2, String, xs, 1n), St.Store.empty(), "", ""),
      Bool.pick(String, Is(cmd, "event"), Event.cmd(St.LogEvent.read(Nth(xs, 1n))) ++ "\n",
      Bool.pick(String, Is(cmd, "log"), Log.cmd(St.Log.read(Nth(xs, 1n))) ++ "\n",
      "BAD COMMAND\n"))))
