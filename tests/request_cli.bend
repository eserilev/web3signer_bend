# Test CLI for src/request.bend. tests/run_requests.py calls it once for
# each body.
#
#   request_cli <body> [<network config>]
#
# Prints "OK <type> <signing root>" or "ERR <cause>". The network config is
# a JSON object of config.yaml strings. Without it, the network is mainnet.
import Base
import ../src/ssz.bend as S
import ../src/request.bend as R
import ../src/json.bend as J

def Out.root(name: String, r: Result<&2, &2, String, S.B32>) -> String:
  match r:
    case Fail{e}:
      "ERR " ++ e
    case Done{root}:
      "OK " ++ name ++ " " ++ S.Hex.b32(root)

def Out(r: Result<&2, &2, String, R.Request>, log_spe: Nat) -> String:
  match r:
    case Fail{e}:
      "ERR " ++ e
    case Done{+req}:
      match req:
        case R.Request{+msg, fork, gvr, claimed}:
          Out.root(R.Msg.name(msg), R.Request.check(R.Request{msg, fork, gvr, claimed}, log_spe))

def Args.data(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{h, Args.data(t)}

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

def Net.of(m: Maybe<&2, J.Json>) -> Result<&2, &2, String, R.Net>:
  match m:
    case None{}:
      Fail{"invalid network config JSON"}
    case Some{+o}:
      R.Net.read(o)

def Net.arg(s: String) -> Result<&2, &2, String, R.Net>:
  match s:
    case SNil{}:
      Done{R.Net.mainnet()}
    case SCon{c, t}:
      Net.of(J.Json.parse(SCon{c, t}))

def Run(n: Result<&2, &2, String, R.Net>, body: String) -> String:
  match n:
    case Fail{e}:
      "CONFIG " ++ e
    case Done{+net}:
      Out(R.Request.decode(body, net), R.Net.log_spe(net))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +xs : List<&2, String> = Args.data(args)
    IO.print(Run(Net.arg(Nth(xs, 1n)), Nth(xs, 0n)))
