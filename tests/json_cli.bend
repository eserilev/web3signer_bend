# Test CLI for src/json.bend. tests/run_json.py calls it once for each case.
#
#   json_cli parse <text>        prints the value as compact JSON, or ERR
#   json_cli get <text> <key>    prints the value of key, or ERR
import Base
import ../src/json.bend as J

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

def Out(m: Maybe<&2, J.Json>) -> String:
  match m:
    case None{}:
      "ERR"
    case Some{j}:
      J.Json.show(j)

def Get(+xs: List<&2, String>) -> Maybe<&2, J.Json>:
  do Maybe<&2, J.Json>:
    j : J.Json <- J.Json.parse(Args.nth(xs, 1n))
    J.Json.get(j, Args.nth(xs, 2n))

def Run(+cmd: String, +xs: List<&2, String>) -> String:
  Bool.pick(String, String.eq(cmd, "parse"), Out(J.Json.parse(Args.nth(xs, 1n))),
  Bool.pick(String, String.eq(cmd, "get"), Out(Get(xs)),
  "BAD COMMAND"))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +xs : List<&2, String> = Args.data(args)
    IO.print(Run(Args.nth(xs, 0n), xs))
