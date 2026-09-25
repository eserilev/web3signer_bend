# Phase 0 spike: sign one root with blst through a foreign effect.
#
#   ./build.sh && ../../build/phase0/sign <secret_key_hex> <signing_root_hex>
import Base

def Bls.sign(sk: String, root: String) -> IO(Result<&1, &1, U32 & String, String>):
  import "./bls.c"

def usage() -> IO(Unit):
  IO.die(Unit, 2, "usage: sign <secret_key_hex> <signing_root_hex>")

def sign_args(args: List<String>) -> IO(Unit):
  match args:
    case Con{sk, rest}:
      match rest:
        case Con{root, more}:
          do IO<Unit>:
            sig : String <- IO.try(String, Bls.sign(sk, root))
            IO.print(sig)
        case Nil{}:
          usage()
    case Nil{}:
      usage()

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    sign_args(args)
