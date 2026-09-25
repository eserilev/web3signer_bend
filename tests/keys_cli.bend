# Test CLI for src/keys.bend. tests/run_keys.py calls it.
#
#   keys_cli <key-config dir>
#
# Loads the directory. For each key, prints its public key and its
# signature of the root 0x4242...42. A key that does not load stops the
# program with an error, as it stops Bulkhead.
import Base
import ../src/ssz.bend as S
import ../src/ffi.bend as F
import ../src/keys.bend as K

def root() -> String:
  "0x4242424242424242424242424242424242424242424242424242424242424242"

def show(ls: List<&2, K.Loaded>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{l, rest}:
      match l:
        case K.Loaded{key, index}:
          do IO<Unit>:
            sig : String <- IO.try(String, F.Bls.sign_key(index, root()))
            IO.print(S.Hex.pubkey(key) ++ " " ++ sig)
            show(rest)

def first(xs: List<String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      h

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    ls : List<&2, K.Loaded> <- K.Keys.load_dir(first(args))
    show(ls)
