# Definitions for the signing-root laws of Bulkhead. DRAFT for review: the
# owner of LAWS.bend owns this file too, and the code does not edit it.
import Base
import ../src/ssz.bend as S
import ../src/request.bend as R

# The body claims a root that is not root.
def claims_other(r: R.Request, +root: S.B32) -> Bool:
  match r:
    case R.Request{msg, fork, gvr, claimed}:
      match claimed:
        case None{}:
          False{}
        case Some{c}:
          Bool.not(S.B32.is_eq(c, root))

# A check result that gives a root gives exactly root.
def gives_only(res: Result<&2, &2, String, S.B32>, root: S.B32) -> Bool:
  match res:
    case Fail{e}:
      True{}
    case Done{x}:
      S.B32.is_eq(x, root)

def fails(res: Result<&2, &2, String, S.B32>) -> Bool:
  match res:
    case Fail{e}:
      True{}
    case Done{x}:
      False{}
