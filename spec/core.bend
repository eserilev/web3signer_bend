# Definitions for the core laws of web3signer_bend (L10). DRAFT for review:
# the owner of LAWS.bend owns this file too, and the code does not edit it.
import Base
import ../src/core.bend as Co

def is_reply(p: Co.Plan) -> Bool:
  match p:
    case Co.PRefuse{c, why}:
      True{}
    case Co.PGrant{}:
      True{}
    case Co.PWrite{es, n}:
      False{}

# A plan writes at most once, and only before its reply: so a grant, after
# which a signature goes out, never comes before the write.
def write_first(p: Co.Plan) -> Bool:
  match p:
    case Co.PRefuse{c, why}:
      True{}
    case Co.PGrant{}:
      True{}
    case Co.PWrite{es, n}:
      is_reply(n)
