# Runs the laws of LAWS.bend as checks on one sequence of operations. This
# is a test, not a proof: tests/run_laws.py sends many random sequences.
#
#   laws_cli <op>...
#
#   b <slot> <root> 0            a block request
#   a <source> <target> <root>   an attestation request
#   mb <slot> 0 0                set the block watermark
#   ma <source> <target> 0       set the attestation watermark
#   ub <slot> 0 0                add a block record with an unknown root
#   ua <source> <target> 0       add an attestation record with an unknown root
#
# Each operation is four tokens; pad unused arguments with 0.
# A root is a small number n; it stands for the B32 {n, 0, 0, 0, 0, 0, 0, 0}.
# For each request, the output has one line: R (reject), P (repeat) or S
# (record), then the name of each law that failed.
import Base
import ../src/ssz.bend as S
import ../src/slashing.bend as Slash
import ../spec/safety.bend as Spec

def Args.data(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{h, Args.data(t)}

def Num(s: String) -> S.U64:
  Maybe.default(&2, S.U64, S.U64.read(s), S.U64.zero())

def Root.of(n: S.U64) -> S.B32:
  match n:
    case S.U64{h, l}:
      S.B32{l, 0, 0, 0, 0, 0, 0, 0}

def Root(s: String) -> S.B32:
  Root.of(Num(s))

def Tag(d: Slash.Decision) -> String:
  match d:
    case Slash.Reject{r}:
      "R"
    case Slash.Repeat{}:
      "P"
    case Slash.Record{s}:
      "S"

def Implies(a: Bool, b: Bool) -> Bool:
  Bool.or(Bool.not(a), b)

def Flag(ok: Bool, name: String) -> String:
  match ok:
    case True{}:
      ""
    case False{}:
      " FAIL:" ++ name

def Check.block(+ks: Slash.KeyState, +slot: S.U64, +root: S.B32) -> String:
  +d = Slash.Block.decide(ks, slot, root)
  +after = Slash.KeyState.after(ks, d)
  Tag(d)
    ++ Flag(Implies(Spec.safe(ks), Spec.safe(after)), "block_keeps_safe")
    ++ Flag(Spec.signs_block_recorded(d, ks, Slash.BlockRec{slot, Some{root}}), "block_recorded")
    ++ Flag(Spec.keeps(ks, after), "block_keeps_records")
    ++ Flag(Implies(Spec.signs(d), Spec.block_above_mark(slot, Spec.block_mark(ks))), "block_respects_mark")
    ++ Flag(Implies(Spec.block_clear(ks, slot, root), Spec.signs(d)), "block_signs_when_clear")

def Check.att(+ks: Slash.KeyState, +source: S.U64, +target: S.U64, +root: S.B32) -> String:
  +d = Slash.Att.decide(ks, source, target, root)
  +after = Slash.KeyState.after(ks, d)
  Tag(d)
    ++ Flag(Implies(Spec.safe(ks), Spec.safe(after)), "att_keeps_safe")
    ++ Flag(Spec.signs_att_recorded(d, ks, Slash.AttRec{source, target, Some{root}}), "att_recorded")
    ++ Flag(Spec.keeps(ks, after), "att_keeps_records")
    ++ Flag(Implies(Spec.signs(d), Spec.att_above_mark(source, target, Spec.att_mark(ks))), "att_respects_mark")
    ++ Flag(Implies(Spec.att_clear(ks, source, target, root), Spec.signs(d)), "att_signs_when_clear")

def Step.block(+ks: Slash.KeyState, +slot: S.U64, +root: S.B32) -> Slash.KeyState:
  Slash.KeyState.after(ks, Slash.Block.decide(ks, slot, root))

def Step.att(+ks: Slash.KeyState, +source: S.U64, +target: S.U64, +root: S.B32) -> Slash.KeyState:
  Slash.KeyState.after(ks, Slash.Att.decide(ks, source, target, root))

def Set.block_mark(ks: Slash.KeyState, m: S.U64) -> Slash.KeyState:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      Slash.KeyState{bs, as, Some{m}, am}

def Set.att_mark(ks: Slash.KeyState, s: S.U64, t: S.U64) -> Slash.KeyState:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      Slash.KeyState{bs, as, bm, Some{Slash.AttMark{s, t}}}

def Add.block(ks: Slash.KeyState, slot: S.U64) -> Slash.KeyState:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      Slash.KeyState{Con{Slash.BlockRec{slot, None{}}, bs}, as, bm, am}

def Add.att(ks: Slash.KeyState, s: S.U64, t: S.U64) -> Slash.KeyState:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      Slash.KeyState{bs, Con{Slash.AttRec{s, t, None{}}, as}, bm, am}

def Is(+s: String, name: String) -> Bool:
  String.eq(s, name)

def Apply.state(+ks: Slash.KeyState, +k: String, +x: String, +y: String, +z: String) -> Slash.KeyState:
  Bool.pick(Slash.KeyState, Is(k, "b"), Step.block(ks, Num(x), Root(y)),
  Bool.pick(Slash.KeyState, Is(k, "a"), Step.att(ks, Num(x), Num(y), Root(z)),
  Bool.pick(Slash.KeyState, Is(k, "mb"), Set.block_mark(ks, Num(x)),
  Bool.pick(Slash.KeyState, Is(k, "ma"), Set.att_mark(ks, Num(x), Num(y)),
  Bool.pick(Slash.KeyState, Is(k, "ub"), Add.block(ks, Num(x)),
  Bool.pick(Slash.KeyState, Is(k, "ua"), Add.att(ks, Num(x), Num(y)),
  ks))))))

def Apply.out(+ks: Slash.KeyState, +k: String, +x: String, +y: String, +z: String) -> String:
  Bool.pick(String, Is(k, "b"), Check.block(ks, Num(x), Root(y)) ++ "\n",
  Bool.pick(String, Is(k, "a"), Check.att(ks, Num(x), Num(y), Root(z)) ++ "\n",
  ""))

# Each operation is exactly four tokens: the kind, then three arguments.
# Unused arguments are 0.
def Run(xs: List<&2, String>, +ks: Slash.KeyState, out: String) -> String:
  match xs:
    case Nil{}:
      out
    case Con{+k, t1}:
      match t1:
        case Nil{}:
          out ++ "BAD OP\n"
        case Con{+x, t2}:
          match t2:
            case Nil{}:
              out ++ "BAD OP\n"
            case Con{+y, t3}:
              match t3:
                case Nil{}:
                  out ++ "BAD OP\n"
                case Con{+z, rest}:
                  Run(rest, Apply.state(ks, k, x, y, z), out ++ Apply.out(ks, k, x, y, z))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    IO.write(Run(Args.data(args), Slash.KeyState.empty(), ""))
