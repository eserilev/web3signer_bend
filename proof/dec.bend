# Lemmas for the decimal law u64_show_read. show doubles a digit list once
# for each bit, and read halves it once for each bit. Both sides are
# measured with G, the value of the bits after a start value v, so no
# statement holds a large constant.
import Base
import ../src/ssz.bend as S
import ./lemmas.bend as Lm
import ./num.bend as N

# The value of v followed by the n bits of w, high bit first.
def G(n: Nat, +v: Nat, w: Word(n)) -> Nat:
  match n:
    case 0n:
      v
    case 1n+p:
      match w:
        case WCon{b, t}:
          Nat.add(S.Dec.bit(b), Nat.double(G(p, v, t)))

def V(ds: List<&2, Nat>) -> Nat:
  S.Dec.val(ds)

# Each digit is below 10.
def Digits(ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, r}:
      Nat.is_lt(d, 10n) && Digits(r)

# Nat
# ===

def Add.shuffle(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), N.Add.assoc(a, b, Nat.add(c, d))) : {_ == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), N.Add.assoc(a, c, Nat.add(b, d))) : {Nat.add(a, Nat.add(b, Nat.add(c, d))) == _ : Nat}
  %Equal.sym(Nat, Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), N.Add.swap(b, c, d)) : {Nat.add(a, _) == Nat.add(a, Nat.add(c, Nat.add(b, d))) : Nat}
  {==}

def Mul.add_r(k: Nat, +a: Nat, +b: Nat) -> {Nat.mul(k, Nat.add(a, b)) == Nat.add(Nat.mul(k, a), Nat.mul(k, b)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      +q = p
      %Equal.sym(Nat, Nat.mul(q, Nat.add(a, b)), Nat.add(Nat.mul(q, a), Nat.mul(q, b)), Mul.add_r(q, a, b)) : {Nat.add(Nat.add(a, b), _) == Nat.add(Nat.add(a, Nat.mul(q, a)), Nat.add(b, Nat.mul(q, b))) : Nat}
      Add.shuffle(a, b, Nat.mul(q, a), Nat.mul(q, b))

def Dbl.add_d(+a: Nat, +b: Nat) -> {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}:
  %N.Dbl.add(Nat.add(a, b)) : {_ == Nat.add(Nat.double(a), Nat.double(b)) : Nat}
  %N.Dbl.add(a) : {Nat.add(Nat.add(a, b), Nat.add(a, b)) == Nat.add(_, Nat.double(b)) : Nat}
  %N.Dbl.add(b) : {Nat.add(Nat.add(a, b), Nat.add(a, b)) == Nat.add(Nat.add(a, a), _) : Nat}
  Add.shuffle(a, b, a, b)

def Mul.dbl_r(+k: Nat, +v: Nat) -> {Nat.mul(k, Nat.double(v)) == Nat.double(Nat.mul(k, v)) : Nat}:
  %N.Dbl.add(v) : {Nat.mul(k, _) == Nat.double(Nat.mul(k, v)) : Nat}
  %N.Dbl.add(Nat.mul(k, v)) : {Nat.mul(k, Nat.add(v, v)) == _ : Nat}
  Mul.add_r(k, v, v)

def Le.sub_add(k: Nat, x: Nat, h: {Nat.is_le(k, x) == True{} : Bool}) -> {Nat.add(Nat.sub(x, k), k) == x : Nat}:
  match k x:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      N.Add.zero_r(1n+q)
    case 1n+p 0n:
      Empty.absurd({Nat.add(Nat.sub(0n, 1n+p), 1n+p) == 0n : Nat}, Lm.Bool.ft(h))
    case 1n+p0 1n+q0:
      +p = p0
      +q = q0
      %Equal.sym(Nat, Nat.add(Nat.sub(q, p), 1n+p), 1n+Nat.add(Nat.sub(q, p), p), N.Add.succ_r(Nat.sub(q, p), p)) : {_ == 1n+q : Nat}
      Equal.cong(Nat, Nat, y => 1n+y, Nat.add(Nat.sub(q, p), p), q, Le.sub_add(p, q, h))

# A digit sum x splits into its low digit and a carry of 10.
def Dig.split.go(b: Bool, +x: Nat, e: {Nat.is_le(10n, x) == b : Bool})
  -> {Nat.add(S.Dec.lo.go(b, x), Nat.mul(10n, S.Dec.bit(b))) == x : Nat}:
  match b:
    case True{}:
      Le.sub_add(10n, x, e)
    case False{}:
      N.Add.zero_r(x)

def Dig.split(+x: Nat) -> {Nat.add(S.Dec.lo(x), Nat.mul(10n, S.Dec.bit(S.Dec.hi(x)))) == x : Nat}:
  Dig.split.go(Nat.is_le(10n, x), x, {==})

def Lt.none(k: Nat, h: {Nat.is_lt(k, 0n) == True{} : Bool}) -> {False{} == True{} : Bool}:
  match k:
    case 0n:
      h
    case 1n+p:
      h

def Dig.rt(d: Nat, h: {Nat.is_lt(d, 10n) == True{} : Bool}) -> {S.Dec.digit(S.Dec.char(d)) == Some{d} : Maybe<&2, Nat>}:
  match d:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+k:
      Empty.absurd({S.Dec.digit(S.Dec.char(1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+k)) == Some{1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+k} : Maybe<&2, Nat>}, Lm.Bool.ft(Lt.none(k, h)))

def Dig.lo_lt(c: Bool, d: Nat, h: {Nat.is_lt(d, 10n) == True{} : Bool}) -> {Nat.is_lt(S.Dec.lo(Nat.add(S.Dec.bit(c), Nat.double(d))), 10n) == True{} : Bool}:
  match c d:
    case True{} 0n:
      {==}
    case True{} 1n:
      {==}
    case True{} 2n:
      {==}
    case True{} 3n:
      {==}
    case True{} 4n:
      {==}
    case True{} 5n:
      {==}
    case True{} 6n:
      {==}
    case True{} 7n:
      {==}
    case True{} 8n:
      {==}
    case True{} 9n:
      {==}
    case True{} 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+k:
      Empty.absurd({Nat.is_lt(S.Dec.lo(Nat.add(S.Dec.bit(True{}), Nat.double(1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+k))), 10n) == True{} : Bool}, Lm.Bool.ft(Lt.none(k, h)))
    case False{} 0n:
      {==}
    case False{} 1n:
      {==}
    case False{} 2n:
      {==}
    case False{} 3n:
      {==}
    case False{} 4n:
      {==}
    case False{} 5n:
      {==}
    case False{} 6n:
      {==}
    case False{} 7n:
      {==}
    case False{} 8n:
      {==}
    case False{} 9n:
      {==}
    case False{} 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+k:
      Empty.absurd({Nat.is_lt(S.Dec.lo(Nat.add(S.Dec.bit(False{}), Nat.double(1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+k))), 10n) == True{} : Bool}, Lm.Bool.ft(Lt.none(k, h)))

# Doubling
# ========

def Dbl.val(ds: List<&2, Nat>, +c: Bool) -> {V(S.Dec.dbl(ds, c)) == Nat.add(S.Dec.bit(c), Nat.double(V(ds))) : Nat}:
  match ds:
    case Nil{}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{+d, +r}:
      +x = Nat.add(S.Dec.bit(c), Nat.double(d))
      %Equal.sym(Nat, V(S.Dec.dbl(r, S.Dec.hi(x))), Nat.add(S.Dec.bit(S.Dec.hi(x)), Nat.double(V(r))), Dbl.val(r, S.Dec.hi(x))) : {Nat.add(S.Dec.lo(x), Nat.mul(10n, _)) == Nat.add(S.Dec.bit(c), Nat.double(Nat.add(d, Nat.mul(10n, V(r))))) : Nat}
      %Equal.sym(Nat, Nat.mul(10n, Nat.add(S.Dec.bit(S.Dec.hi(x)), Nat.double(V(r)))), Nat.add(Nat.mul(10n, S.Dec.bit(S.Dec.hi(x))), Nat.mul(10n, Nat.double(V(r)))), Mul.add_r(10n, S.Dec.bit(S.Dec.hi(x)), Nat.double(V(r)))) : {Nat.add(S.Dec.lo(x), _) == Nat.add(S.Dec.bit(c), Nat.double(Nat.add(d, Nat.mul(10n, V(r))))) : Nat}
      %N.Add.assoc(S.Dec.lo(x), Nat.mul(10n, S.Dec.bit(S.Dec.hi(x))), Nat.mul(10n, Nat.double(V(r)))) : {_ == Nat.add(S.Dec.bit(c), Nat.double(Nat.add(d, Nat.mul(10n, V(r))))) : Nat}
      %Equal.sym(Nat, Nat.add(S.Dec.lo(x), Nat.mul(10n, S.Dec.bit(S.Dec.hi(x)))), x, Dig.split(x)) : {Nat.add(_, Nat.mul(10n, Nat.double(V(r)))) == Nat.add(S.Dec.bit(c), Nat.double(Nat.add(d, Nat.mul(10n, V(r))))) : Nat}
      %Equal.sym(Nat, Nat.double(Nat.add(d, Nat.mul(10n, V(r)))), Nat.add(Nat.double(d), Nat.double(Nat.mul(10n, V(r)))), Dbl.add_d(d, Nat.mul(10n, V(r)))) : {Nat.add(x, Nat.mul(10n, Nat.double(V(r)))) == Nat.add(S.Dec.bit(c), _) : Nat}
      %Equal.sym(Nat, Nat.mul(10n, Nat.double(V(r))), Nat.double(Nat.mul(10n, V(r))), Mul.dbl_r(10n, V(r))) : {Nat.add(x, _) == Nat.add(S.Dec.bit(c), Nat.add(Nat.double(d), Nat.double(Nat.mul(10n, V(r))))) : Nat}
      N.Add.assoc(S.Dec.bit(c), Nat.double(d), Nat.double(Nat.mul(10n, V(r))))

def Bits.val(n: Nat, w: Word(n), +ds: List<&2, Nat>) -> {V(S.Dec.of_bits(n, w, ds)) == G(n, V(ds), w) : Nat}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          +q = p
          %Equal.sym(Nat, V(S.Dec.dbl(S.Dec.of_bits(q, t, ds), b)), Nat.add(S.Dec.bit(b), Nat.double(V(S.Dec.of_bits(q, t, ds)))), Dbl.val(S.Dec.of_bits(q, t, ds), b)) : {_ == G(1n+q, V(ds), WCon{b, t}) : Nat}
          Equal.cong(Nat, Nat, y => Nat.add(S.Dec.bit(b), Nat.double(y)), V(S.Dec.of_bits(q, t, ds)), G(q, V(ds), t), Bits.val(q, t, ds))

# Small facts
# ===========

def IsZ(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      False{}

def Pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def Nat.zero_succ(+x: Nat, h: {0n == 1n+x : Nat}) -> {False{} == True{} : Bool}:
  Equal.sym(Bool, True{}, False{}, Equal.cong(Nat, Bool, y => IsZ(y), 0n, 1n+x, h))

def Nat.succ_inj(+a: Nat, +b: Nat, h: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, y => Pred(y), 1n+a, 1n+b, h)

def And.intro(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, Lm.Bool.ft(ea))

def Dbl.inj(a: Nat, b: Nat, e: {Nat.double(a) == Nat.double(b) : Nat}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q0:
      +q = q0
      Empty.absurd({0n == 1n+q : Nat}, Lm.Bool.ft(Nat.zero_succ(1n+Nat.double(q), e)))
    case 1n+p0 0n:
      +p = p0
      Empty.absurd({1n+p == 0n : Nat}, Lm.Bool.ft(Nat.zero_succ(1n+Nat.double(p), Equal.sym(Nat, 2n+Nat.double(p), 0n, e))))
    case 1n+p0 1n+q0:
      +p = p0
      +q = q0
      Equal.cong(Nat, Nat, y => 1n+y, p, q, Dbl.inj(p, q, Nat.succ_inj(Nat.double(p), Nat.double(q), Nat.succ_inj(1n+Nat.double(p), 1n+Nat.double(q), e))))

def Dbl.ne(a: Nat, b: Nat, e: {Nat.double(a) == 1n+Nat.double(b) : Nat}) -> {False{} == True{} : Bool}:
  match a b:
    case 0n _:
      Nat.zero_succ(Nat.double(b), e)
    case 1n+p0 0n:
      +p = p0
      Nat.zero_succ(Nat.double(p), Equal.sym(Nat, 1n+Nat.double(p), 0n, Nat.succ_inj(1n+Nat.double(p), 0n, e)))
    case 1n+p0 1n+q0:
      +p = p0
      +q = q0
      Dbl.ne(p, q, Nat.succ_inj(Nat.double(p), 1n+Nat.double(q), Nat.succ_inj(1n+Nat.double(p), 2n+Nat.double(q), e)))

# A parity bit and a half are unique.
def Par.uniq(o: Bool, b: Bool, +x: Nat, +y: Nat, e: {Nat.add(S.Dec.bit(o), Nat.double(x)) == Nat.add(S.Dec.bit(b), Nat.double(y)) : Nat})
  -> {o == b : Bool} & {x == y : Nat}:
  match o b:
    case False{} False{}:
      ({==}, Dbl.inj(x, y, e))
    case True{} True{}:
      ({==}, Dbl.inj(x, y, Nat.succ_inj(Nat.double(x), Nat.double(y), e)))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool} & {x == y : Nat}, Lm.Bool.ft(Dbl.ne(x, y, e)))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool} & {x == y : Nat}, Lm.Bool.ft(Dbl.ne(y, x, Equal.sym(Nat, 1n+Nat.double(x), Nat.double(y), e))))

def Add.zero_split(a: Nat, +b: Nat, e: {Nat.add(a, b) == 0n : Nat}) -> {a == 0n : Nat} & {b == 0n : Nat}:
  match a:
    case 0n:
      ({==}, e)
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat} & {b == 0n : Nat}, Lm.Bool.ft(Nat.zero_succ(Nat.add(p, b), Equal.sym(Nat, 1n+Nat.add(p, b), 0n, e))))

# Halving
# =======

def Halve.step_val(+d: Nat, +r: List<&2, Nat>, h: S.Halved,
  e: {V(r) == Nat.add(S.Dec.bit(S.Halved.odd(h)), Nat.double(V(S.Halved.q(h)))) : Nat})
  -> {Nat.add(d, Nat.mul(10n, V(r))) == Nat.add(S.Dec.bit(S.Halved.odd(S.Dec.halve.step(d, h))), Nat.double(V(S.Halved.q(S.Dec.halve.step(d, h))))) : Nat}:
  match h:
    case S.Halved{+q, +o}:
      +x = Nat.add(d, Nat.mul(10n, S.Dec.bit(o)))
      %Equal.sym(Nat, V(r), Nat.add(S.Dec.bit(o), Nat.double(V(q))), e) : {Nat.add(d, Nat.mul(10n, _)) == Nat.add(S.Dec.bit(S.Dec.odd(x)), Nat.double(Nat.add(S.Dec.half(x), Nat.mul(10n, V(q))))) : Nat}
      %Equal.sym(Nat, Nat.mul(10n, Nat.add(S.Dec.bit(o), Nat.double(V(q)))), Nat.add(Nat.mul(10n, S.Dec.bit(o)), Nat.mul(10n, Nat.double(V(q)))), Mul.add_r(10n, S.Dec.bit(o), Nat.double(V(q)))) : {Nat.add(d, _) == Nat.add(S.Dec.bit(S.Dec.odd(x)), Nat.double(Nat.add(S.Dec.half(x), Nat.mul(10n, V(q))))) : Nat}
      %N.Add.assoc(d, Nat.mul(10n, S.Dec.bit(o)), Nat.mul(10n, Nat.double(V(q)))) : {_ == Nat.add(S.Dec.bit(S.Dec.odd(x)), Nat.double(Nat.add(S.Dec.half(x), Nat.mul(10n, V(q))))) : Nat}
      %Equal.sym(Nat, Nat.mul(10n, Nat.double(V(q))), Nat.double(Nat.mul(10n, V(q))), Mul.dbl_r(10n, V(q))) : {Nat.add(x, _) == Nat.add(S.Dec.bit(S.Dec.odd(x)), Nat.double(Nat.add(S.Dec.half(x), Nat.mul(10n, V(q))))) : Nat}
      %Equal.sym(Nat, Nat.double(Nat.add(S.Dec.half(x), Nat.mul(10n, V(q)))), Nat.add(Nat.double(S.Dec.half(x)), Nat.double(Nat.mul(10n, V(q)))), Dbl.add_d(S.Dec.half(x), Nat.mul(10n, V(q)))) : {Nat.add(x, Nat.double(Nat.mul(10n, V(q)))) == Nat.add(S.Dec.bit(S.Dec.odd(x)), _) : Nat}
      %N.Add.assoc(S.Dec.bit(S.Dec.odd(x)), Nat.double(S.Dec.half(x)), Nat.double(Nat.mul(10n, V(q)))) : {Nat.add(x, Nat.double(Nat.mul(10n, V(q)))) == _ : Nat}
      %N.Half.split(x) : {Nat.add(x, Nat.double(Nat.mul(10n, V(q)))) == Nat.add(_, Nat.double(Nat.mul(10n, V(q)))) : Nat}
      {==}

def Halve.val(ds: List<&2, Nat>) -> {V(ds) == Nat.add(S.Dec.bit(S.Halved.odd(S.Dec.halve(ds))), Nat.double(V(S.Halved.q(S.Dec.halve(ds))))) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +r}:
      Halve.step_val(d, r, S.Dec.halve(r), Halve.val(r))

# Bits from digits
# ================

def BitsN.word(n: Nat, r: S.BitsN<n>) -> Word(n):
  match r:
    case S.BitsN{w, rest}:
      w

def BitsN.rest(n: Nat, r: S.BitsN<n>) -> List<&2, Nat>:
  match r:
    case S.BitsN{w, rest}:
      rest

def Con.word(+p: Nat, +b: Bool, r: S.BitsN<p>) -> {BitsN.word(1n+p, S.Dec.bits.con(p, b, r)) == WCon{b, BitsN.word(p, r)} : Word(1n+p)}:
  match r:
    case S.BitsN{w, rest}:
      {==}

def Con.rest(+p: Nat, +b: Bool, r: S.BitsN<p>) -> {BitsN.rest(1n+p, S.Dec.bits.con(p, b, r)) == BitsN.rest(p, r) : List<&2, Nat>}:
  match r:
    case S.BitsN{w, rest}:
      {==}

def Pf.fst(-A: Type, -B: Type, p: A & B) -> A:
  (x, y) = p
  x

def Pf.snd(-A: Type, -B: Type, p: A & B) -> B:
  (x, y) = p
  y

def Halve.uniq(+q: Nat, +ds: List<&2, Nat>, +v: Nat, +b: Bool, +t: Word(q), e: {V(ds) == G(1n+q, v, WCon{b, t}) : Nat})
  -> {S.Halved.odd(S.Dec.halve(ds)) == b : Bool} & {V(S.Halved.q(S.Dec.halve(ds))) == G(q, v, t) : Nat}:
  Par.uniq(S.Halved.odd(S.Dec.halve(ds)), b, V(S.Halved.q(S.Dec.halve(ds))), G(q, v, t),
    Equal.trans(Nat, Nat.add(S.Dec.bit(S.Halved.odd(S.Dec.halve(ds))), Nat.double(V(S.Halved.q(S.Dec.halve(ds))))), V(ds), G(1n+q, v, WCon{b, t}),
      Equal.sym(Nat, V(ds), Nat.add(S.Dec.bit(S.Halved.odd(S.Dec.halve(ds))), Nat.double(V(S.Halved.q(S.Dec.halve(ds))))), Halve.val(ds)), e))

def Bits.word.go(+q: Nat, +ds: List<&2, Nat>, +b: Bool, +t: Word(q),
  eo: {S.Halved.odd(S.Dec.halve(ds)) == b : Bool}, ih: {BitsN.word(q, S.Dec.to_bits(q, S.Halved.q(S.Dec.halve(ds)))) == t : Word(q)})
  -> {BitsN.word(1n+q, S.Dec.to_bits(1n+q, ds)) == WCon{b, t} : Word(1n+q)}:
  %Equal.sym(Word(1n+q), BitsN.word(1n+q, S.Dec.bits.con(q, S.Halved.odd(S.Dec.halve(ds)), S.Dec.to_bits(q, S.Halved.q(S.Dec.halve(ds))))), WCon{S.Halved.odd(S.Dec.halve(ds)), BitsN.word(q, S.Dec.to_bits(q, S.Halved.q(S.Dec.halve(ds))))}, Con.word(q, S.Halved.odd(S.Dec.halve(ds)), S.Dec.to_bits(q, S.Halved.q(S.Dec.halve(ds))))) : {_ == WCon{b, t} : Word(1n+q)}
  %Equal.sym(Bool, S.Halved.odd(S.Dec.halve(ds)), b, eo) : {WCon{_, BitsN.word(q, S.Dec.to_bits(q, S.Halved.q(S.Dec.halve(ds))))} == WCon{b, t} : Word(1n+q)}
  %Equal.sym(Word(q), BitsN.word(q, S.Dec.to_bits(q, S.Halved.q(S.Dec.halve(ds)))), t, ih) : {WCon{b, _} == WCon{b, t} : Word(1n+q)}
  {==}

# If ds has the value of v followed by the bits of w, then to_bits gives w,
# and its rest has the value v.
def Bits.word(n: Nat, +ds: List<&2, Nat>, +v: Nat, w: Word(n), e: {V(ds) == G(n, v, w) : Nat})
  -> {BitsN.word(n, S.Dec.to_bits(n, ds)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          +q = p
          +e2 = e
          Bits.word.go(q, ds, b, t,
            Pf.fst({S.Halved.odd(S.Dec.halve(ds)) == b : Bool}, {V(S.Halved.q(S.Dec.halve(ds))) == G(q, v, t) : Nat}, Halve.uniq(q, ds, v, b, t, e2)),
            Bits.word(q, S.Halved.q(S.Dec.halve(ds)), v, t,
              Pf.snd({S.Halved.odd(S.Dec.halve(ds)) == b : Bool}, {V(S.Halved.q(S.Dec.halve(ds))) == G(q, v, t) : Nat}, Halve.uniq(q, ds, v, b, t, e2))))

def Bits.rest(n: Nat, +ds: List<&2, Nat>, +v: Nat, w: Word(n), e: {V(ds) == G(n, v, w) : Nat})
  -> {V(BitsN.rest(n, S.Dec.to_bits(n, ds))) == v : Nat}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          e
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          +q = p
          %Equal.sym(List<&2, Nat>, BitsN.rest(1n+q, S.Dec.bits.con(q, S.Halved.odd(S.Dec.halve(ds)), S.Dec.to_bits(q, S.Halved.q(S.Dec.halve(ds))))), BitsN.rest(q, S.Dec.to_bits(q, S.Halved.q(S.Dec.halve(ds)))), Con.rest(q, S.Halved.odd(S.Dec.halve(ds)), S.Dec.to_bits(q, S.Halved.q(S.Dec.halve(ds))))) : {V(_) == v : Nat}
          Bits.rest(q, S.Halved.q(S.Dec.halve(ds)), v, t,
            Pf.snd({S.Halved.odd(S.Dec.halve(ds)) == b : Bool}, {V(S.Halved.q(S.Dec.halve(ds))) == G(q, v, t) : Nat}, Halve.uniq(q, ds, v, b, t, e)))

# The zero test
# =============

def Mul10.zero(+x: Nat, e: {Nat.mul(10n, x) == 0n : Nat}) -> {x == 0n : Nat}:
  Pf.fst({x == 0n : Nat}, {Nat.mul(9n, x) == 0n : Nat}, Add.zero_split(x, Nat.mul(9n, x), e))

def Zero.of(ds: List<&2, Nat>, e: {V(ds) == 0n : Nat}) -> {S.Dec.zero(ds) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +r}:
      +e2 = e
      %Equal.sym(Nat, d, 0n, Pf.fst({d == 0n : Nat}, {Nat.mul(10n, V(r)) == 0n : Nat}, Add.zero_split(d, Nat.mul(10n, V(r)), e2))) : {Bool.and(Nat.is_eq(_, 0n), S.Dec.zero(r)) == True{} : Bool}
      Zero.of(r, Mul10.zero(V(r), Pf.snd({d == 0n : Nat}, {Nat.mul(10n, V(r)) == 0n : Nat}, Add.zero_split(d, Nat.mul(10n, V(r)), e2))))

# Words
# =====

def Word.lo_cat(m: Nat, +n: Nat, a: Word(m), +b: Word(n)) -> {S.Word.lo(m, n, S.Word.cat(m, n, a, b)) == a : Word(m)}:
  match m:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{+x, +t}:
          +q = p
          Equal.cong(Word(q), Word(1n+q), y => WCon{x, y}, S.Word.lo(q, n, S.Word.cat(q, n, t, b)), t, Word.lo_cat(q, n, t, b))

def Word.hi_cat(m: Nat, +n: Nat, a: Word(m), +b: Word(n)) -> {S.Word.hi(m, n, S.Word.cat(m, n, a, b)) == b : Word(n)}:
  match m:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{x, t}:
          Word.hi_cat(p, n, t, b)

def U64.of_bits_words(h: U32, l: U32) -> {S.U64.of_bits(S.U64.bits(S.U64{h, l})) == S.U64{h, l} : S.U64}:
  match h l:
    case U32{+hw} U32{+lw}:
      %Equal.sym(Word(32n), S.Word.hi(32n, 32n, S.Word.cat(32n, 32n, lw, hw)), hw, Word.hi_cat(32n, 32n, lw, hw)) : {S.U64{U32{_}, U32{S.Word.lo(32n, 32n, S.Word.cat(32n, 32n, lw, hw))}} == S.U64{U32{hw}, U32{lw}} : S.U64}
      %Equal.sym(Word(32n), S.Word.lo(32n, 32n, S.Word.cat(32n, 32n, lw, hw)), lw, Word.lo_cat(32n, 32n, lw, hw)) : {S.U64{U32{hw}, U32{_}} == S.U64{U32{hw}, U32{lw}} : S.U64}
      {==}

def U64.of_bits_bits(a: S.U64) -> {S.U64.of_bits(S.U64.bits(a)) == a : S.U64}:
  match a:
    case S.U64{h, l}:
      U64.of_bits_words(h, l)

# Valid digits
# ============

def Digits.dbl(ds: List<&2, Nat>, +c: Bool, h: {Digits(ds) == True{} : Bool}) -> {Digits(S.Dec.dbl(ds, c)) == True{} : Bool}:
  match ds:
    case Nil{}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{+d, +r}:
      +h2 = h
      And.intro(Nat.is_lt(S.Dec.lo(Nat.add(S.Dec.bit(c), Nat.double(d))), 10n), Digits(S.Dec.dbl(r, S.Dec.hi(Nat.add(S.Dec.bit(c), Nat.double(d))))),
        Dig.lo_lt(c, d, Pf.fst({Nat.is_lt(d, 10n) == True{} : Bool}, {Digits(r) == True{} : Bool}, Lm.Bool.and_true(Nat.is_lt(d, 10n), Digits(r), h2))),
        Digits.dbl(r, S.Dec.hi(Nat.add(S.Dec.bit(c), Nat.double(d))), Pf.snd({Nat.is_lt(d, 10n) == True{} : Bool}, {Digits(r) == True{} : Bool}, Lm.Bool.and_true(Nat.is_lt(d, 10n), Digits(r), h2))))

def Digits.of_bits(n: Nat, w: Word(n), +ds: List<&2, Nat>, +h: {Digits(ds) == True{} : Bool}) -> {Digits(S.Dec.of_bits(n, w, ds)) == True{} : Bool}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          h
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          +q = p
          Digits.dbl(S.Dec.of_bits(q, t, ds), b, Digits.of_bits(q, t, ds, h))

# Reading back
# ============

def List.append_nil(ds: List<&2, Nat>) -> {List.append(&2, Nat, ds, []) == ds : List<&2, Nat>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +r}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, y => Con{d, y}, List.append(&2, Nat, r, []), r, List.append_nil(r))

def Parse.digit(+d: Nat, +s: String, +x: List<&2, Nat>, h: {Nat.is_lt(d, 10n) == True{} : Bool})
  -> {S.Dec.parse(SCon{S.Dec.char(d), s}, x) == S.Dec.parse(s, Con{d, x}) : Maybe<&2, List<&2, Nat>>}:
  %Equal.sym(Maybe<&2, Nat>, S.Dec.digit(S.Dec.char(d)), Some{d}, Dig.rt(d, h)) : {Maybe.bind(&2, Nat, List<&2, Nat>, _, k => S.Dec.parse(s, Con{k, x})) == S.Dec.parse(s, Con{d, x}) : Maybe<&2, List<&2, Nat>>}
  {==}

# Parsing the string of ds gives ds back, low digit first.
def Parse.str(ds: List<&2, Nat>, +s: String, +acc: List<&2, Nat>, h: {Digits(ds) == True{} : Bool})
  -> {S.Dec.parse(S.Dec.str(ds, s), acc) == S.Dec.parse(s, List.append(&2, Nat, ds, acc)) : Maybe<&2, List<&2, Nat>>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +r}:
      +h2 = h
      Equal.trans(Maybe<&2, List<&2, Nat>>, S.Dec.parse(S.Dec.str(r, SCon{S.Dec.char(d), s}), acc), S.Dec.parse(SCon{S.Dec.char(d), s}, List.append(&2, Nat, r, acc)), S.Dec.parse(s, Con{d, List.append(&2, Nat, r, acc)}),
        Parse.str(r, SCon{S.Dec.char(d), s}, acc, Pf.snd({Nat.is_lt(d, 10n) == True{} : Bool}, {Digits(r) == True{} : Bool}, Lm.Bool.and_true(Nat.is_lt(d, 10n), Digits(r), h2))),
        Parse.digit(d, s, List.append(&2, Nat, r, acc), Pf.fst({Nat.is_lt(d, 10n) == True{} : Bool}, {Digits(r) == True{} : Bool}, Lm.Bool.and_true(Nat.is_lt(d, 10n), Digits(r), h2))))

def Read.go(s: String) -> Maybe<&2, S.U64>:
  Maybe.bind(&2, List<&2, Nat>, S.U64, S.Dec.parse(s, []), ds => S.U64.of_digits(ds))

# read on a string that str builds with a non-empty tail.
def Read.str(r: List<&2, Nat>, +c: Char, +s: String) -> {S.U64.read(S.Dec.str(r, SCon{c, s})) == Read.go(S.Dec.str(r, SCon{c, s})) : Maybe<&2, S.U64>}:
  match r:
    case Nil{}:
      {==}
    case Con{d, t}:
      Read.str(t, S.Dec.char(d), SCon{c, s})

def Of_digits.go(+a: S.U64, r: S.BitsN<64n>, ew: {BitsN.word(64n, r) == S.U64.bits(a) : Word(64n)}, er: {V(BitsN.rest(64n, r)) == 0n : Nat})
  -> {S.U64.of_digits.go(r) == Some{a} : Maybe<&2, S.U64>}:
  match r:
    case S.BitsN{+w, +rest}:
      %Equal.sym(Bool, S.Dec.zero(rest), True{}, Zero.of(rest, er)) : {S.U64.of_digits.fin(_, w) == Some{a} : Maybe<&2, S.U64>}
      %Equal.sym(Word(64n), w, S.U64.bits(a), ew) : {Some{S.U64.of_bits(_)} == Some{a} : Maybe<&2, S.U64>}
      %Equal.sym(S.U64, S.U64.of_bits(S.U64.bits(a)), a, U64.of_bits_bits(a)) : {Some{_} == Some{a} : Maybe<&2, S.U64>}
      {==}

def Of_digits(+ds: List<&2, Nat>, +a: S.U64, +hv: {V(ds) == G(64n, 0n, S.U64.bits(a)) : Nat}) -> {S.U64.of_digits(ds) == Some{a} : Maybe<&2, S.U64>}:
  Of_digits.go(a, S.Dec.to_bits(64n, ds), Bits.word(64n, ds, 0n, S.U64.bits(a), hv), Bits.rest(64n, ds, 0n, S.U64.bits(a), hv))

def Show.read.go(+a: S.U64, ds: List<&2, Nat>, hv: {V(ds) == G(64n, 0n, S.U64.bits(a)) : Nat}, hd: {Digits(ds) == True{} : Bool})
  -> {S.U64.read(S.Dec.show(ds)) == Some{a} : Maybe<&2, S.U64>}:
  match ds:
    case Nil{}:
      Of_digits([0n], a, hv)
    case Con{+d, +r}:
      %Equal.sym(Maybe<&2, S.U64>, S.U64.read(S.Dec.str(r, SCon{S.Dec.char(d), ""})), Read.go(S.Dec.str(r, SCon{S.Dec.char(d), ""})), Read.str(r, S.Dec.char(d), "")) : {_ == Some{a} : Maybe<&2, S.U64>}
      %Equal.sym(Maybe<&2, List<&2, Nat>>, S.Dec.parse(S.Dec.str(Con{d, r}, ""), []), S.Dec.parse("", List.append(&2, Nat, Con{d, r}, [])), Parse.str(Con{d, r}, "", [], hd)) : {Maybe.bind(&2, List<&2, Nat>, S.U64, _, k => S.U64.of_digits(k)) == Some{a} : Maybe<&2, S.U64>}
      %Equal.sym(List<&2, Nat>, List.append(&2, Nat, Con{d, r}, []), Con{d, r}, List.append_nil(Con{d, r})) : {S.U64.of_digits(_) == Some{a} : Maybe<&2, S.U64>}
      Of_digits(Con{d, r}, a, hv)

def U64.show_read(+a: S.U64) -> {S.U64.read(S.U64.show(a)) == Some{a} : Maybe<&2, S.U64>}:
  Show.read.go(a, S.Dec.of_bits(64n, S.U64.bits(a), []), Bits.val(64n, S.U64.bits(a), []), Digits.of_bits(64n, S.U64.bits(a), [], {==}))
