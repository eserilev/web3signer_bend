# Number lemmas for the U64 and encoding laws: Word against Nat, and Nat
# arithmetic that Base does not prove. 2^32 stays a symbol in every
# statement: the checker expands a Nat in unary, so it never evaluates it.
import Base
import ../src/ssz.bend as S
import ./lemmas.bend as Lm

# Nat order
# =========

def Fin.same(x: Bool, c: Cmp) -> {Word.cmp.fin(x, x, c) == c : Cmp}:
  match x c:
    case True{} LT{}:
      {==}
    case True{} EQ{}:
      {==}
    case True{} GT{}:
      {==}
    case False{} LT{}:
      {==}
    case False{} EQ{}:
      {==}
    case False{} GT{}:
      {==}

def Cmp.double(a: Nat, b: Nat) -> {Nat.cmp(Nat.double(a), Nat.double(b)) == Nat.cmp(a, b) : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Cmp.double(p, q)

def Cmp.double_ft(a: Nat, b: Nat) -> {Nat.cmp(Nat.double(a), 1n+Nat.double(b)) == Word.cmp.fin(False{}, True{}, Nat.cmp(a, b)) : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Cmp.double_ft(p, q)

def Cmp.double_tf(a: Nat, b: Nat) -> {Nat.cmp(1n+Nat.double(a), Nat.double(b)) == Word.cmp.fin(True{}, False{}, Nat.cmp(a, b)) : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Cmp.double_tf(p, q)

# Word order is Nat order
# =======================

def Word.cmp_step(+p: Nat, x: Bool, y: Bool, +at: Word(p), +bt: Word(p))
  -> {Word.cmp.fin(x, y, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))) == Nat.cmp(Word.to_nat(1n+p, WCon{x, at}), Word.to_nat(1n+p, WCon{y, bt})) : Cmp}:
  match x y:
    case False{} False{}:
      %Equal.sym(Cmp, Word.cmp.fin(False{}, False{}, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)), Fin.same(False{}, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)))) : {_ == Nat.cmp(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))) : Cmp}
      Equal.sym(Cmp, Nat.cmp(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)), Cmp.double(Word.to_nat(p, at), Word.to_nat(p, bt)))
    case True{} True{}:
      %Equal.sym(Cmp, Word.cmp.fin(True{}, True{}, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)), Fin.same(True{}, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)))) : {_ == Nat.cmp(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))) : Cmp}
      Equal.sym(Cmp, Nat.cmp(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)), Cmp.double(Word.to_nat(p, at), Word.to_nat(p, bt)))
    case False{} True{}:
      Equal.sym(Cmp, Nat.cmp(Nat.double(Word.to_nat(p, at)), 1n+Nat.double(Word.to_nat(p, bt))), Word.cmp.fin(False{}, True{}, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))), Cmp.double_ft(Word.to_nat(p, at), Word.to_nat(p, bt)))
    case True{} False{}:
      Equal.sym(Cmp, Nat.cmp(1n+Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))), Word.cmp.fin(True{}, False{}, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))), Cmp.double_tf(Word.to_nat(p, at), Word.to_nat(p, bt)))

def Word.cmp_nat(n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          +q = p
          %Equal.sym(Cmp, Word.cmp(q, at, bt), Nat.cmp(Word.to_nat(q, at), Word.to_nat(q, bt)), Word.cmp_nat(q, at, bt)) : {Word.cmp.fin(x, y, _) == Nat.cmp(Word.to_nat(1n+q, WCon{x, at}), Word.to_nat(1n+q, WCon{y, bt})) : Cmp}
          Word.cmp_step(q, x, y, at, bt)

# Nat algebra
# ===========

def Add.zero_r(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, Add.zero_r(p))

def Add.succ_r(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 1n+b), 1n+Nat.add(p, b), Add.succ_r(p, b))

def Add.assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), Add.assoc(p, b, c))

def Add.comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, Add.zero_r(b))
    case 1n+p:
      +q = p
      %Equal.sym(Nat, Nat.add(b, 1n+q), 1n+Nat.add(b, q), Add.succ_r(b, q)) : {1n+Nat.add(q, b) == _ : Nat}
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(q, b), Nat.add(b, q), Add.comm(q, b))

def Dbl.add(a: Nat) -> {Nat.add(a, a) == Nat.double(a) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      +q = p
      %Equal.sym(Nat, Nat.add(q, 1n+q), 1n+Nat.add(q, q), Add.succ_r(q, q)) : {1n+_ == 2n+Nat.double(q) : Nat}
      Equal.cong(Nat, Nat, x => 2n+x, Nat.add(q, q), Nat.double(q), Dbl.add(q))

# 2 * P, as Nat.pow unfolds it.
def Dbl.pow(+a: Nat) -> {Nat.add(a, Nat.add(a, 0n)) == Nat.double(a) : Nat}:
  %Equal.sym(Nat, Nat.add(a, 0n), a, Add.zero_r(a)) : {Nat.add(a, _) == Nat.double(a) : Nat}
  Dbl.add(a)

def Cmp.cancel(k: Nat, +x: Nat, +y: Nat) -> {Nat.cmp(Nat.add(k, x), Nat.add(k, y)) == Nat.cmp(x, y) : Cmp}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Cmp.cancel(p, x, y)

def Cmp.lt_add(l: Nat, k: Nat, +z: Nat, h: {Nat.is_lt(l, k) == True{} : Bool}) -> {Nat.cmp(l, Nat.add(k, z)) == LT{} : Cmp}:
  match l k:
    case 0n 0n:
      Empty.absurd({Nat.cmp(0n, Nat.add(0n, z)) == LT{} : Cmp}, Lm.Bool.ft(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.cmp(1n+p, Nat.add(0n, z)) == LT{} : Cmp}, Lm.Bool.ft(h))
    case 1n+p 1n+q:
      Cmp.lt_add(p, q, z, h)

def Cmp.gt_add(l: Nat, k: Nat, +z: Nat, h: {Nat.is_lt(l, k) == True{} : Bool}) -> {Nat.cmp(Nat.add(k, z), l) == GT{} : Cmp}:
  match l k:
    case 0n 0n:
      Empty.absurd({Nat.cmp(Nat.add(0n, z), 0n) == GT{} : Cmp}, Lm.Bool.ft(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.cmp(Nat.add(0n, z), 1n+p) == GT{} : Cmp}, Lm.Bool.ft(h))
    case 1n+p 1n+q:
      Cmp.gt_add(p, q, z, h)

# Two-digit numbers in base k compare high digit first.
def Lex(h1: Nat, h2: Nat, +l1: Nat, +l2: Nat, +k: Nat,
  +hl1: {Nat.is_lt(l1, k) == True{} : Bool}, +hl2: {Nat.is_lt(l2, k) == True{} : Bool})
  -> {Nat.cmp(Nat.add(Nat.mul(h1, k), l1), Nat.add(Nat.mul(h2, k), l2)) == S.U64.cmp.lo(Nat.cmp(h1, h2), Nat.cmp(l1, l2)) : Cmp}:
  match h1 h2:
    case 0n 0n:
      {==}
    case 0n 1n+q0:
      +q = q0
      %Equal.sym(Nat, Nat.add(Nat.add(k, Nat.mul(q, k)), l2), Nat.add(k, Nat.add(Nat.mul(q, k), l2)), Add.assoc(k, Nat.mul(q, k), l2)) : {Nat.cmp(l1, _) == LT{} : Cmp}
      Cmp.lt_add(l1, k, Nat.add(Nat.mul(q, k), l2), hl1)
    case 1n+p0 0n:
      +p = p0
      %Equal.sym(Nat, Nat.add(Nat.add(k, Nat.mul(p, k)), l1), Nat.add(k, Nat.add(Nat.mul(p, k), l1)), Add.assoc(k, Nat.mul(p, k), l1)) : {Nat.cmp(_, l2) == GT{} : Cmp}
      Cmp.gt_add(l2, k, Nat.add(Nat.mul(p, k), l1), hl2)
    case 1n+p0 1n+q0:
      +p = p0
      +q = q0
      %Equal.sym(Nat, Nat.add(Nat.add(k, Nat.mul(p, k)), l1), Nat.add(k, Nat.add(Nat.mul(p, k), l1)), Add.assoc(k, Nat.mul(p, k), l1)) : {Nat.cmp(_, Nat.add(Nat.add(k, Nat.mul(q, k)), l2)) == S.U64.cmp.lo(Nat.cmp(p, q), Nat.cmp(l1, l2)) : Cmp}
      %Equal.sym(Nat, Nat.add(Nat.add(k, Nat.mul(q, k)), l2), Nat.add(k, Nat.add(Nat.mul(q, k), l2)), Add.assoc(k, Nat.mul(q, k), l2)) : {Nat.cmp(Nat.add(k, Nat.add(Nat.mul(p, k), l1)), _) == S.U64.cmp.lo(Nat.cmp(p, q), Nat.cmp(l1, l2)) : Cmp}
      %Equal.sym(Cmp, Nat.cmp(Nat.add(k, Nat.add(Nat.mul(p, k), l1)), Nat.add(k, Nat.add(Nat.mul(q, k), l2))), Nat.cmp(Nat.add(Nat.mul(p, k), l1), Nat.add(Nat.mul(q, k), l2)), Cmp.cancel(k, Nat.add(Nat.mul(p, k), l1), Nat.add(Nat.mul(q, k), l2))) : {_ == S.U64.cmp.lo(Nat.cmp(p, q), Nat.cmp(l1, l2)) : Cmp}
      Lex(p, q, l1, l2, k, hl1, hl2)

# Word bound
# ==========

def Lt.double1(t: Nat, p: Nat, h: {Nat.is_lt(t, p) == True{} : Bool}) -> {Nat.is_lt(1n+Nat.double(t), Nat.double(p)) == True{} : Bool}:
  match t p:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(1n, 0n) == True{} : Bool}, Lm.Bool.ft(h))
    case 0n 1n+q:
      {==}
    case 1n+a 0n:
      Empty.absurd({Nat.is_lt(1n+Nat.double(1n+a), 0n) == True{} : Bool}, Lm.Bool.ft(h))
    case 1n+a 1n+q:
      Lt.double1(a, q, h)

def Lt.double0(t: Nat, p: Nat, h: {Nat.is_lt(t, p) == True{} : Bool}) -> {Nat.is_lt(Nat.double(t), Nat.double(p)) == True{} : Bool}:
  match t p:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, Lm.Bool.ft(h))
    case 0n 1n+q:
      {==}
    case 1n+a 0n:
      Empty.absurd({Nat.is_lt(Nat.double(1n+a), 0n) == True{} : Bool}, Lm.Bool.ft(h))
    case 1n+a 1n+q:
      Lt.double0(a, q, h)

def Word.lt_bit(+p: Nat, b: Bool, +t: Word(p), +h: {Nat.is_lt(Word.to_nat(p, t), Nat.pow(2n, p)) == True{} : Bool})
  -> {Nat.is_lt(Word.to_nat(1n+p, WCon{b, t}), Nat.double(Nat.pow(2n, p))) == True{} : Bool}:
  match b:
    case False{}:
      Lt.double0(Word.to_nat(p, t), Nat.pow(2n, p), h)
    case True{}:
      Lt.double1(Word.to_nat(p, t), Nat.pow(2n, p), h)

def Word.lt_pow(n: Nat, w: Word(n)) -> {Nat.is_lt(Word.to_nat(n, w), Nat.pow(2n, n)) == True{} : Bool}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          +q = p
          %Equal.sym(Nat, Nat.add(Nat.pow(2n, q), Nat.add(Nat.pow(2n, q), 0n)), Nat.double(Nat.pow(2n, q)), Dbl.pow(Nat.pow(2n, q))) : {Nat.is_lt(Word.to_nat(1n+q, WCon{b, t}), _) == True{} : Bool}
          Word.lt_bit(q, b, t, Word.lt_pow(q, t))

# U64 order
# =========

def Lo.eq_r(h: Cmp) -> {S.U64.cmp.lo(h, EQ{}) == h : Cmp}:
  match h:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def Fin.lo(+x: Bool, +y: Bool, h: Cmp, +l: Cmp)
  -> {Word.cmp.fin(x, y, S.U64.cmp.lo(h, l)) == S.U64.cmp.lo(h, Word.cmp.fin(x, y, l)) : Cmp}:
  match h:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# Words joined low part first compare high part first.
def Word.cmp_cat(m: Nat, +n: Nat, l1: Word(m), l2: Word(m), +h1: Word(n), +h2: Word(n))
  -> {Word.cmp(Nat.add(m, n), S.Word.cat(m, n, l1, h1), S.Word.cat(m, n, l2, h2)) == S.U64.cmp.lo(Word.cmp(n, h1, h2), Word.cmp(m, l1, l2)) : Cmp}:
  match m:
    case 0n:
      match l1 l2:
        case WNil{} WNil{}:
          Equal.sym(Cmp, S.U64.cmp.lo(Word.cmp(n, h1, h2), EQ{}), Word.cmp(n, h1, h2), Lo.eq_r(Word.cmp(n, h1, h2)))
    case 1n+p:
      match l1 l2:
        case WCon{+x, +t1} WCon{+y, +t2}:
          +q = p
          %Equal.sym(Cmp, Word.cmp(Nat.add(q, n), S.Word.cat(q, n, t1, h1), S.Word.cat(q, n, t2, h2)), S.U64.cmp.lo(Word.cmp(n, h1, h2), Word.cmp(q, t1, t2)), Word.cmp_cat(q, n, t1, t2, h1, h2)) : {Word.cmp.fin(x, y, _) == S.U64.cmp.lo(Word.cmp(n, h1, h2), Word.cmp(1n+q, WCon{x, t1}, WCon{y, t2})) : Cmp}
          Fin.lo(x, y, Word.cmp(n, h1, h2), Word.cmp(q, t1, t2))

def U64.cmp_words(+ah: Word(32n), +al: Word(32n), +bh: Word(32n), +bl: Word(32n))
  -> {S.U64.cmp(S.U64{U32{ah}, U32{al}}, S.U64{U32{bh}, U32{bl}}) == Nat.cmp(S.U64.to_nat(S.U64{U32{ah}, U32{al}}), S.U64.to_nat(S.U64{U32{bh}, U32{bl}})) : Cmp}:
  %Word.cmp_nat(64n, S.Word.cat(32n, 32n, al, ah), S.Word.cat(32n, 32n, bl, bh)) : {S.U64.cmp.lo(Word.cmp(32n, ah, bh), Word.cmp(32n, al, bl)) == _ : Cmp}
  Equal.sym(Cmp, Word.cmp(Nat.add(32n, 32n), S.Word.cat(32n, 32n, al, ah), S.Word.cat(32n, 32n, bl, bh)), S.U64.cmp.lo(Word.cmp(32n, ah, bh), Word.cmp(32n, al, bl)), Word.cmp_cat(32n, 32n, al, bl, ah, bh))

def U64.cmp_u32(+ah: U32, +al: U32, +bh: U32, +bl: U32)
  -> {S.U64.cmp(S.U64{ah, al}, S.U64{bh, bl}) == Nat.cmp(S.U64.to_nat(S.U64{ah, al}), S.U64.to_nat(S.U64{bh, bl})) : Cmp}:
  match ah al bh bl:
    case U32{w1} U32{w2} U32{w3} U32{w4}:
      U64.cmp_words(w1, w2, w3, w4)

def U64.cmp_nat(+a: S.U64, +b: S.U64) -> {S.U64.cmp(a, b) == Nat.cmp(S.U64.to_nat(a), S.U64.to_nat(b)) : Cmp}:
  match a b:
    case S.U64{ah, al} S.U64{bh, bl}:
      U64.cmp_u32(ah, al, bh, bl)

# Nat facts for division
# ======================

def Nat.cmp_refl(a: Nat) -> {Nat.cmp(a, a) == EQ{} : Cmp}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.cmp_refl(p)

def Nat.eq_of_cmp(a: Nat, b: Nat, e: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, Lm.Cmp.lt_eq(e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, Lm.Cmp.gt_eq(e))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, Nat.eq_of_cmp(p, q, e))

def Lo.left(h: Cmp, +l: Cmp, e: {S.U64.cmp.lo(h, l) == EQ{} : Cmp}) -> {h == EQ{} : Cmp}:
  match h:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, Lm.Cmp.lt_eq(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, Lm.Cmp.gt_eq(e))

def Lt.succ(r: Nat) -> {Nat.is_lt(r, 1n+r) == True{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      Lt.succ(p)

# r is below 1 + m + r.
def Lt.add(+m: Nat, r: Nat) -> {Nat.is_lt(r, 1n+Nat.add(m, r)) == True{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      +q = p
      %Equal.sym(Nat, Nat.add(m, 1n+q), 1n+Nat.add(m, q), Add.succ_r(m, q)) : {Nat.is_lt(q, _) == True{} : Bool}
      Lt.add(m, q)

def Lt.add_r(r: Nat, m: Nat, +z: Nat, h: {Nat.is_lt(r, m) == True{} : Bool}) -> {Nat.is_lt(r, Nat.add(m, z)) == True{} : Bool}:
  match r m:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.add(0n, z)) == True{} : Bool}, Lm.Bool.ft(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(1n+p, Nat.add(0n, z)) == True{} : Bool}, Lm.Bool.ft(h))
    case 1n+p 1n+q:
      Lt.add_r(p, q, z, h)

def Lt.cancel(k: Nat, +x: Nat, +y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(Nat.add(k, x), Nat.add(k, y)) == True{} : Bool}:
  match k:
    case 0n:
      h
    case 1n+p:
      Lt.cancel(p, x, y, h)

def Lt0.add(p: Nat, +z: Nat, h: {Nat.is_lt(0n, p) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.add(p, z)) == True{} : Bool}:
  match p:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.add(0n, z)) == True{} : Bool}, Lm.Bool.ft(h))
    case 1n+q:
      {==}

def Pow.pos(p: Nat) -> {Nat.is_lt(0n, Nat.pow(2n, p)) == True{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      +r = q
      Lt0.add(Nat.pow(2n, r), Nat.mul(1n, Nat.pow(2n, r)), Pow.pos(r))

def Mul.add_l(a: Nat, +b: Nat, +m: Nat) -> {Nat.mul(Nat.add(a, b), m) == Nat.add(Nat.mul(a, m), Nat.mul(b, m)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      +q = p
      %Equal.sym(Nat, Nat.mul(Nat.add(q, b), m), Nat.add(Nat.mul(q, m), Nat.mul(b, m)), Mul.add_l(q, b, m)) : {Nat.add(m, _) == Nat.add(Nat.add(m, Nat.mul(q, m)), Nat.mul(b, m)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(m, Nat.mul(q, m)), Nat.mul(b, m)), Nat.add(m, Nat.add(Nat.mul(q, m), Nat.mul(b, m))), Add.assoc(m, Nat.mul(q, m), Nat.mul(b, m)))

def Mul.double_l(h: Nat, +m: Nat) -> {Nat.mul(Nat.double(h), m) == Nat.mul(h, Nat.mul(2n, m)) : Nat}:
  match h:
    case 0n:
      {==}
    case 1n+p:
      +q = p
      %Equal.sym(Nat, Nat.mul(Nat.double(q), m), Nat.mul(q, Nat.mul(2n, m)), Mul.double_l(q, m)) : {Nat.add(m, Nat.add(m, _)) == Nat.add(Nat.mul(2n, m), Nat.mul(q, Nat.mul(2n, m))) : Nat}
      %Add.assoc(m, m, Nat.mul(q, Nat.mul(2n, m))) : {_ == Nat.add(Nat.mul(2n, m), Nat.mul(q, Nat.mul(2n, m))) : Nat}
      %Equal.sym(Nat, Nat.add(m, m), Nat.double(m), Dbl.add(m)) : {Nat.add(_, Nat.mul(q, Nat.mul(2n, m))) == Nat.add(Nat.mul(2n, m), Nat.mul(q, Nat.mul(2n, m))) : Nat}
      %Dbl.pow(m) : {Nat.add(_, Nat.mul(q, Nat.mul(2n, m))) == Nat.add(Nat.mul(2n, m), Nat.mul(q, Nat.mul(2n, m))) : Nat}
      {==}

# Division
# ========

def Go.lhs(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(n, m, d, r)), 1n+bp), Nat.mod.fin(Nat.divmod.go(n, m, d, r)))

def Go.alg(+s: Nat, +bp: Nat, +m: Nat, +k: Nat, h: {s == bp : Nat})
  -> {Nat.add(Nat.add(1n+bp, m), k) == Nat.add(m, Nat.add(s, 1n+k)) : Nat}:
  %h : {Nat.add(Nat.add(1n+_, m), k) == Nat.add(m, Nat.add(s, 1n+k)) : Nat}
  %Equal.sym(Nat, Nat.add(s, 1n+k), 1n+Nat.add(s, k), Add.succ_r(s, k)) : {1n+Nat.add(Nat.add(s, m), k) == Nat.add(m, _) : Nat}
  %Equal.sym(Nat, Nat.add(m, 1n+Nat.add(s, k)), 1n+Nat.add(m, Nat.add(s, k)), Add.succ_r(m, Nat.add(s, k))) : {1n+Nat.add(Nat.add(s, m), k) == _ : Nat}
  %Add.assoc(m, s, k) : {1n+Nat.add(Nat.add(s, m), k) == 1n+_ : Nat}
  %Add.comm(m, s) : {1n+Nat.add(_, k) == 1n+Nat.add(Nat.add(m, s), k) : Nat}
  {==}

def Go.eq(n: Nat, m: Nat, +d: Nat, +r: Nat, +bp: Nat, +h: {Nat.add(m, r) == bp : Nat})
  -> {Go.lhs(n, m, d, r, bp) == Nat.add(Nat.mul(d, 1n+bp), Nat.add(r, n)) : Nat}:
  match n:
    case 0n:
      %Equal.sym(Nat, Nat.add(r, 0n), r, Add.zero_r(r)) : {Nat.add(Nat.mul(d, 1n+bp), r) == Nat.add(Nat.mul(d, 1n+bp), _) : Nat}
      {==}
    case 1n+np:
      match m:
        case 0n:
          +k = np
          +s = r
          Equal.trans(Nat, Go.lhs(k, s, 1n+d, 0n, bp), Nat.add(Nat.mul(1n+d, 1n+bp), Nat.add(0n, k)), Nat.add(Nat.mul(d, 1n+bp), Nat.add(s, 1n+k)),
            Go.eq(k, s, 1n+d, 0n, bp, Equal.trans(Nat, Nat.add(s, 0n), s, bp, Add.zero_r(s), h)),
            Go.alg(s, bp, Nat.mul(d, 1n+bp), k, h))
        case 1n+mp0:
          +mp = mp0
          +k = np
          +s = r
          +h2 = Equal.trans(Nat, Nat.add(mp, 1n+s), 1n+Nat.add(mp, s), bp, Add.succ_r(mp, s), h)
          %Equal.sym(Nat, Nat.add(s, 1n+k), 1n+Nat.add(s, k), Add.succ_r(s, k)) : {Go.lhs(1n+k, 1n+mp, d, s, bp) == Nat.add(Nat.mul(d, 1n+bp), _) : Nat}
          Go.eq(k, mp, d, 1n+s, bp, h2)

def Go.rem(+n: Nat, +m: Nat, +d: Nat, +r: Nat) -> Nat:
  Nat.mod.fin(Nat.divmod.go(n, m, d, r))

def Go.lt(n: Nat, m: Nat, +d: Nat, +r: Nat, +bp: Nat, h: {Nat.add(m, r) == bp : Nat})
  -> {Nat.is_lt(Go.rem(n, m, d, r), 1n+bp) == True{} : Bool}:
  match n:
    case 0n:
      %h : {Nat.is_lt(r, 1n+_) == True{} : Bool}
      Lt.add(m, r)
    case 1n+np:
      match m:
        case 0n:
          +s = r
          Go.lt(np, s, 1n+d, 0n, bp, Equal.trans(Nat, Nat.add(s, 0n), s, bp, Add.zero_r(s), h))
        case 1n+mp0:
          +mp = mp0
          +s = r
          Go.lt(np, mp, d, 1n+s, bp, Equal.trans(Nat, Nat.add(mp, 1n+s), 1n+Nat.add(mp, s), bp, Add.succ_r(mp, s), h))

# x div b and x mod b give x back, and x mod b is below b.
def Div.eq(+x: Nat, b: Nat, hb: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.add(Nat.mul(Nat.div(x, b), b), Nat.mod(x, b)) == x : Nat}:
  match b:
    case 0n:
      Empty.absurd({Nat.add(Nat.mul(Nat.div(x, 0n), 0n), Nat.mod(x, 0n)) == x : Nat}, Lm.Bool.ft(hb))
    case 1n+bp:
      +c = bp
      Go.eq(x, c, 0n, 0n, c, Add.zero_r(c))

def Div.lt(+x: Nat, b: Nat, hb: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.is_lt(Nat.mod(x, b), b) == True{} : Bool}:
  match b:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.mod(x, 0n), 0n) == True{} : Bool}, Lm.Bool.ft(hb))
    case 1n+bp:
      +c = bp
      Go.lt(x, c, 0n, 0n, c, Add.zero_r(c))

# The quotient is the only q with x = q b + r and r below b.
def Div.cmp_eq(+x: Nat, +a: Nat, +b: Nat, ea: {a == x : Nat}, eb: {x == b : Nat}) -> {Nat.cmp(a, b) == EQ{} : Cmp}:
  %Equal.sym(Nat, a, x, ea) : {Nat.cmp(_, b) == EQ{} : Cmp}
  %eb : {Nat.cmp(x, _) == EQ{} : Cmp}
  Nat.cmp_refl(x)

def Div.unique(+x: Nat, +b: Nat, +q: Nat, +r: Nat, +hb: {Nat.is_lt(0n, b) == True{} : Bool},
  e: {x == Nat.add(Nat.mul(q, b), r) : Nat}, hr: {Nat.is_lt(r, b) == True{} : Bool})
  -> {Nat.div(x, b) == q : Nat}:
  +lex = Lex(Nat.div(x, b), q, Nat.mod(x, b), r, b, Div.lt(x, b, hb), hr)
  +e1 = Div.eq(x, b, hb)
  +c = Equal.trans(Cmp, S.U64.cmp.lo(Nat.cmp(Nat.div(x, b), q), Nat.cmp(Nat.mod(x, b), r)),
    Nat.cmp(Nat.add(Nat.mul(Nat.div(x, b), b), Nat.mod(x, b)), Nat.add(Nat.mul(q, b), r)), EQ{},
    Equal.sym(Cmp, Nat.cmp(Nat.add(Nat.mul(Nat.div(x, b), b), Nat.mod(x, b)), Nat.add(Nat.mul(q, b), r)), S.U64.cmp.lo(Nat.cmp(Nat.div(x, b), q), Nat.cmp(Nat.mod(x, b), r)), lex),
    Div.cmp_eq(x, Nat.add(Nat.mul(Nat.div(x, b), b), Nat.mod(x, b)), Nat.add(Nat.mul(q, b), r), e1, e))
  Nat.eq_of_cmp(Nat.div(x, b), q, Lo.left(Nat.cmp(Nat.div(x, b), q), Nat.cmp(Nat.mod(x, b), r), c))

# Halves
# ======

def Bool.not_not(b: Bool) -> {Bool.not(Bool.not(b)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# q is its parity bit plus twice its half.
def Half.split(q: Nat) -> {q == Nat.add(S.Dec.bit(S.Dec.odd(q)), Nat.double(S.Dec.half(q))) : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+k0:
          +k = k0
          %Equal.sym(Bool, Bool.not(Bool.not(S.Dec.odd(k))), S.Dec.odd(k), Bool.not_not(S.Dec.odd(k))) : {2n+k == Nat.add(S.Dec.bit(_), 2n+Nat.double(S.Dec.half(k))) : Nat}
          %Equal.sym(Nat, Nat.add(S.Dec.bit(S.Dec.odd(k)), 2n+Nat.double(S.Dec.half(k))), 1n+Nat.add(S.Dec.bit(S.Dec.odd(k)), 1n+Nat.double(S.Dec.half(k))), Add.succ_r(S.Dec.bit(S.Dec.odd(k)), 1n+Nat.double(S.Dec.half(k)))) : {2n+k == _ : Nat}
          %Equal.sym(Nat, Nat.add(S.Dec.bit(S.Dec.odd(k)), 1n+Nat.double(S.Dec.half(k))), 1n+Nat.add(S.Dec.bit(S.Dec.odd(k)), Nat.double(S.Dec.half(k))), Add.succ_r(S.Dec.bit(S.Dec.odd(k)), Nat.double(S.Dec.half(k)))) : {2n+k == 1n+_ : Nat}
          %Half.split(k) : {2n+k == 2n+_ : Nat}
          {==}

def Half.double(t: Nat) -> {S.Dec.half(Nat.double(t)) == t : Nat}:
  match t:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, S.Dec.half(Nat.double(p)), p, Half.double(p))

def Half.double1(t: Nat) -> {S.Dec.half(1n+Nat.double(t)) == t : Nat}:
  match t:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, S.Dec.half(1n+Nat.double(p)), p, Half.double1(p))

def Mul.one_r(a: Nat) -> {Nat.mul(a, 1n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.mul(p, 1n), p, Mul.one_r(p))

def Add.swap(+a: Nat, +b: Nat, +r: Nat) -> {Nat.add(a, Nat.add(b, r)) == Nat.add(b, Nat.add(a, r)) : Nat}:
  %Add.assoc(a, b, r) : {_ == Nat.add(b, Nat.add(a, r)) : Nat}
  %Add.assoc(b, a, r) : {Nat.add(Nat.add(a, b), r) == _ : Nat}
  %Add.comm(b, a) : {Nat.add(_, r) == Nat.add(Nat.add(b, a), r) : Nat}
  {==}

def Div.one(+x: Nat) -> {Nat.div(x, 1n) == x : Nat}:
  Div.unique(x, 1n, x, 0n, {==},
    Equal.sym(Nat, Nat.add(Nat.mul(x, 1n), 0n), x,
      Equal.trans(Nat, Nat.add(Nat.mul(x, 1n), 0n), Nat.mul(x, 1n), x, Add.zero_r(Nat.mul(x, 1n)), Mul.one_r(x))),
    {==})

def Half.bound(o: Bool, +m: Nat, +r: Nat, h: {Nat.is_lt(r, m) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(S.Dec.bit(o), m), r), Nat.mul(2n, m)) == True{} : Bool}:
  match o:
    case False{}:
      Lt.add_r(r, m, Nat.mul(1n, m), h)
    case True{}:
      %Equal.sym(Nat, Nat.add(m, 0n), m, Add.zero_r(m)) : {Nat.is_lt(Nat.add(_, r), Nat.add(m, Nat.add(m, 0n))) == True{} : Bool}
      Lt.cancel(m, r, Nat.add(m, 0n), Lt.add_r(r, m, 0n, h))

# x = q m + r with q = o + 2 h gives x = h (2 m) + (o m + r).
def Half.eq(+x: Nat, +m: Nat, +q: Nat, +r: Nat, +o: Bool, +h: Nat,
  e1: {Nat.add(Nat.mul(q, m), r) == x : Nat}, sp: {q == Nat.add(S.Dec.bit(o), Nat.double(h)) : Nat})
  -> {x == Nat.add(Nat.mul(h, Nat.mul(2n, m)), Nat.add(Nat.mul(S.Dec.bit(o), m), r)) : Nat}:
  %e1 : {_ == Nat.add(Nat.mul(h, Nat.mul(2n, m)), Nat.add(Nat.mul(S.Dec.bit(o), m), r)) : Nat}
  %Equal.sym(Nat, q, Nat.add(S.Dec.bit(o), Nat.double(h)), sp) : {Nat.add(Nat.mul(_, m), r) == Nat.add(Nat.mul(h, Nat.mul(2n, m)), Nat.add(Nat.mul(S.Dec.bit(o), m), r)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(S.Dec.bit(o), Nat.double(h)), m), Nat.add(Nat.mul(S.Dec.bit(o), m), Nat.mul(Nat.double(h), m)), Mul.add_l(S.Dec.bit(o), Nat.double(h), m)) : {Nat.add(_, r) == Nat.add(Nat.mul(h, Nat.mul(2n, m)), Nat.add(Nat.mul(S.Dec.bit(o), m), r)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.double(h), m), Nat.mul(h, Nat.mul(2n, m)), Mul.double_l(h, m)) : {Nat.add(Nat.add(Nat.mul(S.Dec.bit(o), m), _), r) == Nat.add(Nat.mul(h, Nat.mul(2n, m)), Nat.add(Nat.mul(S.Dec.bit(o), m), r)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(S.Dec.bit(o), m), Nat.mul(h, Nat.mul(2n, m))), r), Nat.add(Nat.mul(S.Dec.bit(o), m), Nat.add(Nat.mul(h, Nat.mul(2n, m)), r)), Add.assoc(Nat.mul(S.Dec.bit(o), m), Nat.mul(h, Nat.mul(2n, m)), r)) : {_ == Nat.add(Nat.mul(h, Nat.mul(2n, m)), Nat.add(Nat.mul(S.Dec.bit(o), m), r)) : Nat}
  Add.swap(Nat.mul(S.Dec.bit(o), m), Nat.mul(h, Nat.mul(2n, m)), r)

# Half of x div m is x div 2m.
def Half.div(+x: Nat, +m: Nat, +hm: {Nat.is_lt(0n, m) == True{} : Bool})
  -> {S.Dec.half(Nat.div(x, m)) == Nat.div(x, Nat.mul(2n, m)) : Nat}:
  Equal.sym(Nat, Nat.div(x, Nat.mul(2n, m)), S.Dec.half(Nat.div(x, m)),
    Div.unique(x, Nat.mul(2n, m), S.Dec.half(Nat.div(x, m)), Nat.add(Nat.mul(S.Dec.bit(S.Dec.odd(Nat.div(x, m))), m), Nat.mod(x, m)),
      Lt0.add(m, Nat.mul(1n, m), hm),
      Half.eq(x, m, Nat.div(x, m), Nat.mod(x, m), S.Dec.odd(Nat.div(x, m)), S.Dec.half(Nat.div(x, m)), Div.eq(x, m, hm), Half.split(Nat.div(x, m))),
      Half.bound(S.Dec.odd(Nat.div(x, m)), m, Nat.mod(x, m), Div.lt(x, m, hm))))

# Shifts
# ======

def Word.pad_bit(+p: Nat, b: Bool, +t: Word(p), e: {Word.to_nat(1n+p, Word.shr.pad(p, t)) == Word.to_nat(p, t) : Nat})
  -> {Word.to_nat(2n+p, WCon{b, Word.shr.pad(p, t)}) == Word.to_nat(1n+p, WCon{b, t}) : Nat}:
  match b:
    case False{}:
      Equal.cong(Nat, Nat, x => Nat.double(x), Word.to_nat(1n+p, Word.shr.pad(p, t)), Word.to_nat(p, t), e)
    case True{}:
      Equal.cong(Nat, Nat, x => 1n+Nat.double(x), Word.to_nat(1n+p, Word.shr.pad(p, t)), Word.to_nat(p, t), e)

def Word.half_bit(+p: Nat, b: Bool, +t: Word(p)) -> {Word.to_nat(p, t) == S.Dec.half(Word.to_nat(1n+p, WCon{b, t})) : Nat}:
  match b:
    case False{}:
      Equal.sym(Nat, S.Dec.half(Nat.double(Word.to_nat(p, t))), Word.to_nat(p, t), Half.double(Word.to_nat(p, t)))
    case True{}:
      Equal.sym(Nat, S.Dec.half(1n+Nat.double(Word.to_nat(p, t))), Word.to_nat(p, t), Half.double1(Word.to_nat(p, t)))

def Word.pad_nat(n: Nat, w: Word(n)) -> {Word.to_nat(1n+n, Word.shr.pad(n, w)) == Word.to_nat(n, w) : Nat}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, +t}:
          +q = p
          Word.pad_bit(q, b, t, Word.pad_nat(q, t))

def Word.shr_nat(n: Nat, w: Word(n)) -> {Word.to_nat(n, Word.shr(n, w)) == S.Dec.half(Word.to_nat(n, w)) : Nat}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, +t}:
          +q = p
          %Equal.sym(Nat, Word.to_nat(1n+q, Word.shr.pad(q, t)), Word.to_nat(q, t), Word.pad_nat(q, t)) : {_ == S.Dec.half(Word.to_nat(1n+q, WCon{b, t})) : Nat}
          Word.half_bit(q, b, t)

def Cat.lo_hi(m: Nat, +n: Nat, w: Word(Nat.add(m, n)))
  -> {S.Word.cat(m, n, S.Word.lo(m, n, w), S.Word.hi(m, n, w)) == w : Word(Nat.add(m, n))}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{+x, +t}:
          +q = p
          Equal.cong(Word(Nat.add(q, n)), Word(1n+Nat.add(q, n)), y => WCon{x, y}, S.Word.cat(q, n, S.Word.lo(q, n, t), S.Word.hi(q, n, t)), t, Cat.lo_hi(q, n, t))

def U64.shr1_nat(+y: S.U64) -> {S.U64.to_nat(S.U64.shr1(y)) == S.Dec.half(S.U64.to_nat(y)) : Nat}:
  %Equal.sym(Word(64n), S.Word.cat(32n, 32n, S.Word.lo(32n, 32n, Word.shr(64n, S.U64.bits(y))), S.Word.hi(32n, 32n, Word.shr(64n, S.U64.bits(y)))), Word.shr(64n, S.U64.bits(y)), Cat.lo_hi(32n, 32n, Word.shr(64n, S.U64.bits(y)))) : {Word.to_nat(64n, _) == S.Dec.half(S.U64.to_nat(y)) : Nat}
  Word.shr_nat(64n, S.U64.bits(y))

def U64.shrn_nat(n: Nat, +a: S.U64) -> {S.U64.to_nat(S.U64.shrn(n, a)) == Nat.div(S.U64.to_nat(a), Nat.pow(2n, n)) : Nat}:
  match n:
    case 0n:
      Equal.sym(Nat, Nat.div(S.U64.to_nat(a), 1n), S.U64.to_nat(a), Div.one(S.U64.to_nat(a)))
    case 1n+p:
      +q = p
      %Equal.sym(Nat, S.U64.to_nat(S.U64.shr1(S.U64.shrn(q, a))), S.Dec.half(S.U64.to_nat(S.U64.shrn(q, a))), U64.shr1_nat(S.U64.shrn(q, a))) : {_ == Nat.div(S.U64.to_nat(a), Nat.pow(2n, 1n+q)) : Nat}
      %Equal.sym(Nat, S.U64.to_nat(S.U64.shrn(q, a)), Nat.div(S.U64.to_nat(a), Nat.pow(2n, q)), U64.shrn_nat(q, a)) : {S.Dec.half(_) == Nat.div(S.U64.to_nat(a), Nat.pow(2n, 1n+q)) : Nat}
      Half.div(S.U64.to_nat(a), Nat.pow(2n, q), Pow.pos(q))
