# Lemmas for PROOF.bend: facts about Bool, Word, U32, U64 and B32 that Base
# does not prove.
import Base
import ../src/ssz.bend as S

# Bool
# ====

def Bool.cmp_refl(b: Bool) -> {EQ{} == Bool.cmp(b, b) : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# False == True and True == False have no proof.
def Bool.disc_t(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def Bool.disc_f(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def Bool.ft(h: {False{} == True{} : Bool}) -> Bool.disc_t(True{}):
  %h : Bool.disc_t(_)
  Unit{}

def Bool.tf(h: {True{} == False{} : Bool}) -> Bool.disc_f(False{}):
  %h : Bool.disc_f(_)
  Unit{}

# not (a || b) gives (not a) && (not b).
def Bool.nor(a: Bool, b: Bool, h: {Bool.not(Bool.or(a, b)) == True{} : Bool})
  -> {Bool.and(Bool.not(a), Bool.not(b)) == True{} : Bool}:
  match a b:
    case True{} True{}:
      Empty.absurd({Bool.and(Bool.not(True{}), Bool.not(True{})) == True{} : Bool}, Bool.ft(h))
    case True{} False{}:
      Empty.absurd({Bool.and(Bool.not(True{}), Bool.not(False{})) == True{} : Bool}, Bool.ft(h))
    case False{} True{}:
      Empty.absurd({Bool.and(Bool.not(False{}), Bool.not(True{})) == True{} : Bool}, Bool.ft(h))
    case False{} False{}:
      {==}

def Bool.and_tt(-a: Bool, -b: Bool, ea: {True{} == a : Bool}, eb: {True{} == b : Bool})
  -> {True{} == Bool.and(a, b) : Bool}:
  %ea : {True{} == Bool.and(_, b) : Bool}
  %eb : {True{} == Bool.and(True{}, _) : Bool}
  {==}

# Word
# ====

def Word.cmp_refl(n: Nat, +w: Word(n)) -> {EQ{} == Word.cmp(n, w, w) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          %Word.cmp_refl(p, t) : {EQ{} == Word.cmp.fin(b, b, _) : Cmp}
          Bool.cmp_refl(b)

# U32, U64, B32
# =============

def U32.cmp_refl(+a: U32) -> {EQ{} == U32.cmp(a, a) : Cmp}:
  match a:
    case U32{+w}:
      Word.cmp_refl(32n, w)

def U32.is_eq_refl(+a: U32) -> {True{} == U32.is_eq(a, a) : Bool}:
  %U32.cmp_refl(a) : {True{} == Cmp.is_eq(_) : Bool}
  {==}

def U64.cmp_refl(+a: S.U64) -> {EQ{} == S.U64.cmp(a, a) : Cmp}:
  match a:
    case S.U64{+h, +l}:
      %U32.cmp_refl(h) : {EQ{} == S.U64.cmp.lo(_, U32.cmp(l, l)) : Cmp}
      %U32.cmp_refl(l) : {EQ{} == S.U64.cmp.lo(EQ{}, _) : Cmp}
      {==}

def B32.is_eq_refl(+x: S.B32) -> {True{} == S.B32.is_eq(x, x) : Bool}:
  match x:
    case S.B32{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      Bool.and_tt(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(U32.is_eq(a0, a0), U32.is_eq(a1, a1)), U32.is_eq(a2, a2)), U32.is_eq(a3, a3)), U32.is_eq(a4, a4)), U32.is_eq(a5, a5)), U32.is_eq(a6, a6)), U32.is_eq(a7, a7),
        Bool.and_tt(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(U32.is_eq(a0, a0), U32.is_eq(a1, a1)), U32.is_eq(a2, a2)), U32.is_eq(a3, a3)), U32.is_eq(a4, a4)), U32.is_eq(a5, a5)), U32.is_eq(a6, a6),
        Bool.and_tt(Bool.and(Bool.and(Bool.and(Bool.and(U32.is_eq(a0, a0), U32.is_eq(a1, a1)), U32.is_eq(a2, a2)), U32.is_eq(a3, a3)), U32.is_eq(a4, a4)), U32.is_eq(a5, a5),
        Bool.and_tt(Bool.and(Bool.and(Bool.and(U32.is_eq(a0, a0), U32.is_eq(a1, a1)), U32.is_eq(a2, a2)), U32.is_eq(a3, a3)), U32.is_eq(a4, a4),
        Bool.and_tt(Bool.and(Bool.and(U32.is_eq(a0, a0), U32.is_eq(a1, a1)), U32.is_eq(a2, a2)), U32.is_eq(a3, a3),
        Bool.and_tt(Bool.and(U32.is_eq(a0, a0), U32.is_eq(a1, a1)), U32.is_eq(a2, a2),
        Bool.and_tt(U32.is_eq(a0, a0), U32.is_eq(a1, a1),
        U32.is_eq_refl(a0),
        U32.is_eq_refl(a1)),
        U32.is_eq_refl(a2)),
        U32.is_eq_refl(a3)),
        U32.is_eq_refl(a4)),
        U32.is_eq_refl(a5)),
        U32.is_eq_refl(a6)),
        U32.is_eq_refl(a7))

# Equality from is_eq
# ===================

# Empty at EQ, Unit elsewhere.
def Cmp.disc_eq(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Empty
    case GT{}:
      Unit

# LT == EQ and GT == EQ have no proof.
def Cmp.lt_eq(h: {LT{} == EQ{} : Cmp}) -> Cmp.disc_eq(EQ{}):
  %h : Cmp.disc_eq(_)
  Unit{}

def Cmp.gt_eq(h: {GT{} == EQ{} : Cmp}) -> Cmp.disc_eq(EQ{}):
  %h : Cmp.disc_eq(_)
  Unit{}

# A cmp.fin that answers EQ had EQ from the tail and equal head bits.
def Word.fin_eq(t: Cmp, ab: Bool, bb: Bool, h: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp})
  -> {t == EQ{} : Cmp} & {ab == bb : Bool}:
  match t:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp} & {ab == bb : Bool}, Cmp.lt_eq(h))
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp} & {ab == bb : Bool}, Cmp.gt_eq(h))
    case EQ{}:
      match ab bb:
        case True{} True{}:
          ({==}, {==})
        case False{} False{}:
          ({==}, {==})
        case True{} False{}:
          Empty.absurd({EQ{} == EQ{} : Cmp} & {True{} == False{} : Bool}, Cmp.gt_eq(h))
        case False{} True{}:
          Empty.absurd({EQ{} == EQ{} : Cmp} & {False{} == True{} : Bool}, Cmp.lt_eq(h))

def Word.cmp_eq.con(p: Nat, -ab: Bool, -bb: Bool, -at: Word(p), -bt: Word(p),
  pr: {Word.cmp(p, at, bt) == EQ{} : Cmp} & {ab == bb : Bool},
  ih: {Word.cmp(p, at, bt) == EQ{} : Cmp} -> {at == bt : Word(p)})
  -> {WCon{ab, at} == WCon{bb, bt} : Word(1n+p)}:
  (e1, e2) = pr
  %e2 : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
  %ih(e1) : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
  {==}

# A Word.cmp that answers EQ compares two equal words.
def Word.cmp_eq(+n: Nat, +a: Word(n), +b: Word(n), h: {Word.cmp(n, a, b) == EQ{} : Cmp}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          Word.cmp_eq.con(p, ab, bb, at, bt, Word.fin_eq(Word.cmp(p, at, bt), ab, bb, h), Word.cmp_eq(p, at, bt))

def Cmp.is_eq_true(c: Cmp, h: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, Bool.ft(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, Bool.ft(h))

def U32.eq_of(+a: U32, +b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      %Word.cmp_eq(32n, x, y, Cmp.is_eq_true(Word.cmp(32n, x, y), h)) : {U32{x} == U32{_} : U32}
      {==}

def Bool.and_true(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool} & {b == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & {b == True{} : Bool}, Bool.ft(h))
    case True{}:
      ({==}, h)

def B32.eq_words(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32, +b5: U32, +b6: U32, +b7: U32, e0: {a0 == b0 : U32}, e1: {a1 == b1 : U32}, e2: {a2 == b2 : U32}, e3: {a3 == b3 : U32}, e4: {a4 == b4 : U32}, e5: {a5 == b5 : U32}, e6: {a6 == b6 : U32}, e7: {a7 == b7 : U32})
  -> {S.B32{a0, a1, a2, a3, a4, a5, a6, a7} == S.B32{b0, b1, b2, b3, b4, b5, b6, b7} : S.B32}:
  %e0 : {S.B32{a0, a1, a2, a3, a4, a5, a6, a7} == S.B32{_, b1, b2, b3, b4, b5, b6, b7} : S.B32}
  %e1 : {S.B32{a0, a1, a2, a3, a4, a5, a6, a7} == S.B32{a0, _, b2, b3, b4, b5, b6, b7} : S.B32}
  %e2 : {S.B32{a0, a1, a2, a3, a4, a5, a6, a7} == S.B32{a0, a1, _, b3, b4, b5, b6, b7} : S.B32}
  %e3 : {S.B32{a0, a1, a2, a3, a4, a5, a6, a7} == S.B32{a0, a1, a2, _, b4, b5, b6, b7} : S.B32}
  %e4 : {S.B32{a0, a1, a2, a3, a4, a5, a6, a7} == S.B32{a0, a1, a2, a3, _, b5, b6, b7} : S.B32}
  %e5 : {S.B32{a0, a1, a2, a3, a4, a5, a6, a7} == S.B32{a0, a1, a2, a3, a4, _, b6, b7} : S.B32}
  %e6 : {S.B32{a0, a1, a2, a3, a4, a5, a6, a7} == S.B32{a0, a1, a2, a3, a4, a5, _, b7} : S.B32}
  %e7 : {S.B32{a0, a1, a2, a3, a4, a5, a6, a7} == S.B32{a0, a1, a2, a3, a4, a5, a6, _} : S.B32}
  {==}

def B32.split1(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32, +b5: U32, +b6: U32, +b7: U32, h: {U32.is_eq(a0, b0) == True{} : Bool}, e1: {a1 == b1 : U32}, e2: {a2 == b2 : U32}, e3: {a3 == b3 : U32}, e4: {a4 == b4 : U32}, e5: {a5 == b5 : U32}, e6: {a6 == b6 : U32}, e7: {a7 == b7 : U32})
  -> {S.B32{a0, a1, a2, a3, a4, a5, a6, a7} == S.B32{b0, b1, b2, b3, b4, b5, b6, b7} : S.B32}:
  B32.eq_words(a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7, U32.eq_of(a0, b0, h), e1, e2, e3, e4, e5, e6, e7)

def B32.split2(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32, +b5: U32, +b6: U32, +b7: U32, pr: {U32.is_eq(a0, b0) == True{} : Bool} & {U32.is_eq(a1, b1) == True{} : Bool}, e2: {a2 == b2 : U32}, e3: {a3 == b3 : U32}, e4: {a4 == b4 : U32}, e5: {a5 == b5 : U32}, e6: {a6 == b6 : U32}, e7: {a7 == b7 : U32})
  -> {S.B32{a0, a1, a2, a3, a4, a5, a6, a7} == S.B32{b0, b1, b2, b3, b4, b5, b6, b7} : S.B32}:
  (hl, hr) = pr
  B32.split1(a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7, hl, U32.eq_of(a1, b1, hr), e2, e3, e4, e5, e6, e7)

def B32.split3(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32, +b5: U32, +b6: U32, +b7: U32, pr: {Bool.and(U32.is_eq(a0, b0), U32.is_eq(a1, b1)) == True{} : Bool} & {U32.is_eq(a2, b2) == True{} : Bool}, e3: {a3 == b3 : U32}, e4: {a4 == b4 : U32}, e5: {a5 == b5 : U32}, e6: {a6 == b6 : U32}, e7: {a7 == b7 : U32})
  -> {S.B32{a0, a1, a2, a3, a4, a5, a6, a7} == S.B32{b0, b1, b2, b3, b4, b5, b6, b7} : S.B32}:
  (hl, hr) = pr
  B32.split2(a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7, Bool.and_true(U32.is_eq(a0, b0), U32.is_eq(a1, b1), hl), U32.eq_of(a2, b2, hr), e3, e4, e5, e6, e7)

def B32.split4(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32, +b5: U32, +b6: U32, +b7: U32, pr: {Bool.and(Bool.and(U32.is_eq(a0, b0), U32.is_eq(a1, b1)), U32.is_eq(a2, b2)) == True{} : Bool} & {U32.is_eq(a3, b3) == True{} : Bool}, e4: {a4 == b4 : U32}, e5: {a5 == b5 : U32}, e6: {a6 == b6 : U32}, e7: {a7 == b7 : U32})
  -> {S.B32{a0, a1, a2, a3, a4, a5, a6, a7} == S.B32{b0, b1, b2, b3, b4, b5, b6, b7} : S.B32}:
  (hl, hr) = pr
  B32.split3(a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7, Bool.and_true(Bool.and(U32.is_eq(a0, b0), U32.is_eq(a1, b1)), U32.is_eq(a2, b2), hl), U32.eq_of(a3, b3, hr), e4, e5, e6, e7)

def B32.split5(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32, +b5: U32, +b6: U32, +b7: U32, pr: {Bool.and(Bool.and(Bool.and(U32.is_eq(a0, b0), U32.is_eq(a1, b1)), U32.is_eq(a2, b2)), U32.is_eq(a3, b3)) == True{} : Bool} & {U32.is_eq(a4, b4) == True{} : Bool}, e5: {a5 == b5 : U32}, e6: {a6 == b6 : U32}, e7: {a7 == b7 : U32})
  -> {S.B32{a0, a1, a2, a3, a4, a5, a6, a7} == S.B32{b0, b1, b2, b3, b4, b5, b6, b7} : S.B32}:
  (hl, hr) = pr
  B32.split4(a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7, Bool.and_true(Bool.and(Bool.and(U32.is_eq(a0, b0), U32.is_eq(a1, b1)), U32.is_eq(a2, b2)), U32.is_eq(a3, b3), hl), U32.eq_of(a4, b4, hr), e5, e6, e7)

def B32.split6(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32, +b5: U32, +b6: U32, +b7: U32, pr: {Bool.and(Bool.and(Bool.and(Bool.and(U32.is_eq(a0, b0), U32.is_eq(a1, b1)), U32.is_eq(a2, b2)), U32.is_eq(a3, b3)), U32.is_eq(a4, b4)) == True{} : Bool} & {U32.is_eq(a5, b5) == True{} : Bool}, e6: {a6 == b6 : U32}, e7: {a7 == b7 : U32})
  -> {S.B32{a0, a1, a2, a3, a4, a5, a6, a7} == S.B32{b0, b1, b2, b3, b4, b5, b6, b7} : S.B32}:
  (hl, hr) = pr
  B32.split5(a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7, Bool.and_true(Bool.and(Bool.and(Bool.and(U32.is_eq(a0, b0), U32.is_eq(a1, b1)), U32.is_eq(a2, b2)), U32.is_eq(a3, b3)), U32.is_eq(a4, b4), hl), U32.eq_of(a5, b5, hr), e6, e7)

def B32.split7(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32, +b5: U32, +b6: U32, +b7: U32, pr: {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(U32.is_eq(a0, b0), U32.is_eq(a1, b1)), U32.is_eq(a2, b2)), U32.is_eq(a3, b3)), U32.is_eq(a4, b4)), U32.is_eq(a5, b5)) == True{} : Bool} & {U32.is_eq(a6, b6) == True{} : Bool}, e7: {a7 == b7 : U32})
  -> {S.B32{a0, a1, a2, a3, a4, a5, a6, a7} == S.B32{b0, b1, b2, b3, b4, b5, b6, b7} : S.B32}:
  (hl, hr) = pr
  B32.split6(a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7, Bool.and_true(Bool.and(Bool.and(Bool.and(Bool.and(U32.is_eq(a0, b0), U32.is_eq(a1, b1)), U32.is_eq(a2, b2)), U32.is_eq(a3, b3)), U32.is_eq(a4, b4)), U32.is_eq(a5, b5), hl), U32.eq_of(a6, b6, hr), e7)

def B32.split8(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32, +b5: U32, +b6: U32, +b7: U32, pr: {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(U32.is_eq(a0, b0), U32.is_eq(a1, b1)), U32.is_eq(a2, b2)), U32.is_eq(a3, b3)), U32.is_eq(a4, b4)), U32.is_eq(a5, b5)), U32.is_eq(a6, b6)) == True{} : Bool} & {U32.is_eq(a7, b7) == True{} : Bool})
  -> {S.B32{a0, a1, a2, a3, a4, a5, a6, a7} == S.B32{b0, b1, b2, b3, b4, b5, b6, b7} : S.B32}:
  (hl, hr) = pr
  B32.split7(a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7, Bool.and_true(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(U32.is_eq(a0, b0), U32.is_eq(a1, b1)), U32.is_eq(a2, b2)), U32.is_eq(a3, b3)), U32.is_eq(a4, b4)), U32.is_eq(a5, b5)), U32.is_eq(a6, b6), hl), U32.eq_of(a7, b7, hr))

def B32.eq_of(+a: S.B32, +b: S.B32, h: {S.B32.is_eq(a, b) == True{} : Bool}) -> {a == b : S.B32}:
  match a b:
    case S.B32{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7} S.B32{+b0, +b1, +b2, +b3, +b4, +b5, +b6, +b7}:
      B32.split8(a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7, Bool.and_true(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(U32.is_eq(a0, b0), U32.is_eq(a1, b1)), U32.is_eq(a2, b2)), U32.is_eq(a3, b3)), U32.is_eq(a4, b4)), U32.is_eq(a5, b5)), U32.is_eq(a6, b6)), U32.is_eq(a7, b7), h))

def B16.eq_words(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, e0: {a0 == b0 : U32}, e1: {a1 == b1 : U32}, e2: {a2 == b2 : U32}, e3: {a3 == b3 : U32})
  -> {S.B16{a0, a1, a2, a3} == S.B16{b0, b1, b2, b3} : S.B16}:
  %e0 : {S.B16{a0, a1, a2, a3} == S.B16{_, b1, b2, b3} : S.B16}
  %e1 : {S.B16{a0, a1, a2, a3} == S.B16{a0, _, b2, b3} : S.B16}
  %e2 : {S.B16{a0, a1, a2, a3} == S.B16{a0, a1, _, b3} : S.B16}
  %e3 : {S.B16{a0, a1, a2, a3} == S.B16{a0, a1, a2, _} : S.B16}
  {==}

def B16.split1(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, h: {U32.is_eq(a0, b0) == True{} : Bool}, e1: {a1 == b1 : U32}, e2: {a2 == b2 : U32}, e3: {a3 == b3 : U32})
  -> {S.B16{a0, a1, a2, a3} == S.B16{b0, b1, b2, b3} : S.B16}:
  B16.eq_words(a0, a1, a2, a3, b0, b1, b2, b3, U32.eq_of(a0, b0, h), e1, e2, e3)

def B16.split2(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, pr: {U32.is_eq(a0, b0) == True{} : Bool} & {U32.is_eq(a1, b1) == True{} : Bool}, e2: {a2 == b2 : U32}, e3: {a3 == b3 : U32})
  -> {S.B16{a0, a1, a2, a3} == S.B16{b0, b1, b2, b3} : S.B16}:
  (hl, hr) = pr
  B16.split1(a0, a1, a2, a3, b0, b1, b2, b3, hl, U32.eq_of(a1, b1, hr), e2, e3)

def B16.split3(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, pr: {Bool.and(U32.is_eq(a0, b0), U32.is_eq(a1, b1)) == True{} : Bool} & {U32.is_eq(a2, b2) == True{} : Bool}, e3: {a3 == b3 : U32})
  -> {S.B16{a0, a1, a2, a3} == S.B16{b0, b1, b2, b3} : S.B16}:
  (hl, hr) = pr
  B16.split2(a0, a1, a2, a3, b0, b1, b2, b3, Bool.and_true(U32.is_eq(a0, b0), U32.is_eq(a1, b1), hl), U32.eq_of(a2, b2, hr), e3)

def B16.split4(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, pr: {Bool.and(Bool.and(U32.is_eq(a0, b0), U32.is_eq(a1, b1)), U32.is_eq(a2, b2)) == True{} : Bool} & {U32.is_eq(a3, b3) == True{} : Bool})
  -> {S.B16{a0, a1, a2, a3} == S.B16{b0, b1, b2, b3} : S.B16}:
  (hl, hr) = pr
  B16.split3(a0, a1, a2, a3, b0, b1, b2, b3, Bool.and_true(Bool.and(U32.is_eq(a0, b0), U32.is_eq(a1, b1)), U32.is_eq(a2, b2), hl), U32.eq_of(a3, b3, hr))

def B16.eq_of(+a: S.B16, +b: S.B16, h: {S.B16.is_eq(a, b) == True{} : Bool}) -> {a == b : S.B16}:
  match a b:
    case S.B16{+a0, +a1, +a2, +a3} S.B16{+b0, +b1, +b2, +b3}:
      B16.split4(a0, a1, a2, a3, b0, b1, b2, b3, Bool.and_true(Bool.and(Bool.and(U32.is_eq(a0, b0), U32.is_eq(a1, b1)), U32.is_eq(a2, b2)), U32.is_eq(a3, b3), h))

def Pubkey.eq_of.pair(+ah: S.B32, +al: S.B16, +bh: S.B32, +bl: S.B16,
  pr: {S.B32.is_eq(ah, bh) == True{} : Bool} & {S.B16.is_eq(al, bl) == True{} : Bool})
  -> {S.Pubkey{ah, al} == S.Pubkey{bh, bl} : S.Pubkey}:
  (h1, h2) = pr
  %B32.eq_of(ah, bh, h1) : {S.Pubkey{ah, al} == S.Pubkey{_, bl} : S.Pubkey}
  %B16.eq_of(al, bl, h2) : {S.Pubkey{ah, al} == S.Pubkey{ah, _} : S.Pubkey}
  {==}

def Pubkey.eq_of(+a: S.Pubkey, +b: S.Pubkey, h: {S.Pubkey.is_eq(a, b) == True{} : Bool}) -> {a == b : S.Pubkey}:
  match a b:
    case S.Pubkey{+ah, +al} S.Pubkey{+bh, +bl}:
      Pubkey.eq_of.pair(ah, al, bh, bl, Bool.and_true(S.B32.is_eq(ah, bh), S.B16.is_eq(al, bl), h))

def B16.is_eq_refl(+x: S.B16) -> {True{} == S.B16.is_eq(x, x) : Bool}:
  match x:
    case S.B16{+a0, +a1, +a2, +a3}:
      Bool.and_tt(Bool.and(Bool.and(U32.is_eq(a0, a0), U32.is_eq(a1, a1)), U32.is_eq(a2, a2)), U32.is_eq(a3, a3),
        Bool.and_tt(Bool.and(U32.is_eq(a0, a0), U32.is_eq(a1, a1)), U32.is_eq(a2, a2),
          Bool.and_tt(U32.is_eq(a0, a0), U32.is_eq(a1, a1), U32.is_eq_refl(a0), U32.is_eq_refl(a1)),
          U32.is_eq_refl(a2)),
        U32.is_eq_refl(a3))

def Pubkey.is_eq_refl(+k: S.Pubkey) -> {True{} == S.Pubkey.is_eq(k, k) : Bool}:
  match k:
    case S.Pubkey{+h, +l}:
      Bool.and_tt(S.B32.is_eq(h, h), S.B16.is_eq(l, l), B32.is_eq_refl(h), B16.is_eq_refl(l))
