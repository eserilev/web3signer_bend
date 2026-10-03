# Lemmas for the log laws event_roundtrip and log_roundtrip. A line splits
# at a separator only where the writer put one: the pieces it writes (hex,
# decimal, "-") hold no space and no newline.
import Base
import ../src/ssz.bend as S
import ../src/store.bend as St
import ../src/slashing.bend as Slash
import ./lemmas.bend as Lm
import ./num.bend as N
import ./dec.bend as Dec
import ./hex.bend as H

# s holds no sep character.
def NoSep(s: String, +sep: U32) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      match c:
        case Chr{x}:
          Bool.and(Bool.not(U32.is_eq(x, sep)), NoSep(t, sep))

# s holds no space and no newline.
def Clean(+s: String) -> Bool:
  Bool.and(NoSep(s, 32), NoSep(s, 10))

def Not.t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Lm.Bool.ft(h))
    case False{}:
      {==}

def Clean.ns32(+s: String, h: {Clean(s) == True{} : Bool}) -> {NoSep(s, 32) == True{} : Bool}:
  Dec.Pf.fst({NoSep(s, 32) == True{} : Bool}, {NoSep(s, 10) == True{} : Bool}, Lm.Bool.and_true(NoSep(s, 32), NoSep(s, 10), h))

def Clean.ns10(+s: String, h: {Clean(s) == True{} : Bool}) -> {NoSep(s, 10) == True{} : Bool}:
  Dec.Pf.snd({NoSep(s, 32) == True{} : Bool}, {NoSep(s, 10) == True{} : Bool}, Lm.Bool.and_true(NoSep(s, 32), NoSep(s, 10), h))

# Pieces
# ======

def Pieces.cut(s: String, +t: String, +sep: U32, h: {NoSep(s, sep) == True{} : Bool})
  -> {St.Pieces(String.append(s, SCon{Chr{sep}, t}), sep) == Con{s, St.Pieces(t, sep)} : List<&2, String>}:
  match s:
    case SNil{}:
      %Lm.U32.is_eq_refl(sep) : {St.Pieces.add(_, Chr{sep}, St.Pieces(t, sep)) == Con{"", St.Pieces(t, sep)} : List<&2, String>}
      {==}
    case SCon{c, r}:
      match c:
        case Chr{+x}:
          +r1 = r
          +hp = h
          %Equal.sym(Bool, U32.is_eq(x, sep), False{}, Not.t(U32.is_eq(x, sep), Dec.Pf.fst({Bool.not(U32.is_eq(x, sep)) == True{} : Bool}, {NoSep(r1, sep) == True{} : Bool}, Lm.Bool.and_true(Bool.not(U32.is_eq(x, sep)), NoSep(r1, sep), hp)))) : {St.Pieces.add(_, Chr{x}, St.Pieces(String.append(r1, SCon{Chr{sep}, t}), sep)) == Con{SCon{Chr{x}, r1}, St.Pieces(t, sep)} : List<&2, String>}
          %Equal.sym(List<&2, String>, St.Pieces(String.append(r1, SCon{Chr{sep}, t}), sep), Con{r1, St.Pieces(t, sep)}, Pieces.cut(r1, t, sep, Dec.Pf.snd({Bool.not(U32.is_eq(x, sep)) == True{} : Bool}, {NoSep(r1, sep) == True{} : Bool}, Lm.Bool.and_true(Bool.not(U32.is_eq(x, sep)), NoSep(r1, sep), hp)))) : {St.Piece.cons(Chr{x}, _) == Con{SCon{Chr{x}, r1}, St.Pieces(t, sep)} : List<&2, String>}
          {==}

def Pieces.whole(s: String, +sep: U32, h: {NoSep(s, sep) == True{} : Bool}) -> {St.Pieces(s, sep) == [s] : List<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, r}:
      match c:
        case Chr{+x}:
          +r1 = r
          +hp = h
          %Equal.sym(Bool, U32.is_eq(x, sep), False{}, Not.t(U32.is_eq(x, sep), Dec.Pf.fst({Bool.not(U32.is_eq(x, sep)) == True{} : Bool}, {NoSep(r1, sep) == True{} : Bool}, Lm.Bool.and_true(Bool.not(U32.is_eq(x, sep)), NoSep(r1, sep), hp)))) : {St.Pieces.add(_, Chr{x}, St.Pieces(r1, sep)) == [SCon{Chr{x}, r1}] : List<&2, String>}
          %Equal.sym(List<&2, String>, St.Pieces(r1, sep), [r1], Pieces.whole(r1, sep, Dec.Pf.snd({Bool.not(U32.is_eq(x, sep)) == True{} : Bool}, {NoSep(r1, sep) == True{} : Bool}, Lm.Bool.and_true(Bool.not(U32.is_eq(x, sep)), NoSep(r1, sep), hp)))) : {St.Piece.cons(Chr{x}, _) == [SCon{Chr{x}, r1}] : List<&2, String>}
          {==}

def NoSep.app(a: String, +b: String, +sep: U32, ha: {NoSep(a, sep) == True{} : Bool}, hb: {NoSep(b, sep) == True{} : Bool})
  -> {NoSep(String.append(a, b), sep) == True{} : Bool}:
  match a:
    case SNil{}:
      hb
    case SCon{c, r}:
      match c:
        case Chr{+x}:
          +r1 = r
          +hp = ha
          Dec.And.intro(Bool.not(U32.is_eq(x, sep)), NoSep(String.append(r1, b), sep),
            Dec.Pf.fst({Bool.not(U32.is_eq(x, sep)) == True{} : Bool}, {NoSep(r1, sep) == True{} : Bool}, Lm.Bool.and_true(Bool.not(U32.is_eq(x, sep)), NoSep(r1, sep), hp)),
            NoSep.app(r1, b, sep, Dec.Pf.snd({Bool.not(U32.is_eq(x, sep)) == True{} : Bool}, {NoSep(r1, sep) == True{} : Bool}, Lm.Bool.and_true(Bool.not(U32.is_eq(x, sep)), NoSep(r1, sep), hp)), hb))

def Clean.app(+a: String, +b: String, ha: {Clean(a) == True{} : Bool}, hb: {Clean(b) == True{} : Bool}) -> {Clean(String.append(a, b)) == True{} : Bool}:
  +ha1 = ha
  +hb1 = hb
  Dec.And.intro(NoSep(String.append(a, b), 32), NoSep(String.append(a, b), 10),
    NoSep.app(a, b, 32, Clean.ns32(a, ha1), Clean.ns32(b, hb1)),
    NoSep.app(a, b, 10, Clean.ns10(a, ha1), Clean.ns10(b, hb1)))

# Clean writers
# =============

def Clean.nib(b0: Bool, b1: Bool, b2: Bool, b3: Bool, +acc: String, h: {Clean(acc) == True{} : Bool})
  -> {Clean(SCon{S.Hex.nib(b0, b1, b2, b3), acc}) == True{} : Bool}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      h
    case True{} False{} False{} False{}:
      h
    case False{} True{} False{} False{}:
      h
    case True{} True{} False{} False{}:
      h
    case False{} False{} True{} False{}:
      h
    case True{} False{} True{} False{}:
      h
    case False{} True{} True{} False{}:
      h
    case True{} True{} True{} False{}:
      h
    case False{} False{} False{} True{}:
      h
    case True{} False{} False{} True{}:
      h
    case False{} True{} False{} True{}:
      h
    case True{} True{} False{} True{}:
      h
    case False{} False{} True{} True{}:
      h
    case True{} False{} True{} True{}:
      h
    case False{} True{} True{} True{}:
      h
    case True{} True{} True{} True{}:
      h

def Clean.ws(g: Nat, w: Word(Nat.mul(g, 4n)), +acc: String, h: {Clean(acc) == True{} : Bool}) -> {Clean(S.Hex.ws(g, w, acc)) == True{} : Bool}:
  match g:
    case 0n:
      h
    case 1n+q:
      match w:
        case WCon{+b0, t0}:
          match t0:
            case WCon{+b1, t1}:
              match t1:
                case WCon{+b2, t2}:
                  match t2:
                    case WCon{+b3, t}:
                      Clean.ws(q, t, SCon{S.Hex.nib(b0, b1, b2, b3), acc}, Clean.nib(b0, b1, b2, b3, acc, h))

def Clean.word(a: U32, +acc: String, h: {Clean(acc) == True{} : Bool}) -> {Clean(S.Hex.word(a, acc)) == True{} : Bool}:
  match a:
    case U32{x}:
      Clean.ws(8n, x, acc, h)

def Clean.b32(x: S.B32) -> {Clean(S.Hex.b32(x)) == True{} : Bool}:
  match x:
    case S.B32{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      Clean.word(a0, S.Hex.word(a1, S.Hex.word(a2, S.Hex.word(a3, S.Hex.word(a4, S.Hex.word(a5, S.Hex.word(a6, S.Hex.word(a7, ""))))))), Clean.word(a1, S.Hex.word(a2, S.Hex.word(a3, S.Hex.word(a4, S.Hex.word(a5, S.Hex.word(a6, S.Hex.word(a7, "")))))), Clean.word(a2, S.Hex.word(a3, S.Hex.word(a4, S.Hex.word(a5, S.Hex.word(a6, S.Hex.word(a7, ""))))), Clean.word(a3, S.Hex.word(a4, S.Hex.word(a5, S.Hex.word(a6, S.Hex.word(a7, "")))), Clean.word(a4, S.Hex.word(a5, S.Hex.word(a6, S.Hex.word(a7, ""))), Clean.word(a5, S.Hex.word(a6, S.Hex.word(a7, "")), Clean.word(a6, S.Hex.word(a7, ""), Clean.word(a7, "", {==}))))))))

def Clean.pubkey(k: S.Pubkey) -> {Clean(S.Hex.pubkey(k)) == True{} : Bool}:
  match k:
    case S.Pubkey{+hi, lo}:
      match lo:
        case S.B16{+l0, +l1, +l2, +l3}:
          Clean.app(S.Hex.b32(hi), S.Hex.word(l0, S.Hex.word(l1, S.Hex.word(l2, S.Hex.word(l3, "")))), Clean.b32(hi),
            Clean.word(l0, S.Hex.word(l1, S.Hex.word(l2, S.Hex.word(l3, ""))), Clean.word(l1, S.Hex.word(l2, S.Hex.word(l3, "")), Clean.word(l2, S.Hex.word(l3, ""), Clean.word(l3, "", {==})))))

def Clean.char(d: Nat, +acc: String, h: {Clean(acc) == True{} : Bool}) -> {Clean(SCon{S.Dec.char(d), acc}) == True{} : Bool}:
  match d:
    case 0n:
      h
    case 1n+d1:
      match d1:
        case 0n:
          h
        case 1n+d2:
          match d2:
            case 0n:
              h
            case 1n+d3:
              match d3:
                case 0n:
                  h
                case 1n+d4:
                  match d4:
                    case 0n:
                      h
                    case 1n+d5:
                      match d5:
                        case 0n:
                          h
                        case 1n+d6:
                          match d6:
                            case 0n:
                              h
                            case 1n+d7:
                              match d7:
                                case 0n:
                                  h
                                case 1n+d8:
                                  match d8:
                                    case 0n:
                                      h
                                    case 1n+d9:
                                      match d9:
                                        case 0n:
                                          h
                                        case 1n+d10:
                                          h

def Clean.str(ds: List<&2, Nat>, +acc: String, h: {Clean(acc) == True{} : Bool}) -> {Clean(S.Dec.str(ds, acc)) == True{} : Bool}:
  match ds:
    case Nil{}:
      h
    case Con{+d, r}:
      Clean.str(r, SCon{S.Dec.char(d), acc}, Clean.char(d, acc, h))

def Clean.dshow(ds: List<&2, Nat>) -> {Clean(S.Dec.show(ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, r}:
      Clean.str(Con{d, r}, "", {==})

def Clean.u64(a: S.U64) -> {Clean(S.U64.show(a)) == True{} : Bool}:
  Clean.dshow(S.Dec.of_bits(64n, S.U64.bits(a), []))

def Clean.root(r: Maybe<&2, S.B32>) -> {Clean(St.Log.root(r)) == True{} : Bool}:
  match r:
    case None{}:
      {==}
    case Some{x}:
      Clean.b32(x)

# Pubkey
# ======
#
# A pubkey is 12 words of hex. Wl writes a list of words, Bl reads their
# bits back, last word first.

def Wl(ws: List<&2, Word(32n)>, s: String) -> String:
  match ws:
    case Nil{}:
      s
    case Con{w, r}:
      S.Hex.ws(8n, w, Wl(r, s))

def Bl(ws: List<&2, Word(32n)>, acc: List<&2, Bool>) -> List<&2, Bool>:
  match ws:
    case Nil{}:
      acc
    case Con{w, r}:
      Bl(r, List.append(&2, Bool, S.Word.to_list(32n, w), acc))

def Wc(ws: List<&2, Word(32n)>, j: Nat) -> Nat:
  match ws:
    case Nil{}:
      j
    case Con{w, r}:
      Nat.add(8n, Wc(r, j))

def Ap(ws: List<&2, Word(32n)>, acc: List<&2, Bool>) -> List<&2, Bool>:
  match ws:
    case Nil{}:
      acc
    case Con{w, r}:
      List.append(&2, Bool, S.Word.to_list(32n, w), Ap(r, acc))

def Len(ws: List<&2, Word(32n)>) -> Nat:
  match ws:
    case Nil{}:
      0n
    case Con{w, r}:
      1n+Len(r)

def Ws.app(g: Nat, w: Word(Nat.mul(g, 4n)), +acc: String, +t: String)
  -> {String.append(S.Hex.ws(g, w, acc), t) == S.Hex.ws(g, w, String.append(acc, t)) : String}:
  match g:
    case 0n:
      {==}
    case 1n+q:
      match w:
        case WCon{+b0, t0}:
          match t0:
            case WCon{+b1, t1}:
              match t1:
                case WCon{+b2, t2}:
                  match t2:
                    case WCon{+b3, r}:
                      Ws.app(q, r, SCon{S.Hex.nib(b0, b1, b2, b3), acc}, t)

def Wl.app(ws: List<&2, Word(32n)>, +s: String, +t: String) -> {String.append(Wl(ws, s), t) == Wl(ws, String.append(s, t)) : String}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, r}:
      +r1 = r
      Equal.trans(String, String.append(S.Hex.ws(8n, w, Wl(r1, s)), t), S.Hex.ws(8n, w, String.append(Wl(r1, s), t)), S.Hex.ws(8n, w, Wl(r1, String.append(s, t))),
        Ws.app(8n, w, Wl(r1, s), t),
        Equal.cong(String, String, y => S.Hex.ws(8n, w, y), String.append(Wl(r1, s), t), Wl(r1, String.append(s, t)), Wl.app(r1, s, t)))

def Rd.wl(ws: List<&2, Word(32n)>, +j: Nat, +s: String, +acc: List<&2, Bool>) -> {S.Hex.rd(Wc(ws, j), Wl(ws, s), acc) == S.Hex.rd(j, s, Bl(ws, acc)) : Maybe<&2, S.HexRd>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, r}:
      +r1 = r
      Equal.trans(Maybe<&2, S.HexRd>, S.Hex.rd(Nat.add(8n, Wc(r1, j)), S.Hex.ws(8n, w, Wl(r1, s)), acc), S.Hex.rd(Wc(r1, j), Wl(r1, s), List.append(&2, Bool, S.Word.to_list(32n, w), acc)), S.Hex.rd(j, s, Bl(r1, List.append(&2, Bool, S.Word.to_list(32n, w), acc))),
        H.Rd.ws(8n, Wc(r1, j), w, Wl(r1, s), acc),
        Rd.wl(r1, j, s, List.append(&2, Bool, S.Word.to_list(32n, w), acc)))

def Pick(pre: List<&2, Word(32n)>, +w: Word(32n), +r: List<&2, Bool>) -> {S.U32.of_list(Ap(pre, List.append(&2, Bool, S.Word.to_list(32n, w), r)), Len(pre)) == U32{w} : U32}:
  match pre:
    case Nil{}:
      H.U32.of_list.here(w, r)
    case Con{+p, rest}:
      +rest1 = rest
      Equal.trans(U32, S.U32.of_list(List.append(&2, Bool, S.Word.to_list(32n, p), Ap(rest1, List.append(&2, Bool, S.Word.to_list(32n, w), r))), 1n+Len(rest1)), S.U32.of_list(Ap(rest1, List.append(&2, Bool, S.Word.to_list(32n, w), r)), Len(rest1)), U32{w},
        H.U32.of_list.skip(p, Ap(rest1, List.append(&2, Bool, S.Word.to_list(32n, w), r)), Len(rest1)),
        Pick(rest1, w, r))

def Pk.words(+w0: Word(32n), +w1: Word(32n), +w2: Word(32n), +w3: Word(32n), +w4: Word(32n), +w5: Word(32n), +w6: Word(32n), +w7: Word(32n), +v0: Word(32n), +v1: Word(32n), +v2: Word(32n), +v3: Word(32n)) -> {S.Hex.read_pubkey(S.Hex.pubkey(S.Pubkey{S.B32{U32{w0}, U32{w1}, U32{w2}, U32{w3}, U32{w4}, U32{w5}, U32{w6}, U32{w7}}, S.B16{U32{v0}, U32{v1}, U32{v2}, U32{v3}}})) == Some{S.Pubkey{S.B32{U32{w0}, U32{w1}, U32{w2}, U32{w3}, U32{w4}, U32{w5}, U32{w6}, U32{w7}}, S.B16{U32{v0}, U32{v1}, U32{v2}, U32{v3}}}} : Maybe<&2, S.Pubkey>}:
  %Equal.sym(String, String.append(Wl([w0, w1, w2, w3, w4, w5, w6, w7], ""), Wl([v0, v1, v2, v3], "")), Wl([w0, w1, w2, w3, w4, w5, w6, w7], String.append("", Wl([v0, v1, v2, v3], ""))), Wl.app([w0, w1, w2, w3, w4, w5, w6, w7], "", Wl([v0, v1, v2, v3], ""))) : {S.Hex.read_pubkey.if(S.Hex.rd(96n, _, [])) == Some{S.Pubkey{S.B32{U32{w0}, U32{w1}, U32{w2}, U32{w3}, U32{w4}, U32{w5}, U32{w6}, U32{w7}}, S.B16{U32{v0}, U32{v1}, U32{v2}, U32{v3}}}} : Maybe<&2, S.Pubkey>}
  %Equal.sym(Maybe<&2, S.HexRd>, S.Hex.rd(Wc([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], 0n), Wl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], ""), []), S.Hex.rd(0n, "", Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], [])), Rd.wl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], 0n, "", [])) : {S.Hex.read_pubkey.if(_) == Some{S.Pubkey{S.B32{U32{w0}, U32{w1}, U32{w2}, U32{w3}, U32{w4}, U32{w5}, U32{w6}, U32{w7}}, S.B16{U32{v0}, U32{v1}, U32{v2}, U32{v3}}}} : Maybe<&2, S.Pubkey>}
  %Equal.sym(S.B32, S.B32{S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 11n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 10n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 9n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 8n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 7n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 6n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 5n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 4n)}, S.B32{U32{w0}, U32{w1}, U32{w2}, U32{w3}, U32{w4}, U32{w5}, U32{w6}, U32{w7}}, Lm.B32.eq_words(S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 11n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 10n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 9n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 8n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 7n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 6n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 5n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 4n), U32{w0}, U32{w1}, U32{w2}, U32{w3}, U32{w4}, U32{w5}, U32{w6}, U32{w7}, Pick([v3, v2, v1, v0, w7, w6, w5, w4, w3, w2, w1], w0, Ap([], [])), Pick([v3, v2, v1, v0, w7, w6, w5, w4, w3, w2], w1, Ap([w0], [])), Pick([v3, v2, v1, v0, w7, w6, w5, w4, w3], w2, Ap([w1, w0], [])), Pick([v3, v2, v1, v0, w7, w6, w5, w4], w3, Ap([w2, w1, w0], [])), Pick([v3, v2, v1, v0, w7, w6, w5], w4, Ap([w3, w2, w1, w0], [])), Pick([v3, v2, v1, v0, w7, w6], w5, Ap([w4, w3, w2, w1, w0], [])), Pick([v3, v2, v1, v0, w7], w6, Ap([w5, w4, w3, w2, w1, w0], [])), Pick([v3, v2, v1, v0], w7, Ap([w6, w5, w4, w3, w2, w1, w0], [])))) : {Some{S.Pubkey{_, S.B16{S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 3n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 2n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 1n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 0n)}}} == Some{S.Pubkey{S.B32{U32{w0}, U32{w1}, U32{w2}, U32{w3}, U32{w4}, U32{w5}, U32{w6}, U32{w7}}, S.B16{U32{v0}, U32{v1}, U32{v2}, U32{v3}}}} : Maybe<&2, S.Pubkey>}
  %Equal.sym(S.B16, S.B16{S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 3n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 2n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 1n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 0n)}, S.B16{U32{v0}, U32{v1}, U32{v2}, U32{v3}}, Lm.B16.eq_words(S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 3n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 2n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 1n), S.U32.of_list(Bl([w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3], []), 0n), U32{v0}, U32{v1}, U32{v2}, U32{v3}, Pick([v3, v2, v1], v0, Ap([w7, w6, w5, w4, w3, w2, w1, w0], [])), Pick([v3, v2], v1, Ap([v0, w7, w6, w5, w4, w3, w2, w1, w0], [])), Pick([v3], v2, Ap([v1, v0, w7, w6, w5, w4, w3, w2, w1, w0], [])), Pick([], v3, Ap([v2, v1, v0, w7, w6, w5, w4, w3, w2, w1, w0], [])))) : {Some{S.Pubkey{S.B32{U32{w0}, U32{w1}, U32{w2}, U32{w3}, U32{w4}, U32{w5}, U32{w6}, U32{w7}}, _}} == Some{S.Pubkey{S.B32{U32{w0}, U32{w1}, U32{w2}, U32{w3}, U32{w4}, U32{w5}, U32{w6}, U32{w7}}, S.B16{U32{v0}, U32{v1}, U32{v2}, U32{v3}}}} : Maybe<&2, S.Pubkey>}
  {==}

def Pk.u32(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +a8: U32, +a9: U32, +a10: U32, +a11: U32) -> {S.Hex.read_pubkey(S.Hex.pubkey(S.Pubkey{S.B32{a0, a1, a2, a3, a4, a5, a6, a7}, S.B16{a8, a9, a10, a11}})) == Some{S.Pubkey{S.B32{a0, a1, a2, a3, a4, a5, a6, a7}, S.B16{a8, a9, a10, a11}}} : Maybe<&2, S.Pubkey>}:
  match a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11:
    case U32{w0} U32{w1} U32{w2} U32{w3} U32{w4} U32{w5} U32{w6} U32{w7} U32{v0} U32{v1} U32{v2} U32{v3}:
      Pk.words(w0, w1, w2, w3, w4, w5, w6, w7, v0, v1, v2, v3)

def Pk.rt(+k: S.Pubkey) -> {S.Hex.read_pubkey(S.Hex.pubkey(k)) == Some{k} : Maybe<&2, S.Pubkey>}:
  match k:
    case S.Pubkey{hi, lo}:
      match hi lo:
        case S.B32{a0, a1, a2, a3, a4, a5, a6, a7} S.B16{a8, a9, a10, a11}:
          Pk.u32(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11)

# Events
# ======

def Rt(r: Maybe<&2, S.B32>) -> {St.Log.read_root(St.Log.root(r)) == Some{r} : Maybe<&2, Maybe<&2, S.B32>>}:
  match r:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case S.B32{+a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7}:
          %Equal.sym(Maybe<&2, S.B32>, S.Hex.read_b32(S.Hex.b32(S.B32{a0, a1, a2, a3, a4, a5, a6, a7})), Some{S.B32{a0, a1, a2, a3, a4, a5, a6, a7}}, H.B32.hex_rt(S.B32{a0, a1, a2, a3, a4, a5, a6, a7})) : {St.Log.some_root(_) == Some{Some{S.B32{a0, a1, a2, a3, a4, a5, a6, a7}}} : Maybe<&2, Maybe<&2, S.B32>>}
          {==}

def W.cut(+p: String, +t: String, h: {Clean(p) == True{} : Bool}) -> {St.Pieces(String.append(p, String.append(" ", t)), 32) == Con{p, St.Pieces(t, 32)} : List<&2, String>}:
  Pieces.cut(p, t, 32, Clean.ns32(p, h))

def W.last(+p: String, h: {Clean(p) == True{} : Bool}) -> {St.Pieces(p, 32) == [p] : List<&2, String>}:
  Pieces.whole(p, 32, Clean.ns32(p, h))

# A line reads back as its event.
def Ev.rt(e: St.LogEvent) -> {St.LogEvent.read(St.LogEvent.show(e)) == Some{e} : Maybe<&2, St.LogEvent>}:
  match e:
    case St.EGvr{+g}:
      %Equal.sym(List<&2, String>, St.Pieces(S.Hex.b32(g), 32), [S.Hex.b32(g)], W.last(S.Hex.b32(g), Clean.b32(g))) : {St.LogEvent.read.words(Con{"G", _}) == Some{St.EGvr{g}} : Maybe<&2, St.LogEvent>}
      %Equal.sym(Maybe<&2, S.B32>, S.Hex.read_b32(S.Hex.b32(g)), Some{g}, H.B32.hex_rt(g)) : {St.Log.read.g1(_) == Some{St.EGvr{g}} : Maybe<&2, St.LogEvent>}
      {==}
    case St.EBlock{+k, rec}:
      match rec:
        case Slash.BlockRec{+x, +r}:
          %Equal.sym(List<&2, String>, St.Pieces(String.append(S.Hex.pubkey(k), String.append(" ", String.append(S.U64.show(x), String.append(" ", St.Log.root(r))))), 32), Con{S.Hex.pubkey(k), St.Pieces(String.append(S.U64.show(x), String.append(" ", St.Log.root(r))), 32)}, W.cut(S.Hex.pubkey(k), String.append(S.U64.show(x), String.append(" ", St.Log.root(r))), Clean.pubkey(k))) : {St.LogEvent.read.words(Con{"B", _}) == Some{St.EBlock{k, Slash.BlockRec{x, r}}} : Maybe<&2, St.LogEvent>}
          %Equal.sym(List<&2, String>, St.Pieces(String.append(S.U64.show(x), String.append(" ", St.Log.root(r))), 32), Con{S.U64.show(x), St.Pieces(St.Log.root(r), 32)}, W.cut(S.U64.show(x), St.Log.root(r), Clean.u64(x))) : {St.LogEvent.read.words(Con{"B", Con{S.Hex.pubkey(k), _}}) == Some{St.EBlock{k, Slash.BlockRec{x, r}}} : Maybe<&2, St.LogEvent>}
          %Equal.sym(List<&2, String>, St.Pieces(St.Log.root(r), 32), [St.Log.root(r)], W.last(St.Log.root(r), Clean.root(r))) : {St.LogEvent.read.words(Con{"B", Con{S.Hex.pubkey(k), Con{S.U64.show(x), _}}}) == Some{St.EBlock{k, Slash.BlockRec{x, r}}} : Maybe<&2, St.LogEvent>}
          %Equal.sym(Maybe<&2, S.Pubkey>, S.Hex.read_pubkey(S.Hex.pubkey(k)), Some{k}, Pk.rt(k)) : {St.Log.read.b3(_, S.U64.read(S.U64.show(x)), St.Log.read_root(St.Log.root(r))) == Some{St.EBlock{k, Slash.BlockRec{x, r}}} : Maybe<&2, St.LogEvent>}
          %Equal.sym(Maybe<&2, S.U64>, S.U64.read(S.U64.show(x)), Some{x}, Dec.U64.show_read(x)) : {St.Log.read.b3(Some{k}, _, St.Log.read_root(St.Log.root(r))) == Some{St.EBlock{k, Slash.BlockRec{x, r}}} : Maybe<&2, St.LogEvent>}
          %Equal.sym(Maybe<&2, Maybe<&2, S.B32>>, St.Log.read_root(St.Log.root(r)), Some{r}, Rt(r)) : {St.Log.read.b3(Some{k}, Some{x}, _) == Some{St.EBlock{k, Slash.BlockRec{x, r}}} : Maybe<&2, St.LogEvent>}
          {==}
    case St.EAtt{+k, rec}:
      match rec:
        case Slash.AttRec{+x, +y, +r}:
          %Equal.sym(List<&2, String>, St.Pieces(String.append(S.Hex.pubkey(k), String.append(" ", String.append(S.U64.show(x), String.append(" ", String.append(S.U64.show(y), String.append(" ", St.Log.root(r))))))), 32), Con{S.Hex.pubkey(k), St.Pieces(String.append(S.U64.show(x), String.append(" ", String.append(S.U64.show(y), String.append(" ", St.Log.root(r))))), 32)}, W.cut(S.Hex.pubkey(k), String.append(S.U64.show(x), String.append(" ", String.append(S.U64.show(y), String.append(" ", St.Log.root(r))))), Clean.pubkey(k))) : {St.LogEvent.read.words(Con{"A", _}) == Some{St.EAtt{k, Slash.AttRec{x, y, r}}} : Maybe<&2, St.LogEvent>}
          %Equal.sym(List<&2, String>, St.Pieces(String.append(S.U64.show(x), String.append(" ", String.append(S.U64.show(y), String.append(" ", St.Log.root(r))))), 32), Con{S.U64.show(x), St.Pieces(String.append(S.U64.show(y), String.append(" ", St.Log.root(r))), 32)}, W.cut(S.U64.show(x), String.append(S.U64.show(y), String.append(" ", St.Log.root(r))), Clean.u64(x))) : {St.LogEvent.read.words(Con{"A", Con{S.Hex.pubkey(k), _}}) == Some{St.EAtt{k, Slash.AttRec{x, y, r}}} : Maybe<&2, St.LogEvent>}
          %Equal.sym(List<&2, String>, St.Pieces(String.append(S.U64.show(y), String.append(" ", St.Log.root(r))), 32), Con{S.U64.show(y), St.Pieces(St.Log.root(r), 32)}, W.cut(S.U64.show(y), St.Log.root(r), Clean.u64(y))) : {St.LogEvent.read.words(Con{"A", Con{S.Hex.pubkey(k), Con{S.U64.show(x), _}}}) == Some{St.EAtt{k, Slash.AttRec{x, y, r}}} : Maybe<&2, St.LogEvent>}
          %Equal.sym(List<&2, String>, St.Pieces(St.Log.root(r), 32), [St.Log.root(r)], W.last(St.Log.root(r), Clean.root(r))) : {St.LogEvent.read.words(Con{"A", Con{S.Hex.pubkey(k), Con{S.U64.show(x), Con{S.U64.show(y), _}}}}) == Some{St.EAtt{k, Slash.AttRec{x, y, r}}} : Maybe<&2, St.LogEvent>}
          %Equal.sym(Maybe<&2, S.Pubkey>, S.Hex.read_pubkey(S.Hex.pubkey(k)), Some{k}, Pk.rt(k)) : {St.Log.read.a4(_, S.U64.read(S.U64.show(x)), S.U64.read(S.U64.show(y)), St.Log.read_root(St.Log.root(r))) == Some{St.EAtt{k, Slash.AttRec{x, y, r}}} : Maybe<&2, St.LogEvent>}
          %Equal.sym(Maybe<&2, S.U64>, S.U64.read(S.U64.show(x)), Some{x}, Dec.U64.show_read(x)) : {St.Log.read.a4(Some{k}, _, S.U64.read(S.U64.show(y)), St.Log.read_root(St.Log.root(r))) == Some{St.EAtt{k, Slash.AttRec{x, y, r}}} : Maybe<&2, St.LogEvent>}
          %Equal.sym(Maybe<&2, S.U64>, S.U64.read(S.U64.show(y)), Some{y}, Dec.U64.show_read(y)) : {St.Log.read.a4(Some{k}, Some{x}, _, St.Log.read_root(St.Log.root(r))) == Some{St.EAtt{k, Slash.AttRec{x, y, r}}} : Maybe<&2, St.LogEvent>}
          %Equal.sym(Maybe<&2, Maybe<&2, S.B32>>, St.Log.read_root(St.Log.root(r)), Some{r}, Rt(r)) : {St.Log.read.a4(Some{k}, Some{x}, Some{y}, _) == Some{St.EAtt{k, Slash.AttRec{x, y, r}}} : Maybe<&2, St.LogEvent>}
          {==}
    case St.EBlockMark{+k, +x}:
      %Equal.sym(List<&2, String>, St.Pieces(String.append(S.Hex.pubkey(k), String.append(" ", S.U64.show(x))), 32), Con{S.Hex.pubkey(k), St.Pieces(S.U64.show(x), 32)}, W.cut(S.Hex.pubkey(k), S.U64.show(x), Clean.pubkey(k))) : {St.LogEvent.read.words(Con{"WB", _}) == Some{St.EBlockMark{k, x}} : Maybe<&2, St.LogEvent>}
      %Equal.sym(List<&2, String>, St.Pieces(S.U64.show(x), 32), [S.U64.show(x)], W.last(S.U64.show(x), Clean.u64(x))) : {St.LogEvent.read.words(Con{"WB", Con{S.Hex.pubkey(k), _}}) == Some{St.EBlockMark{k, x}} : Maybe<&2, St.LogEvent>}
      %Equal.sym(Maybe<&2, S.Pubkey>, S.Hex.read_pubkey(S.Hex.pubkey(k)), Some{k}, Pk.rt(k)) : {St.Log.read.wb2(_, S.U64.read(S.U64.show(x))) == Some{St.EBlockMark{k, x}} : Maybe<&2, St.LogEvent>}
      %Equal.sym(Maybe<&2, S.U64>, S.U64.read(S.U64.show(x)), Some{x}, Dec.U64.show_read(x)) : {St.Log.read.wb2(Some{k}, _) == Some{St.EBlockMark{k, x}} : Maybe<&2, St.LogEvent>}
      {==}
    case St.EAttMark{+k, m}:
      match m:
        case Slash.AttMark{+x, +y}:
          %Equal.sym(List<&2, String>, St.Pieces(String.append(S.Hex.pubkey(k), String.append(" ", String.append(S.U64.show(x), String.append(" ", S.U64.show(y))))), 32), Con{S.Hex.pubkey(k), St.Pieces(String.append(S.U64.show(x), String.append(" ", S.U64.show(y))), 32)}, W.cut(S.Hex.pubkey(k), String.append(S.U64.show(x), String.append(" ", S.U64.show(y))), Clean.pubkey(k))) : {St.LogEvent.read.words(Con{"WA", _}) == Some{St.EAttMark{k, Slash.AttMark{x, y}}} : Maybe<&2, St.LogEvent>}
          %Equal.sym(List<&2, String>, St.Pieces(String.append(S.U64.show(x), String.append(" ", S.U64.show(y))), 32), Con{S.U64.show(x), St.Pieces(S.U64.show(y), 32)}, W.cut(S.U64.show(x), S.U64.show(y), Clean.u64(x))) : {St.LogEvent.read.words(Con{"WA", Con{S.Hex.pubkey(k), _}}) == Some{St.EAttMark{k, Slash.AttMark{x, y}}} : Maybe<&2, St.LogEvent>}
          %Equal.sym(List<&2, String>, St.Pieces(S.U64.show(y), 32), [S.U64.show(y)], W.last(S.U64.show(y), Clean.u64(y))) : {St.LogEvent.read.words(Con{"WA", Con{S.Hex.pubkey(k), Con{S.U64.show(x), _}}}) == Some{St.EAttMark{k, Slash.AttMark{x, y}}} : Maybe<&2, St.LogEvent>}
          %Equal.sym(Maybe<&2, S.Pubkey>, S.Hex.read_pubkey(S.Hex.pubkey(k)), Some{k}, Pk.rt(k)) : {St.Log.read.wa3(_, S.U64.read(S.U64.show(x)), S.U64.read(S.U64.show(y))) == Some{St.EAttMark{k, Slash.AttMark{x, y}}} : Maybe<&2, St.LogEvent>}
          %Equal.sym(Maybe<&2, S.U64>, S.U64.read(S.U64.show(x)), Some{x}, Dec.U64.show_read(x)) : {St.Log.read.wa3(Some{k}, _, S.U64.read(S.U64.show(y))) == Some{St.EAttMark{k, Slash.AttMark{x, y}}} : Maybe<&2, St.LogEvent>}
          %Equal.sym(Maybe<&2, S.U64>, S.U64.read(S.U64.show(y)), Some{y}, Dec.U64.show_read(y)) : {St.Log.read.wa3(Some{k}, Some{x}, _) == Some{St.EAttMark{k, Slash.AttMark{x, y}}} : Maybe<&2, St.LogEvent>}
          {==}

# A line holds no newline.
def Ev.ns10(e: St.LogEvent) -> {NoSep(St.LogEvent.show(e), 10) == True{} : Bool}:
  match e:
    case St.EGvr{+g}:
      Clean.ns10(S.Hex.b32(g), Clean.b32(g))
    case St.EBlock{+k, rec}:
      match rec:
        case Slash.BlockRec{+x, +r}:
          NoSep.app(S.Hex.pubkey(k), String.append(" ", String.append(S.U64.show(x), String.append(" ", St.Log.root(r)))), 10, Clean.ns10(S.Hex.pubkey(k), Clean.pubkey(k)), NoSep.app(S.U64.show(x), String.append(" ", St.Log.root(r)), 10, Clean.ns10(S.U64.show(x), Clean.u64(x)), Clean.ns10(St.Log.root(r), Clean.root(r))))
    case St.EAtt{+k, rec}:
      match rec:
        case Slash.AttRec{+x, +y, +r}:
          NoSep.app(S.Hex.pubkey(k), String.append(" ", String.append(S.U64.show(x), String.append(" ", String.append(S.U64.show(y), String.append(" ", St.Log.root(r)))))), 10, Clean.ns10(S.Hex.pubkey(k), Clean.pubkey(k)), NoSep.app(S.U64.show(x), String.append(" ", String.append(S.U64.show(y), String.append(" ", St.Log.root(r)))), 10, Clean.ns10(S.U64.show(x), Clean.u64(x)), NoSep.app(S.U64.show(y), String.append(" ", St.Log.root(r)), 10, Clean.ns10(S.U64.show(y), Clean.u64(y)), Clean.ns10(St.Log.root(r), Clean.root(r)))))
    case St.EBlockMark{+k, +x}:
      NoSep.app(S.Hex.pubkey(k), String.append(" ", S.U64.show(x)), 10, Clean.ns10(S.Hex.pubkey(k), Clean.pubkey(k)), Clean.ns10(S.U64.show(x), Clean.u64(x)))
    case St.EAttMark{+k, m}:
      match m:
        case Slash.AttMark{+x, +y}:
          NoSep.app(S.Hex.pubkey(k), String.append(" ", String.append(S.U64.show(x), String.append(" ", S.U64.show(y)))), 10, Clean.ns10(S.Hex.pubkey(k), Clean.pubkey(k)), NoSep.app(S.U64.show(x), String.append(" ", S.U64.show(y)), 10, Clean.ns10(S.U64.show(x), Clean.u64(x)), Clean.ns10(S.U64.show(y), Clean.u64(y))))

# Log
# ===

def Shows(es: List<&2, St.LogEvent>) -> List<&2, String>:
  match es:
    case Nil{}:
      []
    case Con{e, r}:
      Con{St.LogEvent.show(e), Shows(r)}

def Lz.show(es: List<&2, St.LogEvent>) -> {St.Lz.of(St.Pieces(St.Log.show(es), 10)) == St.Lz{True{}, Shows(es), ""} : St.Lz}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +r}:
      %Equal.sym(List<&2, String>, St.Pieces(String.append(St.LogEvent.show(e), SCon{Chr{10}, St.Log.show(r)}), 10), Con{St.LogEvent.show(e), St.Pieces(St.Log.show(r), 10)}, Pieces.cut(St.LogEvent.show(e), St.Log.show(r), 10, Ev.ns10(e))) : {St.Lz.of(_) == St.Lz{True{}, Shows(Con{e, r}), ""} : St.Lz}
      %Equal.sym(St.Lz, St.Lz.of(St.Pieces(St.Log.show(r), 10)), St.Lz{True{}, Shows(r), ""}, Lz.show(r)) : {St.Lz.add(St.LogEvent.show(e), _) == St.Lz{True{}, Shows(Con{e, r}), ""} : St.Lz}
      {==}

def Rl(es: List<&2, St.LogEvent>) -> {St.Log.read_lines(Shows(es)) == Some{es} : Maybe<&2, List<&2, St.LogEvent>>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +r}:
      %Equal.sym(Maybe<&2, St.LogEvent>, St.LogEvent.read(St.LogEvent.show(e)), Some{e}, Ev.rt(e)) : {St.Log.cons(_, St.Log.read_lines(Shows(r))) == Some{Con{e, r}} : Maybe<&2, List<&2, St.LogEvent>>}
      %Equal.sym(Maybe<&2, List<&2, St.LogEvent>>, St.Log.read_lines(Shows(r)), Some{r}, Rl(r)) : {St.Log.cons(Some{e}, _) == Some{Con{e, r}} : Maybe<&2, List<&2, St.LogEvent>>}
      {==}

# A log reads back as its events.
def Log.rt(+es: List<&2, St.LogEvent>) -> {St.Log.read(St.Log.show(es)) == Some{es} : Maybe<&2, List<&2, St.LogEvent>>}:
  %Equal.sym(St.Lz, St.Lz.of(St.Pieces(St.Log.show(es), 10)), St.Lz{True{}, Shows(es), ""}, Lz.show(es)) : {St.Log.read.from_lines(St.Lz.lines(_)) == Some{es} : Maybe<&2, List<&2, St.LogEvent>>}
  Rl(es)
