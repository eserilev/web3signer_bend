# SSZ for Bulkhead: 64-bit numbers, 32-byte chunks, SHA-256 over two chunks,
# byte strings, bitlists and bitvectors, merkleization with a limit and
# progressive merkleization, and the hash tree roots of the containers that
# Bulkhead signs. Each root is a tree of 64-byte hashes, so this file needs
# no general-length SHA-256.
import Base

# U64
# ===
#
# A u64 as two words: hi holds bits 63..32, lo holds bits 31..0.

type U64 is Data:
  U64{hi: U32, lo: U32}

def U64.zero() -> U64:
  U64{0, 0}

def U64.from_u32(x: U32) -> U64:
  U64{0, x}

# The value as a Nat: hi * 2^32 + lo. Laws use it; the running code does not.
def U64.to_nat(a: U64) -> Nat:
  match a:
    case U64{h, l}:
      Nat.add(Nat.mul(U32.to_nat(h), Nat.pow(2n, 32n)), U32.to_nat(l))

def U64.cmp.lo(hi: Cmp, lo: Cmp) -> Cmp:
  match hi:
    case LT{}:
      LT{}
    case EQ{}:
      lo
    case GT{}:
      GT{}

def U64.cmp(a: U64, b: U64) -> Cmp:
  match a b:
    case U64{ah, al} U64{bh, bl}:
      U64.cmp.lo(U32.cmp(ah, bh), U32.cmp(al, bl))

def U64.is_eq(a: U64, b: U64) -> Bool:
  Cmp.is_eq(U64.cmp(a, b))

def U64.is_lt(a: U64, b: U64) -> Bool:
  Cmp.is_lt(U64.cmp(a, b))

def U64.is_le(a: U64, b: U64) -> Bool:
  Bool.not(Cmp.is_gt(U64.cmp(a, b)))

def U64.is_gt(a: U64, b: U64) -> Bool:
  Cmp.is_gt(U64.cmp(a, b))

def U64.is_zero(a: U64) -> Bool:
  match a:
    case U64{h, l}:
      Bool.and(U32.is_eq(h, 0), U32.is_eq(l, 0))

# Wrapping addition.
def U64.add(a: U64, b: U64) -> U64:
  match a b:
    case U64{ah, +al} U64{bh, bl}:
      +lo = (al + bl : U32)
      U64{(ah + bh + Bool.to_u32(U32.is_lt(lo, al)) : U32), lo}

def U64.shl1(a: U64) -> U64:
  match a:
    case U64{h, +l}:
      U64{((h * 2 : U32) .|. (l / 2147483648 : U32) : U32), (l * 2 : U32)}

def U64.shr1(a: U64) -> U64:
  match a:
    case U64{+h, l}:
      U64{(h / 2 : U32), ((l / 2 : U32) .|. ((h .&. 1 : U32) * 2147483648 : U32) : U32)}

def U64.shrn(n: Nat, a: U64) -> U64:
  match n:
    case 0n:
      a
    case 1n+p:
      U64.shr1(U64.shrn(p, a))

# 2^64 - 1 divided by 10, rounded down: 0x1999999999999999.
def U64.max_div10() -> U64:
  U64{429496729, 2576980377}

# a * 10 + d, wrapping.
def U64.mul10_add(+a: U64, d: U32) -> U64:
  U64.add(U64.add(U64.shl1(U64.shl1(U64.shl1(a))), U64.shl1(a)), U64.from_u32(d))

# a * 10 + d, or None if the result does not fit in 64 bits.
def U64.mul10_add.checked.lim(+a: U64, d: U32, big: Bool) -> Maybe<&2, U64>:
  match big:
    case True{}:
      None{}
    case False{}:
      Some{U64.mul10_add(a, d)}

def U64.mul10_add.checked.go(+a: U64, +d: U32, over: Bool, at_max: Bool) -> Maybe<&2, U64>:
  match over:
    case True{}:
      None{}
    case False{}:
      match at_max:
        case True{}:
          U64.mul10_add.checked.lim(a, d, U32.is_gt(d, 5))
        case False{}:
          Some{U64.mul10_add(a, d)}

def U64.mul10_add.checked(+a: U64, +d: U32) -> Maybe<&2, U64>:
  U64.mul10_add.checked.go(a, d, U64.is_gt(a, U64.max_div10()), U64.is_eq(a, U64.max_div10()))

def Char.digit.if(+c: U32, ok: Bool) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      Some{(c - 48 : U32)}
    case False{}:
      None{}

def Char.digit(c: Char) -> Maybe<&2, U32>:
  match c:
    case Chr{+x}:
      Char.digit.if(x, Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)))

def U64.read.go(s: String, +acc: U64) -> Maybe<&2, U64>:
  match s:
    case SNil{}:
      Some{acc}
    case SCon{c, t}:
      do Maybe<&2, U64>:
        d : U32 <- Char.digit(c)
        next : U64 <- U64.mul10_add.checked(acc, d)
        U64.read.go(t, next)

# Parses a non-empty decimal string. Rejects other characters and values
# that do not fit in 64 bits.
def U64.read(s: String) -> Maybe<&2, U64>:
  match s:
    case SNil{}:
      None{}
    case SCon{c, t}:
      U64.read.go(SCon{c, t}, U64.zero())

# a / 10 and a % 10. The low word goes through in 16-bit halves, so no
# intermediate value exceeds 32 bits.
def U64.div10(a: U64) -> U64:
  match a:
    case U64{+h, +l}:
      +t1 = (((h % 10 : U32) * 65536 : U32) + (l / 65536 : U32) : U32)
      +t2 = (((t1 % 10 : U32) * 65536 : U32) + (l .&. 65535 : U32) : U32)
      U64{(h / 10 : U32), (((t1 / 10 : U32) * 65536 : U32) + (t2 / 10 : U32) : U32)}

def U64.mod10(a: U64) -> U32:
  match a:
    case U64{h, +l}:
      +t1 = (((h % 10 : U32) * 65536 : U32) + (l / 65536 : U32) : U32)
      ((((t1 % 10 : U32) * 65536 : U32) + (l .&. 65535 : U32) : U32) % 10 : U32)

def U64.show.push(zero: Bool, d: U32, acc: String) -> String:
  match zero:
    case True{}:
      acc
    case False{}:
      SCon{Chr{(d + 48 : U32)}, acc}

# Prepends one digit for each step while a is not zero.
def U64.show.go(n: Nat, +a: U64, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      U64.show.go(p, U64.div10(a), U64.show.push(U64.is_zero(a), U64.mod10(a), acc))

def U64.show.fix(s: String) -> String:
  match s:
    case SNil{}:
      "0"
    case SCon{c, t}:
      SCon{c, t}

# Decimal. A u64 has at most 20 digits.
def U64.show(+a: U64) -> String:
  U64.show.fix(U64.show.go(20n, a, ""))

# B32
# ===
#
# 32 bytes as eight big-endian words: w0 holds bytes 0..3. SHA-256 reads
# its input in this layout, so a chunk goes into the hash with no copy.

type B32 is Data:
  B32{w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32}

def B32.zero() -> B32:
  B32{0, 0, 0, 0, 0, 0, 0, 0}

def B32.is_eq(a: B32, b: B32) -> Bool:
  match a b:
    case B32{a0, a1, a2, a3, a4, a5, a6, a7} B32{b0, b1, b2, b3, b4, b5, b6, b7}:
      U32.is_eq(a0, b0) && U32.is_eq(a1, b1) && U32.is_eq(a2, b2) && U32.is_eq(a3, b3)
        && U32.is_eq(a4, b4) && U32.is_eq(a5, b5) && U32.is_eq(a6, b6) && U32.is_eq(a7, b7)

# Hex
# ===

def Hex.digit.if(d: U32, low: Bool) -> Char:
  match low:
    case True{}:
      Chr{(d + 48 : U32)}
    case False{}:
      Chr{(d + 87 : U32)}

def Hex.digit(+d: U32) -> Char:
  Hex.digit.if(d, U32.is_lt(d, 10))

# The last n hex digits of w, before acc.
def Hex.word.go(n: Nat, +w: U32, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      Hex.word.go(p, (w / 16 : U32), SCon{Hex.digit((w .&. 15 : U32)), acc})

def Hex.word(+w: U32, acc: String) -> String:
  Hex.word.go(8n, w, acc)

def Hex.b32(a: B32) -> String:
  match a:
    case B32{a0, a1, a2, a3, a4, a5, a6, a7}:
      "0x" ++ Hex.word(a0, Hex.word(a1, Hex.word(a2, Hex.word(a3,
        Hex.word(a4, Hex.word(a5, Hex.word(a6, Hex.word(a7, ""))))))))

def Hex.bytes4(+w: U32) -> String:
  "0x" ++ Hex.word(w, "")

def Hex.nibble.up(+c: U32, ok: Bool) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      Some{(c - 55 : U32)}
    case False{}:
      None{}

def Hex.nibble.af(+c: U32, ok: Bool) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      Some{(c - 87 : U32)}
    case False{}:
      Hex.nibble.up(c, Bool.and(U32.is_ge(c, 65), U32.is_le(c, 70)))

def Hex.nibble.dec(+c: U32, ok: Bool) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      Some{(c - 48 : U32)}
    case False{}:
      Hex.nibble.af(c, Bool.and(U32.is_ge(c, 97), U32.is_le(c, 102)))

def Hex.nibble(c: Char) -> Maybe<&2, U32>:
  match c:
    case Chr{+x}:
      Hex.nibble.dec(x, Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)))

# Drops a leading "0x" or "0X", if s has one.
def Hex.strip.x(c: Char, t: String, ok: Bool) -> String:
  match ok:
    case True{}:
      t
    case False{}:
      SCon{Chr{48}, SCon{c, t}}

def Hex.strip.zero(t: String) -> String:
  match t:
    case SNil{}:
      SCon{Chr{48}, SNil{}}
    case SCon{c, u}:
      match c:
        case Chr{+x}:
          Hex.strip.x(Chr{x}, u, Bool.or(U32.is_eq(x, 120), U32.is_eq(x, 88)))

def Hex.strip.if(c: Char, t: String, zero: Bool) -> String:
  match zero:
    case True{}:
      Hex.strip.zero(t)
    case False{}:
      SCon{c, t}

def Hex.strip(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          Hex.strip.if(Chr{x}, t, U32.is_eq(x, 48))

def Hex.end(-A: Data, s: String, +v: A) -> Maybe<&2, A>:
  match s:
    case SNil{}:
      Some{v}
    case SCon{c, t}:
      None{}

# Shifts the 256-bit value left by 4 bits and puts d in the low 4 bits.
# w0 is the most significant word.
def B32.push_nibble(acc: B32, d: U32) -> B32:
  match acc:
    case B32{a0, +a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      B32{((a0 * 16 : U32) .|. (a1 / 268435456 : U32) : U32),
          ((a1 * 16 : U32) .|. (a2 / 268435456 : U32) : U32),
          ((a2 * 16 : U32) .|. (a3 / 268435456 : U32) : U32),
          ((a3 * 16 : U32) .|. (a4 / 268435456 : U32) : U32),
          ((a4 * 16 : U32) .|. (a5 / 268435456 : U32) : U32),
          ((a5 * 16 : U32) .|. (a6 / 268435456 : U32) : U32),
          ((a6 * 16 : U32) .|. (a7 / 268435456 : U32) : U32),
          ((a7 * 16 : U32) .|. d : U32)}

def Hex.read_b32.go(n: Nat, s: String, acc: B32) -> Maybe<&2, B32>:
  match n:
    case 0n:
      Hex.end(B32, s, acc)
    case 1n+p:
      match s:
        case SNil{}:
          None{}
        case SCon{c, t}:
          do Maybe<&2, B32>:
            d : U32 <- Hex.nibble(c)
            Hex.read_b32.go(p, t, B32.push_nibble(acc, d))

# Reads "0x" and exactly 64 hex digits.
def Hex.read_b32(s: String) -> Maybe<&2, B32>:
  Hex.read_b32.go(64n, Hex.strip(s), B32.zero())

def Hex.read_bytes4.go(n: Nat, s: String, +acc: U32) -> Maybe<&2, U32>:
  match n:
    case 0n:
      Hex.end(U32, s, acc)
    case 1n+p:
      match s:
        case SNil{}:
          None{}
        case SCon{c, t}:
          do Maybe<&2, U32>:
            d : U32 <- Hex.nibble(c)
            Hex.read_bytes4.go(p, t, ((acc * 16 : U32) .|. d : U32))

# Reads "0x" and exactly 8 hex digits: a Bytes4 value (a fork version).
def Hex.read_bytes4(s: String) -> Maybe<&2, U32>:
  Hex.read_bytes4.go(8n, Hex.strip(s), 0)

# Pubkey
# ======
#
# A 48-byte BLS public key: hi holds bytes 0..31 and lo holds bytes 32..47.

type B16 is Data:
  B16{w0: U32, w1: U32, w2: U32, w3: U32}

type Pubkey is Data:
  Pubkey{hi: B32, lo: B16}

# A value read from the front of a string, and the rest of the string.
type HexPart is Data:
  HexPart{value: B32, rest: String}
  HexNone{}

def Hex.take.end(bad: Bool, acc: B32, s: String) -> HexPart:
  match bad:
    case True{}:
      HexNone{}
    case False{}:
      HexPart{acc, s}

# Reads n hex digits into the low end of acc, and keeps the rest of s. bad
# records a character that is not a hex digit.
def Hex.take.go(n: Nat, s: String, acc: B32, bad: Bool) -> HexPart:
  match n:
    case 0n:
      Hex.take.end(bad, acc, s)
    case 1n+p:
      match s:
        case SNil{}:
          HexNone{}
        case SCon{+c, t}:
          Hex.take.go(p, t, B32.push_nibble(acc, Maybe.default(&2, U32, Hex.nibble(c), 0)),
            bad || Maybe.is_none(&2, U32, Hex.nibble(c)))

# 32 digits pushed into a B32 land in its low words w4..w7.
def B16.low(b: B32) -> B16:
  match b:
    case B32{a0, a1, a2, a3, a4, a5, a6, a7}:
      B16{a4, a5, a6, a7}

def Hex.read_pubkey.lo(hi: B32, p: HexPart) -> Maybe<&2, Pubkey>:
  match p:
    case HexNone{}:
      None{}
    case HexPart{lo, rest}:
      Hex.end(Pubkey, rest, Pubkey{hi, B16.low(lo)})

def Hex.read_pubkey.hi(p: HexPart) -> Maybe<&2, Pubkey>:
  match p:
    case HexNone{}:
      None{}
    case HexPart{hi, rest}:
      Hex.read_pubkey.lo(hi, Hex.take.go(32n, rest, B32.zero(), False{}))

# Reads "0x" and exactly 96 hex digits.
def Hex.read_pubkey(s: String) -> Maybe<&2, Pubkey>:
  Hex.read_pubkey.hi(Hex.take.go(64n, Hex.strip(s), B32.zero(), False{}))

def Hex.pubkey(k: Pubkey) -> String:
  match k:
    case Pubkey{hi, lo}:
      match lo:
        case B16{l0, l1, l2, l3}:
          Hex.b32(hi) ++ Hex.word(l0, Hex.word(l1, Hex.word(l2, Hex.word(l3, ""))))

def B16.is_eq(a: B16, b: B16) -> Bool:
  match a b:
    case B16{a0, a1, a2, a3} B16{b0, b1, b2, b3}:
      U32.is_eq(a0, b0) && U32.is_eq(a1, b1) && U32.is_eq(a2, b2) && U32.is_eq(a3, b3)

def Pubkey.is_eq(a: Pubkey, b: Pubkey) -> Bool:
  match a b:
    case Pubkey{ah, al} Pubkey{bh, bl}:
      B32.is_eq(ah, bh) && B16.is_eq(al, bl)

# SHA-256
# =======

def Sha.k() -> List<U32>:
  [1116352408, 1899447441, 3049323471, 3921009573, 961987163, 1508970993, 2453635748, 2870763221,
   3624381080, 310598401, 607225278, 1426881987, 1925078388, 2162078206, 2614888103, 3248222580,
   3835390401, 4022224774, 264347078, 604807628, 770255983, 1249150122, 1555081692, 1996064986,
   2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895,
   666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037,
   2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344,
   430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779,
   1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298]

def Sha.iv() -> B32:
  B32{1779033703, 3144134277, 1013904242, 2773480762, 1359893119, 2600822924, 528734635, 1541459225}

# Rotate right by n, given d = 2^n and m = 2^(32 - n).
def Sha.rotr(+x: U32, d: U32, m: U32) -> U32:
  ((x / d : U32) .|. (x * m : U32) : U32)

def Sha.big0(+x: U32) -> U32:
  (Sha.rotr(x, 4, 1073741824) .^. Sha.rotr(x, 8192, 524288) .^. Sha.rotr(x, 4194304, 1024) : U32)

def Sha.big1(+x: U32) -> U32:
  (Sha.rotr(x, 64, 67108864) .^. Sha.rotr(x, 2048, 2097152) .^. Sha.rotr(x, 33554432, 128) : U32)

def Sha.small0(+x: U32) -> U32:
  (Sha.rotr(x, 128, 33554432) .^. Sha.rotr(x, 262144, 16384) .^. (x / 8 : U32) : U32)

def Sha.small1(+x: U32) -> U32:
  (Sha.rotr(x, 131072, 32768) .^. Sha.rotr(x, 524288, 8192) .^. (x / 1024 : U32) : U32)

def Sha.ch(+e: U32, f: U32, g: U32) -> U32:
  ((e .&. f : U32) .^. (U32.not(e) .&. g : U32) : U32)

def Sha.maj(+a: U32, +b: U32, +c: U32) -> U32:
  ((a .&. b : U32) .^. (a .&. c : U32) .^. (b .&. c : U32) : U32)

# The message schedule as a window of 16 words. Each round reads w0, then
# the window moves by one and computes the word 16 rounds ahead.
type Sha.W is Data:
  Sha.W{w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32, w7: U32,
        w8: U32, w9: U32, w10: U32, w11: U32, w12: U32, w13: U32, w14: U32, w15: U32}

def Sha.W.from(a: B32, b: B32) -> Sha.W:
  match a b:
    case B32{a0, a1, a2, a3, a4, a5, a6, a7} B32{b0, b1, b2, b3, b4, b5, b6, b7}:
      Sha.W{a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7}

def Sha.round(+k: U32, +w: U32, s: B32) -> B32:
  match s:
    case B32{+a, +b, +c, +d, +e, +f, +g, +h}:
      +t1 = (h + Sha.big1(e) + Sha.ch(e, f, g) + k + w : U32)
      +t2 = (Sha.big0(a) + Sha.maj(a, b, c) : U32)
      B32{(t1 + t2 : U32), a, b, c, (d + t1 : U32), e, f, g}

def Sha.rounds(ks: List<U32>, s: B32, w: Sha.W) -> B32:
  match ks:
    case Nil{}:
      s
    case Con{k, rest}:
      match w:
        case Sha.W{+w0, +w1, w2, w3, w4, w5, w6, w7, w8, +w9, w10, w11, w12, w13, +w14, w15}:
          +next = (Sha.small1(w14) + w9 + Sha.small0(w1) + w0 : U32)
          Sha.rounds(rest, Sha.round(k, w0, s),
            Sha.W{w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, next})

def Sha.add(a: B32, b: B32) -> B32:
  match a b:
    case B32{a0, a1, a2, a3, a4, a5, a6, a7} B32{b0, b1, b2, b3, b4, b5, b6, b7}:
      B32{(a0 + b0 : U32), (a1 + b1 : U32), (a2 + b2 : U32), (a3 + b3 : U32),
          (a4 + b4 : U32), (a5 + b5 : U32), (a6 + b6 : U32), (a7 + b7 : U32)}

def Sha.compress(+s: B32, w: Sha.W) -> B32:
  Sha.add(s, Sha.rounds(Sha.k(), s, w))

# The second block of a 64-byte message: 0x80, zeros, and the bit length 512.
def Sha.pad64() -> Sha.W:
  Sha.W{2147483648, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 512}

# sha256(a ++ b): the hash of one merkle node.
def Sha.hash64(a: B32, b: B32) -> B32:
  Sha.compress(Sha.compress(Sha.iv(), Sha.W.from(a, b)), Sha.pad64())

# SSZ
# ===

# Reverses the byte order of a word.
def Ssz.bswap(+x: U32) -> U32:
  (((x .&. 255 : U32) * 16777216 : U32) .|. ((x .&. 65280 : U32) * 256 : U32)
    .|. ((x / 256 : U32) .&. 65280 : U32) .|. (x / 16777216 : U32) : U32)

# A uint64 chunk: 8 little-endian bytes, then zeros.
def Ssz.u64(a: U64) -> B32:
  match a:
    case U64{h, l}:
      B32{Ssz.bswap(l), Ssz.bswap(h), 0, 0, 0, 0, 0, 0}

# A Bytes4 chunk. The word already holds the 4 bytes in order.
def Ssz.bytes4(w: U32) -> B32:
  B32{w, 0, 0, 0, 0, 0, 0, 0}

def Ssz.merkle4(a: B32, b: B32, c: B32, d: B32) -> B32:
  Sha.hash64(Sha.hash64(a, b), Sha.hash64(c, d))

def Ssz.merkle8(a: B32, b: B32, c: B32, d: B32, e: B32, f: B32, g: B32, h: B32) -> B32:
  Sha.hash64(Ssz.merkle4(a, b, c, d), Ssz.merkle4(e, f, g, h))

# Containers
# ==========

type Checkpoint is Data:
  Checkpoint{epoch: U64, root: B32}

def Checkpoint.root(c: Checkpoint) -> B32:
  match c:
    case Checkpoint{e, r}:
      Sha.hash64(Ssz.u64(e), r)

type AttestationData is Data:
  AttestationData{slot: U64, index: U64, beacon_block_root: B32, source: Checkpoint, target: Checkpoint}

def AttestationData.root(a: AttestationData) -> B32:
  match a:
    case AttestationData{slot, index, bbr, src, tgt}:
      Ssz.merkle8(Ssz.u64(slot), Ssz.u64(index), bbr, Checkpoint.root(src), Checkpoint.root(tgt),
        B32.zero(), B32.zero(), B32.zero())

type BeaconBlockHeader is Data:
  BeaconBlockHeader{slot: U64, proposer_index: U64, parent_root: B32, state_root: B32, body_root: B32}

def BeaconBlockHeader.root(h: BeaconBlockHeader) -> B32:
  match h:
    case BeaconBlockHeader{slot, pi, pr, sr, br}:
      Ssz.merkle8(Ssz.u64(slot), Ssz.u64(pi), pr, sr, br, B32.zero(), B32.zero(), B32.zero())

# previous_version and current_version are Bytes4 words.
type Fork is Data:
  Fork{previous_version: U32, current_version: U32, epoch: U64}

def Fork.root(f: Fork) -> B32:
  match f:
    case Fork{p, c, e}:
      Ssz.merkle4(Ssz.bytes4(p), Ssz.bytes4(c), Ssz.u64(e), B32.zero())

def ForkData.root(current_version: U32, genesis_validators_root: B32) -> B32:
  Sha.hash64(Ssz.bytes4(current_version), genesis_validators_root)

def SigningData.root(object_root: B32, domain: B32) -> B32:
  Sha.hash64(object_root, domain)

# Domains
# =======

# The spec's compute_fork_version: the previous version before fork.epoch.
def Domain.fork_version.if(p: U32, c: U32, before: Bool) -> U32:
  match before:
    case True{}:
      p
    case False{}:
      c

def Domain.fork_version(f: Fork, epoch: U64) -> U32:
  match f:
    case Fork{p, c, e}:
      Domain.fork_version.if(p, c, U64.is_lt(epoch, e))

# The spec's compute_domain. domain_type is the 4 domain-type bytes as one
# word: DOMAIN_BEACON_ATTESTER (0x01000000) is 16777216.
def Domain.compute.prefix(domain_type: U32, fork_data_root: B32) -> B32:
  match fork_data_root:
    case B32{r0, r1, r2, r3, r4, r5, r6, r7}:
      B32{domain_type, r0, r1, r2, r3, r4, r5, r6}

def Domain.compute(domain_type: U32, fork_version: U32, genesis_validators_root: B32) -> B32:
  Domain.compute.prefix(domain_type, ForkData.root(fork_version, genesis_validators_root))

def Domain.beacon_proposer() -> U32:
  0

def Domain.beacon_attester() -> U32:
  16777216

def Domain.randao() -> U32:
  33554432

def Domain.selection_proof() -> U32:
  83886080

def Domain.voluntary_exit() -> U32:
  67108864

def Domain.aggregate_and_proof() -> U32:
  100663296

def Domain.sync_committee() -> U32:
  117440512

def Domain.sync_committee_selection_proof() -> U32:
  134217728

def Domain.contribution_and_proof() -> U32:
  150994944

# DOMAIN_APPLICATION_BUILDER is 0x00000001.
def Domain.application_builder() -> U32:
  1

# Byte strings
# ============
#
# A byte string is a list of bytes, one byte in each U32.

def Hex.bytes.go(s: String, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match s:
    case SNil{}:
      Some{List.reverse(&2, U32, acc)}
    case SCon{c, t}:
      match t:
        case SNil{}:
          None{}
        case SCon{d, u}:
          do Maybe<&2, List<&2, U32>>:
            hi : U32 <- Hex.nibble(c)
            lo : U32 <- Hex.nibble(d)
            Hex.bytes.go(u, Con{((hi * 16 : U32) .|. lo : U32), acc})

# Reads "0x" and an even number of hex digits.
def Hex.bytes(s: String) -> Maybe<&2, List<&2, U32>>:
  Hex.bytes.go(Hex.strip(s), [])

# The first byte, or 0 for an empty string.
def Bytes.head(bs: List<&2, U32>) -> U32:
  match bs:
    case Nil{}:
      0
    case Con{b, t}:
      b

def Bytes.count(bs: List<&2, U32>) -> U32:
  match bs:
    case Nil{}:
      0
    case Con{b, t}:
      (1 + Bytes.count(t) : U32)

# Packs bytes into chunks. cur holds n bytes so far.
type Pack is Data:
  Pack{done: List<&2, B32>, cur: B32, n: U32}

def Pack.fix(+done: List<&2, B32>, +cur: B32, +n: U32) -> Pack:
  Bool.pick(Pack, U32.is_eq(n, 32), Pack{Con{cur, done}, B32.zero(), 0}, Pack{done, cur, n})

def Pack.step(st: Pack, +b: U32) -> Pack:
  match st:
    case Pack{done, cur, n}:
      Pack.fix(done, B32.push_nibble(B32.push_nibble(cur, (b / 16 : U32)), (b .&. 15 : U32)), (n + 1 : U32))

def Pack.go(bs: List<&2, U32>, st: Pack) -> Pack:
  match bs:
    case Nil{}:
      st
    case Con{b, t}:
      Pack.go(t, Pack.step(st, b))

# Shifts acc left by k zero bytes.
def B32.shift_bytes(k: Nat, acc: B32) -> B32:
  match k:
    case 0n:
      acc
    case 1n+p:
      B32.shift_bytes(p, B32.push_nibble(B32.push_nibble(acc, 0), 0))

def Pack.last(+done: List<&2, B32>, cur: B32, +n: U32) -> List<&2, B32>:
  Bool.pick(List<&2, B32>, U32.is_eq(n, 0), done,
    Con{B32.shift_bytes(U32.to_nat((32 - n : U32)), cur), done})

def Pack.finish(st: Pack) -> List<&2, B32>:
  match st:
    case Pack{done, cur, n}:
      List.reverse(&2, B32, Pack.last(done, cur, n))

# The spec's pack: the bytes in 32-byte chunks, the last one padded with
# zeros.
def Ssz.chunks(bs: List<&2, U32>) -> List<&2, B32>:
  Pack.finish(Pack.go(bs, Pack{[], B32.zero(), 0}))

# Merkleization
# =============

# One tree level: the hash of each pair. z is the zero root of this level
# and pairs with an odd last node.
def Merk.level(xs: List<&2, B32>, +z: B32) -> List<&2, B32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      match t:
        case Nil{}:
          [Sha.hash64(a, z)]
        case Con{b, r}:
          Con{Sha.hash64(a, b), Merk.level(r, z)}

def Merk.first(xs: List<&2, B32>, z: B32) -> B32:
  match xs:
    case Nil{}:
      z
    case Con{h, t}:
      h

def Merk.go(d: Nat, xs: List<&2, B32>, +z: B32) -> B32:
  match d:
    case 0n:
      Merk.first(xs, z)
    case 1n+p:
      Merk.go(p, Merk.level(xs, z), Sha.hash64(z, z))

# The spec's merkleize with a limit of 2^depth chunks. The caller makes sure
# that xs has no more chunks than that.
def Ssz.merkleize(xs: List<&2, B32>, depth: Nat) -> B32:
  Merk.go(depth, xs, B32.zero())

def Ssz.mix_len(root: B32, n: U32) -> B32:
  Sha.hash64(root, Ssz.u64(U64.from_u32(n)))

# The spec's merkleize_progressive (EIP-7916): the first width chunks form
# a subtree on the left, and the rest continue on the right with 4 times
# the width. fuel bounds the recursion: each step takes one chunk or more.
def Prog.go(fuel: Nat, xs: List<&2, B32>, +width: Nat, +depth: Nat) -> B32:
  match fuel:
    case 0n:
      B32.zero()
    case 1n+f:
      match xs:
        case Nil{}:
          B32.zero()
        case Con{+h, +t}:
          Sha.hash64(
            Ssz.merkleize(List.take(&2, B32, Con{h, t}, width), depth),
            Prog.go(f, List.drop(&2, B32, Con{h, t}, width), Nat.mul(4n, width), Nat.add(depth, 2n)))

def Ssz.progressive(+xs: List<&2, B32>) -> B32:
  Prog.go(1n+List.length(&2, B32, xs), xs, 1n, 0n)

# Bits
# ====

# The highest set bit of a byte, as a value, and its index.
def Byte.top(+b: U32) -> U32:
  Bool.pick(U32, U32.is_ge(b, 128), 128, Bool.pick(U32, U32.is_ge(b, 64), 64,
  Bool.pick(U32, U32.is_ge(b, 32), 32, Bool.pick(U32, U32.is_ge(b, 16), 16,
  Bool.pick(U32, U32.is_ge(b, 8), 8, Bool.pick(U32, U32.is_ge(b, 4), 4,
  Bool.pick(U32, U32.is_ge(b, 2), 2, Bool.pick(U32, U32.is_ge(b, 1), 1, 0))))))))

def Byte.index(+t: U32) -> U32:
  Bool.pick(U32, U32.is_eq(t, 128), 7, Bool.pick(U32, U32.is_eq(t, 64), 6,
  Bool.pick(U32, U32.is_eq(t, 32), 5, Bool.pick(U32, U32.is_eq(t, 16), 4,
  Bool.pick(U32, U32.is_eq(t, 8), 3, Bool.pick(U32, U32.is_eq(t, 4), 2,
  Bool.pick(U32, U32.is_eq(t, 2), 1, 0)))))))

# 2^k for k in 0..8.
def Byte.pow2(+k: U32) -> U32:
  Bool.pick(U32, U32.is_eq(k, 0), 1, Bool.pick(U32, U32.is_eq(k, 1), 2,
  Bool.pick(U32, U32.is_eq(k, 2), 4, Bool.pick(U32, U32.is_eq(k, 3), 8,
  Bool.pick(U32, U32.is_eq(k, 4), 16, Bool.pick(U32, U32.is_eq(k, 5), 32,
  Bool.pick(U32, U32.is_eq(k, 6), 64, Bool.pick(U32, U32.is_eq(k, 7), 128, 256))))))))

# A bitlist without its length bit: the packed chunks and the bit count.
type Bitlist is Data:
  Bitlist{chunks: List<&2, B32>, len: U32}

def Bitlist.keep(+top: U32, last: U32, +rest: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, U32.is_eq(top, 1), rest, Con{(last - top : U32), rest})

def Bitlist.last(+top: U32, +last: U32, +rest: List<&2, U32>) -> Maybe<&2, Bitlist>:
  Bool.pick(Maybe<&2, Bitlist>, U32.is_eq(top, 0), None{},
    Some{Bitlist{Ssz.chunks(List.reverse(&2, U32, Bitlist.keep(top, last, rest))),
      ((Bytes.count(rest) * 8 : U32) + Byte.index(top) : U32)}})

# The last byte holds the length bit: its highest set bit. A last byte of
# zero or an empty string is not a bitlist.
def Bitlist.of(rev: List<&2, U32>) -> Maybe<&2, Bitlist>:
  match rev:
    case Nil{}:
      None{}
    case Con{+last, rest}:
      Bitlist.last(Byte.top(last), last, rest)

def Bitlist.limit(b: Bitlist, +limit: U32) -> Maybe<&2, Bitlist>:
  match b:
    case Bitlist{cs, +n}:
      Bool.pick(Maybe<&2, Bitlist>, U32.is_le(n, limit), Some{Bitlist{cs, n}}, None{})

# Reads a bitlist of at most limit bits.
def Hex.bitlist(s: String, +limit: U32) -> Maybe<&2, Bitlist>:
  do Maybe<&2, Bitlist>:
    bs : List<&2, U32> <- Hex.bytes(s)
    b : Bitlist <- Bitlist.of(List.reverse(&2, U32, bs))
    Bitlist.limit(b, limit)

def Bitlist.root(b: Bitlist, depth: Nat) -> B32:
  match b:
    case Bitlist{cs, n}:
      Ssz.mix_len(Ssz.merkleize(cs, depth), n)

def Bitlist.root_progressive(b: Bitlist) -> B32:
  match b:
    case Bitlist{cs, n}:
      Ssz.mix_len(Ssz.progressive(cs), n)

def Bitvector.check(+bs: List<&2, U32>, +bits: U32, +last: U32) -> Maybe<&2, B32>:
  Bool.pick(Maybe<&2, B32>,
    U32.is_eq(Bytes.count(bs), ((bits + 7 : U32) / 8 : U32))
      && U32.is_lt(last, Byte.pow2(Bool.pick(U32, U32.is_eq((bits .&. 7 : U32), 0), 8, (bits .&. 7 : U32)))),
    Some{Merk.first(Ssz.chunks(bs), B32.zero())}, None{})

def Bitvector.of(+bs: List<&2, U32>, +bits: U32) -> Maybe<&2, B32>:
  Bitvector.check(bs, bits, Bytes.head(List.reverse(&2, U32, bs)))

# Reads a bitvector of bits bits, at most 256. The unused high bits of the
# last byte must be zero. The result is its root: the one chunk.
def Hex.bitvector(s: String, +bits: U32) -> Maybe<&2, B32>:
  do Maybe<&2, B32>:
    bs : List<&2, U32> <- Hex.bytes(s)
    Bitvector.of(bs, bits)

# Fixed-size byte strings
# =======================

def Fixed.check(+bs: List<&2, U32>, +n: U32) -> Maybe<&2, List<&2, B32>>:
  Bool.pick(Maybe<&2, List<&2, B32>>, U32.is_eq(Bytes.count(bs), n), Some{Ssz.chunks(bs)}, None{})

# Reads exactly n bytes and packs them into chunks.
def Hex.fixed(s: String, +n: U32) -> Maybe<&2, List<&2, B32>>:
  do Maybe<&2, List<&2, B32>>:
    bs : List<&2, U32> <- Hex.bytes(s)
    Fixed.check(bs, n)

# A BLS signature: 96 bytes in 3 chunks. The root is all this file needs,
# so the reader returns it.
def Hex.signature_root(s: String) -> Maybe<&2, B32>:
  do Maybe<&2, B32>:
    cs : List<&2, B32> <- Hex.fixed(s, 96)
    return Ssz.merkleize(cs, 2n)

# A Bytes20 value (an execution address) as its root.
def Hex.bytes20_root(s: String) -> Maybe<&2, B32>:
  do Maybe<&2, B32>:
    cs : List<&2, B32> <- Hex.fixed(s, 20)
    return Merk.first(cs, B32.zero())

def Pubkey.root(k: Pubkey) -> B32:
  match k:
    case Pubkey{hi, lo}:
      match lo:
        case B16{l0, l1, l2, l3}:
          Sha.hash64(hi, B32{l0, l1, l2, l3, 0, 0, 0, 0})

# Phase 2 containers
# ==================
#
# Signatures and bit fields are kept as their roots: the signer needs only
# the root of each field.

type VoluntaryExit is Data:
  VoluntaryExit{epoch: U64, validator_index: U64}

def VoluntaryExit.root(e: VoluntaryExit) -> B32:
  match e:
    case VoluntaryExit{ep, vi}:
      Sha.hash64(Ssz.u64(ep), Ssz.u64(vi))

type SyncSelection is Data:
  SyncSelection{slot: U64, subcommittee_index: U64}

def SyncSelection.root(s: SyncSelection) -> B32:
  match s:
    case SyncSelection{slot, sub}:
      Sha.hash64(Ssz.u64(slot), Ssz.u64(sub))

# aggregation_bits is a Bitvector[SYNC_COMMITTEE_SIZE / 4], at most 128 bits,
# so its root is one chunk.
type Contribution is Data:
  Contribution{slot: U64, beacon_block_root: B32, subcommittee_index: U64, bits_root: B32, signature_root: B32}

def Contribution.root(c: Contribution) -> B32:
  match c:
    case Contribution{slot, bbr, sub, bits, sig}:
      Ssz.merkle8(Ssz.u64(slot), bbr, Ssz.u64(sub), bits, sig, B32.zero(), B32.zero(), B32.zero())

type ContributionAndProof is Data:
  ContributionAndProof{aggregator_index: U64, contribution: Contribution, selection_proof_root: B32}

def ContributionAndProof.root(c: ContributionAndProof) -> B32:
  match c:
    case ContributionAndProof{ai, con, sel}:
      Ssz.merkle4(Ssz.u64(ai), Contribution.root(con), sel, B32.zero())

type Registration is Data:
  Registration{fee_recipient_root: B32, gas_limit: U64, timestamp: U64, pubkey: Pubkey}

def Registration.root(r: Registration) -> B32:
  match r:
    case Registration{fee, gas, ts, pk}:
      Ssz.merkle4(fee, Ssz.u64(gas), Ssz.u64(ts), Pubkey.root(pk))

# The three Attestation shapes. Base has a Bitlist[MAX_VALIDATORS_PER_COMMITTEE]
# (depth 3). Electra has a Bitlist[MAX_VALIDATORS_PER_COMMITTEE *
# MAX_COMMITTEES_PER_SLOT], whose depth depends on the preset, and
# committee_bits. Gloas has a ProgressiveBitlist and is a ProgressiveContainer
# with all four fields active (EIP-7688).
type Attestation is Data:
  AttBase{bits: Bitlist, data: AttestationData, signature_root: B32}
  AttElectra{bits: Bitlist, depth: Nat, data: AttestationData, signature_root: B32, committee_bits_root: B32}
  AttGloas{bits: Bitlist, data: AttestationData, signature_root: B32, committee_bits_root: B32}

# The active_fields chunk of a ProgressiveContainer with fields 0..3 active.
def Ssz.active4() -> B32:
  B32{251658240, 0, 0, 0, 0, 0, 0, 0}

def Attestation.root(a: Attestation) -> B32:
  match a:
    case AttBase{bits, data, sig}:
      Ssz.merkle4(Bitlist.root(bits, 3n), AttestationData.root(data), sig, B32.zero())
    case AttElectra{bits, depth, data, sig, cb}:
      Ssz.merkle4(Bitlist.root(bits, depth), AttestationData.root(data), sig, cb)
    case AttGloas{bits, data, sig, cb}:
      Sha.hash64(Ssz.progressive([Bitlist.root_progressive(bits), AttestationData.root(data), sig, cb]),
        Ssz.active4())

def Attestation.slot(a: Attestation) -> U64:
  match a:
    case AttBase{bits, data, sig}:
      match data:
        case AttestationData{slot, index, bbr, src, tgt}:
          slot
    case AttElectra{bits, depth, data, sig, cb}:
      match data:
        case AttestationData{slot, index, bbr, src, tgt}:
          slot
    case AttGloas{bits, data, sig, cb}:
      match data:
        case AttestationData{slot, index, bbr, src, tgt}:
          slot

type AggregateAndProof is Data:
  AggregateAndProof{aggregator_index: U64, aggregate: Attestation, selection_proof_root: B32}

def AggregateAndProof.root(a: AggregateAndProof) -> B32:
  match a:
    case AggregateAndProof{ai, att, sel}:
      Ssz.merkle4(Ssz.u64(ai), Attestation.root(att), sel, B32.zero())
