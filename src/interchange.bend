# EIP-3076 interchange import (docs/SPEC.md section 8.9).
#
# An import is all or nothing. Each imported record goes through the
# definitions of spec/safety.bend, against the state with the records
# imported before it:
# - a record that the state already has is skipped;
# - a record that is slashable with the state, or an attestation with its
#   source after its target, fails the whole import, and nothing changes;
# - any other record is added.
# The EIP-3076 test vectors allow this: an implementation can reject an
# interchange that holds slashable data.
#
# A key that has no low watermark gets one: the lowest slot, or the lowest
# source and target, in the imported data for that key. An import never
# changes a watermark that exists.
#
# Like a decision, an import gives log events, and the new state is
# apply_all of them. LAWS.bend states L7 and L8 on Imp.after.
import Base
import ./ssz.bend as S
import ./slashing.bend as Slash
import ./store.bend as St
import ./json.bend as J
import ./request.bend as R
import ../spec/safety.bend as Spec

type Entry is Data:
  Entry{key: S.Pubkey, blocks: List<&2, Slash.BlockRec>, atts: List<&2, Slash.AttRec>}

type Interchange is Data:
  Interchange{gvr: S.B32, data: List<&2, Entry>}

# One step of an import.
type Item is Data:
  IBlock{key: S.Pubkey, rec: Slash.BlockRec}
  IAtt{key: S.Pubkey, rec: Slash.AttRec}
  IBlockMark{key: S.Pubkey, slot: S.U64}
  IAttMark{key: S.Pubkey, mark: Slash.AttMark}

# Items
# =====

def Items.blocks(+k: S.Pubkey, bs: List<&2, Slash.BlockRec>) -> List<&2, Item>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      Con{IBlock{k, b}, Items.blocks(k, rest)}

def Items.atts(+k: S.Pubkey, as: List<&2, Slash.AttRec>) -> List<&2, Item>:
  match as:
    case Nil{}:
      []
    case Con{a, rest}:
      Con{IAtt{k, a}, Items.atts(k, rest)}

def Min(+a: S.U64, +b: S.U64) -> S.U64:
  Bool.pick(S.U64, S.U64.is_lt(b, a), b, a)

def Min.slot(bs: List<&2, Slash.BlockRec>, +m: S.U64) -> S.U64:
  match bs:
    case Nil{}:
      m
    case Con{b, rest}:
      match b:
        case Slash.BlockRec{s, r}:
          Min.slot(rest, Min(m, s))

def Min.mark(as: List<&2, Slash.AttRec>, +ms: S.U64, +mt: S.U64) -> Slash.AttMark:
  match as:
    case Nil{}:
      Slash.AttMark{ms, mt}
    case Con{a, rest}:
      match a:
        case Slash.AttRec{s, t, r}:
          Min.mark(rest, Min(ms, s), Min(mt, t))

def Items.block_mark(+k: S.Pubkey, bs: List<&2, Slash.BlockRec>) -> List<&2, Item>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case Slash.BlockRec{s, r}:
          [IBlockMark{k, Min.slot(rest, s)}]

def Items.att_mark(+k: S.Pubkey, as: List<&2, Slash.AttRec>) -> List<&2, Item>:
  match as:
    case Nil{}:
      []
    case Con{a, rest}:
      match a:
        case Slash.AttRec{s, t, r}:
          [IAttMark{k, Min.mark(rest, s, t)}]

def Items.entry(e: Entry) -> List<&2, Item>:
  match e:
    case Entry{+k, +bs, +as}:
      List.append(&2, Item, Items.blocks(k, bs),
        List.append(&2, Item, Items.atts(k, as),
          List.append(&2, Item, Items.block_mark(k, bs), Items.att_mark(k, as))))

def Items.of(es: List<&2, Entry>) -> List<&2, Item>:
  match es:
    case Nil{}:
      []
    case Con{e, rest}:
      List.append(&2, Item, Items.entry(e), Items.of(rest))

# One item
# ========

def Store.entries(s: St.Store) -> List<&2, St.Entry>:
  match s:
    case St.Store{g, es}:
      es

def Key.state(+s: St.Store, +k: S.Pubkey) -> Slash.KeyState:
  St.Store.get(Store.entries(s), k)

def KS.blocks(ks: Slash.KeyState) -> List<&2, Slash.BlockRec>:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      bs

def KS.atts(ks: Slash.KeyState) -> List<&2, Slash.AttRec>:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      as

def KS.block_mark(ks: Slash.KeyState) -> Maybe<&2, S.U64>:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      bm

def KS.att_mark(ks: Slash.KeyState) -> Maybe<&2, Slash.AttMark>:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      am

# The item is allowed: not slashable with the state.
def Item.ok(+s: St.Store, i: Item) -> Bool:
  match i:
    case IBlock{+k, +r}:
      Spec.has_block(r, KS.blocks(Key.state(s, k)))
        || Bool.not(Spec.block_clashes_any(r, KS.blocks(Key.state(s, k))))
    case IAtt{+k, +r}:
      Spec.att_ordered(r) && (Spec.has_att(r, KS.atts(Key.state(s, k)))
        || Bool.not(Spec.att_clashes_any(r, KS.atts(Key.state(s, k)))))
    case IBlockMark{k, m}:
      True{}
    case IAttMark{k, m}:
      True{}

# The events of the item: none for a record the state has, or for a key
# that has a watermark.
def Item.events(+s: St.Store, i: Item) -> List<&2, St.LogEvent>:
  match i:
    case IBlock{+k, +r}:
      Bool.pick(List<&2, St.LogEvent>, Spec.has_block(r, KS.blocks(Key.state(s, k))), [], [St.EBlock{k, r}])
    case IAtt{+k, +r}:
      Bool.pick(List<&2, St.LogEvent>, Spec.has_att(r, KS.atts(Key.state(s, k))), [], [St.EAtt{k, r}])
    case IBlockMark{+k, m}:
      Bool.pick(List<&2, St.LogEvent>, Maybe.is_none(&2, S.U64, KS.block_mark(Key.state(s, k))), [St.EBlockMark{k, m}], [])
    case IAttMark{+k, m}:
      Bool.pick(List<&2, St.LogEvent>, Maybe.is_none(&2, Slash.AttMark, KS.att_mark(Key.state(s, k))), [St.EAttMark{k, m}], [])

# All items
# =========

type Res is Data:
  Res{events: List<&2, St.LogEvent>, ok: Bool}

def Res.cons(+e: List<&2, St.LogEvent>, ok: Bool, r: Res) -> Res:
  match r:
    case Res{es, ok2}:
      Res{List.append(&2, St.LogEvent, e, es), Bool.and(ok, ok2)}

# Each item sees the state after the items before it.
def Imp.go(its: List<&2, Item>, +s: St.Store) -> Res:
  match its:
    case Nil{}:
      Res{[], True{}}
    case Con{+i, rest}:
      Res.cons(Item.events(s, i), Item.ok(s, i), Imp.go(rest, St.Store.apply_all(Item.events(s, i), s)))

def Imp.fin(p: List<&2, St.LogEvent>, r: Res) -> Maybe<&2, List<&2, St.LogEvent>>:
  match r:
    case Res{es, ok}:
      match ok:
        case True{}:
          Some{List.append(&2, St.LogEvent, p, es)}
        case False{}:
          None{}

def Imp.run.go(pre: Maybe<&2, List<&2, St.LogEvent>>, +s: St.Store, its: List<&2, Item>) -> Maybe<&2, List<&2, St.LogEvent>>:
  match pre:
    case None{}:
      None{}
    case Some{+p}:
      Imp.fin(p, Imp.go(its, St.Store.apply_all(p, s)))

# The events of an import, or None if it fails: its genesis validators root
# is not the root of the store, or its data is slashable.
def Imp.run(s: St.Store, ix: Interchange) -> Maybe<&2, List<&2, St.LogEvent>>:
  match s:
    case St.Store{+have, +es}:
      match ix:
        case Interchange{+g, data}:
          Imp.run.go(St.Store.decide.gvr(g, have), St.Store{have, es}, Items.of(data))

def Imp.after.go(m: Maybe<&2, List<&2, St.LogEvent>>, s: St.Store) -> St.Store:
  match m:
    case None{}:
      s
    case Some{es}:
      St.Store.apply_all(es, s)

# The store after an import: unchanged if the import fails.
def Imp.after(+s: St.Store, ix: Interchange) -> St.Store:
  Imp.after.go(Imp.run(s, ix), s)

# Reading the JSON
# ================

def Read.root.at(m: Maybe<&2, J.Json>) -> Maybe<&2, Maybe<&2, S.B32>>:
  match m:
    case None{}:
      Some{None{}}
    case Some{+j}:
      Bool.pick(Maybe<&2, Maybe<&2, S.B32>>, J.Json.is_null(j), Some{None{}},
        Maybe.map(&2, S.B32, Maybe<&2, S.B32>, x => Some{x}, R.Dec.b32(j)))

def Read.root(o: J.Json) -> Maybe<&2, Maybe<&2, S.B32>>:
  match o:
    case J.JObj{fs}:
      Read.root.at(J.Json.find(fs, "signing_root"))
    case _:
      None{}

def Read.block(+o: J.Json) -> Maybe<&2, Slash.BlockRec>:
  do Maybe<&2, Slash.BlockRec>:
    s : S.U64 <- R.Get.u64(o, "slot")
    r : Maybe<&2, S.B32> <- Read.root(o)
    return Slash.BlockRec{s, r}

def Read.att(+o: J.Json) -> Maybe<&2, Slash.AttRec>:
  do Maybe<&2, Slash.AttRec>:
    s : S.U64 <- R.Get.u64(o, "source_epoch")
    t : S.U64 <- R.Get.u64(o, "target_epoch")
    r : Maybe<&2, S.B32> <- Read.root(o)
    return Slash.AttRec{s, t, r}

def Read.blocks(xs: List<&2, J.Json>) -> Maybe<&2, List<&2, Slash.BlockRec>>:
  match xs:
    case Nil{}:
      Some{[]}
    case Con{+x, rest}:
      do Maybe<&2, List<&2, Slash.BlockRec>>:
        b : Slash.BlockRec <- Read.block(x)
        bs : List<&2, Slash.BlockRec> <- Read.blocks(rest)
        return Con{b, bs}

def Read.atts(xs: List<&2, J.Json>) -> Maybe<&2, List<&2, Slash.AttRec>>:
  match xs:
    case Nil{}:
      Some{[]}
    case Con{+x, rest}:
      do Maybe<&2, List<&2, Slash.AttRec>>:
        a : Slash.AttRec <- Read.att(x)
        as : List<&2, Slash.AttRec> <- Read.atts(rest)
        return Con{a, as}

# An array field: a missing field is an empty array.
def Read.arr(m: Maybe<&2, J.Json>) -> Maybe<&2, List<&2, J.Json>>:
  match m:
    case None{}:
      Some{[]}
    case Some{j}:
      match j:
        case J.JArr{xs}:
          Some{xs}
        case _:
          None{}

def Read.entry(+o: J.Json) -> Maybe<&2, Entry>:
  do Maybe<&2, Entry>:
    kj : J.Json <- J.Json.get(o, "pubkey")
    ks : String <- J.Json.str(kj)
    k : S.Pubkey <- S.Hex.read_pubkey(ks)
    bj : List<&2, J.Json> <- Read.arr(J.Json.get(o, "signed_blocks"))
    aj : List<&2, J.Json> <- Read.arr(J.Json.get(o, "signed_attestations"))
    bs : List<&2, Slash.BlockRec> <- Read.blocks(bj)
    as : List<&2, Slash.AttRec> <- Read.atts(aj)
    return Entry{k, bs, as}

def Read.entries(xs: List<&2, J.Json>) -> Maybe<&2, List<&2, Entry>>:
  match xs:
    case Nil{}:
      Some{[]}
    case Con{+x, rest}:
      do Maybe<&2, List<&2, Entry>>:
        e : Entry <- Read.entry(x)
        es : List<&2, Entry> <- Read.entries(rest)
        return Con{e, es}

def Read.version(+s: String) -> Maybe<&2, Unit>:
  Bool.pick(Maybe<&2, Unit>, String.eq(s, "5"), Some{Unit{}}, None{})

# Interchange format version 5.
def Interchange.read(text: String) -> Maybe<&2, Interchange>:
  do Maybe<&2, Interchange>:
    +j : J.Json <- J.Json.parse(text)
    +meta : J.Json <- J.Json.get(j, "metadata")
    vj : J.Json <- J.Json.get(meta, "interchange_format_version")
    v : String <- J.Json.str(vj)
    u : Unit <- Read.version(v)
    gj : J.Json <- J.Json.get(meta, "genesis_validators_root")
    g : S.B32 <- R.Dec.b32(gj)
    dj : List<&2, J.Json> <- Read.arr(J.Json.get(j, "data"))
    es : List<&2, Entry> <- Read.entries(dj)
    return Interchange{g, es}
