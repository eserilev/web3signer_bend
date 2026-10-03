# Proofs of the import laws L7 and L8 (src/interchange.bend). Both follow
# one shape: an invariant of one key holds for the store before each item,
# each item keeps it, and the events of the gvr check do not touch a key.
import Base
import ../src/ssz.bend as S
import ../src/slashing.bend as Slash
import ../src/store.bend as St
import ../src/interchange.bend as I
import ../spec/safety.bend as Spec
import ../spec/store.bend as Sto
import ../spec/import.bend as SpI
import ./lemmas.bend as Lm

# Store lemmas
# ============

def get_put_same.con(b: Bool, +key: S.Pubkey, +k: S.Pubkey, +st: Slash.KeyState, -old: Slash.KeyState,
  -rest: List<&2, St.Entry>, e: {b == S.Pubkey.is_eq(key, k) : Bool},
  ih: {St.Store.get(St.Store.put(rest, key, st), key) == st : Slash.KeyState})
  -> {St.Store.get(Bool.pick(List<&2, St.Entry>, b, Con{St.Entry{k, st}, rest},
       Con{St.Entry{k, old}, St.Store.put(rest, key, st)}), key) == st : Slash.KeyState}:
  match b:
    case True{}:
      %e : {Bool.pick(Slash.KeyState, _, st, St.Store.get(rest, key)) == st : Slash.KeyState}
      {==}
    case False{}:
      %e : {Bool.pick(Slash.KeyState, _, old, St.Store.get(St.Store.put(rest, key, st), key)) == st : Slash.KeyState}
      ih

def get_put_same(es: List<&2, St.Entry>, +key: S.Pubkey, +st: Slash.KeyState)
  -> {St.Store.get(St.Store.put(es, key, st), key) == st : Slash.KeyState}:
  match es:
    case Nil{}:
      %Lm.Pubkey.is_eq_refl(key) : {Bool.pick(Slash.KeyState, _, st, Slash.KeyState.empty()) == st : Slash.KeyState}
      {==}
    case Con{e, +rest}:
      match e:
        case St.Entry{+k, +old}:
          get_put_same.con(S.Pubkey.is_eq(key, k), key, k, st, old, rest, {==}, get_put_same(rest, key, st))

def get_put_other.con(b: Bool, +key: S.Pubkey, +k: S.Pubkey, +other: S.Pubkey, +st: Slash.KeyState, +old: Slash.KeyState,
  +rest: List<&2, St.Entry>, e: {b == S.Pubkey.is_eq(key, k) : Bool},
  h: {S.Pubkey.is_eq(other, key) == False{} : Bool},
  ih: {St.Store.get(St.Store.put(rest, key, st), other) == St.Store.get(rest, other) : Slash.KeyState})
  -> {St.Store.get(Bool.pick(List<&2, St.Entry>, b, Con{St.Entry{k, st}, rest},
       Con{St.Entry{k, old}, St.Store.put(rest, key, st)}), other)
     == Bool.pick(Slash.KeyState, S.Pubkey.is_eq(other, k), old, St.Store.get(rest, other)) : Slash.KeyState}:
  match b:
    case True{}:
      %Lm.Pubkey.eq_of(key, k, Equal.sym(Bool, True{}, S.Pubkey.is_eq(key, k), e))
        : {Bool.pick(Slash.KeyState, S.Pubkey.is_eq(other, _), st, St.Store.get(rest, other))
           == Bool.pick(Slash.KeyState, S.Pubkey.is_eq(other, _), old, St.Store.get(rest, other)) : Slash.KeyState}
      %Equal.sym(Bool, S.Pubkey.is_eq(other, key), False{}, h)
        : {Bool.pick(Slash.KeyState, _, st, St.Store.get(rest, other))
           == Bool.pick(Slash.KeyState, _, old, St.Store.get(rest, other)) : Slash.KeyState}
      {==}
    case False{}:
      %ih : {Bool.pick(Slash.KeyState, S.Pubkey.is_eq(other, k), old, St.Store.get(St.Store.put(rest, key, st), other))
             == Bool.pick(Slash.KeyState, S.Pubkey.is_eq(other, k), old, _) : Slash.KeyState}
      {==}

def get_put_other(es: List<&2, St.Entry>, +key: S.Pubkey, +other: S.Pubkey, +st: Slash.KeyState,
  +h: {S.Pubkey.is_eq(other, key) == False{} : Bool})
  -> {St.Store.get(St.Store.put(es, key, st), other) == St.Store.get(es, other) : Slash.KeyState}:
  match es:
    case Nil{}:
      %Equal.sym(Bool, S.Pubkey.is_eq(other, key), False{}, h)
        : {Bool.pick(Slash.KeyState, _, st, Slash.KeyState.empty()) == Slash.KeyState.empty() : Slash.KeyState}
      {==}
    case Con{e, +rest}:
      match e:
        case St.Entry{+k, +old}:
          get_put_other.con(S.Pubkey.is_eq(key, k), key, k, other, st, old, rest, {==}, h,
            get_put_other(rest, key, other, st, h))

def Ent(s: St.Store) -> List<&2, St.Entry>:
  match s:
    case St.Store{g, es}:
      es

def key_state_ent(+s: St.Store, +key: S.Pubkey) -> {St.Store.get(Ent(s), key) == Sto.key_state(s, key) : Slash.KeyState}:
  match s:
    case St.Store{g, es}:
      {==}

def AllGvr(es: List<&2, St.LogEvent>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, rest}:
      match e:
        case St.EGvr{g}:
          AllGvr(rest)
        case St.EBlock{k, r}:
          False{}
        case St.EAtt{k, r}:
          False{}
        case St.EBlockMark{k, m}:
          False{}
        case St.EAttMark{k, m}:
          False{}

def PreGvr(p: Maybe<&2, List<&2, St.LogEvent>>) -> Bool:
  match p:
    case None{}:
      True{}
    case Some{l}:
      AllGvr(l)

def pre_gvr_pick(b: Bool) -> {PreGvr(Bool.pick(Maybe<&2, List<&2, St.LogEvent>>, b, Some{[]}, None{})) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pre_gvr(+g: S.B32, have: Maybe<&2, S.B32>) -> {PreGvr(St.Store.decide.gvr(g, have)) == True{} : Bool}:
  match have:
    case None{}:
      {==}
    case Some{+x}:
      pre_gvr_pick(S.B32.is_eq(g, x))

def gvrs_keep(p: List<&2, St.LogEvent>, -g: Maybe<&2, S.B32>, +es: List<&2, St.Entry>, h: {AllGvr(p) == True{} : Bool})
  -> {es == Ent(St.Store.apply_all(p, St.Store{g, es})) : List<&2, St.Entry>}:
  match p:
    case Nil{}:
      {==}
    case Con{e, rest}:
      match e:
        case St.EGvr{x}:
          gvrs_keep(rest, Some{x}, es, h)
        case St.EBlock{k, r}:
          Empty.absurd({es == Ent(St.Store.apply_all(Con{St.EBlock{k, r}, rest}, St.Store{g, es})) : List<&2, St.Entry>}, Lm.Bool.ft(h))
        case St.EAtt{k, r}:
          Empty.absurd({es == Ent(St.Store.apply_all(Con{St.EAtt{k, r}, rest}, St.Store{g, es})) : List<&2, St.Entry>}, Lm.Bool.ft(h))
        case St.EBlockMark{k, m}:
          Empty.absurd({es == Ent(St.Store.apply_all(Con{St.EBlockMark{k, m}, rest}, St.Store{g, es})) : List<&2, St.Entry>}, Lm.Bool.ft(h))
        case St.EAttMark{k, m}:
          Empty.absurd({es == Ent(St.Store.apply_all(Con{St.EAttMark{k, m}, rest}, St.Store{g, es})) : List<&2, St.Entry>}, Lm.Bool.ft(h))

# The key state after the gvr events is the key state before them.
def gvr_key_state(+p: List<&2, St.LogEvent>, +s: St.Store, +key: S.Pubkey, h: {AllGvr(p) == True{} : Bool})
  -> {Sto.key_state(St.Store.apply_all(p, s), key) == Sto.key_state(s, key) : Slash.KeyState}:
  match s:
    case St.Store{+g, +es}:
      %key_state_ent(St.Store.apply_all(p, St.Store{g, es}), key) : {_ == St.Store.get(es, key) : Slash.KeyState}
      %gvrs_keep(p, g, es, h) : {St.Store.get(_, key) == St.Store.get(es, key) : Slash.KeyState}
      {==}

def apply_all_app(a: List<&2, St.LogEvent>, +b: List<&2, St.LogEvent>, +s: St.Store)
  -> {St.Store.apply_all(List.append(&2, St.LogEvent, a, b), s) == St.Store.apply_all(b, St.Store.apply_all(a, s)) : St.Store}:
  match a:
    case Nil{}:
      {==}
    case Con{x, rest}:
      apply_all_app(rest, b, St.Store.apply(s, x))

# Results
# =======

def Res.events(r: I.Res) -> List<&2, St.LogEvent>:
  match r:
    case I.Res{es, ok}:
      es

def Res.ok(r: I.Res) -> Bool:
  match r:
    case I.Res{es, ok}:
      ok

def res_events(+e: List<&2, St.LogEvent>, -o: Bool, r: I.Res)
  -> {Res.events(I.Res.cons(e, o, r)) == List.append(&2, St.LogEvent, e, Res.events(r)) : List<&2, St.LogEvent>}:
  match r:
    case I.Res{es, ok}:
      {==}

def res_ok(-e: List<&2, St.LogEvent>, +o: Bool, r: I.Res)
  -> {Res.ok(I.Res.cons(e, o, r)) == Bool.and(o, Res.ok(r)) : Bool}:
  match r:
    case I.Res{es, ok}:
      {==}

# Small facts
# ===========

def or_f(-a: Bool, -b: Bool, ea: {False{} == a : Bool}, h: {Bool.or(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  %Equal.sym(Bool, False{}, a, ea) : {Bool.or(_, b) == True{} : Bool}
  h

def tr_block(+es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +r: Slash.BlockRec, e: {key == k : S.Pubkey},
  h: {Bool.not(Spec.block_clashes_any(r, I.KS.blocks(St.Store.get(es, k)))) == True{} : Bool})
  -> {Bool.not(Spec.block_clashes_any(r, I.KS.blocks(St.Store.get(es, key)))) == True{} : Bool}:
  %Equal.sym(S.Pubkey, key, k, e) : {Bool.not(Spec.block_clashes_any(r, I.KS.blocks(St.Store.get(es, _)))) == True{} : Bool}
  h

def tr_att(+es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +r: Slash.AttRec, e: {key == k : S.Pubkey},
  h: {Bool.not(Spec.att_clashes_any(r, I.KS.atts(St.Store.get(es, k)))) == True{} : Bool})
  -> {Bool.not(Spec.att_clashes_any(r, I.KS.atts(St.Store.get(es, key)))) == True{} : Bool}:
  %Equal.sym(S.Pubkey, key, k, e) : {Bool.not(Spec.att_clashes_any(r, I.KS.atts(St.Store.get(es, _)))) == True{} : Bool}
  h

def tr_none_bm(+es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, e: {key == k : S.Pubkey},
  h: {True{} == Maybe.is_none(&2, S.U64, I.KS.block_mark(St.Store.get(es, k))) : Bool})
  -> {True{} == Maybe.is_none(&2, S.U64, I.KS.block_mark(St.Store.get(es, key))) : Bool}:
  %Equal.sym(S.Pubkey, key, k, e) : {True{} == Maybe.is_none(&2, S.U64, I.KS.block_mark(St.Store.get(es, _))) : Bool}
  h

def tr_none_am(+es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, e: {key == k : S.Pubkey},
  h: {True{} == Maybe.is_none(&2, Slash.AttMark, I.KS.att_mark(St.Store.get(es, k))) : Bool})
  -> {True{} == Maybe.is_none(&2, Slash.AttMark, I.KS.att_mark(St.Store.get(es, key))) : Bool}:
  %Equal.sym(S.Pubkey, key, k, e) : {True{} == Maybe.is_none(&2, Slash.AttMark, I.KS.att_mark(St.Store.get(es, _))) : Bool}
  h

# L7: one key state
# =================

def safe_add_block.go(+bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>, +r: Slash.BlockRec,
  pr: {Spec.blocks_safe(bs) == True{} : Bool} & {Spec.atts_safe(as) == True{} : Bool},
  hn: {Bool.not(Spec.block_clashes_any(r, bs)) == True{} : Bool})
  -> {True{} == Bool.and(Spec.blocks_safe(Con{r, bs}), Spec.atts_safe(as)) : Bool}:
  (hb, ha) = pr
  Lm.Bool.and_tt(Spec.blocks_safe(Con{r, bs}), Spec.atts_safe(as),
    Lm.Bool.and_tt(Bool.not(Spec.block_clashes_any(r, bs)), Spec.blocks_safe(bs),
      Equal.sym(Bool, Bool.not(Spec.block_clashes_any(r, bs)), True{}, hn),
      Equal.sym(Bool, Spec.blocks_safe(bs), True{}, hb)),
    Equal.sym(Bool, Spec.atts_safe(as), True{}, ha))

def safe_add_block(ks: Slash.KeyState, +r: Slash.BlockRec, hs: {Spec.safe(ks) == True{} : Bool},
  hn: {Bool.not(Spec.block_clashes_any(r, I.KS.blocks(ks))) == True{} : Bool})
  -> {Spec.safe(St.KeyState.add_block(ks, r)) == True{} : Bool}:
  match ks:
    case Slash.KeyState{+bs, +as, bm, am}:
      Equal.sym(Bool, True{}, Spec.safe(Slash.KeyState{Con{r, bs}, as, bm, am}),
        safe_add_block.go(bs, as, r, Lm.Bool.and_true(Spec.blocks_safe(bs), Spec.atts_safe(as), hs), hn))

def safe_add_att.go(+bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>, +r: Slash.AttRec,
  pr: {Spec.blocks_safe(bs) == True{} : Bool} & {Spec.atts_safe(as) == True{} : Bool},
  ho: {Spec.att_ordered(r) == True{} : Bool},
  hn: {Bool.not(Spec.att_clashes_any(r, as)) == True{} : Bool})
  -> {True{} == Bool.and(Spec.blocks_safe(bs), Spec.atts_safe(Con{r, as})) : Bool}:
  (hb, ha) = pr
  Lm.Bool.and_tt(Spec.blocks_safe(bs), Spec.atts_safe(Con{r, as}),
    Equal.sym(Bool, Spec.blocks_safe(bs), True{}, hb),
    Lm.Bool.and_tt(Bool.and(Spec.att_ordered(r), Bool.not(Spec.att_clashes_any(r, as))), Spec.atts_safe(as),
      Lm.Bool.and_tt(Spec.att_ordered(r), Bool.not(Spec.att_clashes_any(r, as)),
        Equal.sym(Bool, Spec.att_ordered(r), True{}, ho),
        Equal.sym(Bool, Bool.not(Spec.att_clashes_any(r, as)), True{}, hn)),
      Equal.sym(Bool, Spec.atts_safe(as), True{}, ha)))

def safe_add_att(ks: Slash.KeyState, +r: Slash.AttRec, hs: {Spec.safe(ks) == True{} : Bool},
  ho: {Spec.att_ordered(r) == True{} : Bool},
  hn: {Bool.not(Spec.att_clashes_any(r, I.KS.atts(ks))) == True{} : Bool})
  -> {Spec.safe(St.KeyState.add_att(ks, r)) == True{} : Bool}:
  match ks:
    case Slash.KeyState{+bs, +as, bm, am}:
      Equal.sym(Bool, True{}, Spec.safe(Slash.KeyState{bs, Con{r, as}, bm, am}),
        safe_add_att.go(bs, as, r, Lm.Bool.and_true(Spec.blocks_safe(bs), Spec.atts_safe(as), hs), ho, hn))

def safe_set_bm(ks: Slash.KeyState, -m: S.U64, hs: {Spec.safe(ks) == True{} : Bool})
  -> {Spec.safe(St.KeyState.set_block_mark(ks, m)) == True{} : Bool}:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      hs

def safe_set_am(ks: Slash.KeyState, -m: Slash.AttMark, hs: {Spec.safe(ks) == True{} : Bool})
  -> {Spec.safe(St.KeyState.set_att_mark(ks, m)) == True{} : Bool}:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      hs

# L7: one event
# =============

def ev_block_safe(+es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +r: Slash.BlockRec,
  c: Bool, ec: {c == S.Pubkey.is_eq(key, k) : Bool},
  hs: {Spec.safe(St.Store.get(es, key)) == True{} : Bool},
  hn: {Bool.not(Spec.block_clashes_any(r, I.KS.blocks(St.Store.get(es, k)))) == True{} : Bool})
  -> {Spec.safe(St.Store.get(St.Store.put(es, k, St.KeyState.add_block(St.Store.get(es, k), r)), key)) == True{} : Bool}:
  match c:
    case True{}:
      +e = Lm.Pubkey.eq_of(key, k, Equal.sym(Bool, True{}, S.Pubkey.is_eq(key, k), ec))
      %e : {Spec.safe(St.Store.get(St.Store.put(es, _, St.KeyState.add_block(St.Store.get(es, _), r)), key)) == True{} : Bool}
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, key, St.KeyState.add_block(St.Store.get(es, key), r)), key),
        St.KeyState.add_block(St.Store.get(es, key), r), get_put_same(es, key, St.KeyState.add_block(St.Store.get(es, key), r)))
        : {Spec.safe(_) == True{} : Bool}
      safe_add_block(St.Store.get(es, key), r, hs, tr_block(es, key, k, r, e, hn))
    case False{}:
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, k, St.KeyState.add_block(St.Store.get(es, k), r)), key),
        St.Store.get(es, key), get_put_other(es, k, key, St.KeyState.add_block(St.Store.get(es, k), r), Equal.sym(Bool, False{}, S.Pubkey.is_eq(key, k), ec)))
        : {Spec.safe(_) == True{} : Bool}
      hs

def ev_att_safe(+es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +r: Slash.AttRec,
  c: Bool, ec: {c == S.Pubkey.is_eq(key, k) : Bool},
  hs: {Spec.safe(St.Store.get(es, key)) == True{} : Bool},
  ho: {Spec.att_ordered(r) == True{} : Bool},
  hn: {Bool.not(Spec.att_clashes_any(r, I.KS.atts(St.Store.get(es, k)))) == True{} : Bool})
  -> {Spec.safe(St.Store.get(St.Store.put(es, k, St.KeyState.add_att(St.Store.get(es, k), r)), key)) == True{} : Bool}:
  match c:
    case True{}:
      +e = Lm.Pubkey.eq_of(key, k, Equal.sym(Bool, True{}, S.Pubkey.is_eq(key, k), ec))
      %e : {Spec.safe(St.Store.get(St.Store.put(es, _, St.KeyState.add_att(St.Store.get(es, _), r)), key)) == True{} : Bool}
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, key, St.KeyState.add_att(St.Store.get(es, key), r)), key),
        St.KeyState.add_att(St.Store.get(es, key), r), get_put_same(es, key, St.KeyState.add_att(St.Store.get(es, key), r)))
        : {Spec.safe(_) == True{} : Bool}
      safe_add_att(St.Store.get(es, key), r, hs, ho, tr_att(es, key, k, r, e, hn))
    case False{}:
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, k, St.KeyState.add_att(St.Store.get(es, k), r)), key),
        St.Store.get(es, key), get_put_other(es, k, key, St.KeyState.add_att(St.Store.get(es, k), r), Equal.sym(Bool, False{}, S.Pubkey.is_eq(key, k), ec)))
        : {Spec.safe(_) == True{} : Bool}
      hs

def ev_bm_safe(+es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +m: S.U64,
  c: Bool, ec: {c == S.Pubkey.is_eq(key, k) : Bool}, hs: {Spec.safe(St.Store.get(es, key)) == True{} : Bool})
  -> {Spec.safe(St.Store.get(St.Store.put(es, k, St.KeyState.set_block_mark(St.Store.get(es, k), m)), key)) == True{} : Bool}:
  match c:
    case True{}:
      +e = Lm.Pubkey.eq_of(key, k, Equal.sym(Bool, True{}, S.Pubkey.is_eq(key, k), ec))
      %e : {Spec.safe(St.Store.get(St.Store.put(es, _, St.KeyState.set_block_mark(St.Store.get(es, _), m)), key)) == True{} : Bool}
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, key, St.KeyState.set_block_mark(St.Store.get(es, key), m)), key),
        St.KeyState.set_block_mark(St.Store.get(es, key), m), get_put_same(es, key, St.KeyState.set_block_mark(St.Store.get(es, key), m)))
        : {Spec.safe(_) == True{} : Bool}
      safe_set_bm(St.Store.get(es, key), m, hs)
    case False{}:
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, k, St.KeyState.set_block_mark(St.Store.get(es, k), m)), key),
        St.Store.get(es, key), get_put_other(es, k, key, St.KeyState.set_block_mark(St.Store.get(es, k), m), Equal.sym(Bool, False{}, S.Pubkey.is_eq(key, k), ec)))
        : {Spec.safe(_) == True{} : Bool}
      hs

def ev_am_safe(+es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +m: Slash.AttMark,
  c: Bool, ec: {c == S.Pubkey.is_eq(key, k) : Bool}, hs: {Spec.safe(St.Store.get(es, key)) == True{} : Bool})
  -> {Spec.safe(St.Store.get(St.Store.put(es, k, St.KeyState.set_att_mark(St.Store.get(es, k), m)), key)) == True{} : Bool}:
  match c:
    case True{}:
      +e = Lm.Pubkey.eq_of(key, k, Equal.sym(Bool, True{}, S.Pubkey.is_eq(key, k), ec))
      %e : {Spec.safe(St.Store.get(St.Store.put(es, _, St.KeyState.set_att_mark(St.Store.get(es, _), m)), key)) == True{} : Bool}
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, key, St.KeyState.set_att_mark(St.Store.get(es, key), m)), key),
        St.KeyState.set_att_mark(St.Store.get(es, key), m), get_put_same(es, key, St.KeyState.set_att_mark(St.Store.get(es, key), m)))
        : {Spec.safe(_) == True{} : Bool}
      safe_set_am(St.Store.get(es, key), m, hs)
    case False{}:
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, k, St.KeyState.set_att_mark(St.Store.get(es, k), m)), key),
        St.Store.get(es, key), get_put_other(es, k, key, St.KeyState.set_att_mark(St.Store.get(es, k), m), Equal.sym(Bool, False{}, S.Pubkey.is_eq(key, k), ec)))
        : {Spec.safe(_) == True{} : Bool}
      hs

# L7: one item
# ============

def item_block_safe.m(-g: Maybe<&2, S.B32>, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +r: Slash.BlockRec,
  b: Bool, eb: {b == Spec.has_block(r, I.KS.blocks(St.Store.get(es, k))) : Bool},
  hs: {Spec.safe(St.Store.get(es, key)) == True{} : Bool},
  hok: {Bool.or(Spec.has_block(r, I.KS.blocks(St.Store.get(es, k))), Bool.not(Spec.block_clashes_any(r, I.KS.blocks(St.Store.get(es, k))))) == True{} : Bool})
  -> {Spec.safe(Sto.key_state(St.Store.apply_all(Bool.pick(List<&2, St.LogEvent>, b, [], [St.EBlock{k, r}]), St.Store{g, es}), key)) == True{} : Bool}:
  match b:
    case True{}:
      hs
    case False{}:
      ev_block_safe(es, key, k, r, S.Pubkey.is_eq(key, k), {==}, hs,
        or_f(Spec.has_block(r, I.KS.blocks(St.Store.get(es, k))), Bool.not(Spec.block_clashes_any(r, I.KS.blocks(St.Store.get(es, k)))), eb, hok))

def item_block_safe(+g: Maybe<&2, S.B32>, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +r: Slash.BlockRec,
  b: Bool, +eb: {b == Spec.has_block(r, I.KS.blocks(St.Store.get(es, k))) : Bool},
  hs: {Spec.safe(St.Store.get(es, key)) == True{} : Bool},
  hok: {I.Item.ok(St.Store{g, es}, I.IBlock{k, r}) == True{} : Bool})
  -> {Spec.safe(Sto.key_state(St.Store.apply_all(I.Item.events(St.Store{g, es}, I.IBlock{k, r}), St.Store{g, es}), key)) == True{} : Bool}:
  %eb : {Spec.safe(Sto.key_state(St.Store.apply_all(Bool.pick(List<&2, St.LogEvent>, _, [], [St.EBlock{k, r}]), St.Store{g, es}), key)) == True{} : Bool}
  item_block_safe.m(g, es, key, k, r, b, eb, hs, hok)

def item_att_safe.no(+es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +r: Slash.AttRec,
  eb: {False{} == Spec.has_att(r, I.KS.atts(St.Store.get(es, k))) : Bool},
  hs: {Spec.safe(St.Store.get(es, key)) == True{} : Bool},
  pr: {Spec.att_ordered(r) == True{} : Bool}
    & {Bool.or(Spec.has_att(r, I.KS.atts(St.Store.get(es, k))), Bool.not(Spec.att_clashes_any(r, I.KS.atts(St.Store.get(es, k))))) == True{} : Bool})
  -> {Spec.safe(St.Store.get(St.Store.put(es, k, St.KeyState.add_att(St.Store.get(es, k), r)), key)) == True{} : Bool}:
  (ho, hor) = pr
  ev_att_safe(es, key, k, r, S.Pubkey.is_eq(key, k), {==}, hs, ho,
    or_f(Spec.has_att(r, I.KS.atts(St.Store.get(es, k))), Bool.not(Spec.att_clashes_any(r, I.KS.atts(St.Store.get(es, k)))), eb, hor))

def item_att_safe.m(-g: Maybe<&2, S.B32>, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +r: Slash.AttRec,
  b: Bool, eb: {b == Spec.has_att(r, I.KS.atts(St.Store.get(es, k))) : Bool},
  hs: {Spec.safe(St.Store.get(es, key)) == True{} : Bool},
  hok: {Bool.and(Spec.att_ordered(r), Bool.or(Spec.has_att(r, I.KS.atts(St.Store.get(es, k))), Bool.not(Spec.att_clashes_any(r, I.KS.atts(St.Store.get(es, k)))))) == True{} : Bool})
  -> {Spec.safe(Sto.key_state(St.Store.apply_all(Bool.pick(List<&2, St.LogEvent>, b, [], [St.EAtt{k, r}]), St.Store{g, es}), key)) == True{} : Bool}:
  match b:
    case True{}:
      hs
    case False{}:
      item_att_safe.no(es, key, k, r, eb, hs,
        Lm.Bool.and_true(Spec.att_ordered(r),
          Bool.or(Spec.has_att(r, I.KS.atts(St.Store.get(es, k))), Bool.not(Spec.att_clashes_any(r, I.KS.atts(St.Store.get(es, k))))), hok))

def item_att_safe(+g: Maybe<&2, S.B32>, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +r: Slash.AttRec,
  b: Bool, +eb: {b == Spec.has_att(r, I.KS.atts(St.Store.get(es, k))) : Bool},
  hs: {Spec.safe(St.Store.get(es, key)) == True{} : Bool},
  hok: {I.Item.ok(St.Store{g, es}, I.IAtt{k, r}) == True{} : Bool})
  -> {Spec.safe(Sto.key_state(St.Store.apply_all(I.Item.events(St.Store{g, es}, I.IAtt{k, r}), St.Store{g, es}), key)) == True{} : Bool}:
  %eb : {Spec.safe(Sto.key_state(St.Store.apply_all(Bool.pick(List<&2, St.LogEvent>, _, [], [St.EAtt{k, r}]), St.Store{g, es}), key)) == True{} : Bool}
  item_att_safe.m(g, es, key, k, r, b, eb, hs, hok)

def item_bm_safe.m(-g: Maybe<&2, S.B32>, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +m: S.U64, b: Bool,
  hs: {Spec.safe(St.Store.get(es, key)) == True{} : Bool})
  -> {Spec.safe(Sto.key_state(St.Store.apply_all(Bool.pick(List<&2, St.LogEvent>, b, [St.EBlockMark{k, m}], []), St.Store{g, es}), key)) == True{} : Bool}:
  match b:
    case True{}:
      ev_bm_safe(es, key, k, m, S.Pubkey.is_eq(key, k), {==}, hs)
    case False{}:
      hs

def item_bm_safe(+g: Maybe<&2, S.B32>, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +m: S.U64,
  b: Bool, eb: {b == Maybe.is_none(&2, S.U64, I.KS.block_mark(St.Store.get(es, k))) : Bool},
  hs: {Spec.safe(St.Store.get(es, key)) == True{} : Bool})
  -> {Spec.safe(Sto.key_state(St.Store.apply_all(I.Item.events(St.Store{g, es}, I.IBlockMark{k, m}), St.Store{g, es}), key)) == True{} : Bool}:
  %eb : {Spec.safe(Sto.key_state(St.Store.apply_all(Bool.pick(List<&2, St.LogEvent>, _, [St.EBlockMark{k, m}], []), St.Store{g, es}), key)) == True{} : Bool}
  item_bm_safe.m(g, es, key, k, m, b, hs)

def item_am_safe.m(-g: Maybe<&2, S.B32>, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +m: Slash.AttMark, b: Bool,
  hs: {Spec.safe(St.Store.get(es, key)) == True{} : Bool})
  -> {Spec.safe(Sto.key_state(St.Store.apply_all(Bool.pick(List<&2, St.LogEvent>, b, [St.EAttMark{k, m}], []), St.Store{g, es}), key)) == True{} : Bool}:
  match b:
    case True{}:
      ev_am_safe(es, key, k, m, S.Pubkey.is_eq(key, k), {==}, hs)
    case False{}:
      hs

def item_am_safe(+g: Maybe<&2, S.B32>, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +m: Slash.AttMark,
  b: Bool, eb: {b == Maybe.is_none(&2, Slash.AttMark, I.KS.att_mark(St.Store.get(es, k))) : Bool},
  hs: {Spec.safe(St.Store.get(es, key)) == True{} : Bool})
  -> {Spec.safe(Sto.key_state(St.Store.apply_all(I.Item.events(St.Store{g, es}, I.IAttMark{k, m}), St.Store{g, es}), key)) == True{} : Bool}:
  %eb : {Spec.safe(Sto.key_state(St.Store.apply_all(Bool.pick(List<&2, St.LogEvent>, _, [St.EAttMark{k, m}], []), St.Store{g, es}), key)) == True{} : Bool}
  item_am_safe.m(g, es, key, k, m, b, hs)

def item_safe(+s: St.Store, +i: I.Item, +key: S.Pubkey,
  hs: {Spec.safe(Sto.key_state(s, key)) == True{} : Bool},
  hok: {I.Item.ok(s, i) == True{} : Bool})
  -> {Spec.safe(Sto.key_state(St.Store.apply_all(I.Item.events(s, i), s), key)) == True{} : Bool}:
  match s:
    case St.Store{+g, +es}:
      match i:
        case I.IBlock{+k, +r}:
          item_block_safe(g, es, key, k, r, Spec.has_block(r, I.KS.blocks(St.Store.get(es, k))), {==}, hs, hok)
        case I.IAtt{+k, +r}:
          item_att_safe(g, es, key, k, r, Spec.has_att(r, I.KS.atts(St.Store.get(es, k))), {==}, hs, hok)
        case I.IBlockMark{+k, +m}:
          item_bm_safe(g, es, key, k, m, Maybe.is_none(&2, S.U64, I.KS.block_mark(St.Store.get(es, k))), {==}, hs)
        case I.IAttMark{+k, +m}:
          item_am_safe(g, es, key, k, m, Maybe.is_none(&2, Slash.AttMark, I.KS.att_mark(St.Store.get(es, k))), {==}, hs)

# L7: all items
# =============

def go_safe.pair(+s: St.Store, +i: I.Item, rest: List<&2, I.Item>, +key: S.Pubkey,
  hs: {Spec.safe(Sto.key_state(s, key)) == True{} : Bool},
  pr: {I.Item.ok(s, i) == True{} : Bool}
    & {Res.ok(I.Imp.go(rest, St.Store.apply_all(I.Item.events(s, i), s))) == True{} : Bool},
  ih: {Spec.safe(Sto.key_state(St.Store.apply_all(I.Item.events(s, i), s), key)) == True{} : Bool}
    -> {Res.ok(I.Imp.go(rest, St.Store.apply_all(I.Item.events(s, i), s))) == True{} : Bool}
    -> {Spec.safe(Sto.key_state(St.Store.apply_all(Res.events(I.Imp.go(rest, St.Store.apply_all(I.Item.events(s, i), s))),
         St.Store.apply_all(I.Item.events(s, i), s)), key)) == True{} : Bool})
  -> {Spec.safe(Sto.key_state(St.Store.apply_all(Res.events(I.Imp.go(rest, St.Store.apply_all(I.Item.events(s, i), s))),
       St.Store.apply_all(I.Item.events(s, i), s)), key)) == True{} : Bool}:
  (hi, hr) = pr
  ih(item_safe(s, i, key, hs, hi), hr)

def go_safe(its: List<&2, I.Item>, +s: St.Store, +key: S.Pubkey,
  hs: {Spec.safe(Sto.key_state(s, key)) == True{} : Bool},
  hok: {Res.ok(I.Imp.go(its, s)) == True{} : Bool})
  -> {Spec.safe(Sto.key_state(St.Store.apply_all(Res.events(I.Imp.go(its, s)), s), key)) == True{} : Bool}:
  match its:
    case Nil{}:
      hs
    case Con{+i, +rest}:
      +E = I.Item.events(s, i)
      +R = I.Imp.go(rest, St.Store.apply_all(E, s))
      %Equal.sym(List<&2, St.LogEvent>, Res.events(I.Res.cons(E, I.Item.ok(s, i), R)), List.append(&2, St.LogEvent, E, Res.events(R)),
        res_events(E, I.Item.ok(s, i), R))
        : {Spec.safe(Sto.key_state(St.Store.apply_all(_, s), key)) == True{} : Bool}
      %Equal.sym(St.Store, St.Store.apply_all(List.append(&2, St.LogEvent, E, Res.events(R)), s), St.Store.apply_all(Res.events(R), St.Store.apply_all(E, s)),
        apply_all_app(E, Res.events(R), s))
        : {Spec.safe(Sto.key_state(_, key)) == True{} : Bool}
      go_safe.pair(s, i, rest, key, hs,
        Lm.Bool.and_true(I.Item.ok(s, i), Res.ok(R),
          Equal.trans(Bool, Bool.and(I.Item.ok(s, i), Res.ok(R)), Res.ok(I.Res.cons(E, I.Item.ok(s, i), R)), True{},
            Equal.sym(Bool, Res.ok(I.Res.cons(E, I.Item.ok(s, i), R)), Bool.and(I.Item.ok(s, i), Res.ok(R)), res_ok(E, I.Item.ok(s, i), R)),
            hok)),
        go_safe(rest, St.Store.apply_all(E, s), key))

# L7
# ==

def after_safe.fin(+p: List<&2, St.LogEvent>, r: I.Res, +s: St.Store, +key: S.Pubkey,
  hs: {Spec.safe(Sto.key_state(s, key)) == True{} : Bool},
  h: {Res.ok(r) == True{} : Bool} -> {Spec.safe(Sto.key_state(St.Store.apply_all(Res.events(r), St.Store.apply_all(p, s)), key)) == True{} : Bool})
  -> {Spec.safe(Sto.key_state(I.Imp.after.go(I.Imp.fin(p, r), s), key)) == True{} : Bool}:
  match r:
    case I.Res{+es, ok}:
      match ok:
        case True{}:
          %Equal.sym(St.Store, St.Store.apply_all(List.append(&2, St.LogEvent, p, es), s), St.Store.apply_all(es, St.Store.apply_all(p, s)),
            apply_all_app(p, es, s))
            : {Spec.safe(Sto.key_state(_, key)) == True{} : Bool}
          h({==})
        case False{}:
          hs

def safe_gvr(+p: List<&2, St.LogEvent>, +s: St.Store, +key: S.Pubkey, hp: {AllGvr(p) == True{} : Bool},
  hs: {Spec.safe(Sto.key_state(s, key)) == True{} : Bool})
  -> {Spec.safe(Sto.key_state(St.Store.apply_all(p, s), key)) == True{} : Bool}:
  %Equal.sym(Slash.KeyState, Sto.key_state(St.Store.apply_all(p, s), key), Sto.key_state(s, key), gvr_key_state(p, s, key, hp))
    : {Spec.safe(_) == True{} : Bool}
  hs

def after_safe.pre(pre: Maybe<&2, List<&2, St.LogEvent>>, hp: {PreGvr(pre) == True{} : Bool}, +s: St.Store,
  +its: List<&2, I.Item>, +key: S.Pubkey, +hs: {Spec.safe(Sto.key_state(s, key)) == True{} : Bool})
  -> {Spec.safe(Sto.key_state(I.Imp.after.go(I.Imp.run.go(pre, s, its), s), key)) == True{} : Bool}:
  match pre:
    case None{}:
      hs
    case Some{+p}:
      after_safe.fin(p, I.Imp.go(its, St.Store.apply_all(p, s)), s, key, hs,
        go_safe(its, St.Store.apply_all(p, s), key, safe_gvr(p, s, key, hp, hs)))

def import_keeps_safe(+s: St.Store, +ix: I.Interchange, +key: S.Pubkey,
  h: {Spec.safe(Sto.key_state(s, key)) == True{} : Bool})
  -> {Spec.safe(Sto.key_state(I.Imp.after(s, ix), key)) == True{} : Bool}:
  match s:
    case St.Store{+have, +es}:
      match ix:
        case I.Interchange{+g, data}:
          after_safe.pre(St.Store.decide.gvr(g, have), pre_gvr(g, have), St.Store{have, es}, I.Items.of(data), key, h)

# Within
# ======

def U64.is_eq_refl(+a: S.U64) -> {True{} == S.U64.is_eq(a, a) : Bool}:
  %Lm.U64.cmp_refl(a) : {True{} == Cmp.is_eq(_) : Bool}
  {==}

def Bool.or_tl(-a: Bool, -b: Bool, h: {True{} == a : Bool}) -> {True{} == Bool.or(a, b) : Bool}:
  %h : {True{} == Bool.or(_, b) : Bool}
  {==}

def Bool.or_tr(a: Bool, -b: Bool, h: {True{} == b : Bool}) -> {True{} == Bool.or(a, b) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def root_eq_refl(+r: Maybe<&2, S.B32>) -> {True{} == Spec.root_eq(r, r) : Bool}:
  match r:
    case None{}:
      {==}
    case Some{+x}:
      Lm.B32.is_eq_refl(x)

def block_eq_refl(+x: Slash.BlockRec) -> {True{} == Spec.block_eq(x, x) : Bool}:
  match x:
    case Slash.BlockRec{+s, +r}:
      Lm.Bool.and_tt(Spec.eq(s, s), Spec.root_eq(r, r), U64.is_eq_refl(s), root_eq_refl(r))

def att_eq_refl(+x: Slash.AttRec) -> {True{} == Spec.att_eq(x, x) : Bool}:
  match x:
    case Slash.AttRec{+s, +t, +r}:
      Lm.Bool.and_tt(Bool.and(Spec.eq(s, s), Spec.eq(t, t)), Spec.root_eq(r, r),
        Lm.Bool.and_tt(Spec.eq(s, s), Spec.eq(t, t), U64.is_eq_refl(s), U64.is_eq_refl(t)),
        root_eq_refl(r))

def blocks_weaken.pair(+x: Slash.BlockRec, -t: List<&2, Slash.BlockRec>, +y: Slash.BlockRec, +ys: List<&2, Slash.BlockRec>,
  pr: {Spec.has_block(x, ys) == True{} : Bool} & {Spec.blocks_within(t, ys) == True{} : Bool},
  ih: {True{} == Spec.blocks_within(t, ys) : Bool} -> {True{} == Spec.blocks_within(t, Con{y, ys}) : Bool})
  -> {True{} == Spec.blocks_within(Con{x, t}, Con{y, ys}) : Bool}:
  (h1, h2) = pr
  Lm.Bool.and_tt(Spec.has_block(x, Con{y, ys}), Spec.blocks_within(t, Con{y, ys}),
    Bool.or_tr(Spec.block_eq(x, y), Spec.has_block(x, ys), Equal.sym(Bool, Spec.has_block(x, ys), True{}, h1)),
    ih(Equal.sym(Bool, Spec.blocks_within(t, ys), True{}, h2)))

# A list within ys is within y :: ys.
def blocks_weaken(xs: List<&2, Slash.BlockRec>, +y: Slash.BlockRec, +ys: List<&2, Slash.BlockRec>,
  h: {True{} == Spec.blocks_within(xs, ys) : Bool}) -> {True{} == Spec.blocks_within(xs, Con{y, ys}) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      blocks_weaken.pair(x, t, y, ys,
        Lm.Bool.and_true(Spec.has_block(x, ys), Spec.blocks_within(t, ys), Equal.sym(Bool, True{}, Spec.blocks_within(Con{x, t}, ys), h)),
        blocks_weaken(t, y, ys))

# Every list is within itself.
def blocks_within_refl(+xs: List<&2, Slash.BlockRec>) -> {True{} == Spec.blocks_within(xs, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Lm.Bool.and_tt(Spec.has_block(x, Con{x, t}), Spec.blocks_within(t, Con{x, t}),
        Bool.or_tl(Spec.block_eq(x, x), Spec.has_block(x, t), block_eq_refl(x)),
        blocks_weaken(t, x, t, blocks_within_refl(t)))

def atts_weaken.pair(+x: Slash.AttRec, -t: List<&2, Slash.AttRec>, +y: Slash.AttRec, +ys: List<&2, Slash.AttRec>,
  pr: {Spec.has_att(x, ys) == True{} : Bool} & {Spec.atts_within(t, ys) == True{} : Bool},
  ih: {True{} == Spec.atts_within(t, ys) : Bool} -> {True{} == Spec.atts_within(t, Con{y, ys}) : Bool})
  -> {True{} == Spec.atts_within(Con{x, t}, Con{y, ys}) : Bool}:
  (h1, h2) = pr
  Lm.Bool.and_tt(Spec.has_att(x, Con{y, ys}), Spec.atts_within(t, Con{y, ys}),
    Bool.or_tr(Spec.att_eq(x, y), Spec.has_att(x, ys), Equal.sym(Bool, Spec.has_att(x, ys), True{}, h1)),
    ih(Equal.sym(Bool, Spec.atts_within(t, ys), True{}, h2)))

# A list within ys is within y :: ys.
def atts_weaken(xs: List<&2, Slash.AttRec>, +y: Slash.AttRec, +ys: List<&2, Slash.AttRec>,
  h: {True{} == Spec.atts_within(xs, ys) : Bool}) -> {True{} == Spec.atts_within(xs, Con{y, ys}) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      atts_weaken.pair(x, t, y, ys,
        Lm.Bool.and_true(Spec.has_att(x, ys), Spec.atts_within(t, ys), Equal.sym(Bool, True{}, Spec.atts_within(Con{x, t}, ys), h)),
        atts_weaken(t, y, ys))

# Every list is within itself.
def atts_within_refl(+xs: List<&2, Slash.AttRec>) -> {True{} == Spec.atts_within(xs, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Lm.Bool.and_tt(Spec.has_att(x, Con{x, t}), Spec.atts_within(t, Con{x, t}),
        Bool.or_tl(Spec.att_eq(x, x), Spec.has_att(x, t), att_eq_refl(x)),
        atts_weaken(t, x, t, atts_within_refl(t)))

# L8: one key state
# =================

def lt_irrefl(+x: S.U64) -> {True{} == Bool.not(S.U64.is_lt(x, x)) : Bool}:
  %Lm.U64.cmp_refl(x) : {True{} == Bool.not(Cmp.is_lt(_)) : Bool}
  {==}

def mark_up_refl(+m: Maybe<&2, S.U64>) -> {True{} == SpI.mark_up(m, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      lt_irrefl(x)

def att_mark_up_refl(+m: Maybe<&2, Slash.AttMark>) -> {True{} == SpI.att_mark_up(m, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Slash.AttMark{+ms, +mt}:
          Lm.Bool.and_tt(Bool.not(S.U64.is_lt(ms, ms)), Bool.not(S.U64.is_lt(mt, mt)), lt_irrefl(ms), lt_irrefl(mt))

def up_from(+bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>, +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>,
  +bs2: List<&2, Slash.BlockRec>, +as2: List<&2, Slash.AttRec>, +bm2: Maybe<&2, S.U64>, +am2: Maybe<&2, Slash.AttMark>,
  hb: {True{} == Spec.blocks_within(bs, bs2) : Bool}, ha: {True{} == Spec.atts_within(as, as2) : Bool},
  hm: {True{} == SpI.mark_up(bm, bm2) : Bool}, hn: {True{} == SpI.att_mark_up(am, am2) : Bool})
  -> {SpI.keeps_up(Slash.KeyState{bs, as, bm, am}, Slash.KeyState{bs2, as2, bm2, am2}) == True{} : Bool}:
  Equal.sym(Bool, True{}, SpI.keeps_up(Slash.KeyState{bs, as, bm, am}, Slash.KeyState{bs2, as2, bm2, am2}),
    Lm.Bool.and_tt(Bool.and(Bool.and(Spec.blocks_within(bs, bs2), Spec.atts_within(as, as2)), SpI.mark_up(bm, bm2)),
      SpI.att_mark_up(am, am2),
      Lm.Bool.and_tt(Bool.and(Spec.blocks_within(bs, bs2), Spec.atts_within(as, as2)), SpI.mark_up(bm, bm2),
        Lm.Bool.and_tt(Spec.blocks_within(bs, bs2), Spec.atts_within(as, as2), hb, ha), hm),
      hn))

def up_refl(+ks: Slash.KeyState) -> {SpI.keeps_up(ks, ks) == True{} : Bool}:
  match ks:
    case Slash.KeyState{+bs, +as, +bm, +am}:
      up_from(bs, as, bm, am, bs, as, bm, am, blocks_within_refl(bs), atts_within_refl(as), mark_up_refl(bm), att_mark_up_refl(am))

# keeps_up is and(and(and(blocks, atts), block mark), att mark). Each
# lemma below changes one of the four parts.
def cong1(x: Bool, -y: Bool, -b: Bool, -c: Bool, -d: Bool, f: {True{} == x : Bool} -> {True{} == y : Bool},
  h: {Bool.and(Bool.and(Bool.and(x, b), c), d) == True{} : Bool}) -> {Bool.and(Bool.and(Bool.and(y, b), c), d) == True{} : Bool}:
  match x:
    case True{}:
      %f({==}) : {Bool.and(Bool.and(Bool.and(_, b), c), d) == True{} : Bool}
      h
    case False{}:
      Empty.absurd({Bool.and(Bool.and(Bool.and(y, b), c), d) == True{} : Bool}, Lm.Bool.ft(h))

def cong2(x: Bool, w: Bool, -z: Bool, -c: Bool, -d: Bool, f: {True{} == w : Bool} -> {True{} == z : Bool},
  h: {Bool.and(Bool.and(Bool.and(x, w), c), d) == True{} : Bool}) -> {Bool.and(Bool.and(Bool.and(x, z), c), d) == True{} : Bool}:
  match x:
    case True{}:
      match w:
        case True{}:
          %f({==}) : {Bool.and(Bool.and(Bool.and(True{}, _), c), d) == True{} : Bool}
          h
        case False{}:
          Empty.absurd({Bool.and(Bool.and(Bool.and(True{}, z), c), d) == True{} : Bool}, Lm.Bool.ft(h))
    case False{}:
      Empty.absurd({Bool.and(Bool.and(Bool.and(False{}, z), c), d) == True{} : Bool}, Lm.Bool.ft(h))

def cong3.m(m: Bool, -z: Bool, -d: Bool, f: {True{} == m : Bool} -> {True{} == z : Bool},
  h: {Bool.and(m, d) == True{} : Bool}) -> {Bool.and(z, d) == True{} : Bool}:
  match m:
    case True{}:
      %f({==}) : {Bool.and(_, d) == True{} : Bool}
      h
    case False{}:
      Empty.absurd({Bool.and(z, d) == True{} : Bool}, Lm.Bool.ft(h))

def cong3(x: Bool, w: Bool, m: Bool, -z: Bool, -d: Bool, f: {True{} == m : Bool} -> {True{} == z : Bool},
  h: {Bool.and(Bool.and(Bool.and(x, w), m), d) == True{} : Bool}) -> {Bool.and(Bool.and(Bool.and(x, w), z), d) == True{} : Bool}:
  match x:
    case True{}:
      match w:
        case True{}:
          cong3.m(m, z, d, f, h)
        case False{}:
          Empty.absurd({Bool.and(Bool.and(Bool.and(True{}, False{}), z), d) == True{} : Bool}, Lm.Bool.ft(h))
    case False{}:
      Empty.absurd({Bool.and(Bool.and(Bool.and(False{}, w), z), d) == True{} : Bool}, Lm.Bool.ft(h))

def cong4.m(m: Bool, n: Bool, -z: Bool, f: {True{} == n : Bool} -> {True{} == z : Bool},
  h: {Bool.and(m, n) == True{} : Bool}) -> {Bool.and(m, z) == True{} : Bool}:
  match m:
    case True{}:
      match n:
        case True{}:
          %f({==}) : {Bool.and(True{}, _) == True{} : Bool}
          {==}
        case False{}:
          Empty.absurd({Bool.and(True{}, z) == True{} : Bool}, Lm.Bool.ft(h))
    case False{}:
      Empty.absurd({Bool.and(False{}, z) == True{} : Bool}, Lm.Bool.ft(h))

def cong4(x: Bool, w: Bool, m: Bool, n: Bool, -z: Bool, f: {True{} == n : Bool} -> {True{} == z : Bool},
  h: {Bool.and(Bool.and(Bool.and(x, w), m), n) == True{} : Bool}) -> {Bool.and(Bool.and(Bool.and(x, w), m), z) == True{} : Bool}:
  match x:
    case True{}:
      match w:
        case True{}:
          cong4.m(m, n, z, f, h)
        case False{}:
          Empty.absurd({Bool.and(Bool.and(Bool.and(True{}, False{}), m), z) == True{} : Bool}, Lm.Bool.ft(h))
    case False{}:
      Empty.absurd({Bool.and(Bool.and(Bool.and(False{}, w), m), z) == True{} : Bool}, Lm.Bool.ft(h))

def mark_from_none(obm: Maybe<&2, S.U64>, -m: S.U64, h: {True{} == SpI.mark_up(obm, None{}) : Bool})
  -> {True{} == SpI.mark_up(obm, Some{m}) : Bool}:
  match obm:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({True{} == SpI.mark_up(Some{x}, Some{m}) : Bool}, Lm.Bool.tf(h))

def att_mark_from_none(oam: Maybe<&2, Slash.AttMark>, -m: Slash.AttMark, h: {True{} == SpI.att_mark_up(oam, None{}) : Bool})
  -> {True{} == SpI.att_mark_up(oam, Some{m}) : Bool}:
  match oam:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({True{} == SpI.att_mark_up(Some{x}, Some{m}) : Bool}, Lm.Bool.tf(h))

def up_add_block(orig: Slash.KeyState, ks: Slash.KeyState, +r: Slash.BlockRec,
  h: {SpI.keeps_up(orig, ks) == True{} : Bool}) -> {SpI.keeps_up(orig, St.KeyState.add_block(ks, r)) == True{} : Bool}:
  match orig ks:
    case Slash.KeyState{+obs, +oas, +obm, +oam} Slash.KeyState{+bs, +as, +bm, +am}:
      cong1(Spec.blocks_within(obs, bs), Spec.blocks_within(obs, Con{r, bs}), Spec.atts_within(oas, as),
        SpI.mark_up(obm, bm), SpI.att_mark_up(oam, am), blocks_weaken(obs, r, bs), h)

def up_add_att(orig: Slash.KeyState, ks: Slash.KeyState, +r: Slash.AttRec,
  h: {SpI.keeps_up(orig, ks) == True{} : Bool}) -> {SpI.keeps_up(orig, St.KeyState.add_att(ks, r)) == True{} : Bool}:
  match orig ks:
    case Slash.KeyState{+obs, +oas, +obm, +oam} Slash.KeyState{+bs, +as, +bm, +am}:
      cong2(Spec.blocks_within(obs, bs), Spec.atts_within(oas, as), Spec.atts_within(oas, Con{r, as}),
        SpI.mark_up(obm, bm), SpI.att_mark_up(oam, am), atts_weaken(oas, r, as), h)

def up_set_bm.go(+obs: List<&2, Slash.BlockRec>, +oas: List<&2, Slash.AttRec>, +obm: Maybe<&2, S.U64>, +oam: Maybe<&2, Slash.AttMark>,
  +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>, bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +m: S.U64,
  hn: {True{} == Maybe.is_none(&2, S.U64, bm) : Bool},
  h: {SpI.keeps_up(Slash.KeyState{obs, oas, obm, oam}, Slash.KeyState{bs, as, bm, am}) == True{} : Bool})
  -> {SpI.keeps_up(Slash.KeyState{obs, oas, obm, oam}, Slash.KeyState{bs, as, Some{m}, am}) == True{} : Bool}:
  match bm:
    case None{}:
      cong3(Spec.blocks_within(obs, bs), Spec.atts_within(oas, as), SpI.mark_up(obm, None{}), SpI.mark_up(obm, Some{m}),
        SpI.att_mark_up(oam, am), mark_from_none(obm, m), h)
    case Some{y}:
      Empty.absurd({SpI.keeps_up(Slash.KeyState{obs, oas, obm, oam}, Slash.KeyState{bs, as, Some{m}, am}) == True{} : Bool}, Lm.Bool.tf(hn))

def up_set_bm(orig: Slash.KeyState, ks: Slash.KeyState, +m: S.U64,
  hn: {True{} == Maybe.is_none(&2, S.U64, I.KS.block_mark(ks)) : Bool},
  h: {SpI.keeps_up(orig, ks) == True{} : Bool}) -> {SpI.keeps_up(orig, St.KeyState.set_block_mark(ks, m)) == True{} : Bool}:
  match orig ks:
    case Slash.KeyState{+obs, +oas, +obm, +oam} Slash.KeyState{+bs, +as, bm, +am}:
      up_set_bm.go(obs, oas, obm, oam, bs, as, bm, am, m, hn, h)

def up_set_am.go(+obs: List<&2, Slash.BlockRec>, +oas: List<&2, Slash.AttRec>, +obm: Maybe<&2, S.U64>, +oam: Maybe<&2, Slash.AttMark>,
  +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>, +bm: Maybe<&2, S.U64>, am: Maybe<&2, Slash.AttMark>, +m: Slash.AttMark,
  hn: {True{} == Maybe.is_none(&2, Slash.AttMark, am) : Bool},
  h: {SpI.keeps_up(Slash.KeyState{obs, oas, obm, oam}, Slash.KeyState{bs, as, bm, am}) == True{} : Bool})
  -> {SpI.keeps_up(Slash.KeyState{obs, oas, obm, oam}, Slash.KeyState{bs, as, bm, Some{m}}) == True{} : Bool}:
  match am:
    case None{}:
      cong4(Spec.blocks_within(obs, bs), Spec.atts_within(oas, as), SpI.mark_up(obm, bm), SpI.att_mark_up(oam, None{}),
        SpI.att_mark_up(oam, Some{m}), att_mark_from_none(oam, m), h)
    case Some{y}:
      Empty.absurd({SpI.keeps_up(Slash.KeyState{obs, oas, obm, oam}, Slash.KeyState{bs, as, bm, Some{m}}) == True{} : Bool}, Lm.Bool.tf(hn))

def up_set_am(orig: Slash.KeyState, ks: Slash.KeyState, +m: Slash.AttMark,
  hn: {True{} == Maybe.is_none(&2, Slash.AttMark, I.KS.att_mark(ks)) : Bool},
  h: {SpI.keeps_up(orig, ks) == True{} : Bool}) -> {SpI.keeps_up(orig, St.KeyState.set_att_mark(ks, m)) == True{} : Bool}:
  match orig ks:
    case Slash.KeyState{+obs, +oas, +obm, +oam} Slash.KeyState{+bs, +as, +bm, am}:
      up_set_am.go(obs, oas, obm, oam, bs, as, bm, am, m, hn, h)

# L8: one event
# =============

def ev_block_up(+orig: Slash.KeyState, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +r: Slash.BlockRec,
  c: Bool, ec: {c == S.Pubkey.is_eq(key, k) : Bool},
  hu: {SpI.keeps_up(orig, St.Store.get(es, key)) == True{} : Bool})
  -> {SpI.keeps_up(orig, St.Store.get(St.Store.put(es, k, St.KeyState.add_block(St.Store.get(es, k), r)), key)) == True{} : Bool}:
  match c:
    case True{}:
      +e = Lm.Pubkey.eq_of(key, k, Equal.sym(Bool, True{}, S.Pubkey.is_eq(key, k), ec))
      %e : {SpI.keeps_up(orig, St.Store.get(St.Store.put(es, _, St.KeyState.add_block(St.Store.get(es, _), r)), key)) == True{} : Bool}
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, key, St.KeyState.add_block(St.Store.get(es, key), r)), key), St.KeyState.add_block(St.Store.get(es, key), r), get_put_same(es, key, St.KeyState.add_block(St.Store.get(es, key), r)))
        : {SpI.keeps_up(orig, _) == True{} : Bool}
      up_add_block(orig, St.Store.get(es, key), r, hu)
    case False{}:
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, k, St.KeyState.add_block(St.Store.get(es, k), r)), key), St.Store.get(es, key),
        get_put_other(es, k, key, St.KeyState.add_block(St.Store.get(es, k), r), Equal.sym(Bool, False{}, S.Pubkey.is_eq(key, k), ec)))
        : {SpI.keeps_up(orig, _) == True{} : Bool}
      hu

def ev_att_up(+orig: Slash.KeyState, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +r: Slash.AttRec,
  c: Bool, ec: {c == S.Pubkey.is_eq(key, k) : Bool},
  hu: {SpI.keeps_up(orig, St.Store.get(es, key)) == True{} : Bool})
  -> {SpI.keeps_up(orig, St.Store.get(St.Store.put(es, k, St.KeyState.add_att(St.Store.get(es, k), r)), key)) == True{} : Bool}:
  match c:
    case True{}:
      +e = Lm.Pubkey.eq_of(key, k, Equal.sym(Bool, True{}, S.Pubkey.is_eq(key, k), ec))
      %e : {SpI.keeps_up(orig, St.Store.get(St.Store.put(es, _, St.KeyState.add_att(St.Store.get(es, _), r)), key)) == True{} : Bool}
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, key, St.KeyState.add_att(St.Store.get(es, key), r)), key), St.KeyState.add_att(St.Store.get(es, key), r), get_put_same(es, key, St.KeyState.add_att(St.Store.get(es, key), r)))
        : {SpI.keeps_up(orig, _) == True{} : Bool}
      up_add_att(orig, St.Store.get(es, key), r, hu)
    case False{}:
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, k, St.KeyState.add_att(St.Store.get(es, k), r)), key), St.Store.get(es, key),
        get_put_other(es, k, key, St.KeyState.add_att(St.Store.get(es, k), r), Equal.sym(Bool, False{}, S.Pubkey.is_eq(key, k), ec)))
        : {SpI.keeps_up(orig, _) == True{} : Bool}
      hu

def ev_bm_up(+orig: Slash.KeyState, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +m: S.U64,
  c: Bool, ec: {c == S.Pubkey.is_eq(key, k) : Bool},
  hn: {True{} == Maybe.is_none(&2, S.U64, I.KS.block_mark(St.Store.get(es, k))) : Bool},
  hu: {SpI.keeps_up(orig, St.Store.get(es, key)) == True{} : Bool})
  -> {SpI.keeps_up(orig, St.Store.get(St.Store.put(es, k, St.KeyState.set_block_mark(St.Store.get(es, k), m)), key)) == True{} : Bool}:
  match c:
    case True{}:
      +e = Lm.Pubkey.eq_of(key, k, Equal.sym(Bool, True{}, S.Pubkey.is_eq(key, k), ec))
      %e : {SpI.keeps_up(orig, St.Store.get(St.Store.put(es, _, St.KeyState.set_block_mark(St.Store.get(es, _), m)), key)) == True{} : Bool}
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, key, St.KeyState.set_block_mark(St.Store.get(es, key), m)), key), St.KeyState.set_block_mark(St.Store.get(es, key), m), get_put_same(es, key, St.KeyState.set_block_mark(St.Store.get(es, key), m)))
        : {SpI.keeps_up(orig, _) == True{} : Bool}
      up_set_bm(orig, St.Store.get(es, key), m, tr_none_bm(es, key, k, e, hn), hu)
    case False{}:
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, k, St.KeyState.set_block_mark(St.Store.get(es, k), m)), key), St.Store.get(es, key),
        get_put_other(es, k, key, St.KeyState.set_block_mark(St.Store.get(es, k), m), Equal.sym(Bool, False{}, S.Pubkey.is_eq(key, k), ec)))
        : {SpI.keeps_up(orig, _) == True{} : Bool}
      hu

def ev_am_up(+orig: Slash.KeyState, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +m: Slash.AttMark,
  c: Bool, ec: {c == S.Pubkey.is_eq(key, k) : Bool},
  hn: {True{} == Maybe.is_none(&2, Slash.AttMark, I.KS.att_mark(St.Store.get(es, k))) : Bool},
  hu: {SpI.keeps_up(orig, St.Store.get(es, key)) == True{} : Bool})
  -> {SpI.keeps_up(orig, St.Store.get(St.Store.put(es, k, St.KeyState.set_att_mark(St.Store.get(es, k), m)), key)) == True{} : Bool}:
  match c:
    case True{}:
      +e = Lm.Pubkey.eq_of(key, k, Equal.sym(Bool, True{}, S.Pubkey.is_eq(key, k), ec))
      %e : {SpI.keeps_up(orig, St.Store.get(St.Store.put(es, _, St.KeyState.set_att_mark(St.Store.get(es, _), m)), key)) == True{} : Bool}
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, key, St.KeyState.set_att_mark(St.Store.get(es, key), m)), key), St.KeyState.set_att_mark(St.Store.get(es, key), m), get_put_same(es, key, St.KeyState.set_att_mark(St.Store.get(es, key), m)))
        : {SpI.keeps_up(orig, _) == True{} : Bool}
      up_set_am(orig, St.Store.get(es, key), m, tr_none_am(es, key, k, e, hn), hu)
    case False{}:
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, k, St.KeyState.set_att_mark(St.Store.get(es, k), m)), key), St.Store.get(es, key),
        get_put_other(es, k, key, St.KeyState.set_att_mark(St.Store.get(es, k), m), Equal.sym(Bool, False{}, S.Pubkey.is_eq(key, k), ec)))
        : {SpI.keeps_up(orig, _) == True{} : Bool}
      hu

# L8: one item
# ============

def item_block_up.m(-g: Maybe<&2, S.B32>, +orig: Slash.KeyState, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +r: Slash.BlockRec, b: Bool,
  hu: {SpI.keeps_up(orig, St.Store.get(es, key)) == True{} : Bool})
  -> {SpI.keeps_up(orig, Sto.key_state(St.Store.apply_all(Bool.pick(List<&2, St.LogEvent>, b, [], [St.EBlock{k, r}]), St.Store{g, es}), key)) == True{} : Bool}:
  match b:
    case True{}:
      hu
    case False{}:
      ev_block_up(orig, es, key, k, r, S.Pubkey.is_eq(key, k), {==}, hu)

def item_block_up(+g: Maybe<&2, S.B32>, +orig: Slash.KeyState, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +r: Slash.BlockRec,
  b: Bool, eb: {b == Spec.has_block(r, I.KS.blocks(St.Store.get(es, k))) : Bool},
  hu: {SpI.keeps_up(orig, St.Store.get(es, key)) == True{} : Bool})
  -> {SpI.keeps_up(orig, Sto.key_state(St.Store.apply_all(I.Item.events(St.Store{g, es}, I.IBlock{k, r}), St.Store{g, es}), key)) == True{} : Bool}:
  %eb : {SpI.keeps_up(orig, Sto.key_state(St.Store.apply_all(Bool.pick(List<&2, St.LogEvent>, _, [], [St.EBlock{k, r}]), St.Store{g, es}), key)) == True{} : Bool}
  item_block_up.m(g, orig, es, key, k, r, b, hu)

def item_att_up.m(-g: Maybe<&2, S.B32>, +orig: Slash.KeyState, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +r: Slash.AttRec, b: Bool,
  hu: {SpI.keeps_up(orig, St.Store.get(es, key)) == True{} : Bool})
  -> {SpI.keeps_up(orig, Sto.key_state(St.Store.apply_all(Bool.pick(List<&2, St.LogEvent>, b, [], [St.EAtt{k, r}]), St.Store{g, es}), key)) == True{} : Bool}:
  match b:
    case True{}:
      hu
    case False{}:
      ev_att_up(orig, es, key, k, r, S.Pubkey.is_eq(key, k), {==}, hu)

def item_att_up(+g: Maybe<&2, S.B32>, +orig: Slash.KeyState, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +r: Slash.AttRec,
  b: Bool, eb: {b == Spec.has_att(r, I.KS.atts(St.Store.get(es, k))) : Bool},
  hu: {SpI.keeps_up(orig, St.Store.get(es, key)) == True{} : Bool})
  -> {SpI.keeps_up(orig, Sto.key_state(St.Store.apply_all(I.Item.events(St.Store{g, es}, I.IAtt{k, r}), St.Store{g, es}), key)) == True{} : Bool}:
  %eb : {SpI.keeps_up(orig, Sto.key_state(St.Store.apply_all(Bool.pick(List<&2, St.LogEvent>, _, [], [St.EAtt{k, r}]), St.Store{g, es}), key)) == True{} : Bool}
  item_att_up.m(g, orig, es, key, k, r, b, hu)

def item_bm_up.m(-g: Maybe<&2, S.B32>, +orig: Slash.KeyState, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +m: S.U64,
  b: Bool, eb: {b == Maybe.is_none(&2, S.U64, I.KS.block_mark(St.Store.get(es, k))) : Bool},
  hu: {SpI.keeps_up(orig, St.Store.get(es, key)) == True{} : Bool})
  -> {SpI.keeps_up(orig, Sto.key_state(St.Store.apply_all(Bool.pick(List<&2, St.LogEvent>, b, [St.EBlockMark{k, m}], []), St.Store{g, es}), key)) == True{} : Bool}:
  match b:
    case True{}:
      ev_bm_up(orig, es, key, k, m, S.Pubkey.is_eq(key, k), {==}, eb, hu)
    case False{}:
      hu

def item_bm_up(+g: Maybe<&2, S.B32>, +orig: Slash.KeyState, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +m: S.U64,
  b: Bool, +eb: {b == Maybe.is_none(&2, S.U64, I.KS.block_mark(St.Store.get(es, k))) : Bool},
  hu: {SpI.keeps_up(orig, St.Store.get(es, key)) == True{} : Bool})
  -> {SpI.keeps_up(orig, Sto.key_state(St.Store.apply_all(I.Item.events(St.Store{g, es}, I.IBlockMark{k, m}), St.Store{g, es}), key)) == True{} : Bool}:
  %eb : {SpI.keeps_up(orig, Sto.key_state(St.Store.apply_all(Bool.pick(List<&2, St.LogEvent>, _, [St.EBlockMark{k, m}], []), St.Store{g, es}), key)) == True{} : Bool}
  item_bm_up.m(g, orig, es, key, k, m, b, eb, hu)

def item_am_up.m(-g: Maybe<&2, S.B32>, +orig: Slash.KeyState, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +m: Slash.AttMark,
  b: Bool, eb: {b == Maybe.is_none(&2, Slash.AttMark, I.KS.att_mark(St.Store.get(es, k))) : Bool},
  hu: {SpI.keeps_up(orig, St.Store.get(es, key)) == True{} : Bool})
  -> {SpI.keeps_up(orig, Sto.key_state(St.Store.apply_all(Bool.pick(List<&2, St.LogEvent>, b, [St.EAttMark{k, m}], []), St.Store{g, es}), key)) == True{} : Bool}:
  match b:
    case True{}:
      ev_am_up(orig, es, key, k, m, S.Pubkey.is_eq(key, k), {==}, eb, hu)
    case False{}:
      hu

def item_am_up(+g: Maybe<&2, S.B32>, +orig: Slash.KeyState, +es: List<&2, St.Entry>, +key: S.Pubkey, +k: S.Pubkey, +m: Slash.AttMark,
  b: Bool, +eb: {b == Maybe.is_none(&2, Slash.AttMark, I.KS.att_mark(St.Store.get(es, k))) : Bool},
  hu: {SpI.keeps_up(orig, St.Store.get(es, key)) == True{} : Bool})
  -> {SpI.keeps_up(orig, Sto.key_state(St.Store.apply_all(I.Item.events(St.Store{g, es}, I.IAttMark{k, m}), St.Store{g, es}), key)) == True{} : Bool}:
  %eb : {SpI.keeps_up(orig, Sto.key_state(St.Store.apply_all(Bool.pick(List<&2, St.LogEvent>, _, [St.EAttMark{k, m}], []), St.Store{g, es}), key)) == True{} : Bool}
  item_am_up.m(g, orig, es, key, k, m, b, eb, hu)

def item_up(+orig: Slash.KeyState, +s: St.Store, +i: I.Item, +key: S.Pubkey,
  hu: {SpI.keeps_up(orig, Sto.key_state(s, key)) == True{} : Bool})
  -> {SpI.keeps_up(orig, Sto.key_state(St.Store.apply_all(I.Item.events(s, i), s), key)) == True{} : Bool}:
  match s:
    case St.Store{+g, +es}:
      match i:
        case I.IBlock{+k, +r}:
          item_block_up(g, orig, es, key, k, r, Spec.has_block(r, I.KS.blocks(St.Store.get(es, k))), {==}, hu)
        case I.IAtt{+k, +r}:
          item_att_up(g, orig, es, key, k, r, Spec.has_att(r, I.KS.atts(St.Store.get(es, k))), {==}, hu)
        case I.IBlockMark{+k, +m}:
          item_bm_up(g, orig, es, key, k, m, Maybe.is_none(&2, S.U64, I.KS.block_mark(St.Store.get(es, k))), {==}, hu)
        case I.IAttMark{+k, +m}:
          item_am_up(g, orig, es, key, k, m, Maybe.is_none(&2, Slash.AttMark, I.KS.att_mark(St.Store.get(es, k))), {==}, hu)

# L8: all items
# =============

def go_up(+orig: Slash.KeyState, its: List<&2, I.Item>, +s: St.Store, +key: S.Pubkey,
  hu: {SpI.keeps_up(orig, Sto.key_state(s, key)) == True{} : Bool})
  -> {SpI.keeps_up(orig, Sto.key_state(St.Store.apply_all(Res.events(I.Imp.go(its, s)), s), key)) == True{} : Bool}:
  match its:
    case Nil{}:
      hu
    case Con{+i, +rest}:
      +E = I.Item.events(s, i)
      +R = I.Imp.go(rest, St.Store.apply_all(E, s))
      %Equal.sym(List<&2, St.LogEvent>, Res.events(I.Res.cons(E, I.Item.ok(s, i), R)), List.append(&2, St.LogEvent, E, Res.events(R)),
        res_events(E, I.Item.ok(s, i), R))
        : {SpI.keeps_up(orig, Sto.key_state(St.Store.apply_all(_, s), key)) == True{} : Bool}
      %Equal.sym(St.Store, St.Store.apply_all(List.append(&2, St.LogEvent, E, Res.events(R)), s), St.Store.apply_all(Res.events(R), St.Store.apply_all(E, s)),
        apply_all_app(E, Res.events(R), s))
        : {SpI.keeps_up(orig, Sto.key_state(_, key)) == True{} : Bool}
      go_up(orig, rest, St.Store.apply_all(E, s), key, item_up(orig, s, i, key, hu))

# L8
# ==

def after_up.fin(+orig: Slash.KeyState, +p: List<&2, St.LogEvent>, r: I.Res, +s: St.Store, +key: S.Pubkey,
  hu: {SpI.keeps_up(orig, Sto.key_state(s, key)) == True{} : Bool},
  h: {SpI.keeps_up(orig, Sto.key_state(St.Store.apply_all(Res.events(r), St.Store.apply_all(p, s)), key)) == True{} : Bool})
  -> {SpI.keeps_up(orig, Sto.key_state(I.Imp.after.go(I.Imp.fin(p, r), s), key)) == True{} : Bool}:
  match r:
    case I.Res{+es, ok}:
      match ok:
        case True{}:
          %Equal.sym(St.Store, St.Store.apply_all(List.append(&2, St.LogEvent, p, es), s), St.Store.apply_all(es, St.Store.apply_all(p, s)),
            apply_all_app(p, es, s))
            : {SpI.keeps_up(orig, Sto.key_state(_, key)) == True{} : Bool}
          h
        case False{}:
          hu

def up_gvr(+orig: Slash.KeyState, +p: List<&2, St.LogEvent>, +s: St.Store, +key: S.Pubkey, hp: {AllGvr(p) == True{} : Bool},
  hu: {SpI.keeps_up(orig, Sto.key_state(s, key)) == True{} : Bool})
  -> {SpI.keeps_up(orig, Sto.key_state(St.Store.apply_all(p, s), key)) == True{} : Bool}:
  %Equal.sym(Slash.KeyState, Sto.key_state(St.Store.apply_all(p, s), key), Sto.key_state(s, key), gvr_key_state(p, s, key, hp))
    : {SpI.keeps_up(orig, _) == True{} : Bool}
  hu

def after_up.pre(+orig: Slash.KeyState, pre: Maybe<&2, List<&2, St.LogEvent>>, hp: {PreGvr(pre) == True{} : Bool}, +s: St.Store,
  +its: List<&2, I.Item>, +key: S.Pubkey, +hu: {SpI.keeps_up(orig, Sto.key_state(s, key)) == True{} : Bool})
  -> {SpI.keeps_up(orig, Sto.key_state(I.Imp.after.go(I.Imp.run.go(pre, s, its), s), key)) == True{} : Bool}:
  match pre:
    case None{}:
      hu
    case Some{+p}:
      after_up.fin(orig, p, I.Imp.go(its, St.Store.apply_all(p, s)), s, key, hu,
        go_up(orig, its, St.Store.apply_all(p, s), key, up_gvr(orig, p, s, key, hp, hu)))

def import_monotone(+s: St.Store, +ix: I.Interchange, +key: S.Pubkey)
  -> {SpI.keeps_up(Sto.key_state(s, key), Sto.key_state(I.Imp.after(s, ix), key)) == True{} : Bool}:
  match s:
    case St.Store{+have, +es}:
      match ix:
        case I.Interchange{+g, data}:
          after_up.pre(St.Store.get(es, key), St.Store.decide.gvr(g, have), pre_gvr(g, have), St.Store{have, es}, I.Items.of(data), key,
            up_refl(St.Store.get(es, key)))
