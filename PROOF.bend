# The proofs of LAWS.bend. `bend PROOF.bend` is the gate: it fails while a
# law is open, and prints "All terms check." when every law holds.
import Base
import ./src/ssz.bend as S
import ./src/slashing.bend as Slash
import ./src/request.bend as R
import ./spec/safety.bend as Spec
import ./spec/signing.bend as Sig
import ./src/store.bend as St
import ./spec/store.bend as Sto
import ./proof/lemmas.bend as Lm
import ./LAWS.bend as Laws

# L3
# ==

def Laws.empty_safe():
  {==}

# L1-L2
# =====

def Root.mismatch() -> String:
  "signing root does not match the request"

def gives_pick(b: Bool, +root: S.B32)
  -> {Sig.gives_only(Bool.pick(Result<&2, &2, String, S.B32>, b, Done{root}, Fail{Root.mismatch()}), root) == True{} : Bool}:
  match b:
    case True{}:
      %Lm.B32.is_eq_refl(root) : {_ == True{} : Bool}
      {==}
    case False{}:
      {==}

def fails_pick(b: Bool, +root: S.B32, h: {Bool.not(b) == True{} : Bool})
  -> {Sig.fails(Bool.pick(Result<&2, &2, String, S.B32>, b, Done{root}, Fail{Root.mismatch()})) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Sig.fails(Done{root}) == True{} : Bool}, Lm.Bool.ft(h))
    case False{}:
      {==}

def accepts_pick(b: Bool, +root: S.B32, h: {Bool.not(b) == False{} : Bool})
  -> {Sig.fails(Bool.pick(Result<&2, &2, String, S.B32>, b, Done{root}, Fail{Root.mismatch()})) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Sig.fails(Fail{Root.mismatch()}) == False{} : Bool}, Lm.Bool.tf(h))

def Laws.signs_computed_root(r, n):
  match r:
    case R.Request{+msg, +fork, +gvr, claimed}:
      match claimed:
        case None{}:
          %Lm.B32.is_eq_refl(R.Request.signing_root(R.Request{msg, fork, gvr, None{}}, n)) : {_ == True{} : Bool}
          {==}
        case Some{+c}:
          gives_pick(S.B32.is_eq(c, R.Request.signing_root(R.Request{msg, fork, gvr, Some{c}}, n)),
            R.Request.signing_root(R.Request{msg, fork, gvr, Some{c}}, n))

def Laws.rejects_bad_root(r, n, h):
  match r:
    case R.Request{+msg, +fork, +gvr, claimed}:
      match claimed:
        case None{}:
          Empty.absurd({Sig.fails(R.Request.check(R.Request{msg, fork, gvr, None{}}, n)) == True{} : Bool}, Lm.Bool.ft(h))
        case Some{+c}:
          fails_pick(S.B32.is_eq(c, R.Request.signing_root(R.Request{msg, fork, gvr, Some{c}}, n)),
            R.Request.signing_root(R.Request{msg, fork, gvr, Some{c}}, n), h)

def Laws.accepts_own_root(r, n, h):
  match r:
    case R.Request{+msg, +fork, +gvr, claimed}:
      match claimed:
        case None{}:
          {==}
        case Some{+c}:
          accepts_pick(S.B32.is_eq(c, R.Request.signing_root(R.Request{msg, fork, gvr, Some{c}}, n)),
            R.Request.signing_root(R.Request{msg, fork, gvr, Some{c}}, n), h)

# L9
# ==

def block_mark_go(b: Bool, -ks: Slash.KeyState, -slot: S.U64, -root: S.B32,
  h: {Spec.signs(Slash.Block.decide.go(b, ks, slot, root)) == True{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, Lm.Bool.ft(h))
    case False{}:
      {==}

def Laws.block_respects_mark(ks, slot, root, h):
  match ks:
    case Slash.KeyState{+bs, +as, bm, +am}:
      match bm:
        case None{}:
          {==}
        case Some{+w}:
          block_mark_go(S.U64.is_lt(slot, w), Slash.KeyState{bs, as, Some{w}, am}, slot, root, h)

def att_scan_go(c: Bool, -ks: Slash.KeyState, -source: S.U64, -target: S.U64, -root: S.B32,
  h: {Spec.signs(Slash.Att.decide.scan(c, ks, source, target, root)) == True{} : Bool}) -> {Bool.not(c) == True{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, Lm.Bool.ft(h))
    case False{}:
      {==}

def att_order_go(o: Bool, -bs: List<&2, Slash.BlockRec>, -as: List<&2, Slash.AttRec>, -bm: Maybe<&2, S.U64>,
  +ms: S.U64, +mt: S.U64, +source: S.U64, +target: S.U64, -root: S.B32,
  h: {Spec.signs(Slash.Att.decide.go(o, Slash.KeyState{bs, as, bm, Some{Slash.AttMark{ms, mt}}}, source, target, root)) == True{} : Bool})
  -> {Bool.not(Slash.Att.below(source, target, Some{Slash.AttMark{ms, mt}})) == True{} : Bool}:
  match o:
    case False{}:
      Empty.absurd({Bool.not(Slash.Att.below(source, target, Some{Slash.AttMark{ms, mt}})) == True{} : Bool}, Lm.Bool.ft(h))
    case True{}:
      att_scan_go(Slash.Att.below(source, target, Some{Slash.AttMark{ms, mt}}),
        Slash.KeyState{bs, as, bm, Some{Slash.AttMark{ms, mt}}}, source, target, root, h)

def Laws.att_respects_mark(ks, source, target, root, h):
  match ks:
    case Slash.KeyState{+bs, +as, +bm, am}:
      match am:
        case None{}:
          {==}
        case Some{m}:
          match m:
            case Slash.AttMark{+ms, +mt}:
              Lm.Bool.nor(S.U64.is_lt(source, ms), S.U64.is_lt(target, mt),
                att_order_go(Bool.not(S.U64.is_lt(target, source)), bs, as, bm, ms, mt, source, target, root, h))

# L6: the store
# =============

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

# get after put on the same key gives the state that put stored.
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

# get on another key does not see a put.
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

# The state that a Record decision carries.
def RecShape(d: Slash.Decision, want: Slash.KeyState) -> Type:
  match d:
    case Slash.Reject{r}:
      Unit
    case Slash.Repeat{}:
      Unit
    case Slash.Record{st}:
      {st == want : Slash.KeyState}

def att_shape.fin(sc: Slash.Scan, +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>,
  +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +s: S.U64, +t: S.U64, +r: S.B32)
  -> RecShape(Slash.Att.finish(sc, Slash.KeyState{bs, as, bm, am}, s, t, r),
       St.KeyState.add_att(Slash.KeyState{bs, as, bm, am}, Slash.AttRec{s, t, Some{r}})):
  match sc:
    case Slash.Clash{x}:
      Unit{}
    case Slash.Again{}:
      Unit{}
    case Slash.Clear{}:
      {==}

def att_shape.scan(c: Bool, +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>,
  +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +s: S.U64, +t: S.U64, +r: S.B32)
  -> RecShape(Slash.Att.decide.scan(c, Slash.KeyState{bs, as, bm, am}, s, t, r),
       St.KeyState.add_att(Slash.KeyState{bs, as, bm, am}, Slash.AttRec{s, t, Some{r}})):
  match c:
    case True{}:
      Unit{}
    case False{}:
      att_shape.fin(Slash.Att.scan(as, s, t, r), bs, as, bm, am, s, t, r)

def att_shape.go(o: Bool, +ks: Slash.KeyState, +s: S.U64, +t: S.U64, +r: S.B32)
  -> RecShape(Slash.Att.decide.go(o, ks, s, t, r), St.KeyState.add_att(ks, Slash.AttRec{s, t, Some{r}})):
  match o:
    case False{}:
      Unit{}
    case True{}:
      match ks:
        case Slash.KeyState{+bs, +as, +bm, +am}:
          att_shape.scan(Slash.Att.below(s, t, am), bs, as, bm, am, s, t, r)

def att_shape(+ks: Slash.KeyState, +s: S.U64, +t: S.U64, +r: S.B32)
  -> RecShape(Slash.Att.decide(ks, s, t, r), St.KeyState.add_att(ks, Slash.AttRec{s, t, Some{r}})):
  att_shape.go(Bool.not(S.U64.is_lt(t, s)), ks, s, t, r)

def block_shape.fin(sc: Slash.Scan, +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>,
  +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +slot: S.U64, +r: S.B32)
  -> RecShape(Slash.Block.finish(sc, Slash.KeyState{bs, as, bm, am}, slot, r),
       St.KeyState.add_block(Slash.KeyState{bs, as, bm, am}, Slash.BlockRec{slot, Some{r}})):
  match sc:
    case Slash.Clash{x}:
      Unit{}
    case Slash.Again{}:
      Unit{}
    case Slash.Clear{}:
      {==}

def block_shape.go(below: Bool, +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>,
  +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +slot: S.U64, +r: S.B32)
  -> RecShape(Slash.Block.decide.go(below, Slash.KeyState{bs, as, bm, am}, slot, r),
       St.KeyState.add_block(Slash.KeyState{bs, as, bm, am}, Slash.BlockRec{slot, Some{r}})):
  match below:
    case True{}:
      Unit{}
    case False{}:
      block_shape.fin(Slash.Block.scan(bs, slot, r), bs, as, bm, am, slot, r)

def block_shape(+ks: Slash.KeyState, +slot: S.U64, +r: S.B32)
  -> RecShape(Slash.Block.decide(ks, slot, r), St.KeyState.add_block(ks, Slash.BlockRec{slot, Some{r}})):
  match ks:
    case Slash.KeyState{+bs, +as, +bm, +am}:
      block_shape.go(Slash.Block.below(slot, bm), bs, as, bm, am, slot, r)

def Ent(s: St.Store) -> List<&2, St.Entry>:
  match s:
    case St.Store{g, es}:
      es

# The events are all EGvr: they set the root and touch no key.
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

def PreOk(p: Maybe<&2, List<&2, St.LogEvent>>) -> Bool:
  match p:
    case None{}:
      False{}
    case Some{l}:
      AllGvr(l)

def key_state_ent(+s: St.Store, +key: S.Pubkey) -> {St.Store.get(Ent(s), key) == Sto.key_state(s, key) : Slash.KeyState}:
  match s:
    case St.Store{g, es}:
      {==}

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

def apply_all_snoc(p: List<&2, St.LogEvent>, +s: St.Store, +e: St.LogEvent)
  -> {St.Store.apply(St.Store.apply_all(p, s), e) == St.Store.apply_all(List.append(&2, St.LogEvent, p, [e]), s) : St.Store}:
  match p:
    case Nil{}:
      {==}
    case Con{x, rest}:
      apply_all_snoc(rest, St.Store.apply(s, x), e)

def apply_att_ent(+s: St.Store, +key: S.Pubkey, +rec: Slash.AttRec)
  -> {St.Store.put(Ent(s), key, St.KeyState.add_att(St.Store.get(Ent(s), key), rec)) == Ent(St.Store.apply(s, St.EAtt{key, rec})) : List<&2, St.Entry>}:
  match s:
    case St.Store{g, es}:
      {==}

def apply_block_ent(+s: St.Store, +key: S.Pubkey, +rec: Slash.BlockRec)
  -> {St.Store.put(Ent(s), key, St.KeyState.add_block(St.Store.get(Ent(s), key), rec)) == Ent(St.Store.apply(s, St.EBlock{key, rec})) : List<&2, St.Entry>}:
  match s:
    case St.Store{g, es}:
      {==}

def pre_ok_pick(b: Bool, h: {b == True{} : Bool})
  -> {PreOk(Bool.pick(Maybe<&2, List<&2, St.LogEvent>>, b, Some{[]}, None{})) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({PreOk(None{}) == True{} : Bool}, Lm.Bool.ft(h))

def att_out(D: Slash.Decision, +es: List<&2, St.Entry>, +key: S.Pubkey, +rec: Slash.AttRec,
  shape: RecShape(D, St.KeyState.add_att(St.Store.get(es, key), rec)),
  +p: List<&2, St.LogEvent>, +hp: {AllGvr(p) == True{} : Bool}, +have: Maybe<&2, S.B32>)
  -> {Sto.key_state(St.Store.after(St.Store{have, es}, St.Outcome.of(p, D, St.EAtt{key, rec})), key)
      == Slash.KeyState.after(St.Store.get(es, key), D) : Slash.KeyState}:
  match D:
    case Slash.Reject{r}:
      {==}
    case Slash.Repeat{}:
      %key_state_ent(St.Store.apply_all(p, St.Store{have, es}), key) : {_ == St.Store.get(es, key) : Slash.KeyState}
      %gvrs_keep(p, have, es, hp) : {St.Store.get(_, key) == St.Store.get(es, key) : Slash.KeyState}
      {==}
    case Slash.Record{+st}:
      %key_state_ent(St.Store.apply_all(List.append(&2, St.LogEvent, p, [St.EAtt{key, rec}]), St.Store{have, es}), key)
        : {_ == st : Slash.KeyState}
      %apply_all_snoc(p, St.Store{have, es}, St.EAtt{key, rec}) : {St.Store.get(Ent(_), key) == st : Slash.KeyState}
      %apply_att_ent(St.Store.apply_all(p, St.Store{have, es}), key, rec) : {St.Store.get(_, key) == st : Slash.KeyState}
      %gvrs_keep(p, have, es, hp)
        : {St.Store.get(St.Store.put(_, key, St.KeyState.add_att(St.Store.get(_, key), rec)), key) == st : Slash.KeyState}
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, key, St.KeyState.add_att(St.Store.get(es, key), rec)), key),
          St.KeyState.add_att(St.Store.get(es, key), rec), get_put_same(es, key, St.KeyState.add_att(St.Store.get(es, key), rec)))
        : {_ == st : Slash.KeyState}
      Equal.sym(Slash.KeyState, st, St.KeyState.add_att(St.Store.get(es, key), rec), shape)

def block_out(D: Slash.Decision, +es: List<&2, St.Entry>, +key: S.Pubkey, +rec: Slash.BlockRec,
  shape: RecShape(D, St.KeyState.add_block(St.Store.get(es, key), rec)),
  +p: List<&2, St.LogEvent>, +hp: {AllGvr(p) == True{} : Bool}, +have: Maybe<&2, S.B32>)
  -> {Sto.key_state(St.Store.after(St.Store{have, es}, St.Outcome.of(p, D, St.EBlock{key, rec})), key)
      == Slash.KeyState.after(St.Store.get(es, key), D) : Slash.KeyState}:
  match D:
    case Slash.Reject{r}:
      {==}
    case Slash.Repeat{}:
      %key_state_ent(St.Store.apply_all(p, St.Store{have, es}), key) : {_ == St.Store.get(es, key) : Slash.KeyState}
      %gvrs_keep(p, have, es, hp) : {St.Store.get(_, key) == St.Store.get(es, key) : Slash.KeyState}
      {==}
    case Slash.Record{+st}:
      %key_state_ent(St.Store.apply_all(List.append(&2, St.LogEvent, p, [St.EBlock{key, rec}]), St.Store{have, es}), key)
        : {_ == st : Slash.KeyState}
      %apply_all_snoc(p, St.Store{have, es}, St.EBlock{key, rec}) : {St.Store.get(Ent(_), key) == st : Slash.KeyState}
      %apply_block_ent(St.Store.apply_all(p, St.Store{have, es}), key, rec) : {St.Store.get(_, key) == st : Slash.KeyState}
      %gvrs_keep(p, have, es, hp)
        : {St.Store.get(St.Store.put(_, key, St.KeyState.add_block(St.Store.get(_, key), rec)), key) == st : Slash.KeyState}
      %Equal.sym(Slash.KeyState, St.Store.get(St.Store.put(es, key, St.KeyState.add_block(St.Store.get(es, key), rec)), key),
          St.KeyState.add_block(St.Store.get(es, key), rec), get_put_same(es, key, St.KeyState.add_block(St.Store.get(es, key), rec)))
        : {_ == st : Slash.KeyState}
      Equal.sym(Slash.KeyState, st, St.KeyState.add_block(St.Store.get(es, key), rec), shape)

def att_go(pre: Maybe<&2, List<&2, St.LogEvent>>, hp: {PreOk(pre) == True{} : Bool}, +have: Maybe<&2, S.B32>,
  +es: List<&2, St.Entry>, +key: S.Pubkey, +d: S.AttestationData, +root: S.B32)
  -> {Sto.key_state(St.Store.after(St.Store{have, es}, St.Store.decide.go(pre, es, key, R.MAttestation{d}, root)), key)
      == Slash.KeyState.after(St.Store.get(es, key),
           Slash.Att.decide(St.Store.get(es, key), Sto.source(d), Sto.target(d), root)) : Slash.KeyState}:
  match pre:
    case None{}:
      Empty.absurd({Sto.key_state(St.Store.after(St.Store{have, es}, St.Store.decide.go(None{}, es, key, R.MAttestation{d}, root)), key)
        == Slash.KeyState.after(St.Store.get(es, key),
             Slash.Att.decide(St.Store.get(es, key), Sto.source(d), Sto.target(d), root)) : Slash.KeyState}, Lm.Bool.ft(hp))
    case Some{+p}:
      match d:
        case S.AttestationData{+slot, +index, +bbr, src, tgt}:
          match src tgt:
            case S.Checkpoint{+se, +sr} S.Checkpoint{+te, +tr}:
              att_out(Slash.Att.decide(St.Store.get(es, key), se, te, root), es, key, Slash.AttRec{se, te, Some{root}},
                att_shape(St.Store.get(es, key), se, te, root), p, hp, have)

def block_go(pre: Maybe<&2, List<&2, St.LogEvent>>, hp: {PreOk(pre) == True{} : Bool}, +have: Maybe<&2, S.B32>,
  +es: List<&2, St.Entry>, +key: S.Pubkey, +hd: S.BeaconBlockHeader, +root: S.B32)
  -> {Sto.key_state(St.Store.after(St.Store{have, es}, St.Store.decide.go(pre, es, key, R.MBlock{hd}, root)), key)
      == Slash.KeyState.after(St.Store.get(es, key),
           Slash.Block.decide(St.Store.get(es, key), Sto.slot(hd), root)) : Slash.KeyState}:
  match pre:
    case None{}:
      Empty.absurd({Sto.key_state(St.Store.after(St.Store{have, es}, St.Store.decide.go(None{}, es, key, R.MBlock{hd}, root)), key)
        == Slash.KeyState.after(St.Store.get(es, key),
             Slash.Block.decide(St.Store.get(es, key), Sto.slot(hd), root)) : Slash.KeyState}, Lm.Bool.ft(hp))
    case Some{+p}:
      match hd:
        case S.BeaconBlockHeader{+slot, +pi, +pr, +sr, +br}:
          block_out(Slash.Block.decide(St.Store.get(es, key), slot, root), es, key, Slash.BlockRec{slot, Some{root}},
            block_shape(St.Store.get(es, key), slot, root), p, hp, have)

def Laws.store_att_is_key_decision(s, key, d, fork, gvr, claimed, root, h):
  match s:
    case St.Store{have, +es}:
      match have:
        case None{}:
          att_go(Some{[St.EGvr{gvr}]}, {==}, None{}, es, key, d, root)
        case Some{+x}:
          att_go(St.Store.decide.gvr(gvr, Some{x}), pre_ok_pick(S.B32.is_eq(gvr, x), h), Some{x}, es, key, d, root)

def Laws.store_block_is_key_decision(s, key, hd, fork, gvr, claimed, root, h):
  match s:
    case St.Store{have, +es}:
      match have:
        case None{}:
          block_go(Some{[St.EGvr{gvr}]}, {==}, None{}, es, key, hd, root)
        case Some{+x}:
          block_go(St.Store.decide.gvr(gvr, Some{x}), pre_ok_pick(S.B32.is_eq(gvr, x), h), Some{x}, es, key, hd, root)

# The prefix is None (the gvr check failed) or only EGvr events.
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

def other_keep(+es: List<&2, St.Entry>, +other: S.Pubkey, +p: List<&2, St.LogEvent>,
  +hp: {AllGvr(p) == True{} : Bool}, +have: Maybe<&2, S.B32>)
  -> {Sto.key_state(St.Store.apply_all(p, St.Store{have, es}), other) == St.Store.get(es, other) : Slash.KeyState}:
  %key_state_ent(St.Store.apply_all(p, St.Store{have, es}), other) : {_ == St.Store.get(es, other) : Slash.KeyState}
  %gvrs_keep(p, have, es, hp) : {St.Store.get(_, other) == St.Store.get(es, other) : Slash.KeyState}
  {==}

def other_att(D: Slash.Decision, +es: List<&2, St.Entry>, +key: S.Pubkey, +other: S.Pubkey, +rec: Slash.AttRec,
  +p: List<&2, St.LogEvent>, +hp: {AllGvr(p) == True{} : Bool}, +have: Maybe<&2, S.B32>,
  +h: {S.Pubkey.is_eq(other, key) == False{} : Bool})
  -> {Sto.key_state(St.Store.after(St.Store{have, es}, St.Outcome.of(p, D, St.EAtt{key, rec})), other)
      == St.Store.get(es, other) : Slash.KeyState}:
  match D:
    case Slash.Reject{r}:
      {==}
    case Slash.Repeat{}:
      other_keep(es, other, p, hp, have)
    case Slash.Record{st}:
      %key_state_ent(St.Store.apply_all(List.append(&2, St.LogEvent, p, [St.EAtt{key, rec}]), St.Store{have, es}), other)
        : {_ == St.Store.get(es, other) : Slash.KeyState}
      %apply_all_snoc(p, St.Store{have, es}, St.EAtt{key, rec}) : {St.Store.get(Ent(_), other) == St.Store.get(es, other) : Slash.KeyState}
      %apply_att_ent(St.Store.apply_all(p, St.Store{have, es}), key, rec) : {St.Store.get(_, other) == St.Store.get(es, other) : Slash.KeyState}
      %gvrs_keep(p, have, es, hp)
        : {St.Store.get(St.Store.put(_, key, St.KeyState.add_att(St.Store.get(_, key), rec)), other) == St.Store.get(es, other) : Slash.KeyState}
      get_put_other(es, key, other, St.KeyState.add_att(St.Store.get(es, key), rec), h)

def other_block(D: Slash.Decision, +es: List<&2, St.Entry>, +key: S.Pubkey, +other: S.Pubkey, +rec: Slash.BlockRec,
  +p: List<&2, St.LogEvent>, +hp: {AllGvr(p) == True{} : Bool}, +have: Maybe<&2, S.B32>,
  +h: {S.Pubkey.is_eq(other, key) == False{} : Bool})
  -> {Sto.key_state(St.Store.after(St.Store{have, es}, St.Outcome.of(p, D, St.EBlock{key, rec})), other)
      == St.Store.get(es, other) : Slash.KeyState}:
  match D:
    case Slash.Reject{r}:
      {==}
    case Slash.Repeat{}:
      other_keep(es, other, p, hp, have)
    case Slash.Record{st}:
      %key_state_ent(St.Store.apply_all(List.append(&2, St.LogEvent, p, [St.EBlock{key, rec}]), St.Store{have, es}), other)
        : {_ == St.Store.get(es, other) : Slash.KeyState}
      %apply_all_snoc(p, St.Store{have, es}, St.EBlock{key, rec}) : {St.Store.get(Ent(_), other) == St.Store.get(es, other) : Slash.KeyState}
      %apply_block_ent(St.Store.apply_all(p, St.Store{have, es}), key, rec) : {St.Store.get(_, other) == St.Store.get(es, other) : Slash.KeyState}
      %gvrs_keep(p, have, es, hp)
        : {St.Store.get(St.Store.put(_, key, St.KeyState.add_block(St.Store.get(_, key), rec)), other) == St.Store.get(es, other) : Slash.KeyState}
      get_put_other(es, key, other, St.KeyState.add_block(St.Store.get(es, key), rec), h)

def other_go(pre: Maybe<&2, List<&2, St.LogEvent>>, hp: {PreGvr(pre) == True{} : Bool}, +have: Maybe<&2, S.B32>,
  +es: List<&2, St.Entry>, +key: S.Pubkey, +other: S.Pubkey, msg: R.Msg, +root: S.B32,
  +h: {S.Pubkey.is_eq(other, key) == False{} : Bool})
  -> {Sto.key_state(St.Store.after(St.Store{have, es}, St.Store.decide.go(pre, es, key, msg, root)), other)
      == St.Store.get(es, other) : Slash.KeyState}:
  match pre:
    case None{}:
      {==}
    case Some{+p}:
      match msg:
        case R.MAttestation{d}:
          match d:
            case S.AttestationData{+slot, +index, +bbr, src, tgt}:
              match src tgt:
                case S.Checkpoint{+se, +sr} S.Checkpoint{+te, +tr}:
                  other_att(Slash.Att.decide(St.Store.get(es, key), se, te, root), es, key, other,
                    Slash.AttRec{se, te, Some{root}}, p, hp, have, h)
        case R.MBlock{hd}:
          match hd:
            case S.BeaconBlockHeader{+slot, +pi, +pr, +sr, +br}:
              other_block(Slash.Block.decide(St.Store.get(es, key), slot, root), es, key, other,
                Slash.BlockRec{slot, Some{root}}, p, hp, have, h)
        case R.MRandao{e}:
          other_keep(es, other, p, hp, have)
        case R.MAggSlot{x}:
          other_keep(es, other, p, hp, have)
        case R.MAggregate{a}:
          other_keep(es, other, p, hp, have)
        case R.MSyncMsg{x, r}:
          other_keep(es, other, p, hp, have)
        case R.MSyncSel{d}:
          other_keep(es, other, p, hp, have)
        case R.MContribution{c}:
          other_keep(es, other, p, hp, have)
        case R.MExit{e, c, d}:
          other_keep(es, other, p, hp, have)
        case R.MRegistration{x, v}:
          other_keep(es, other, p, hp, have)

# A registration skips the gvr check: its prefix is empty.
def pre_gvr_msg(+msg: R.Msg, +g: S.B32, have: Maybe<&2, S.B32>) -> {PreGvr(St.Store.decide.pre(msg, g, have)) == True{} : Bool}:
  match msg:
    case R.MRegistration{x, v}:
      {==}
    case R.MAttestation{a}:
      pre_gvr(g, have)
    case R.MBlock{hd}:
      pre_gvr(g, have)
    case R.MRandao{e}:
      pre_gvr(g, have)
    case R.MAggSlot{x}:
      pre_gvr(g, have)
    case R.MAggregate{a}:
      pre_gvr(g, have)
    case R.MSyncMsg{x, r}:
      pre_gvr(g, have)
    case R.MSyncSel{d}:
      pre_gvr(g, have)
    case R.MContribution{c}:
      pre_gvr(g, have)
    case R.MExit{e, c, d}:
      pre_gvr(g, have)

def Laws.store_other_keys(s, key, other, r, root, h):
  match s:
    case St.Store{have, +es}:
      match r:
        case R.Request{+msg, fork, +g, claimed}:
          other_go(St.Store.decide.pre(msg, g, have), pre_gvr_msg(msg, g, have), have, es, key, other, msg, root, h)

# L5: records
# ===========

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

def mark_eq_refl(+m: Maybe<&2, S.U64>) -> {True{} == Spec.mark_eq(m, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      U64.is_eq_refl(x)

def att_mark_eq_refl(+m: Maybe<&2, Slash.AttMark>) -> {True{} == Spec.att_mark_eq(m, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Slash.AttMark{+ms, +mt}:
          Lm.Bool.and_tt(Spec.eq(ms, ms), Spec.eq(mt, mt), U64.is_eq_refl(ms), U64.is_eq_refl(mt))

# keeps(ks, ks2) when the block records of ks are within bs2, and the rest is equal.
def keeps_from(+bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>, +bm: Maybe<&2, S.U64>,
  +am: Maybe<&2, Slash.AttMark>, +bs2: List<&2, Slash.BlockRec>, +as2: List<&2, Slash.AttRec>,
  hb: {True{} == Spec.blocks_within(bs, bs2) : Bool}, ha: {True{} == Spec.atts_within(as, as2) : Bool})
  -> {Spec.keeps(Slash.KeyState{bs, as, bm, am}, Slash.KeyState{bs2, as2, bm, am}) == True{} : Bool}:
  Equal.sym(Bool, True{}, Spec.keeps(Slash.KeyState{bs, as, bm, am}, Slash.KeyState{bs2, as2, bm, am}),
    Lm.Bool.and_tt(Bool.and(Bool.and(Spec.blocks_within(bs, bs2), Spec.atts_within(as, as2)), Spec.mark_eq(bm, bm)),
      Spec.att_mark_eq(am, am),
      Lm.Bool.and_tt(Bool.and(Spec.blocks_within(bs, bs2), Spec.atts_within(as, as2)), Spec.mark_eq(bm, bm),
        Lm.Bool.and_tt(Spec.blocks_within(bs, bs2), Spec.atts_within(as, as2), hb, ha),
        mark_eq_refl(bm)),
      att_mark_eq_refl(am)))

def keeps_refl(+ks: Slash.KeyState) -> {Spec.keeps(ks, ks) == True{} : Bool}:
  match ks:
    case Slash.KeyState{+bs, +as, +bm, +am}:
      keeps_from(bs, as, bm, am, bs, as, blocks_within_refl(bs), atts_within_refl(as))

def keeps_add_att(+ks: Slash.KeyState, +r: Slash.AttRec) -> {Spec.keeps(ks, St.KeyState.add_att(ks, r)) == True{} : Bool}:
  match ks:
    case Slash.KeyState{+bs, +as, +bm, +am}:
      keeps_from(bs, as, bm, am, bs, Con{r, as}, blocks_within_refl(bs), atts_weaken(as, r, as, atts_within_refl(as)))

def keeps_add_block(+ks: Slash.KeyState, +r: Slash.BlockRec) -> {Spec.keeps(ks, St.KeyState.add_block(ks, r)) == True{} : Bool}:
  match ks:
    case Slash.KeyState{+bs, +as, +bm, +am}:
      keeps_from(bs, as, bm, am, Con{r, bs}, as, blocks_weaken(bs, r, bs, blocks_within_refl(bs)), atts_within_refl(as))

def keeps_after_att(D: Slash.Decision, +ks: Slash.KeyState, +r: Slash.AttRec, shape: RecShape(D, St.KeyState.add_att(ks, r)))
  -> {Spec.keeps(ks, Slash.KeyState.after(ks, D)) == True{} : Bool}:
  match D:
    case Slash.Reject{x}:
      keeps_refl(ks)
    case Slash.Repeat{}:
      keeps_refl(ks)
    case Slash.Record{+st}:
      %Equal.sym(Slash.KeyState, st, St.KeyState.add_att(ks, r), shape) : {Spec.keeps(ks, _) == True{} : Bool}
      keeps_add_att(ks, r)

def keeps_after_block(D: Slash.Decision, +ks: Slash.KeyState, +r: Slash.BlockRec, shape: RecShape(D, St.KeyState.add_block(ks, r)))
  -> {Spec.keeps(ks, Slash.KeyState.after(ks, D)) == True{} : Bool}:
  match D:
    case Slash.Reject{x}:
      keeps_refl(ks)
    case Slash.Repeat{}:
      keeps_refl(ks)
    case Slash.Record{+st}:
      %Equal.sym(Slash.KeyState, st, St.KeyState.add_block(ks, r), shape) : {Spec.keeps(ks, _) == True{} : Bool}
      keeps_add_block(ks, r)

def Laws.att_keeps_records(ks, source, target, root):
  keeps_after_att(Slash.Att.decide(ks, source, target, root), ks, Slash.AttRec{source, target, Some{root}},
    att_shape(ks, source, target, root))

def Laws.block_keeps_records(ks, slot, root):
  keeps_after_block(Slash.Block.decide(ks, slot, root), ks, Slash.BlockRec{slot, Some{root}}, block_shape(ks, slot, root))

# A scan that answers Again found the request in the records.

# Empty at Again, Unit elsewhere.
def Scan.disc_again(s: Slash.Scan) -> Type:
  match s:
    case Slash.Clear{}:
      Unit
    case Slash.Again{}:
      Empty
    case Slash.Clash{r}:
      Unit

def Scan.clash_again(-r: Slash.Reason, h: {Slash.Clash{r} == Slash.Again{} : Slash.Scan}) -> Scan.disc_again(Slash.Again{}):
  %h : Scan.disc_again(_)
  Unit{}

def Scan.clear_again(h: {Slash.Clear{} == Slash.Again{} : Slash.Scan}) -> Scan.disc_again(Slash.Again{}):
  %h : Scan.disc_again(_)
  Unit{}

def att_one_again.tail(p1: Bool, p2: Bool,
  h: {Bool.pick(Slash.Scan, p1, Slash.Clash{Slash.Surrounded{}},
        Bool.pick(Slash.Scan, p2, Slash.Clash{Slash.Surrounds{}}, Slash.Clear{})) == Slash.Again{} : Slash.Scan})
  -> Scan.disc_again(Slash.Again{}):
  match p1:
    case True{}:
      Scan.clash_again(Slash.Surrounded{}, h)
    case False{}:
      match p2:
        case True{}:
          Scan.clash_again(Slash.Surrounds{}, h)
        case False{}:
          Scan.clear_again(h)

def att_one_again.same(br: Bool, bs: Bool, h: {Slash.Att.same_target(br, bs) == Slash.Again{} : Slash.Scan})
  -> {Bool.and(Bool.and(bs, True{}), br) == True{} : Bool}:
  match br:
    case False{}:
      Empty.absurd({Bool.and(Bool.and(bs, True{}), False{}) == True{} : Bool}, Scan.clash_again(Slash.DoubleVote{}, h))
    case True{}:
      match bs:
        case True{}:
          {==}
        case False{}:
          Empty.absurd({Bool.and(Bool.and(False{}, True{}), True{}) == True{} : Bool}, Scan.clear_again(h))

def att_one_again.bt(bt: Bool, bs: Bool, +s: S.U64, +t: S.U64, +root: S.B32, +rs: S.U64, +rt: S.U64, rr: Maybe<&2, S.B32>,
  h: {Bool.pick(Slash.Scan, bt, Slash.Att.same_target(Slash.Root.is(root, rr), bs),
        Bool.pick(Slash.Scan, Bool.and(S.U64.is_lt(rs, s), S.U64.is_lt(t, rt)), Slash.Clash{Slash.Surrounded{}},
          Bool.pick(Slash.Scan, Bool.and(S.U64.is_lt(s, rs), S.U64.is_lt(rt, t)), Slash.Clash{Slash.Surrounds{}},
            Slash.Clear{}))) == Slash.Again{} : Slash.Scan})
  -> {Bool.and(Bool.and(bs, bt), Spec.root_eq(Some{root}, rr)) == True{} : Bool}:
  match bt:
    case False{}:
      Empty.absurd({Bool.and(Bool.and(bs, False{}), Spec.root_eq(Some{root}, rr)) == True{} : Bool},
        att_one_again.tail(Bool.and(S.U64.is_lt(rs, s), S.U64.is_lt(t, rt)), Bool.and(S.U64.is_lt(s, rs), S.U64.is_lt(rt, t)), h))
    case True{}:
      match rr:
        case None{}:
          Empty.absurd({Bool.and(Bool.and(bs, True{}), Spec.root_eq(Some{root}, None{})) == True{} : Bool},
            Scan.clash_again(Slash.DoubleVote{}, h))
        case Some{+y}:
          att_one_again.same(S.B32.is_eq(root, y), bs, h)

def att_one_again(+s: S.U64, +t: S.U64, +root: S.B32, x: Slash.AttRec,
  h: {Slash.Att.scan.one(s, t, root, x) == Slash.Again{} : Slash.Scan})
  -> {Spec.att_eq(Slash.AttRec{s, t, Some{root}}, x) == True{} : Bool}:
  match x:
    case Slash.AttRec{+rs, +rt, +rr}:
      att_one_again.bt(S.U64.is_eq(t, rt), S.U64.is_eq(s, rs), s, t, root, rs, rt, rr, h)

def att_scan_again.join(a: Slash.Scan, -b: Slash.Scan, +s: S.U64, +t: S.U64, +root: S.B32, +x: Slash.AttRec,
  +rest: List<&2, Slash.AttRec>,
  ea: {a == Slash.Att.scan.one(s, t, root, x) : Slash.Scan},
  eb: {b == Slash.Att.scan(rest, s, t, root) : Slash.Scan},
  h: {Slash.Scan.join(a, b) == Slash.Again{} : Slash.Scan},
  ih: {Slash.Att.scan(rest, s, t, root) == Slash.Again{} : Slash.Scan}
      -> {Spec.has_att(Slash.AttRec{s, t, Some{root}}, rest) == True{} : Bool})
  -> {Bool.or(Spec.att_eq(Slash.AttRec{s, t, Some{root}}, x), Spec.has_att(Slash.AttRec{s, t, Some{root}}, rest)) == True{} : Bool}:
  match a:
    case Slash.Clash{r}:
      Empty.absurd({Bool.or(Spec.att_eq(Slash.AttRec{s, t, Some{root}}, x), Spec.has_att(Slash.AttRec{s, t, Some{root}}, rest)) == True{} : Bool},
        Scan.clash_again(r, h))
    case Slash.Again{}:
      Equal.sym(Bool, True{}, Bool.or(Spec.att_eq(Slash.AttRec{s, t, Some{root}}, x), Spec.has_att(Slash.AttRec{s, t, Some{root}}, rest)),
        Bool.or_tl(Spec.att_eq(Slash.AttRec{s, t, Some{root}}, x), Spec.has_att(Slash.AttRec{s, t, Some{root}}, rest),
          Equal.sym(Bool, Spec.att_eq(Slash.AttRec{s, t, Some{root}}, x), True{},
            att_one_again(s, t, root, x, Equal.sym(Slash.Scan, Slash.Again{}, Slash.Att.scan.one(s, t, root, x), ea)))))
    case Slash.Clear{}:
      Equal.sym(Bool, True{}, Bool.or(Spec.att_eq(Slash.AttRec{s, t, Some{root}}, x), Spec.has_att(Slash.AttRec{s, t, Some{root}}, rest)),
        Bool.or_tr(Spec.att_eq(Slash.AttRec{s, t, Some{root}}, x), Spec.has_att(Slash.AttRec{s, t, Some{root}}, rest),
          Equal.sym(Bool, Spec.has_att(Slash.AttRec{s, t, Some{root}}, rest), True{},
            ih(Equal.trans(Slash.Scan, Slash.Att.scan(rest, s, t, root), b, Slash.Again{},
              Equal.sym(Slash.Scan, b, Slash.Att.scan(rest, s, t, root), eb), h)))))

def att_scan_again(xs: List<&2, Slash.AttRec>, +s: S.U64, +t: S.U64, +root: S.B32,
  h: {Slash.Att.scan(xs, s, t, root) == Slash.Again{} : Slash.Scan})
  -> {Spec.has_att(Slash.AttRec{s, t, Some{root}}, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Spec.has_att(Slash.AttRec{s, t, Some{root}}, Nil{}) == True{} : Bool}, Scan.clear_again(h))
    case Con{+x, +rest}:
      att_scan_again.join(Slash.Att.scan.one(s, t, root, x), Slash.Att.scan(rest, s, t, root), s, t, root, x, rest,
        {==}, {==}, h, att_scan_again(rest, s, t, root))

def block_one_again.same(br: Bool, h: {Slash.Scan.same_or(br, Slash.DoubleBlock{}) == Slash.Again{} : Slash.Scan})
  -> {Bool.and(True{}, br) == True{} : Bool}:
  match br:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.and(True{}, False{}) == True{} : Bool}, Scan.clash_again(Slash.DoubleBlock{}, h))

def block_one_again.b(b: Bool, +root: S.B32, rr: Maybe<&2, S.B32>,
  h: {Bool.pick(Slash.Scan, b, Slash.Scan.same_or(Slash.Root.is(root, rr), Slash.DoubleBlock{}), Slash.Clear{}) == Slash.Again{} : Slash.Scan})
  -> {Bool.and(b, Spec.root_eq(Some{root}, rr)) == True{} : Bool}:
  match b:
    case False{}:
      Empty.absurd({Bool.and(False{}, Spec.root_eq(Some{root}, rr)) == True{} : Bool}, Scan.clear_again(h))
    case True{}:
      match rr:
        case None{}:
          Empty.absurd({Bool.and(True{}, Spec.root_eq(Some{root}, None{})) == True{} : Bool},
            Scan.clash_again(Slash.DoubleBlock{}, h))
        case Some{+y}:
          block_one_again.same(S.B32.is_eq(root, y), h)

def block_one_again(+slot: S.U64, +root: S.B32, x: Slash.BlockRec,
  h: {Slash.Block.scan.one(slot, root, x) == Slash.Again{} : Slash.Scan})
  -> {Spec.block_eq(Slash.BlockRec{slot, Some{root}}, x) == True{} : Bool}:
  match x:
    case Slash.BlockRec{+rs, +rr}:
      block_one_again.b(S.U64.is_eq(slot, rs), root, rr, h)

def block_scan_again.join(a: Slash.Scan, -b: Slash.Scan, +slot: S.U64, +root: S.B32, +x: Slash.BlockRec,
  +rest: List<&2, Slash.BlockRec>,
  ea: {a == Slash.Block.scan.one(slot, root, x) : Slash.Scan},
  eb: {b == Slash.Block.scan(rest, slot, root) : Slash.Scan},
  h: {Slash.Scan.join(a, b) == Slash.Again{} : Slash.Scan},
  ih: {Slash.Block.scan(rest, slot, root) == Slash.Again{} : Slash.Scan}
      -> {Spec.has_block(Slash.BlockRec{slot, Some{root}}, rest) == True{} : Bool})
  -> {Bool.or(Spec.block_eq(Slash.BlockRec{slot, Some{root}}, x), Spec.has_block(Slash.BlockRec{slot, Some{root}}, rest)) == True{} : Bool}:
  match a:
    case Slash.Clash{r}:
      Empty.absurd({Bool.or(Spec.block_eq(Slash.BlockRec{slot, Some{root}}, x), Spec.has_block(Slash.BlockRec{slot, Some{root}}, rest)) == True{} : Bool},
        Scan.clash_again(r, h))
    case Slash.Again{}:
      Equal.sym(Bool, True{}, Bool.or(Spec.block_eq(Slash.BlockRec{slot, Some{root}}, x), Spec.has_block(Slash.BlockRec{slot, Some{root}}, rest)),
        Bool.or_tl(Spec.block_eq(Slash.BlockRec{slot, Some{root}}, x), Spec.has_block(Slash.BlockRec{slot, Some{root}}, rest),
          Equal.sym(Bool, Spec.block_eq(Slash.BlockRec{slot, Some{root}}, x), True{},
            block_one_again(slot, root, x, Equal.sym(Slash.Scan, Slash.Again{}, Slash.Block.scan.one(slot, root, x), ea)))))
    case Slash.Clear{}:
      Equal.sym(Bool, True{}, Bool.or(Spec.block_eq(Slash.BlockRec{slot, Some{root}}, x), Spec.has_block(Slash.BlockRec{slot, Some{root}}, rest)),
        Bool.or_tr(Spec.block_eq(Slash.BlockRec{slot, Some{root}}, x), Spec.has_block(Slash.BlockRec{slot, Some{root}}, rest),
          Equal.sym(Bool, Spec.has_block(Slash.BlockRec{slot, Some{root}}, rest), True{},
            ih(Equal.trans(Slash.Scan, Slash.Block.scan(rest, slot, root), b, Slash.Again{},
              Equal.sym(Slash.Scan, b, Slash.Block.scan(rest, slot, root), eb), h)))))

def block_scan_again(xs: List<&2, Slash.BlockRec>, +slot: S.U64, +root: S.B32,
  h: {Slash.Block.scan(xs, slot, root) == Slash.Again{} : Slash.Scan})
  -> {Spec.has_block(Slash.BlockRec{slot, Some{root}}, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Spec.has_block(Slash.BlockRec{slot, Some{root}}, Nil{}) == True{} : Bool}, Scan.clear_again(h))
    case Con{+x, +rest}:
      block_scan_again.join(Slash.Block.scan.one(slot, root, x), Slash.Block.scan(rest, slot, root), slot, root, x, rest,
        {==}, {==}, h, block_scan_again(rest, slot, root))

# What a Repeat decision knows: the request has a record.
def AttRep(d: Slash.Decision, +ks: Slash.KeyState, +r: Slash.AttRec) -> Type:
  match d:
    case Slash.Reject{x}:
      Unit
    case Slash.Repeat{}:
      {Spec.signs_att_recorded(Slash.Repeat{}, ks, r) == True{} : Bool}
    case Slash.Record{st}:
      Unit

def BlockRep(d: Slash.Decision, +ks: Slash.KeyState, +r: Slash.BlockRec) -> Type:
  match d:
    case Slash.Reject{x}:
      Unit
    case Slash.Repeat{}:
      {Spec.signs_block_recorded(Slash.Repeat{}, ks, r) == True{} : Bool}
    case Slash.Record{st}:
      Unit

def att_rep.fin(sc: Slash.Scan, +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>,
  +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +s: S.U64, +t: S.U64, +r: S.B32,
  e: {sc == Slash.Att.scan(as, s, t, r) : Slash.Scan})
  -> AttRep(Slash.Att.finish(sc, Slash.KeyState{bs, as, bm, am}, s, t, r), Slash.KeyState{bs, as, bm, am}, Slash.AttRec{s, t, Some{r}}):
  match sc:
    case Slash.Clash{x}:
      Unit{}
    case Slash.Clear{}:
      Unit{}
    case Slash.Again{}:
      att_scan_again(as, s, t, r, Equal.sym(Slash.Scan, Slash.Again{}, Slash.Att.scan(as, s, t, r), e))

def att_rep.scan(c: Bool, +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>,
  +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +s: S.U64, +t: S.U64, +r: S.B32)
  -> AttRep(Slash.Att.decide.scan(c, Slash.KeyState{bs, as, bm, am}, s, t, r), Slash.KeyState{bs, as, bm, am}, Slash.AttRec{s, t, Some{r}}):
  match c:
    case True{}:
      Unit{}
    case False{}:
      att_rep.fin(Slash.Att.scan(as, s, t, r), bs, as, bm, am, s, t, r, {==})

def att_rep.go(o: Bool, +ks: Slash.KeyState, +s: S.U64, +t: S.U64, +r: S.B32)
  -> AttRep(Slash.Att.decide.go(o, ks, s, t, r), ks, Slash.AttRec{s, t, Some{r}}):
  match o:
    case False{}:
      Unit{}
    case True{}:
      match ks:
        case Slash.KeyState{+bs, +as, +bm, +am}:
          att_rep.scan(Slash.Att.below(s, t, am), bs, as, bm, am, s, t, r)

def block_rep.fin(sc: Slash.Scan, +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>,
  +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +slot: S.U64, +r: S.B32,
  e: {sc == Slash.Block.scan(bs, slot, r) : Slash.Scan})
  -> BlockRep(Slash.Block.finish(sc, Slash.KeyState{bs, as, bm, am}, slot, r), Slash.KeyState{bs, as, bm, am}, Slash.BlockRec{slot, Some{r}}):
  match sc:
    case Slash.Clash{x}:
      Unit{}
    case Slash.Clear{}:
      Unit{}
    case Slash.Again{}:
      block_scan_again(bs, slot, r, Equal.sym(Slash.Scan, Slash.Again{}, Slash.Block.scan(bs, slot, r), e))

def block_rep.go(below: Bool, +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>,
  +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +slot: S.U64, +r: S.B32)
  -> BlockRep(Slash.Block.decide.go(below, Slash.KeyState{bs, as, bm, am}, slot, r), Slash.KeyState{bs, as, bm, am}, Slash.BlockRec{slot, Some{r}}):
  match below:
    case True{}:
      Unit{}
    case False{}:
      block_rep.fin(Slash.Block.scan(bs, slot, r), bs, as, bm, am, slot, r, {==})

def att_recorded_new(+ks: Slash.KeyState, +r: Slash.AttRec)
  -> {Spec.signs_att_recorded(Slash.Record{St.KeyState.add_att(ks, r)}, ks, r) == True{} : Bool}:
  match ks:
    case Slash.KeyState{+bs, +as, +bm, +am}:
      Equal.sym(Bool, True{}, Spec.has_att(r, Con{r, as}),
        Bool.or_tl(Spec.att_eq(r, r), Spec.has_att(r, as), att_eq_refl(r)))

def att_recorded_after(D: Slash.Decision, +ks: Slash.KeyState, +r: Slash.AttRec,
  shape: RecShape(D, St.KeyState.add_att(ks, r)), rep: AttRep(D, ks, r))
  -> {Spec.signs_att_recorded(D, ks, r) == True{} : Bool}:
  match D:
    case Slash.Reject{x}:
      {==}
    case Slash.Repeat{}:
      rep
    case Slash.Record{+st}:
      %Equal.sym(Slash.KeyState, st, St.KeyState.add_att(ks, r), shape)
        : {Spec.signs_att_recorded(Slash.Record{_}, ks, r) == True{} : Bool}
      att_recorded_new(ks, r)

def block_recorded_new(+ks: Slash.KeyState, +r: Slash.BlockRec)
  -> {Spec.signs_block_recorded(Slash.Record{St.KeyState.add_block(ks, r)}, ks, r) == True{} : Bool}:
  match ks:
    case Slash.KeyState{+bs, +as, +bm, +am}:
      Equal.sym(Bool, True{}, Spec.has_block(r, Con{r, bs}),
        Bool.or_tl(Spec.block_eq(r, r), Spec.has_block(r, bs), block_eq_refl(r)))

def block_recorded_after(D: Slash.Decision, +ks: Slash.KeyState, +r: Slash.BlockRec,
  shape: RecShape(D, St.KeyState.add_block(ks, r)), rep: BlockRep(D, ks, r))
  -> {Spec.signs_block_recorded(D, ks, r) == True{} : Bool}:
  match D:
    case Slash.Reject{x}:
      {==}
    case Slash.Repeat{}:
      rep
    case Slash.Record{+st}:
      %Equal.sym(Slash.KeyState, st, St.KeyState.add_block(ks, r), shape)
        : {Spec.signs_block_recorded(Slash.Record{_}, ks, r) == True{} : Bool}
      block_recorded_new(ks, r)

def Laws.att_recorded(ks, source, target, root):
  att_recorded_after(Slash.Att.decide(ks, source, target, root), ks, Slash.AttRec{source, target, Some{root}},
    att_shape(ks, source, target, root), att_rep.go(Bool.not(S.U64.is_lt(target, source)), ks, source, target, root))

def Laws.block_recorded(ks, slot, root):
  match ks:
    case Slash.KeyState{+bs, +as, +bm, +am}:
      block_recorded_after(Slash.Block.decide(Slash.KeyState{bs, as, bm, am}, slot, root), Slash.KeyState{bs, as, bm, am},
        Slash.BlockRec{slot, Some{root}}, block_shape(Slash.KeyState{bs, as, bm, am}, slot, root),
        block_rep.go(Slash.Block.below(slot, bm), bs, as, bm, am, slot, root))

# L4, liveness: a scan clashes exactly when the spec says so
# ==========================================================

def Scan.is_clash(s: Slash.Scan) -> Bool:
  match s:
    case Slash.Clear{}:
      False{}
    case Slash.Again{}:
      False{}
    case Slash.Clash{r}:
      True{}

def join_clash(a: Slash.Scan, b: Slash.Scan)
  -> {Bool.or(Scan.is_clash(a), Scan.is_clash(b)) == Scan.is_clash(Slash.Scan.join(a, b)) : Bool}:
  match a:
    case Slash.Clash{r}:
      {==}
    case Slash.Clear{}:
      {==}
    case Slash.Again{}:
      match b:
        case Slash.Clash{r}:
          {==}
        case Slash.Again{}:
          {==}
        case Slash.Clear{}:
          {==}

def differ_root(+root: S.B32, rr: Maybe<&2, S.B32>)
  -> {Bool.not(Slash.Root.is(root, rr)) == Spec.differ(Some{root}, rr) : Bool}:
  match rr:
    case None{}:
      {==}
    case Some{y}:
      {==}

def cmp_lo_eq(h: Cmp, -l: Cmp, e: {S.U64.cmp.lo(h, l) == EQ{} : Cmp}) -> {h == EQ{} : Cmp} & {l == EQ{} : Cmp}:
  match h:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp} & {l == EQ{} : Cmp}, Lm.Cmp.lt_eq(e))
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp} & {l == EQ{} : Cmp}, Lm.Cmp.gt_eq(e))
    case EQ{}:
      ({==}, e)

def u32_is_eq_of_cmp(+a: U32, +b: U32, e: {U32.cmp(a, b) == EQ{} : Cmp}) -> {U32.is_eq(a, b) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, b), EQ{}, e) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def u64_eq_of.pair(+ah: U32, +al: U32, +bh: U32, +bl: U32,
  pr: {U32.cmp(ah, bh) == EQ{} : Cmp} & {U32.cmp(al, bl) == EQ{} : Cmp})
  -> {S.U64{ah, al} == S.U64{bh, bl} : S.U64}:
  (e1, e2) = pr
  %Lm.U32.eq_of(ah, bh, u32_is_eq_of_cmp(ah, bh, e1)) : {S.U64{ah, al} == S.U64{_, bl} : S.U64}
  %Lm.U32.eq_of(al, bl, u32_is_eq_of_cmp(al, bl, e2)) : {S.U64{ah, al} == S.U64{ah, _} : S.U64}
  {==}

def u64_eq_of(+a: S.U64, +b: S.U64, h: {S.U64.is_eq(a, b) == True{} : Bool}) -> {a == b : S.U64}:
  match a b:
    case S.U64{+ah, +al} S.U64{+bh, +bl}:
      u64_eq_of.pair(ah, al, bh, bl,
        cmp_lo_eq(U32.cmp(ah, bh), U32.cmp(al, bl), Lm.Cmp.is_eq_true(S.U64.cmp(S.U64{ah, al}, S.U64{bh, bl}), h)))

def u64_lt_refl(+a: S.U64) -> {S.U64.is_lt(a, a) == False{} : Bool}:
  %Lm.U64.cmp_refl(a) : {Cmp.is_lt(_) == False{} : Bool}
  {==}

# Equal values: neither is less than the other.
def eq_not_lt(+a: S.U64, +b: S.U64, h: {S.U64.is_eq(a, b) == True{} : Bool})
  -> {S.U64.is_lt(a, b) == False{} : Bool} & {S.U64.is_lt(b, a) == False{} : Bool}:
  %u64_eq_of(a, b, h) : {S.U64.is_lt(a, _) == False{} : Bool} & {S.U64.is_lt(_, a) == False{} : Bool}
  (u64_lt_refl(a), u64_lt_refl(a))

# Blocks

def block_core(b: Bool, ri: Bool)
  -> {Bool.and(b, Bool.not(ri)) == Scan.is_clash(Bool.pick(Slash.Scan, b, Slash.Scan.same_or(ri, Slash.DoubleBlock{}), Slash.Clear{})) : Bool}:
  match b ri:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def block_one_clash(+slot: S.U64, +root: S.B32, x: Slash.BlockRec)
  -> {Spec.blocks_clash(Slash.BlockRec{slot, Some{root}}, x) == Scan.is_clash(Slash.Block.scan.one(slot, root, x)) : Bool}:
  match x:
    case Slash.BlockRec{+rs, +rr}:
      %differ_root(root, rr)
        : {Bool.and(S.U64.is_eq(slot, rs), _) == Scan.is_clash(Slash.Block.scan.one(slot, root, Slash.BlockRec{rs, rr})) : Bool}
      block_core(S.U64.is_eq(slot, rs), Slash.Root.is(root, rr))

def block_scan_clash(xs: List<&2, Slash.BlockRec>, +slot: S.U64, +root: S.B32)
  -> {Spec.block_clashes_any(Slash.BlockRec{slot, Some{root}}, xs) == Scan.is_clash(Slash.Block.scan(xs, slot, root)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %join_clash(Slash.Block.scan.one(slot, root, x), Slash.Block.scan(rest, slot, root))
        : {Spec.block_clashes_any(Slash.BlockRec{slot, Some{root}}, Con{x, rest}) == _ : Bool}
      %block_one_clash(slot, root, x)
        : {Bool.or(Spec.blocks_clash(Slash.BlockRec{slot, Some{root}}, x), Spec.block_clashes_any(Slash.BlockRec{slot, Some{root}}, rest))
           == Bool.or(_, Scan.is_clash(Slash.Block.scan(rest, slot, root))) : Bool}
      %block_scan_clash(rest, slot, root)
        : {Bool.or(Spec.blocks_clash(Slash.BlockRec{slot, Some{root}}, x), Spec.block_clashes_any(Slash.BlockRec{slot, Some{root}}, rest))
           == Bool.or(Spec.blocks_clash(Slash.BlockRec{slot, Some{root}}, x), _) : Bool}
      {==}

# Attestations

def or_pick(x: Bool, y: Bool)
  -> {Bool.or(x, y) == Scan.is_clash(Bool.pick(Slash.Scan, y, Slash.Clash{Slash.Surrounded{}},
       Bool.pick(Slash.Scan, x, Slash.Clash{Slash.Surrounds{}}, Slash.Clear{}))) : Bool}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def att_core.fin(ri: Bool, bs: Bool, A: Bool, C: Bool)
  -> {Bool.or(Bool.or(Bool.not(ri), Bool.and(C, False{})), Bool.and(A, False{})) == Scan.is_clash(Slash.Att.same_target(ri, bs)) : Bool}:
  match ri bs A C:
    case True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{}:
      {==}

def att_core.t(ri: Bool, bs: Bool, A: Bool, -B: Bool, C: Bool, -D: Bool,
  pr: {B == False{} : Bool} & {D == False{} : Bool})
  -> {Bool.or(Bool.or(Bool.not(ri), Bool.and(C, D)), Bool.and(A, B)) == Scan.is_clash(Slash.Att.same_target(ri, bs)) : Bool}:
  (eB, eD) = pr
  %Equal.sym(Bool, B, False{}, eB) : {Bool.or(Bool.or(Bool.not(ri), Bool.and(C, D)), Bool.and(A, _)) == Scan.is_clash(Slash.Att.same_target(ri, bs)) : Bool}
  %Equal.sym(Bool, D, False{}, eD) : {Bool.or(Bool.or(Bool.not(ri), Bool.and(C, _)), Bool.and(A, False{})) == Scan.is_clash(Slash.Att.same_target(ri, bs)) : Bool}
  att_core.fin(ri, bs, A, C)

# The scan of one record against the spec, with every comparison as a
# variable. When the targets are equal (bt), neither B nor D holds.
def att_core(bt: Bool, ri: Bool, bs: Bool, A: Bool, B: Bool, C: Bool, D: Bool,
  hb: {bt == True{} : Bool} -> {B == False{} : Bool} & {D == False{} : Bool})
  -> {Bool.or(Bool.or(Bool.and(bt, Bool.not(ri)), Bool.and(C, D)), Bool.and(A, B))
      == Scan.is_clash(Bool.pick(Slash.Scan, bt, Slash.Att.same_target(ri, bs),
           Bool.pick(Slash.Scan, Bool.and(A, B), Slash.Clash{Slash.Surrounded{}},
             Bool.pick(Slash.Scan, Bool.and(C, D), Slash.Clash{Slash.Surrounds{}}, Slash.Clear{})))) : Bool}:
  match bt:
    case False{}:
      or_pick(Bool.and(C, D), Bool.and(A, B))
    case True{}:
      att_core.t(ri, bs, A, B, C, D, hb({==}))

def att_one_clash(+s: S.U64, +t: S.U64, +root: S.B32, x: Slash.AttRec)
  -> {Spec.atts_clash(Slash.AttRec{s, t, Some{root}}, x) == Scan.is_clash(Slash.Att.scan.one(s, t, root, x)) : Bool}:
  match x:
    case Slash.AttRec{+rs, +rt, +rr}:
      %differ_root(root, rr)
        : {Bool.or(Bool.or(Bool.and(S.U64.is_eq(t, rt), _), Bool.and(S.U64.is_lt(s, rs), S.U64.is_lt(rt, t))),
             Bool.and(S.U64.is_lt(rs, s), S.U64.is_lt(t, rt)))
           == Scan.is_clash(Slash.Att.scan.one(s, t, root, Slash.AttRec{rs, rt, rr})) : Bool}
      att_core(S.U64.is_eq(t, rt), Slash.Root.is(root, rr), S.U64.is_eq(s, rs), S.U64.is_lt(rs, s), S.U64.is_lt(t, rt),
        S.U64.is_lt(s, rs), S.U64.is_lt(rt, t), eq_not_lt(t, rt))

def att_scan_clash(xs: List<&2, Slash.AttRec>, +s: S.U64, +t: S.U64, +root: S.B32)
  -> {Spec.att_clashes_any(Slash.AttRec{s, t, Some{root}}, xs) == Scan.is_clash(Slash.Att.scan(xs, s, t, root)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %join_clash(Slash.Att.scan.one(s, t, root, x), Slash.Att.scan(rest, s, t, root))
        : {Spec.att_clashes_any(Slash.AttRec{s, t, Some{root}}, Con{x, rest}) == _ : Bool}
      %att_one_clash(s, t, root, x)
        : {Bool.or(Spec.atts_clash(Slash.AttRec{s, t, Some{root}}, x), Spec.att_clashes_any(Slash.AttRec{s, t, Some{root}}, rest))
           == Bool.or(_, Scan.is_clash(Slash.Att.scan(rest, s, t, root))) : Bool}
      %att_scan_clash(rest, s, t, root)
        : {Bool.or(Spec.atts_clash(Slash.AttRec{s, t, Some{root}}, x), Spec.att_clashes_any(Slash.AttRec{s, t, Some{root}}, rest))
           == Bool.or(Spec.atts_clash(Slash.AttRec{s, t, Some{root}}, x), _) : Bool}
      {==}

# x and not(x) cannot both be True.
def contra_true_not(x: Bool, e1: {x == True{} : Bool}, e2: {Bool.not(x) == True{} : Bool}) -> Empty:
  match x:
    case True{}:
      Lm.Bool.ft(e2)
    case False{}:
      Lm.Bool.ft(e1)

def demorgan(a: Bool, b: Bool) -> {Bool.not(Bool.or(a, b)) == Bool.and(Bool.not(a), Bool.not(b)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def above_below(+slot: S.U64, bm: Maybe<&2, S.U64>)
  -> {Bool.not(Slash.Block.below(slot, bm)) == Spec.block_above_mark(slot, bm) : Bool}:
  match bm:
    case None{}:
      {==}
    case Some{w}:
      {==}

def att_above_below(+s: S.U64, +t: S.U64, am: Maybe<&2, Slash.AttMark>)
  -> {Bool.not(Slash.Att.below(s, t, am)) == Spec.att_above_mark(s, t, am) : Bool}:
  match am:
    case None{}:
      {==}
    case Some{w}:
      match w:
        case Slash.AttMark{+ms, +mt}:
          demorgan(S.U64.is_lt(s, ms), S.U64.is_lt(t, mt))

# Liveness: blocks

def block_live.fin(sc: Slash.Scan, +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>,
  +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +slot: S.U64, +root: S.B32,
  e: {sc == Slash.Block.scan(bs, slot, root) : Slash.Scan},
  hc: {Bool.not(Spec.block_clashes_any(Slash.BlockRec{slot, Some{root}}, bs)) == True{} : Bool})
  -> {Spec.signs(Slash.Block.finish(sc, Slash.KeyState{bs, as, bm, am}, slot, root)) == True{} : Bool}:
  match sc:
    case Slash.Clash{r}:
      Empty.absurd({Spec.signs(Slash.Reject{r}) == True{} : Bool},
        contra_true_not(Spec.block_clashes_any(Slash.BlockRec{slot, Some{root}}, bs),
          Equal.trans(Bool, Spec.block_clashes_any(Slash.BlockRec{slot, Some{root}}, bs),
            Scan.is_clash(Slash.Block.scan(bs, slot, root)), True{},
            block_scan_clash(bs, slot, root),
            Equal.cong(Slash.Scan, Bool, Scan.is_clash, Slash.Block.scan(bs, slot, root), Slash.Clash{r},
              Equal.sym(Slash.Scan, Slash.Clash{r}, Slash.Block.scan(bs, slot, root), e))),
          hc))
    case Slash.Again{}:
      {==}
    case Slash.Clear{}:
      {==}

def block_live.go(below: Bool, hb: {Bool.not(below) == True{} : Bool}, +bs: List<&2, Slash.BlockRec>,
  +as: List<&2, Slash.AttRec>, +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +slot: S.U64, +root: S.B32,
  hc: {Bool.not(Spec.block_clashes_any(Slash.BlockRec{slot, Some{root}}, bs)) == True{} : Bool})
  -> {Spec.signs(Slash.Block.decide.go(below, Slash.KeyState{bs, as, bm, am}, slot, root)) == True{} : Bool}:
  match below:
    case True{}:
      Empty.absurd({Spec.signs(Slash.Reject{Slash.BelowWatermark{}}) == True{} : Bool}, Lm.Bool.ft(hb))
    case False{}:
      block_live.fin(Slash.Block.scan(bs, slot, root), bs, as, bm, am, slot, root, {==}, hc)

def block_live.pair(+bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>, +bm: Maybe<&2, S.U64>,
  +am: Maybe<&2, Slash.AttMark>, +slot: S.U64, +root: S.B32,
  pr: {Spec.block_above_mark(slot, bm) == True{} : Bool}
      & {Bool.not(Spec.block_clashes_any(Slash.BlockRec{slot, Some{root}}, bs)) == True{} : Bool})
  -> {Spec.signs(Slash.Block.decide(Slash.KeyState{bs, as, bm, am}, slot, root)) == True{} : Bool}:
  (h1, h2) = pr
  block_live.go(Slash.Block.below(slot, bm),
    Equal.trans(Bool, Bool.not(Slash.Block.below(slot, bm)), Spec.block_above_mark(slot, bm), True{}, above_below(slot, bm), h1),
    bs, as, bm, am, slot, root, h2)

def Laws.block_signs_when_clear(ks, slot, root, h):
  match ks:
    case Slash.KeyState{+bs, +as, +bm, +am}:
      block_live.pair(bs, as, bm, am, slot, root,
        Lm.Bool.and_true(Spec.block_above_mark(slot, bm),
          Bool.not(Spec.block_clashes_any(Slash.BlockRec{slot, Some{root}}, bs)), h))

# Liveness: attestations

def att_live.fin(sc: Slash.Scan, +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>,
  +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +s: S.U64, +t: S.U64, +root: S.B32,
  e: {sc == Slash.Att.scan(as, s, t, root) : Slash.Scan},
  hc: {Bool.not(Spec.att_clashes_any(Slash.AttRec{s, t, Some{root}}, as)) == True{} : Bool})
  -> {Spec.signs(Slash.Att.finish(sc, Slash.KeyState{bs, as, bm, am}, s, t, root)) == True{} : Bool}:
  match sc:
    case Slash.Clash{r}:
      Empty.absurd({Spec.signs(Slash.Reject{r}) == True{} : Bool},
        contra_true_not(Spec.att_clashes_any(Slash.AttRec{s, t, Some{root}}, as),
          Equal.trans(Bool, Spec.att_clashes_any(Slash.AttRec{s, t, Some{root}}, as),
            Scan.is_clash(Slash.Att.scan(as, s, t, root)), True{},
            att_scan_clash(as, s, t, root),
            Equal.cong(Slash.Scan, Bool, Scan.is_clash, Slash.Att.scan(as, s, t, root), Slash.Clash{r},
              Equal.sym(Slash.Scan, Slash.Clash{r}, Slash.Att.scan(as, s, t, root), e))),
          hc))
    case Slash.Again{}:
      {==}
    case Slash.Clear{}:
      {==}

def att_live.scan(c: Bool, hb: {Bool.not(c) == True{} : Bool}, +bs: List<&2, Slash.BlockRec>,
  +as: List<&2, Slash.AttRec>, +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +s: S.U64, +t: S.U64, +root: S.B32,
  hc: {Bool.not(Spec.att_clashes_any(Slash.AttRec{s, t, Some{root}}, as)) == True{} : Bool})
  -> {Spec.signs(Slash.Att.decide.scan(c, Slash.KeyState{bs, as, bm, am}, s, t, root)) == True{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({Spec.signs(Slash.Reject{Slash.BelowWatermark{}}) == True{} : Bool}, Lm.Bool.ft(hb))
    case False{}:
      att_live.fin(Slash.Att.scan(as, s, t, root), bs, as, bm, am, s, t, root, {==}, hc)

def att_live.go(o: Bool, ho: {o == True{} : Bool}, +bs: List<&2, Slash.BlockRec>,
  +as: List<&2, Slash.AttRec>, +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +s: S.U64, +t: S.U64, +root: S.B32,
  hb: {Bool.not(Slash.Att.below(s, t, am)) == True{} : Bool},
  hc: {Bool.not(Spec.att_clashes_any(Slash.AttRec{s, t, Some{root}}, as)) == True{} : Bool})
  -> {Spec.signs(Slash.Att.decide.go(o, Slash.KeyState{bs, as, bm, am}, s, t, root)) == True{} : Bool}:
  match o:
    case False{}:
      Empty.absurd({Spec.signs(Slash.Reject{Slash.SourceAfterTarget{}}) == True{} : Bool}, Lm.Bool.ft(ho))
    case True{}:
      att_live.scan(Slash.Att.below(s, t, am), hb, bs, as, bm, am, s, t, root, hc)

def att_live.inner(+bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>, +bm: Maybe<&2, S.U64>,
  +am: Maybe<&2, Slash.AttMark>, +s: S.U64, +t: S.U64, +root: S.B32,
  pr: {Bool.not(Spec.lt(t, s)) == True{} : Bool} & {Spec.att_above_mark(s, t, am) == True{} : Bool},
  hc: {Bool.not(Spec.att_clashes_any(Slash.AttRec{s, t, Some{root}}, as)) == True{} : Bool})
  -> {Spec.signs(Slash.Att.decide(Slash.KeyState{bs, as, bm, am}, s, t, root)) == True{} : Bool}:
  (ho, ha) = pr
  att_live.go(Bool.not(S.U64.is_lt(t, s)), ho, bs, as, bm, am, s, t, root,
    Equal.trans(Bool, Bool.not(Slash.Att.below(s, t, am)), Spec.att_above_mark(s, t, am), True{}, att_above_below(s, t, am), ha),
    hc)

def att_live.pair(+bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>, +bm: Maybe<&2, S.U64>,
  +am: Maybe<&2, Slash.AttMark>, +s: S.U64, +t: S.U64, +root: S.B32,
  pr: {Bool.and(Bool.not(Spec.lt(t, s)), Spec.att_above_mark(s, t, am)) == True{} : Bool}
      & {Bool.not(Spec.att_clashes_any(Slash.AttRec{s, t, Some{root}}, as)) == True{} : Bool})
  -> {Spec.signs(Slash.Att.decide(Slash.KeyState{bs, as, bm, am}, s, t, root)) == True{} : Bool}:
  (h12, h3) = pr
  att_live.inner(bs, as, bm, am, s, t, root,
    Lm.Bool.and_true(Bool.not(Spec.lt(t, s)), Spec.att_above_mark(s, t, am), h12), h3)

def Laws.att_signs_when_clear(ks, source, target, root, h):
  match ks:
    case Slash.KeyState{+bs, +as, +bm, +am}:
      att_live.pair(bs, as, bm, am, source, target, root,
        Lm.Bool.and_true(Bool.and(Bool.not(Spec.lt(target, source)), Spec.att_above_mark(source, target, am)),
          Bool.not(Spec.att_clashes_any(Slash.AttRec{source, target, Some{root}}, as)), h))

# Safety: what a Record decision knows about the new record.

def BlockClear(d: Slash.Decision, +bs: List<&2, Slash.BlockRec>, +r: Slash.BlockRec) -> Type:
  match d:
    case Slash.Reject{x}:
      Unit
    case Slash.Repeat{}:
      Unit
    case Slash.Record{st}:
      {Spec.block_clashes_any(r, bs) == False{} : Bool}

def AttClear(d: Slash.Decision, +as: List<&2, Slash.AttRec>, +r: Slash.AttRec) -> Type:
  match d:
    case Slash.Reject{x}:
      Unit
    case Slash.Repeat{}:
      Unit
    case Slash.Record{st}:
      {Spec.att_ordered(r) == True{} : Bool} & {Spec.att_clashes_any(r, as) == False{} : Bool}

def block_clear.fin(sc: Slash.Scan, +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>,
  +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +slot: S.U64, +root: S.B32,
  e: {sc == Slash.Block.scan(bs, slot, root) : Slash.Scan})
  -> BlockClear(Slash.Block.finish(sc, Slash.KeyState{bs, as, bm, am}, slot, root), bs, Slash.BlockRec{slot, Some{root}}):
  match sc:
    case Slash.Clash{r}:
      Unit{}
    case Slash.Again{}:
      Unit{}
    case Slash.Clear{}:
      Equal.trans(Bool, Spec.block_clashes_any(Slash.BlockRec{slot, Some{root}}, bs),
        Scan.is_clash(Slash.Block.scan(bs, slot, root)), False{},
        block_scan_clash(bs, slot, root),
        Equal.cong(Slash.Scan, Bool, Scan.is_clash, Slash.Block.scan(bs, slot, root), Slash.Clear{},
          Equal.sym(Slash.Scan, Slash.Clear{}, Slash.Block.scan(bs, slot, root), e)))

def block_clear.go(below: Bool, +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>,
  +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +slot: S.U64, +root: S.B32)
  -> BlockClear(Slash.Block.decide.go(below, Slash.KeyState{bs, as, bm, am}, slot, root), bs, Slash.BlockRec{slot, Some{root}}):
  match below:
    case True{}:
      Unit{}
    case False{}:
      block_clear.fin(Slash.Block.scan(bs, slot, root), bs, as, bm, am, slot, root, {==})

def att_clear.fin(sc: Slash.Scan, +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>,
  +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +s: S.U64, +t: S.U64, +root: S.B32,
  e: {sc == Slash.Att.scan(as, s, t, root) : Slash.Scan}, +ho: {Bool.not(S.U64.is_lt(t, s)) == True{} : Bool})
  -> AttClear(Slash.Att.finish(sc, Slash.KeyState{bs, as, bm, am}, s, t, root), as, Slash.AttRec{s, t, Some{root}}):
  match sc:
    case Slash.Clash{r}:
      Unit{}
    case Slash.Again{}:
      Unit{}
    case Slash.Clear{}:
      (ho, Equal.trans(Bool, Spec.att_clashes_any(Slash.AttRec{s, t, Some{root}}, as),
        Scan.is_clash(Slash.Att.scan(as, s, t, root)), False{},
        att_scan_clash(as, s, t, root),
        Equal.cong(Slash.Scan, Bool, Scan.is_clash, Slash.Att.scan(as, s, t, root), Slash.Clear{},
          Equal.sym(Slash.Scan, Slash.Clear{}, Slash.Att.scan(as, s, t, root), e))))

def att_clear.scan(c: Bool, +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>,
  +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +s: S.U64, +t: S.U64, +root: S.B32,
  +ho: {Bool.not(S.U64.is_lt(t, s)) == True{} : Bool})
  -> AttClear(Slash.Att.decide.scan(c, Slash.KeyState{bs, as, bm, am}, s, t, root), as, Slash.AttRec{s, t, Some{root}}):
  match c:
    case True{}:
      Unit{}
    case False{}:
      att_clear.fin(Slash.Att.scan(as, s, t, root), bs, as, bm, am, s, t, root, {==}, ho)

def att_clear.go(o: Bool, +s: S.U64, +t: S.U64, eo: {o == Bool.not(S.U64.is_lt(t, s)) : Bool}, +bs: List<&2, Slash.BlockRec>,
  +as: List<&2, Slash.AttRec>, +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +root: S.B32)
  -> AttClear(Slash.Att.decide.go(o, Slash.KeyState{bs, as, bm, am}, s, t, root), as, Slash.AttRec{s, t, Some{root}}):
  match o:
    case False{}:
      Unit{}
    case True{}:
      att_clear.scan(Slash.Att.below(s, t, am), bs, as, bm, am, s, t, root,
        Equal.sym(Bool, True{}, Bool.not(S.U64.is_lt(t, s)), eo))

def safe_add_block(+bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>, +bm: Maybe<&2, S.U64>,
  +am: Maybe<&2, Slash.AttMark>, +r: Slash.BlockRec, hc: {Spec.block_clashes_any(r, bs) == False{} : Bool},
  h: {Spec.safe(Slash.KeyState{bs, as, bm, am}) == True{} : Bool})
  -> {Spec.safe(St.KeyState.add_block(Slash.KeyState{bs, as, bm, am}, r)) == True{} : Bool}:
  %Equal.sym(Bool, Spec.block_clashes_any(r, bs), False{}, hc)
    : {Bool.and(Bool.and(Bool.not(_), Spec.blocks_safe(bs)), Spec.atts_safe(as)) == True{} : Bool}
  h

def safe_add_att.pair(+bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>, +bm: Maybe<&2, S.U64>,
  +am: Maybe<&2, Slash.AttMark>, +r: Slash.AttRec,
  pr: {Spec.att_ordered(r) == True{} : Bool} & {Spec.att_clashes_any(r, as) == False{} : Bool},
  h: {Spec.safe(Slash.KeyState{bs, as, bm, am}) == True{} : Bool})
  -> {Spec.safe(St.KeyState.add_att(Slash.KeyState{bs, as, bm, am}, r)) == True{} : Bool}:
  (ho, hc) = pr
  %Equal.sym(Bool, Spec.att_ordered(r), True{}, ho)
    : {Bool.and(Spec.blocks_safe(bs), Bool.and(Bool.and(_, Bool.not(Spec.att_clashes_any(r, as))), Spec.atts_safe(as))) == True{} : Bool}
  %Equal.sym(Bool, Spec.att_clashes_any(r, as), False{}, hc)
    : {Bool.and(Spec.blocks_safe(bs), Bool.and(Bool.and(True{}, Bool.not(_)), Spec.atts_safe(as))) == True{} : Bool}
  h

def safe_after_block(D: Slash.Decision, +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>,
  +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +r: Slash.BlockRec,
  shape: RecShape(D, St.KeyState.add_block(Slash.KeyState{bs, as, bm, am}, r)),
  clear: BlockClear(D, bs, r), h: {Spec.safe(Slash.KeyState{bs, as, bm, am}) == True{} : Bool})
  -> {Spec.safe(Slash.KeyState.after(Slash.KeyState{bs, as, bm, am}, D)) == True{} : Bool}:
  match D:
    case Slash.Reject{x}:
      h
    case Slash.Repeat{}:
      h
    case Slash.Record{+st}:
      %Equal.sym(Slash.KeyState, st, St.KeyState.add_block(Slash.KeyState{bs, as, bm, am}, r), shape)
        : {Spec.safe(_) == True{} : Bool}
      safe_add_block(bs, as, bm, am, r, clear, h)

def safe_after_att(D: Slash.Decision, +bs: List<&2, Slash.BlockRec>, +as: List<&2, Slash.AttRec>,
  +bm: Maybe<&2, S.U64>, +am: Maybe<&2, Slash.AttMark>, +r: Slash.AttRec,
  shape: RecShape(D, St.KeyState.add_att(Slash.KeyState{bs, as, bm, am}, r)),
  clear: AttClear(D, as, r), h: {Spec.safe(Slash.KeyState{bs, as, bm, am}) == True{} : Bool})
  -> {Spec.safe(Slash.KeyState.after(Slash.KeyState{bs, as, bm, am}, D)) == True{} : Bool}:
  match D:
    case Slash.Reject{x}:
      h
    case Slash.Repeat{}:
      h
    case Slash.Record{+st}:
      %Equal.sym(Slash.KeyState, st, St.KeyState.add_att(Slash.KeyState{bs, as, bm, am}, r), shape)
        : {Spec.safe(_) == True{} : Bool}
      safe_add_att.pair(bs, as, bm, am, r, clear, h)

def Laws.block_keeps_safe(ks, slot, root, h):
  match ks:
    case Slash.KeyState{+bs, +as, +bm, +am}:
      safe_after_block(Slash.Block.decide(Slash.KeyState{bs, as, bm, am}, slot, root), bs, as, bm, am,
        Slash.BlockRec{slot, Some{root}}, block_shape(Slash.KeyState{bs, as, bm, am}, slot, root),
        block_clear.go(Slash.Block.below(slot, bm), bs, as, bm, am, slot, root), h)

def Laws.att_keeps_safe(ks, source, target, root, h):
  match ks:
    case Slash.KeyState{+bs, +as, +bm, +am}:
      safe_after_att(Slash.Att.decide(Slash.KeyState{bs, as, bm, am}, source, target, root), bs, as, bm, am,
        Slash.AttRec{source, target, Some{root}}, att_shape(Slash.KeyState{bs, as, bm, am}, source, target, root),
        att_clear.go(Bool.not(S.U64.is_lt(target, source)), source, target, {==}, bs, as, bm, am, root), h)
