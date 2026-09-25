# The slashing store: the state of all keys, the events of the slashing log,
# and the decision for one request.
#
# The log is the source of truth. A decision does not build the next state
# itself. It returns the events to append, and the next state is apply_all
# of those events. Replay at start runs the same apply_all over the events in
# the log file, so the state after a restart is the state before it.
#
# docs/SPEC.md section 8 gives the rules and section 8.7 the log format.
import Base
import ./ssz.bend as S
import ./slashing.bend as Slash
import ./request.bend as R

# State
# =====

type Entry is Data:
  Entry{key: S.Pubkey, state: Slash.KeyState}

# gvr is the genesis validators root of the database. The first request or
# import sets it.
type Store is Data:
  Store{gvr: Maybe<&2, S.B32>, entries: List<&2, Entry>}

def Store.empty() -> Store:
  Store{None{}, []}

# The state of one key. A key with no records has the empty state.
def Store.get(es: List<&2, Entry>, +key: S.Pubkey) -> Slash.KeyState:
  match es:
    case Nil{}:
      Slash.KeyState.empty()
    case Con{e, rest}:
      match e:
        case Entry{k, st}:
          Bool.pick(Slash.KeyState, S.Pubkey.is_eq(key, k), st, Store.get(rest, key))

# Replaces the state of one key, or adds the key at the end.
def Store.put(es: List<&2, Entry>, +key: S.Pubkey, +st: Slash.KeyState) -> List<&2, Entry>:
  match es:
    case Nil{}:
      [Entry{key, st}]
    case Con{e, +rest}:
      match e:
        case Entry{+k, +old}:
          Bool.pick(List<&2, Entry>, S.Pubkey.is_eq(key, k), Con{Entry{k, st}, rest},
            Con{Entry{k, old}, Store.put(rest, key, st)})

# Events
# ======

type LogEvent is Data:
  EGvr{root: S.B32}
  EBlock{key: S.Pubkey, rec: Slash.BlockRec}
  EAtt{key: S.Pubkey, rec: Slash.AttRec}
  EBlockMark{key: S.Pubkey, slot: S.U64}
  EAttMark{key: S.Pubkey, mark: Slash.AttMark}

def KeyState.add_block(ks: Slash.KeyState, r: Slash.BlockRec) -> Slash.KeyState:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      Slash.KeyState{Con{r, bs}, as, bm, am}

def KeyState.add_att(ks: Slash.KeyState, r: Slash.AttRec) -> Slash.KeyState:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      Slash.KeyState{bs, Con{r, as}, bm, am}

def KeyState.set_block_mark(ks: Slash.KeyState, m: S.U64) -> Slash.KeyState:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      Slash.KeyState{bs, as, Some{m}, am}

def KeyState.set_att_mark(ks: Slash.KeyState, m: Slash.AttMark) -> Slash.KeyState:
  match ks:
    case Slash.KeyState{bs, as, bm, am}:
      Slash.KeyState{bs, as, bm, Some{m}}

def Store.apply(s: Store, e: LogEvent) -> Store:
  match s:
    case Store{gvr, +es}:
      match e:
        case EGvr{g}:
          Store{Some{g}, es}
        case EBlock{+k, r}:
          Store{gvr, Store.put(es, k, KeyState.add_block(Store.get(es, k), r))}
        case EAtt{+k, r}:
          Store{gvr, Store.put(es, k, KeyState.add_att(Store.get(es, k), r))}
        case EBlockMark{+k, m}:
          Store{gvr, Store.put(es, k, KeyState.set_block_mark(Store.get(es, k), m))}
        case EAttMark{+k, m}:
          Store{gvr, Store.put(es, k, KeyState.set_att_mark(Store.get(es, k), m))}

def Store.apply_all(es: List<&2, LogEvent>, s: Store) -> Store:
  match es:
    case Nil{}:
      s
    case Con{e, rest}:
      Store.apply_all(rest, Store.apply(s, e))

# The state after a restart: every logged event, in order, from empty.
def Store.replay(es: List<&2, LogEvent>) -> Store:
  Store.apply_all(es, Store.empty())

# Decisions
# =========

# Refuse: do not sign; status is the HTTP status. Sign: append events, then
# sign. The events can be empty: a repeat, or a message type without
# slashing protection.
type Outcome is Data:
  Refuse{status: U32, reason: String}
  Sign{events: List<&2, LogEvent>}

def Reason.show(r: Slash.Reason) -> String:
  match r:
    case Slash.BelowWatermark{}:
      "below the low watermark"
    case Slash.DoubleBlock{}:
      "double block proposal"
    case Slash.SourceAfterTarget{}:
      "source epoch after target epoch"
    case Slash.DoubleVote{}:
      "double vote"
    case Slash.Surrounded{}:
      "surrounded vote"
    case Slash.Surrounds{}:
      "surrounding vote"

def Outcome.of(pre: List<&2, LogEvent>, d: Slash.Decision, e: LogEvent) -> Outcome:
  match d:
    case Slash.Reject{r}:
      Refuse{412, Reason.show(r)}
    case Slash.Repeat{}:
      Sign{pre}
    case Slash.Record{st}:
      Sign{List.append(&2, LogEvent, pre, [e])}

def Store.decide.msg(pre: List<&2, LogEvent>, +ks: Slash.KeyState, +key: S.Pubkey, msg: R.Msg, +root: S.B32) -> Outcome:
  match msg:
    case R.MAttestation{a}:
      match a:
        case S.AttestationData{slot, index, bbr, src, tgt}:
          match src tgt:
            case S.Checkpoint{+se, sr} S.Checkpoint{+te, tr}:
              Outcome.of(pre, Slash.Att.decide(ks, se, te, root), EAtt{key, Slash.AttRec{se, te, Some{root}}})
    case R.MBlock{h}:
      match h:
        case S.BeaconBlockHeader{+slot, pi, pr, sr, br}:
          Outcome.of(pre, Slash.Block.decide(ks, slot, root), EBlock{key, Slash.BlockRec{slot, Some{root}}})
    case R.MRandao{e}:
      Sign{pre}
    case R.MAggSlot{s}:
      Sign{pre}
    case R.MAggregate{a}:
      Sign{pre}
    case R.MSyncMsg{s, r}:
      Sign{pre}
    case R.MSyncSel{d}:
      Sign{pre}
    case R.MContribution{c}:
      Sign{pre}
    case R.MExit{e, c, d}:
      Sign{pre}
    case R.MRegistration{r, g}:
      Sign{pre}

def Store.decide.gvr(+g: S.B32, have: Maybe<&2, S.B32>) -> Maybe<&2, List<&2, LogEvent>>:
  match have:
    case None{}:
      Some{[EGvr{g}]}
    case Some{x}:
      Bool.pick(Maybe<&2, List<&2, LogEvent>>, S.B32.is_eq(g, x), Some{[]}, None{})

def Store.decide.go(pre: Maybe<&2, List<&2, LogEvent>>, +es: List<&2, Entry>, +key: S.Pubkey, msg: R.Msg, +root: S.B32) -> Outcome:
  match pre:
    case None{}:
      Refuse{412, "genesis validators root does not match the database"}
    case Some{p}:
      Store.decide.msg(p, Store.get(es, key), key, msg, root)

# A validator registration has no genesis validators root, so the check
# does not apply to it, and it does not set the root of the database.
def Store.decide.pre(+msg: R.Msg, +g: S.B32, have: Maybe<&2, S.B32>) -> Maybe<&2, List<&2, LogEvent>>:
  match msg:
    case R.MRegistration{r, v}:
      Some{[]}
    case R.MAttestation{a}:
      Store.decide.gvr(g, have)
    case R.MBlock{h}:
      Store.decide.gvr(g, have)
    case R.MRandao{e}:
      Store.decide.gvr(g, have)
    case R.MAggSlot{x}:
      Store.decide.gvr(g, have)
    case R.MAggregate{a}:
      Store.decide.gvr(g, have)
    case R.MSyncMsg{x, r}:
      Store.decide.gvr(g, have)
    case R.MSyncSel{d}:
      Store.decide.gvr(g, have)
    case R.MContribution{c}:
      Store.decide.gvr(g, have)
    case R.MExit{e, c, d}:
      Store.decide.gvr(g, have)

# The decision for one request. root is the signing root that Bulkhead
# computed for it (Request.check).
def Store.decide(s: Store, +key: S.Pubkey, r: R.Request, +root: S.B32) -> Outcome:
  match s:
    case Store{gvr, +es}:
      match r:
        case R.Request{+msg, fork, g, claimed}:
          Store.decide.go(Store.decide.pre(msg, g, gvr), es, key, msg, root)

# The state after an outcome.
def Store.after(s: Store, o: Outcome) -> Store:
  match o:
    case Refuse{c, why}:
      s
    case Sign{es}:
      Store.apply_all(es, s)

# The log format
# ==============
#
#   G <gvr>
#   B <pubkey> <slot> <root|->
#   A <pubkey> <source> <target> <root|->
#   WB <pubkey> <slot>
#   WA <pubkey> <source> <target>
#
# Each line ends with a newline. "-" is an unknown root.

def Log.root(r: Maybe<&2, S.B32>) -> String:
  match r:
    case None{}:
      "-"
    case Some{x}:
      S.Hex.b32(x)

def LogEvent.show(e: LogEvent) -> String:
  match e:
    case EGvr{g}:
      "G " ++ S.Hex.b32(g)
    case EBlock{k, r}:
      match r:
        case Slash.BlockRec{slot, root}:
          "B " ++ S.Hex.pubkey(k) ++ " " ++ S.U64.show(slot) ++ " " ++ Log.root(root)
    case EAtt{k, r}:
      match r:
        case Slash.AttRec{src, tgt, root}:
          "A " ++ S.Hex.pubkey(k) ++ " " ++ S.U64.show(src) ++ " " ++ S.U64.show(tgt) ++ " " ++ Log.root(root)
    case EBlockMark{k, m}:
      "WB " ++ S.Hex.pubkey(k) ++ " " ++ S.U64.show(m)
    case EAttMark{k, m}:
      match m:
        case Slash.AttMark{src, tgt}:
          "WA " ++ S.Hex.pubkey(k) ++ " " ++ S.U64.show(src) ++ " " ++ S.U64.show(tgt)

# A string split at one separator character: the finished pieces in reverse
# order, and the current piece in reverse order.
type Split is Data:
  Split{done: List<&2, String>, cur: String}

def Split.step(+sep: U32, st: Split, c: Char) -> Split:
  match st:
    case Split{+done, +cur}:
      match c:
        case Chr{+x}:
          Bool.pick(Split, U32.is_eq(x, sep), Split{Con{String.reverse(cur), done}, ""},
            Split{done, SCon{Chr{x}, cur}})

def Split.go(s: String, +sep: U32, st: Split) -> Split:
  match s:
    case SNil{}:
      st
    case SCon{c, t}:
      Split.go(t, sep, Split.step(sep, st, c))

# Splits a line at single spaces. Two spaces give an empty word, which no
# reader accepts.
def Log.words.end(st: Split) -> List<&2, String>:
  match st:
    case Split{done, cur}:
      List.reverse(&2, String, Con{String.reverse(cur), done})

def Log.words(s: String) -> List<&2, String>:
  Log.words.end(Split.go(s, 32, Split{[], ""}))

def Log.read_root(+s: String) -> Maybe<&2, Maybe<&2, S.B32>>:
  Bool.pick(Maybe<&2, Maybe<&2, S.B32>>, String.eq(s, "-"), Some{None{}},
    Maybe.map(&2, S.B32, Maybe<&2, S.B32>, x => Some{x}, S.Hex.read_b32(s)))

def Log.read.g(ws: List<&2, String>) -> Maybe<&2, LogEvent>:
  match ws:
    case Con{g, rest}:
      match rest:
        case Nil{}:
          do Maybe<&2, LogEvent>:
            root : S.B32 <- S.Hex.read_b32(g)
            return EGvr{root}
        case Con{x, more}:
          None{}
    case Nil{}:
      None{}

def Log.read.b(ws: List<&2, String>) -> Maybe<&2, LogEvent>:
  match ws:
    case [k, slot, root]:
      do Maybe<&2, LogEvent>:
        key : S.Pubkey <- S.Hex.read_pubkey(k)
        s : S.U64 <- S.U64.read(slot)
        r : Maybe<&2, S.B32> <- Log.read_root(root)
        return EBlock{key, Slash.BlockRec{s, r}}
    case _:
      None{}

def Log.read.a(ws: List<&2, String>) -> Maybe<&2, LogEvent>:
  match ws:
    case [k, src, tgt, root]:
      do Maybe<&2, LogEvent>:
        key : S.Pubkey <- S.Hex.read_pubkey(k)
        s : S.U64 <- S.U64.read(src)
        t : S.U64 <- S.U64.read(tgt)
        r : Maybe<&2, S.B32> <- Log.read_root(root)
        return EAtt{key, Slash.AttRec{s, t, r}}
    case _:
      None{}

def Log.read.wb(ws: List<&2, String>) -> Maybe<&2, LogEvent>:
  match ws:
    case [k, slot]:
      do Maybe<&2, LogEvent>:
        key : S.Pubkey <- S.Hex.read_pubkey(k)
        s : S.U64 <- S.U64.read(slot)
        return EBlockMark{key, s}
    case _:
      None{}

def Log.read.wa(ws: List<&2, String>) -> Maybe<&2, LogEvent>:
  match ws:
    case [k, src, tgt]:
      do Maybe<&2, LogEvent>:
        key : S.Pubkey <- S.Hex.read_pubkey(k)
        s : S.U64 <- S.U64.read(src)
        t : S.U64 <- S.U64.read(tgt)
        return EAttMark{key, Slash.AttMark{s, t}}
    case _:
      None{}

def LogEvent.read.tag(+tag: String, +rest: List<&2, String>) -> Maybe<&2, LogEvent>:
  Bool.pick(Maybe<&2, LogEvent>, String.eq(tag, "G"), Log.read.g(rest),
  Bool.pick(Maybe<&2, LogEvent>, String.eq(tag, "B"), Log.read.b(rest),
  Bool.pick(Maybe<&2, LogEvent>, String.eq(tag, "A"), Log.read.a(rest),
  Bool.pick(Maybe<&2, LogEvent>, String.eq(tag, "WB"), Log.read.wb(rest),
  Bool.pick(Maybe<&2, LogEvent>, String.eq(tag, "WA"), Log.read.wa(rest),
  None{})))))

def LogEvent.read.words(ws: List<&2, String>) -> Maybe<&2, LogEvent>:
  match ws:
    case Nil{}:
      None{}
    case Con{tag, rest}:
      LogEvent.read.tag(tag, rest)

def LogEvent.read(line: String) -> Maybe<&2, LogEvent>:
  LogEvent.read.words(Log.words(line))

def Log.show(es: List<&2, LogEvent>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{e, rest}:
      LogEvent.show(e) ++ "\n" ++ Log.show(rest)

# Splits text into complete lines and the text after the last newline.
type Lines is Data:
  Lines{done: List<&2, String>, tail: String}

def Log.lines.end(st: Split) -> Lines:
  match st:
    case Split{done, cur}:
      Lines{List.reverse(&2, String, done), String.reverse(cur)}

def Log.lines(s: String) -> Lines:
  Log.lines.end(Split.go(s, 10, Split{[], ""}))

def Log.read_lines(ls: List<&2, String>) -> Maybe<&2, List<&2, LogEvent>>:
  match ls:
    case Nil{}:
      Some{[]}
    case Con{l, rest}:
      do Maybe<&2, List<&2, LogEvent>>:
        e : LogEvent <- LogEvent.read(l)
        es : List<&2, LogEvent> <- Log.read_lines(rest)
        return Con{e, es}

def Log.read.from_lines(ls: Lines) -> Maybe<&2, List<&2, LogEvent>>:
  match ls:
    case Lines{done, tail}:
      Log.read_lines(done)

# The events of a log file. The text after the last newline is a write that
# did not finish: its fsync never returned, so no signature went out for
# it, and the reader drops it. Any complete line that does not parse makes
# the whole file invalid.
def Log.read(text: String) -> Maybe<&2, List<&2, LogEvent>>:
  Log.read.from_lines(Log.lines(text))
