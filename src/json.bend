# A strict JSON parser for request bodies.
#
# Bend has no mutual recursion, so the parser is two folds. The lexer reads
# one character at a time and keeps its mode in a state value. The parser
# reads one token at a time and keeps the open arrays and objects on a stack.
# Each fold is one tail-recursive loop over its input, with a pure step
# function that does not recurse.
#
# The parser rejects duplicate object keys, trailing content, control
# characters inside strings, and nesting deeper than Json.max_depth.
import Base

type Json is Data:
  JNull{}
  JBool{value: Bool}
  JNum{text: String}
  JStr{text: String}
  JArr{items: List<&2, Json>}
  JObj{fields: List<&2, JField>}

type JField is Data:
  JField{key: String, value: Json}

def Json.max_depth() -> Nat:
  32n

# Lexer
# =====

type Tok is Data:
  TArrOpen{}
  TArrClose{}
  TObjOpen{}
  TObjClose{}
  TColon{}
  TComma{}
  TStr{text: String}
  TNum{text: String}
  TTrue{}
  TFalse{}
  TNull{}

# The lexer mode. buf holds the characters of the current string, number
# or word, in reverse order.
type LMode is Data:
  LNormal{}
  LStr{}
  LEsc{}
  LUni{left: Nat, code: U32}
  LNum{}
  LWord{}
  LFail{}

type LState is Data:
  LState{mode: LMode, buf: String, toks: List<&2, Tok>}

def Lex.code(c: Char) -> U32:
  match c:
    case Chr{x}:
      x

def Lex.in(+c: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_ge(c, lo), U32.is_le(c, hi))

def Lex.is_ws(+c: U32) -> Bool:
  U32.is_eq(c, 32) || U32.is_eq(c, 9) || U32.is_eq(c, 10) || U32.is_eq(c, 13)

def Lex.is_num(+c: U32) -> Bool:
  Lex.in(c, 48, 57) || U32.is_eq(c, 45) || U32.is_eq(c, 43) || U32.is_eq(c, 46)
    || U32.is_eq(c, 101) || U32.is_eq(c, 69)

def Lex.push(t: Tok, toks: List<&2, Tok>) -> LState:
  LState{LNormal{}, "", Con{t, toks}}

def Lex.word(+w: String) -> Maybe<&2, Tok>:
  Bool.pick(Maybe<&2, Tok>, String.eq(w, "true"), Some{TTrue{}},
  Bool.pick(Maybe<&2, Tok>, String.eq(w, "false"), Some{TFalse{}},
  Bool.pick(Maybe<&2, Tok>, String.eq(w, "null"), Some{TNull{}},
  None{})))

# Ends a word: true, false or null.
def Lex.end_word(w: Maybe<&2, Tok>, toks: List<&2, Tok>) -> LState:
  match w:
    case None{}:
      LState{LFail{}, "", []}
    case Some{t}:
      Lex.push(t, toks)

# One character in normal mode: between tokens.
def Lex.normal(+c: U32, +toks: List<&2, Tok>) -> LState:
  Bool.pick(LState, Lex.is_ws(c), LState{LNormal{}, "", toks},
  Bool.pick(LState, U32.is_eq(c, 91), Lex.push(TArrOpen{}, toks),
  Bool.pick(LState, U32.is_eq(c, 93), Lex.push(TArrClose{}, toks),
  Bool.pick(LState, U32.is_eq(c, 123), Lex.push(TObjOpen{}, toks),
  Bool.pick(LState, U32.is_eq(c, 125), Lex.push(TObjClose{}, toks),
  Bool.pick(LState, U32.is_eq(c, 58), Lex.push(TColon{}, toks),
  Bool.pick(LState, U32.is_eq(c, 44), Lex.push(TComma{}, toks),
  Bool.pick(LState, U32.is_eq(c, 34), LState{LStr{}, "", toks},
  Bool.pick(LState, Lex.in(c, 48, 57) || U32.is_eq(c, 45), LState{LNum{}, SCon{Chr{c}, SNil{}}, toks},
  Bool.pick(LState, Lex.in(c, 97, 122), LState{LWord{}, SCon{Chr{c}, SNil{}}, toks},
  LState{LFail{}, "", []}))))))))))

# The character that an escape stands for, or None.
def Lex.escape(+c: U32) -> Maybe<&2, U32>:
  Bool.pick(Maybe<&2, U32>, U32.is_eq(c, 34), Some{34},
  Bool.pick(Maybe<&2, U32>, U32.is_eq(c, 92), Some{92},
  Bool.pick(Maybe<&2, U32>, U32.is_eq(c, 47), Some{47},
  Bool.pick(Maybe<&2, U32>, U32.is_eq(c, 98), Some{8},
  Bool.pick(Maybe<&2, U32>, U32.is_eq(c, 102), Some{12},
  Bool.pick(Maybe<&2, U32>, U32.is_eq(c, 110), Some{10},
  Bool.pick(Maybe<&2, U32>, U32.is_eq(c, 114), Some{13},
  Bool.pick(Maybe<&2, U32>, U32.is_eq(c, 116), Some{9},
  None{}))))))))

def Lex.esc.to(is_u: Bool, e: Maybe<&2, U32>, buf: String, toks: List<&2, Tok>) -> LState:
  match is_u:
    case True{}:
      LState{LUni{4n, 0}, buf, toks}
    case False{}:
      match e:
        case None{}:
          LState{LFail{}, "", []}
        case Some{x}:
          LState{LStr{}, SCon{Chr{x}, buf}, toks}

def Lex.hex(+c: U32) -> Maybe<&2, U32>:
  Bool.pick(Maybe<&2, U32>, Lex.in(c, 48, 57), Some{(c - 48 : U32)},
  Bool.pick(Maybe<&2, U32>, Lex.in(c, 97, 102), Some{(c - 87 : U32)},
  Bool.pick(Maybe<&2, U32>, Lex.in(c, 65, 70), Some{(c - 55 : U32)},
  None{})))

def Lex.uni.done(left: Nat, +code: U32, buf: String, toks: List<&2, Tok>) -> LState:
  match left:
    case 0n:
      LState{LStr{}, SCon{Chr{code}, buf}, toks}
    case 1n+p:
      LState{LUni{1n+p, code}, buf, toks}

def Lex.uni(left: Nat, code: U32, d: Maybe<&2, U32>, buf: String, toks: List<&2, Tok>) -> LState:
  match left:
    case 0n:
      LState{LFail{}, "", []}
    case 1n+p:
      match d:
        case None{}:
          LState{LFail{}, "", []}
        case Some{x}:
          Lex.uni.done(p, ((code * 16 : U32) .|. x : U32), buf, toks)

def Lex.str.more(+c: U32, +buf: String, +toks: List<&2, Tok>) -> LState:
  Bool.pick(LState, U32.is_eq(c, 92), LState{LEsc{}, buf, toks},
  Bool.pick(LState, U32.is_lt(c, 32), LState{LFail{}, "", []},
  LState{LStr{}, SCon{Chr{c}, buf}, toks}))

# The closing quote reverses buf. A match, not Bool.pick, so that the
# reverse runs only at the end of the string: Bool.pick evaluates both of
# its values.
def Lex.str.at(quote: Bool, +c: U32, buf: String, toks: List<&2, Tok>) -> LState:
  match quote:
    case True{}:
      Lex.push(TStr{String.reverse(buf)}, toks)
    case False{}:
      Lex.str.more(c, buf, toks)

def Lex.str(+c: U32, buf: String, toks: List<&2, Tok>) -> LState:
  Lex.str.at(U32.is_eq(c, 34), c, buf, toks)

def Lex.num.at(more: Bool, +c: U32, buf: String, toks: List<&2, Tok>) -> LState:
  match more:
    case True{}:
      LState{LNum{}, SCon{Chr{c}, buf}, toks}
    case False{}:
      Lex.normal(c, Con{TNum{String.reverse(buf)}, toks})

def Lex.num(+c: U32, buf: String, toks: List<&2, Tok>) -> LState:
  Lex.num.at(Lex.is_num(c), c, buf, toks)

def Lex.end_word.then(+c: U32, w: Maybe<&2, Tok>, toks: List<&2, Tok>) -> LState:
  match w:
    case None{}:
      LState{LFail{}, "", []}
    case Some{t}:
      Lex.normal(c, Con{t, toks})

def Lex.letters.at(more: Bool, +c: U32, buf: String, toks: List<&2, Tok>) -> LState:
  match more:
    case True{}:
      LState{LWord{}, SCon{Chr{c}, buf}, toks}
    case False{}:
      Lex.end_word.then(c, Lex.word(String.reverse(buf)), toks)

def Lex.letters(+c: U32, buf: String, toks: List<&2, Tok>) -> LState:
  Lex.letters.at(Lex.in(c, 97, 122), c, buf, toks)

def Lex.step(st: LState, +c: Char) -> LState:
  match st:
    case LState{mode, buf, toks}:
      match mode:
        case LNormal{}:
          Lex.normal(Lex.code(c), toks)
        case LStr{}:
          Lex.str(Lex.code(c), buf, toks)
        case LEsc{}:
          Lex.esc.to(U32.is_eq(Lex.code(c), 117), Lex.escape(Lex.code(c)), buf, toks)
        case LUni{left, code}:
          Lex.uni(left, code, Lex.hex(Lex.code(c)), buf, toks)
        case LNum{}:
          Lex.num(Lex.code(c), buf, toks)
        case LWord{}:
          Lex.letters(Lex.code(c), buf, toks)
        case LFail{}:
          LState{LFail{}, "", []}

def Lex.go(s: String, st: LState) -> LState:
  match s:
    case SNil{}:
      st
    case SCon{c, t}:
      Lex.go(t, Lex.step(st, c))

def Lex.finish.word(w: Maybe<&2, Tok>, toks: List<&2, Tok>) -> Maybe<&2, List<&2, Tok>>:
  match w:
    case None{}:
      None{}
    case Some{t}:
      Some{List.reverse(&2, Tok, Con{t, toks})}

# The end of the input: close an open number or word.
def Lex.finish(st: LState) -> Maybe<&2, List<&2, Tok>>:
  match st:
    case LState{mode, buf, toks}:
      match mode:
        case LNormal{}:
          Some{List.reverse(&2, Tok, toks)}
        case LNum{}:
          Some{List.reverse(&2, Tok, Con{TNum{String.reverse(buf)}, toks})}
        case LWord{}:
          Lex.finish.word(Lex.word(String.reverse(buf)), toks)
        case LStr{}:
          None{}
        case LEsc{}:
          None{}
        case LUni{l, c}:
          None{}
        case LFail{}:
          None{}

def Lex.tokens(s: String) -> Maybe<&2, List<&2, Tok>>:
  Lex.finish(Lex.go(s, LState{LNormal{}, "", []}))

# Number grammar
# ==============
#
# -?(0|[1-9][0-9]*)(.[0-9]+)?([eE][+-]?[0-9]+)?, as a state machine.

type NState is Data:
  NStart{}
  NMinus{}
  NZero{}
  NInt{}
  NDot{}
  NFrac{}
  NExp{}
  NExpSign{}
  NExpDigits{}
  NBad{}

def Num.digit(+c: U32) -> Bool:
  Bool.and(U32.is_ge(c, 48), U32.is_le(c, 57))

def Num.step(st: NState, +c: U32) -> NState:
  match st:
    case NStart{}:
      Bool.pick(NState, U32.is_eq(c, 45), NMinus{},
      Bool.pick(NState, U32.is_eq(c, 48), NZero{},
      Bool.pick(NState, Num.digit(c), NInt{}, NBad{})))
    case NMinus{}:
      Bool.pick(NState, U32.is_eq(c, 48), NZero{},
      Bool.pick(NState, Num.digit(c), NInt{}, NBad{}))
    case NZero{}:
      Bool.pick(NState, U32.is_eq(c, 46), NDot{},
      Bool.pick(NState, U32.is_eq(c, 101) || U32.is_eq(c, 69), NExp{}, NBad{}))
    case NInt{}:
      Bool.pick(NState, Num.digit(c), NInt{},
      Bool.pick(NState, U32.is_eq(c, 46), NDot{},
      Bool.pick(NState, U32.is_eq(c, 101) || U32.is_eq(c, 69), NExp{}, NBad{})))
    case NDot{}:
      Bool.pick(NState, Num.digit(c), NFrac{}, NBad{})
    case NFrac{}:
      Bool.pick(NState, Num.digit(c), NFrac{},
      Bool.pick(NState, U32.is_eq(c, 101) || U32.is_eq(c, 69), NExp{}, NBad{}))
    case NExp{}:
      Bool.pick(NState, U32.is_eq(c, 43) || U32.is_eq(c, 45), NExpSign{},
      Bool.pick(NState, Num.digit(c), NExpDigits{}, NBad{}))
    case NExpSign{}:
      Bool.pick(NState, Num.digit(c), NExpDigits{}, NBad{})
    case NExpDigits{}:
      Bool.pick(NState, Num.digit(c), NExpDigits{}, NBad{})
    case NBad{}:
      NBad{}

def Num.go(s: String, st: NState) -> NState:
  match s:
    case SNil{}:
      st
    case SCon{c, t}:
      match c:
        case Chr{x}:
          Num.go(t, Num.step(st, x))

def Num.accepts(st: NState) -> Bool:
  match st:
    case NZero{}:
      True{}
    case NInt{}:
      True{}
    case NFrac{}:
      True{}
    case NExpDigits{}:
      True{}
    case NStart{}:
      False{}
    case NMinus{}:
      False{}
    case NDot{}:
      False{}
    case NExp{}:
      False{}
    case NExpSign{}:
      False{}
    case NBad{}:
      False{}

def Num.valid(s: String) -> Bool:
  Num.accepts(Num.go(s, NStart{}))

# Parser
# ======

# What the parser accepts next.
type Want is Data:
  WValue{}
  WValueOrEnd{}
  WKey{}
  WKeyOrEnd{}
  WColon{}
  WCommaOrEnd{}
  WDone{}

# An open array or object. Items and fields are in reverse order. key is
# the key that waits for its value.
type Frame is Data:
  FArr{items: List<&2, Json>}
  FObj{fields: List<&2, JField>, key: String}

type PState is Data:
  PState{want: Want, stack: List<&2, Frame>, depth: Nat, result: Maybe<&2, Json>}
  PFail{}

# Puts a finished value into the frame on top of the stack.
def Parse.emit(v: Json, stack: List<&2, Frame>, depth: Nat) -> PState:
  match stack:
    case Nil{}:
      PState{WDone{}, [], depth, Some{v}}
    case Con{f, rest}:
      match f:
        case FArr{items}:
          PState{WCommaOrEnd{}, Con{FArr{Con{v, items}}, rest}, depth, None{}}
        case FObj{fields, k}:
          PState{WCommaOrEnd{}, Con{FObj{Con{JField{k, v}, fields}, ""}, rest}, depth, None{}}

def Parse.has_key(+k: String, fs: List<&2, JField>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{f, t}:
      match f:
        case JField{fk, fv}:
          String.eq(k, fk) || Parse.has_key(k, t)

def Parse.unique(fs: List<&2, JField>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{f, +t}:
      match f:
        case JField{k, v}:
          Bool.not(Parse.has_key(k, t)) && Parse.unique(t)

def Parse.close_obj(ok: Bool, fs: List<&2, JField>, rest: List<&2, Frame>, depth: Nat) -> PState:
  match ok:
    case True{}:
      Parse.emit(JObj{List.reverse(&2, JField, fs)}, rest, depth)
    case False{}:
      PFail{}

def Parse.dec(depth: Nat) -> Nat:
  match depth:
    case 0n:
      0n
    case 1n+p:
      p

# Closes the array on top of the stack.
def Parse.close_arr(stack: List<&2, Frame>, depth: Nat) -> PState:
  match stack:
    case Nil{}:
      PFail{}
    case Con{f, rest}:
      match f:
        case FArr{items}:
          Parse.emit(JArr{List.reverse(&2, Json, items)}, rest, Parse.dec(depth))
        case FObj{fs, k}:
          PFail{}

# Closes the object on top of the stack.
def Parse.close_obj_frame(stack: List<&2, Frame>, depth: Nat) -> PState:
  match stack:
    case Nil{}:
      PFail{}
    case Con{f, rest}:
      match f:
        case FArr{items}:
          PFail{}
        case FObj{+fs, k}:
          Parse.close_obj(Parse.unique(fs), fs, rest, Parse.dec(depth))

def Parse.open(f: Frame, want: Want, stack: List<&2, Frame>, +depth: Nat, ok: Bool) -> PState:
  match ok:
    case True{}:
      PState{want, Con{f, stack}, 1n+depth, None{}}
    case False{}:
      PFail{}

def Parse.number(ok: Bool, s: String, stack: List<&2, Frame>, depth: Nat) -> PState:
  match ok:
    case True{}:
      Parse.emit(JNum{s}, stack, depth)
    case False{}:
      PFail{}

# A token where a value can start.
def Parse.value(t: Tok, can_end: Bool, stack: List<&2, Frame>, +depth: Nat) -> PState:
  match t:
    case TArrOpen{}:
      Parse.open(FArr{[]}, WValueOrEnd{}, stack, depth, Nat.is_lt(depth, Json.max_depth()))
    case TObjOpen{}:
      Parse.open(FObj{[], ""}, WKeyOrEnd{}, stack, depth, Nat.is_lt(depth, Json.max_depth()))
    case TArrClose{}:
      match can_end:
        case True{}:
          Parse.close_arr(stack, depth)
        case False{}:
          PFail{}
    case TObjClose{}:
      PFail{}
    case TColon{}:
      PFail{}
    case TComma{}:
      PFail{}
    case TStr{s}:
      Parse.emit(JStr{s}, stack, depth)
    case TNum{+s}:
      Parse.number(Num.valid(s), s, stack, depth)
    case TTrue{}:
      Parse.emit(JBool{True{}}, stack, depth)
    case TFalse{}:
      Parse.emit(JBool{False{}}, stack, depth)
    case TNull{}:
      Parse.emit(JNull{}, stack, depth)

# Sets the waiting key on the object on top of the stack.
def Parse.key(k: String, stack: List<&2, Frame>, depth: Nat) -> PState:
  match stack:
    case Nil{}:
      PFail{}
    case Con{f, rest}:
      match f:
        case FArr{items}:
          PFail{}
        case FObj{fs, old}:
          PState{WColon{}, Con{FObj{fs, k}, rest}, depth, None{}}

def Parse.key_tok(t: Tok, can_end: Bool, stack: List<&2, Frame>, depth: Nat) -> PState:
  match t:
    case TStr{k}:
      Parse.key(k, stack, depth)
    case TObjClose{}:
      match can_end:
        case True{}:
          Parse.close_obj_frame(stack, depth)
        case False{}:
          PFail{}
    case TArrOpen{}:
      PFail{}
    case TArrClose{}:
      PFail{}
    case TObjOpen{}:
      PFail{}
    case TColon{}:
      PFail{}
    case TComma{}:
      PFail{}
    case TNum{s}:
      PFail{}
    case TTrue{}:
      PFail{}
    case TFalse{}:
      PFail{}
    case TNull{}:
      PFail{}

def Parse.top_is_arr(stack: List<&2, Frame>) -> Bool:
  match stack:
    case Nil{}:
      False{}
    case Con{f, rest}:
      match f:
        case FArr{items}:
          True{}
        case FObj{fs, k}:
          False{}

def Parse.comma(is_arr: Bool, stack: List<&2, Frame>, depth: Nat) -> PState:
  match is_arr:
    case True{}:
      PState{WValue{}, stack, depth, None{}}
    case False{}:
      PState{WKey{}, stack, depth, None{}}

def Parse.after_value(t: Tok, +stack: List<&2, Frame>, depth: Nat) -> PState:
  match t:
    case TComma{}:
      Parse.comma(Parse.top_is_arr(stack), stack, depth)
    case TArrClose{}:
      Parse.close_arr(stack, depth)
    case TObjClose{}:
      Parse.close_obj_frame(stack, depth)
    case TArrOpen{}:
      PFail{}
    case TObjOpen{}:
      PFail{}
    case TColon{}:
      PFail{}
    case TStr{s}:
      PFail{}
    case TNum{s}:
      PFail{}
    case TTrue{}:
      PFail{}
    case TFalse{}:
      PFail{}
    case TNull{}:
      PFail{}

def Parse.colon(t: Tok, stack: List<&2, Frame>, depth: Nat) -> PState:
  match t:
    case TColon{}:
      PState{WValue{}, stack, depth, None{}}
    case TArrOpen{}:
      PFail{}
    case TArrClose{}:
      PFail{}
    case TObjOpen{}:
      PFail{}
    case TObjClose{}:
      PFail{}
    case TComma{}:
      PFail{}
    case TStr{s}:
      PFail{}
    case TNum{s}:
      PFail{}
    case TTrue{}:
      PFail{}
    case TFalse{}:
      PFail{}
    case TNull{}:
      PFail{}

def Parse.step(st: PState, t: Tok) -> PState:
  match st:
    case PFail{}:
      PFail{}
    case PState{want, stack, depth, result}:
      match want:
        case WValue{}:
          Parse.value(t, False{}, stack, depth)
        case WValueOrEnd{}:
          Parse.value(t, True{}, stack, depth)
        case WKey{}:
          Parse.key_tok(t, False{}, stack, depth)
        case WKeyOrEnd{}:
          Parse.key_tok(t, True{}, stack, depth)
        case WColon{}:
          Parse.colon(t, stack, depth)
        case WCommaOrEnd{}:
          Parse.after_value(t, stack, depth)
        case WDone{}:
          PFail{}

def Parse.go(ts: List<&2, Tok>, st: PState) -> PState:
  match ts:
    case Nil{}:
      st
    case Con{t, rest}:
      Parse.go(rest, Parse.step(st, t))

def Parse.finish(st: PState) -> Maybe<&2, Json>:
  match st:
    case PFail{}:
      None{}
    case PState{want, stack, depth, result}:
      match want:
        case WDone{}:
          result
        case WValue{}:
          None{}
        case WValueOrEnd{}:
          None{}
        case WKey{}:
          None{}
        case WKeyOrEnd{}:
          None{}
        case WColon{}:
          None{}
        case WCommaOrEnd{}:
          None{}

def Parse.tokens(ts: Maybe<&2, List<&2, Tok>>) -> Maybe<&2, Json>:
  match ts:
    case None{}:
      None{}
    case Some{xs}:
      Parse.finish(Parse.go(xs, PState{WValue{}, [], 0n, None{}}))

# Parses one JSON value. The whole input must be that value, with optional
# white space around it.
def Json.parse(s: String) -> Maybe<&2, Json>:
  Parse.tokens(Lex.tokens(s))

# Access
# ======

def Json.fields(j: Json) -> Maybe<&2, List<&2, JField>>:
  match j:
    case JObj{fs}:
      Some{fs}
    case JNull{}:
      None{}
    case JBool{b}:
      None{}
    case JNum{s}:
      None{}
    case JStr{s}:
      None{}
    case JArr{xs}:
      None{}

def Json.find(fs: List<&2, JField>, +k: String) -> Maybe<&2, Json>:
  match fs:
    case Nil{}:
      None{}
    case Con{f, t}:
      match f:
        case JField{fk, v}:
          Bool.pick(Maybe<&2, Json>, String.eq(k, fk), Some{v}, Json.find(t, k))

# The value of key k, if j is an object that has k.
def Json.get(j: Json, k: String) -> Maybe<&2, Json>:
  do Maybe<&2, Json>:
    fs : List<&2, JField> <- Json.fields(j)
    Json.find(fs, k)

def Json.str(j: Json) -> Maybe<&2, String>:
  match j:
    case JStr{s}:
      Some{s}
    case JNull{}:
      None{}
    case JBool{b}:
      None{}
    case JNum{s}:
      None{}
    case JArr{xs}:
      None{}
    case JObj{fs}:
      None{}

def Json.is_null(j: Json) -> Bool:
  match j:
    case JNull{}:
      True{}
    case JStr{s}:
      False{}
    case JBool{b}:
      False{}
    case JNum{s}:
      False{}
    case JArr{xs}:
      False{}
    case JObj{fs}:
      False{}

# Printing
# ========
#
# Compact JSON, with the escapes that Python's json.dumps uses. The printer
# walks the value with an explicit stack of work items, because Bend has no
# mutual recursion. fuel bounds the loop.

type Work is Data:
  WText{text: String}
  WVal{value: Json}
  WFields{first: Bool, fields: List<&2, JField>}
  WItems{first: Bool, items: List<&2, Json>}

def Show.nib.if(d: U32, low: Bool) -> Char:
  match low:
    case True{}:
      Chr{(d + 48 : U32)}
    case False{}:
      Chr{(d + 87 : U32)}

def Show.nib(+d: U32) -> Char:
  Show.nib.if(d, U32.is_lt(d, 10))

# A backslash, then the character c.
def Show.esc(c: U32) -> String:
  SCon{Chr{92}, SCon{Chr{c}, SNil{}}}

# \u and four hex digits.
def Show.hex4(+c: U32) -> String:
  SCon{Chr{92}, SCon{Chr{117},
    SCon{Show.nib(((c / 4096 : U32) .&. 15 : U32)), SCon{Show.nib(((c / 256 : U32) .&. 15 : U32)),
    SCon{Show.nib(((c / 16 : U32) .&. 15 : U32)), SCon{Show.nib((c .&. 15 : U32)), SNil{}}}}}}}

def Show.char(+c: U32) -> String:
  Bool.pick(String, U32.is_eq(c, 34), Show.esc(34),
  Bool.pick(String, U32.is_eq(c, 92), Show.esc(92),
  Bool.pick(String, U32.is_eq(c, 10), Show.esc(110),
  Bool.pick(String, U32.is_eq(c, 13), Show.esc(114),
  Bool.pick(String, U32.is_eq(c, 9), Show.esc(116),
  Bool.pick(String, U32.is_eq(c, 8), Show.esc(98),
  Bool.pick(String, U32.is_eq(c, 12), Show.esc(102),
  Bool.pick(String, U32.is_lt(c, 32), Show.hex4(c),
  SCon{Chr{c}, SNil{}}))))))))

def Show.str.go(s: String, acc: List<&2, String>) -> List<&2, String>:
  match s:
    case SNil{}:
      acc
    case SCon{c, t}:
      match c:
        case Chr{x}:
          Show.str.go(t, Con{Show.char(x), acc})

def Show.quote() -> String:
  SCon{Chr{34}, SNil{}}

def Show.str(s: String) -> String:
  Show.quote() ++ String.concat(List.reverse(&2, String, Show.str.go(s, []))) ++ Show.quote()

def Show.expand(v: Json, rest: List<&2, Work>) -> List<&2, Work>:
  match v:
    case JNull{}:
      Con{WText{"null"}, rest}
    case JBool{b}:
      match b:
        case True{}:
          Con{WText{"true"}, rest}
        case False{}:
          Con{WText{"false"}, rest}
    case JNum{s}:
      Con{WText{s}, rest}
    case JStr{s}:
      Con{WText{Show.str(s)}, rest}
    case JArr{xs}:
      Con{WText{"["}, Con{WItems{True{}, xs}, Con{WText{"]"}, rest}}}
    case JObj{fs}:
      Con{WText{"{"}, Con{WFields{True{}, fs}, Con{WText{"}"}, rest}}}

def Show.sep(first: Bool) -> String:
  match first:
    case True{}:
      ""
    case False{}:
      ","

def Show.field(first: Bool, f: JField, more: List<&2, JField>, rest: List<&2, Work>) -> List<&2, Work>:
  match f:
    case JField{k, v}:
      Con{WText{Show.sep(first) ++ Show.str(k) ++ ":"}, Con{WVal{v}, Con{WFields{False{}, more}, rest}}}

def Show.step(w: Work, rest: List<&2, Work>, out: List<&2, String>) -> List<&2, Work> & List<&2, String>:
  match w:
    case WText{s}:
      (rest, Con{s, out})
    case WVal{v}:
      (Show.expand(v, rest), out)
    case WItems{first, xs}:
      match xs:
        case Nil{}:
          (rest, out)
        case Con{x, t}:
          (Con{WVal{x}, Con{WItems{False{}, t}, rest}}, Con{Show.sep(first), out})
    case WFields{first, fs}:
      match fs:
        case Nil{}:
          (rest, out)
        case Con{f, t}:
          (Show.field(first, f, t, rest), out)

def Show.go(fuel: Nat, st: List<&2, Work> & List<&2, String>) -> String:
  match fuel:
    case 0n:
      "<too large>"
    case 1n+p:
      match st:
        case (ws, out):
          match ws:
            case Nil{}:
              String.concat(List.reverse(&2, String, out))
            case Con{w, rest}:
              Show.go(p, Show.step(w, rest, out))

def Json.show(j: Json) -> String:
  Show.go(1000000n, ([WVal{j}], []))
