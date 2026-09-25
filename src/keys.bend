# Key loading: the Web3Signer key-config directory (docs/SPEC.md section
# 9.2). Each *.yaml or *.yml file names one key:
#
#   type: "file-keystore"               type: "file-raw"
#   keystoreFile: "k.json"              privateKey: "0x..."
#   keystorePasswordFile: "k.password"
#
# Bulkhead reads the files here and decrypts in C (src/ffi.bend). A key that
# does not load stops Bulkhead at start: a signer that silently misses a key
# is worse than one that does not start.
import Base
import ./ssz.bend as S
import ./json.bend as J
import ./ffi.bend as F

type Loaded is Data:
  Loaded{key: S.Pubkey, index: U32}

# Text
# ====

def Txt.is_space(+c: U32) -> Bool:
  U32.is_eq(c, 32) || U32.is_eq(c, 9) || U32.is_eq(c, 13)

def Txt.trim_left(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          Bool.pick(String, Txt.is_space(x), Txt.trim_left(t), SCon{Chr{x}, t})

def Txt.trim(s: String) -> String:
  String.reverse(Txt.trim_left(String.reverse(Txt.trim_left(s))))

# The text before and after the first c, or None.
type Cut is Data:
  Cut{before: String, after: String}
  NoCut{}

def Txt.cut.go(s: String, +c: U32, +acc: String) -> Cut:
  match s:
    case SNil{}:
      NoCut{}
    case SCon{h, +t}:
      match h:
        case Chr{+x}:
          Bool.pick(Cut, U32.is_eq(x, c), Cut{String.reverse(acc), t}, Txt.cut.go(t, c, SCon{Chr{x}, acc}))

def Txt.cut(s: String, +c: U32) -> Cut:
  Txt.cut.go(s, c, "")

# The first line of s, without a trailing carriage return.
def Txt.first_line.of(c: Cut, s: String) -> String:
  match c:
    case NoCut{}:
      s
    case Cut{before, after}:
      before

def Txt.strip_cr.rev(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          Bool.pick(String, U32.is_eq(x, 13), t, SCon{Chr{x}, t})

def Txt.strip_cr(s: String) -> String:
  String.reverse(Txt.strip_cr.rev(String.reverse(s)))

def Txt.first_line(+s: String) -> String:
  Txt.strip_cr(Txt.first_line.of(Txt.cut(s, 10), s))

def Txt.unquote.if(+s: String, quoted: Bool) -> String:
  match quoted:
    case True{}:
      String.reverse(String.drop(String.reverse(String.drop(s, 1n)), 1n))
    case False{}:
      s

def Txt.quoted(+s: String, +q: String) -> Bool:
  Nat.is_lt(1n, String.length(s)) && String.starts_with(s, q) && String.ends_with(s, q)

# Removes one pair of double or single quotes around s.
def Txt.unquote(+s: String) -> String:
  Txt.unquote.if(s, Txt.quoted(s, SCon{Chr{34}, SNil{}}) || Txt.quoted(s, SCon{Chr{39}, SNil{}}))

# YAML
# ====
#
# The subset that Web3Signer key files use: one mapping of "key: value"
# lines. Blank lines, comments and "---" lines are skipped. The result is a
# JSON object with string values, so the JSON access functions work on it.

def Yaml.line.field(c: Cut) -> Maybe<&2, J.JField>:
  match c:
    case NoCut{}:
      None{}
    case Cut{k, v}:
      Some{J.JField{Txt.trim(k), J.JStr{Txt.unquote(Txt.trim(v))}}}

def Yaml.skip(+t: String) -> Bool:
  String.is_empty(t) || String.starts_with(t, "#") || String.eq(t, "---")

def Yaml.line(+t: String) -> Maybe<&2, J.JField>:
  Bool.pick(Maybe<&2, J.JField>, Yaml.skip(t), None{}, Yaml.line.field(Txt.cut(t, 58)))

def Yaml.lines.add(m: Maybe<&2, J.JField>, acc: List<&2, J.JField>) -> List<&2, J.JField>:
  match m:
    case None{}:
      acc
    case Some{f}:
      Con{f, acc}

def Yaml.lines(ls: List<&2, String>, acc: List<&2, J.JField>) -> List<&2, J.JField>:
  match ls:
    case Nil{}:
      List.reverse(&2, J.JField, acc)
    case Con{l, rest}:
      Yaml.lines(rest, Yaml.lines.add(Yaml.line(Txt.trim(l)), acc))

type LineSplit is Data:
  LineSplit{done: List<&2, String>, cur: String}

def Yaml.split.step(st: LineSplit, c: Char) -> LineSplit:
  match st:
    case LineSplit{+done, +cur}:
      match c:
        case Chr{+x}:
          Bool.pick(LineSplit, U32.is_eq(x, 10), LineSplit{Con{String.reverse(cur), done}, ""},
            LineSplit{done, SCon{Chr{x}, cur}})

def Yaml.split.go(s: String, st: LineSplit) -> LineSplit:
  match s:
    case SNil{}:
      st
    case SCon{c, t}:
      Yaml.split.go(t, Yaml.split.step(st, c))

def Yaml.split.end(st: LineSplit) -> List<&2, String>:
  match st:
    case LineSplit{done, cur}:
      List.reverse(&2, String, Con{String.reverse(cur), done})

def Yaml.parse(s: String) -> J.Json:
  J.JObj{Yaml.lines(Yaml.split.end(Yaml.split.go(s, LineSplit{[], ""})), [])}

# Keystores
# =========

def Need(-A: Data, m: Maybe<&2, A>, why: String) -> Result<&2, &2, String, A>:
  match m:
    case None{}:
      Fail{why}
    case Some{x}:
      Done{x}

def Get.str(+o: J.Json, k: String) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    j : J.Json <- J.Json.get(o, k)
    J.Json.str(j)

def U32.of_u64(a: S.U64) -> Maybe<&2, U32>:
  match a:
    case S.U64{h, l}:
      Bool.pick(Maybe<&2, U32>, U32.is_eq(h, 0), Some{l}, None{})

def Keys.num(j: J.Json) -> Maybe<&2, S.U64>:
  match j:
    case J.JNum{s}:
      S.U64.read(s)
    case J.JStr{s}:
      S.U64.read(s)
    case J.JNull{}:
      None{}
    case J.JBool{b}:
      None{}
    case J.JArr{xs}:
      None{}
    case J.JObj{fs}:
      None{}

# A JSON number that fits in 32 bits.
def Get.u32(+o: J.Json, k: String) -> Maybe<&2, U32>:
  do Maybe<&2, U32>:
    j : J.Json <- J.Json.get(o, k)
    n : S.U64 <- Keys.num(j)
    U32.of_u64(n)

# The fields of an EIP-2335 keystore that decryption needs. For pbkdf2, n
# holds the iteration count c, and r and p are 0.
type Keystore is Data:
  Keystore{kdf: String, dklen: U32, n: U32, r: U32, p: U32, salt: String, checksum: String,
    cipher: String, iv: String, pubkey: Maybe<&2, String>}

def Keystore.expect(+o: J.Json, +k: String, +want: String) -> Result<&2, &2, String, Unit>:
  do Result<&2, &2, String, Unit>:
    +v : String <- Need(String, Get.str(o, k), "keystore has no " ++ k)
    Bool.pick(Result<&2, &2, String, Unit>, String.eq(v, want), Done{Unit{}},
      Fail{"unsupported keystore " ++ k ++ " " ++ v ++ ", want " ++ want})

def Keystore.pbkdf2_c(+ps: J.Json) -> Result<&2, &2, String, U32>:
  do Result<&2, &2, String, U32>:
    u : Unit <- Keystore.expect(ps, "prf", "hmac-sha256")
    Need(U32, Get.u32(ps, "c"), "keystore pbkdf2 has no c")

def Keystore.kdf_n(+kdf: String, +ps: J.Json) -> Result<&2, &2, String, U32>:
  Bool.pick(Result<&2, &2, String, U32>, String.eq(kdf, "scrypt"), Need(U32, Get.u32(ps, "n"), "keystore scrypt has no n"),
  Bool.pick(Result<&2, &2, String, U32>, String.eq(kdf, "pbkdf2"), Keystore.pbkdf2_c(ps),
    Fail{"unsupported keystore kdf " ++ kdf}))

# An scrypt parameter, or 0 for pbkdf2.
def Keystore.kdf_opt(+kdf: String, +ps: J.Json, +k: String) -> Result<&2, &2, String, U32>:
  Bool.pick(Result<&2, &2, String, U32>, String.eq(kdf, "scrypt"), Need(U32, Get.u32(ps, k), "keystore scrypt has no " ++ k),
    Done{0})

def Keystore.version(v: U32) -> Result<&2, &2, String, Unit>:
  Bool.pick(Result<&2, &2, String, Unit>, U32.is_eq(v, 4), Done{Unit{}}, Fail{"keystore version is not 4"})

def Keystore.decode(+j: J.Json) -> Result<&2, &2, String, Keystore>:
  do Result<&2, &2, String, Keystore>:
    v : U32 <- Need(U32, Get.u32(j, "version"), "keystore has no version")
    u0 : Unit <- Keystore.version(v)
    +crypto : J.Json <- Need(J.Json, J.Json.get(j, "crypto"), "keystore has no crypto")
    +kdfm : J.Json <- Need(J.Json, J.Json.get(crypto, "kdf"), "keystore has no crypto.kdf")
    +kdf : String <- Need(String, Get.str(kdfm, "function"), "keystore has no kdf function")
    +ps : J.Json <- Need(J.Json, J.Json.get(kdfm, "params"), "keystore has no kdf params")
    dklen : U32 <- Need(U32, Get.u32(ps, "dklen"), "keystore has no dklen")
    n : U32 <- Keystore.kdf_n(kdf, ps)
    r : U32 <- Keystore.kdf_opt(kdf, ps, "r")
    p : U32 <- Keystore.kdf_opt(kdf, ps, "p")
    salt : String <- Need(String, Get.str(ps, "salt"), "keystore has no salt")
    +cs : J.Json <- Need(J.Json, J.Json.get(crypto, "checksum"), "keystore has no checksum")
    u1 : Unit <- Keystore.expect(cs, "function", "sha256")
    checksum : String <- Need(String, Get.str(cs, "message"), "keystore has no checksum message")
    +ci : J.Json <- Need(J.Json, J.Json.get(crypto, "cipher"), "keystore has no cipher")
    u2 : Unit <- Keystore.expect(ci, "function", "aes-128-ctr")
    cps : J.Json <- Need(J.Json, J.Json.get(ci, "params"), "keystore has no cipher params")
    iv : String <- Need(String, Get.str(cps, "iv"), "keystore has no iv")
    cipher : String <- Need(String, Get.str(ci, "message"), "keystore has no cipher message")
    return Keystore{kdf, dklen, n, r, p, salt, checksum, cipher, iv, Get.str(j, "pubkey")}

# Loading
# =======

# Stops Bulkhead with a message if r is a failure.
def Load.need(-A: Data, ctx: String, r: Result<&2, &2, String, A>) -> IO(A):
  match r:
    case Fail{e}:
      IO.die(A, 1, ctx ++ ": " ++ e)
    case Done{x}:
      IO.pure(A, x)

def Load.ctx.fin(-A: Type, ctx: String, r: Result<&1, &1, U32 & String, A>) -> IO(A):
  match r:
    case Fail{ce}:
      match ce:
        case (code, msg):
          IO.die(A, 1, ctx ++ ": " ++ msg)
    case Done{x}:
      IO.pure(A, x)

# Runs a fallible effect. If it fails, stops Bulkhead with ctx and the error.
def Load.ctx(-A: Type, ctx: String, act: IO(Result<&1, &1, U32 & String, A>)) -> IO(A):
  IO.bind(Result<&1, &1, U32 & String, A>, A, act, r => Load.ctx.fin(A, ctx, r))

# A path in the key directory, unless the path is absolute.
def Keys.path(+dir: String, +p: String) -> String:
  Bool.pick(String, String.starts_with(p, "/"), p, dir ++ "/" ++ p)

def Keys.decrypt(ks: Keystore, password: String) -> IO(Result<&1, &1, U32 & String, U32>):
  match ks:
    case Keystore{kdf, dklen, n, r, p, salt, checksum, cipher, iv, pk}:
      F.Keys.decrypt(kdf, dklen, n, r, p, salt, checksum, cipher, iv, password)

def Keystore.pubkey(ks: Keystore) -> Maybe<&2, String>:
  match ks:
    case Keystore{kdf, dklen, n, r, p, salt, checksum, cipher, iv, pk}:
      pk

def Keys.check_pubkey.same(+key: S.Pubkey, got: Maybe<&2, S.Pubkey>) -> Result<&2, &2, String, Unit>:
  match got:
    case None{}:
      Fail{"keystore pubkey is not 48 bytes of hex"}
    case Some{g}:
      Bool.pick(Result<&2, &2, String, Unit>, S.Pubkey.is_eq(key, g), Done{Unit{}},
        Fail{"keystore pubkey does not match its secret key"})

# The keystore pubkey field, if it has one, must name the decrypted key.
def Keys.check_pubkey(+key: S.Pubkey, want: Maybe<&2, String>) -> Result<&2, &2, String, Unit>:
  match want:
    case None{}:
      Done{Unit{}}
    case Some{w}:
      Keys.check_pubkey.same(key, S.Hex.read_pubkey(w))

def Keys.finish(+name: String, +index: U32, want: Maybe<&2, String>) -> IO(Loaded):
  do IO<Loaded>:
    hex : String <- Load.ctx(String, name, F.Keys.pubkey(index))
    +key : S.Pubkey <- Load.need(S.Pubkey, name, Need(S.Pubkey, S.Hex.read_pubkey(hex), "bad public key from C"))
    u : Unit <- Load.need(Unit, name, Keys.check_pubkey(key, want))
    return Loaded{key, index}

def Keys.load_keystore(+dir: String, +name: String, +fields: J.Json) -> IO(Loaded):
  do IO<Loaded>:
    +kf : String <- Load.need(String, name, Need(String, Get.str(fields, "keystoreFile"), "no keystoreFile"))
    +pf : String <- Load.need(String, name, Need(String, Get.str(fields, "keystorePasswordFile"), "no keystorePasswordFile"))
    kt : String <- Load.ctx(String, kf, F.Fs.read_text(Keys.path(dir, kf)))
    +pt : String <- Load.ctx(String, pf, F.Fs.read_text(Keys.path(dir, pf)))
    +pw : String = Txt.first_line(pt)
    u : Unit <- Load.need(Unit, pf, Bool.pick(Result<&2, &2, String, Unit>, String.is_empty(pw), Fail{"the password is blank"}, Done{Unit{}}))
    +j : J.Json <- Load.need(J.Json, kf, Need(J.Json, J.Json.parse(kt), "keystore is not valid JSON"))
    +ks : Keystore <- Load.need(Keystore, kf, Keystore.decode(j))
    index : U32 <- Load.ctx(U32, kf, Keys.decrypt(ks, pw))
    Keys.finish(name, index, Keystore.pubkey(ks))

def Keys.load_raw(+name: String, +fields: J.Json) -> IO(Loaded):
  do IO<Loaded>:
    hex : String <- Load.need(String, name, Need(String, Get.str(fields, "privateKey"), "no privateKey"))
    index : U32 <- Load.ctx(U32, name, F.Keys.load_raw(hex))
    Keys.finish(name, index, None{})

def Keys.key_type(t: Maybe<&2, String>) -> Result<&2, &2, String, Unit>:
  match t:
    case None{}:
      Done{Unit{}}
    case Some{+x}:
      Bool.pick(Result<&2, &2, String, Unit>, String.eq(x, "BLS"), Done{Unit{}}, Fail{"unsupported keyType " ++ x})

def Keys.load_kind(+dir: String, +name: String, +fields: J.Json, +kind: String) -> IO(Loaded):
  Bool.pick(IO(Loaded), String.eq(kind, "file-keystore"), Keys.load_keystore(dir, name, fields),
  Bool.pick(IO(Loaded), String.eq(kind, "file-raw"), Keys.load_raw(name, fields),
    IO.die(Loaded, 1, name ++ ": unsupported key type " ++ kind ++ ": Bulkhead supports file-keystore and file-raw")))

def Keys.load_file(+dir: String, +name: String) -> IO(Loaded):
  do IO<Loaded>:
    text : String <- Load.ctx(String, name, F.Fs.read_text(Keys.path(dir, name)))
    +fields : J.Json = Yaml.parse(text)
    u : Unit <- Load.need(Unit, name, Keys.key_type(Get.str(fields, "keyType")))
    kind : String <- Load.need(String, name, Need(String, Get.str(fields, "type"), "no type"))
    Keys.load_kind(dir, name, fields, kind)

def Keys.is_config(+name: String) -> Bool:
  String.ends_with(name, ".yaml") || String.ends_with(name, ".yml")

def Keys.configs.add(keep: Bool, n: String, rest: List<&2, String>) -> List<&2, String>:
  match keep:
    case True{}:
      Con{n, rest}
    case False{}:
      rest

def Keys.configs(ns: List<&2, String>) -> List<&2, String>:
  match ns:
    case Nil{}:
      []
    case Con{+n, rest}:
      Keys.configs.add(Keys.is_config(n), n, Keys.configs(rest))

def Keys.load_names(ns: List<&2, String>, +dir: String, acc: List<&2, Loaded>) -> IO(List<&2, Loaded>):
  match ns:
    case Nil{}:
      IO.pure(List<&2, Loaded>, List.reverse(&2, Loaded, acc))
    case Con{n, rest}:
      do IO<List<&2, Loaded>>:
        l : Loaded <- Keys.load_file(dir, n)
        Keys.load_names(rest, dir, Con{l, acc})

def Keys.has(+k: S.Pubkey, ls: List<&2, Loaded>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{l, t}:
      match l:
        case Loaded{x, i}:
          S.Pubkey.is_eq(k, x) || Keys.has(k, t)

# A public key that appears twice, if any.
def Keys.duplicate(ls: List<&2, Loaded>) -> Maybe<&2, S.Pubkey>:
  match ls:
    case Nil{}:
      None{}
    case Con{l, +t}:
      match l:
        case Loaded{+x, i}:
          Bool.pick(Maybe<&2, S.Pubkey>, Keys.has(x, t), Some{x}, Keys.duplicate(t))

def Keys.no_duplicate(+ls: List<&2, Loaded>, d: Maybe<&2, S.Pubkey>) -> IO(List<&2, Loaded>):
  match d:
    case None{}:
      IO.pure(List<&2, Loaded>, ls)
    case Some{k}:
      IO.die(List<&2, Loaded>, 1, "two key files name the key " ++ S.Hex.pubkey(k))

# Loads every *.yaml and *.yml key file in dir, in name order.
def Keys.load_dir(+dir: String) -> IO(List<&2, Loaded>):
  do IO<List<&2, Loaded>>:
    names : String <- Load.ctx(String, dir, F.Fs.list(dir))
    +ls : List<&2, Loaded> <- Keys.load_names(Keys.configs(Yaml.split.end(Yaml.split.go(names, LineSplit{[], ""}))), dir, [])
    Keys.no_duplicate(ls, Keys.duplicate(ls))
