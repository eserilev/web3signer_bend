# Bulkhead: an eth2 remote signer with the Web3Signer HTTP API.
#
#   bulkhead --key-config-path <dir> --slashing-log <file>
#            [--network-config <config.yaml>] [--http-listen-host 127.0.0.1]
#            [--http-listen-port 9000]
#
# Tasks (docs/SPEC.md section 5):
# - One core task owns the slashing store. It decides each request, appends
#   and fsyncs the log events, and only then answers Go.
# - One task per connection parses HTTP and requests, computes the signing
#   root, asks the core, and signs only after Go. So a record is on disk
#   before its signature exists (law L10, by structure).
import Base
import ./src/ssz.bend as S
import ./src/request.bend as R
import ./src/store.bend as St
import ./src/ffi.bend as F
import ./src/keys.bend as K
import ./src/http.bend as H

# Configuration
# =============

type Config is Data:
  Config{network: Maybe<&2, String>, keys: Maybe<&2, String>, log: Maybe<&2, String>, host: String, port: U32}

def Config.default() -> Config:
  Config{None{}, None{}, None{}, "127.0.0.1", 9000}

def Config.usage() -> String:
  "usage: bulkhead --key-config-path <dir> --slashing-log <file> [--network-config <file>] "
    ++ "[--http-listen-host <ipv4>] [--http-listen-port <port>]"

def Config.set(c: Config, +flag: String, +v: String) -> Maybe<&2, Config>:
  match c:
    case Config{+n, +k, +l, +h, +p}:
      Bool.pick(Maybe<&2, Config>, String.eq(flag, "--network-config"), Some{Config{Some{v}, k, l, h, p}},
      Bool.pick(Maybe<&2, Config>, String.eq(flag, "--key-config-path"), Some{Config{n, Some{v}, l, h, p}},
      Bool.pick(Maybe<&2, Config>, String.eq(flag, "--slashing-log"), Some{Config{n, k, Some{v}, h, p}},
      Bool.pick(Maybe<&2, Config>, String.eq(flag, "--http-listen-host"), Some{Config{n, k, l, v, p}},
      Bool.pick(Maybe<&2, Config>, String.eq(flag, "--http-listen-port"),
        Maybe.map(&2, U32, Config, x => Config{n, k, l, h, x}, U32.read(v)),
        None{})))))

def Config.parse(xs: List<String>, c: Config) -> Maybe<&2, Config>:
  match xs:
    case Nil{}:
      Some{c}
    case Con{+flag, rest}:
      match rest:
        case Nil{}:
          None{}
        case Con{+v, more}:
          do Maybe<&2, Config>:
            c2 : Config <- Config.set(c, flag, v)
            Config.parse(more, c2)

def Config.need(-A: Data, m: Maybe<&2, A>, why: String) -> IO(A):
  match m:
    case None{}:
      IO.die(A, 2, why ++ "\n" ++ Config.usage())
    case Some{x}:
      IO.pure(A, x)

# The network: mainnet without --network-config, or the values that
# Bulkhead needs from the config file.
def Config.net(path: Maybe<&2, String>) -> IO(R.Net):
  match path:
    case None{}:
      IO.pure(R.Net, R.Net.mainnet())
    case Some{+p}:
      do IO<R.Net>:
        text : String <- K.Load.ctx(String, p, F.Fs.read_text(p))
        K.Load.need(R.Net, p, R.Net.read(K.Yaml.parse(text)))

# The slashing log
# ================

# The directory part of a path, or "." if it has none. The fold keeps the
# path so far (reversed) and the text before the last "/".
type DirScan is Data:
  DirScan{cur: String, last: String}

def Dir.of.step(st: DirScan, +c: Char) -> DirScan:
  match st:
    case DirScan{+cur, last}:
      DirScan{SCon{c, cur}, Bool.pick(String, Char.is_eq(c, Chr{47}), String.reverse(cur), last)}

def Dir.of.go(s: String, st: DirScan) -> DirScan:
  match s:
    case SNil{}:
      st
    case SCon{c, t}:
      Dir.of.go(t, Dir.of.step(st, c))

def Dir.of.fix(st: DirScan) -> String:
  match st:
    case DirScan{cur, +last}:
      Bool.pick(String, String.is_empty(last), ".", last)

def Dir.of(p: String) -> String:
  Dir.of.fix(Dir.of.go(p, DirScan{"", ""}))

# The log text and its events. A missing file is an empty log.
def Start.log_text(r: Result<&1, &1, U32 & String, String>) -> IO(String):
  match r:
    case Done{t}:
      IO.pure(String, t)
    case Fail{ce}:
      match ce:
        case (code, msg):
          Bool.pick(IO(String), U32.is_eq(code, 2), IO.pure(String, ""),
            IO.die(String, 1, "cannot read the slashing log: " ++ msg))

# Removes a partial last line: its fsync never returned, so no signature
# went out for it.
def Start.cut_tail(+path: String, +text: String, lines: St.Lines) -> IO(Unit):
  match lines:
    case St.Lines{done, +tail}:
      Bool.pick(IO(Unit), String.is_empty(tail), IO.pure(Unit, Unit{}),
        K.Load.ctx(Unit, path, F.Log.truncate_sync(path,
          U32.from_nat(Nat.sub(String.length(text), String.length(tail))))))

def Start.store(+path: String) -> IO(St.Store):
  do IO<St.Store>:
    r : Result<&1, &1, U32 & String, String> <- F.Fs.read_text(path)
    +text : String <- Start.log_text(r)
    es : List<&2, St.LogEvent> <- K.Load.need(List<&2, St.LogEvent>, path,
      K.Need(List<&2, St.LogEvent>, St.Log.read(text), "the slashing log has a line that does not parse"))
    u1 : Unit <- Start.cut_tail(path, text, St.Log.lines(text))
    u2 : Unit <- K.Load.ctx(Unit, path, F.Log.append_sync(path, ""))
    u3 : Unit <- K.Load.ctx(Unit, Dir.of(path), F.Fs.sync_dir(Dir.of(path)))
    return St.Store.replay(es)

# The core task
# =============

type Verdict is Data:
  Go{}
  No{status: U32, reason: String}

type Job is Type:
  Job{key: S.Pubkey, req: R.Request, root: S.B32, reply: Chan(Verdict)}

@unsafe def Core.loop(+jobs: Chan(Job), +path: String, +store: St.Store) -> IO(Unit):
  do IO<Unit>:
    m : Maybe<&1, Job> <- Chan.recv(Job, jobs)
    Core.handle(m, jobs, path, store)

@unsafe def Core.handle(m: Maybe<&1, Job>, +jobs: Chan(Job), +path: String, +store: St.Store) -> IO(Unit):
  match m:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{job}:
      match job:
        case Job{key, req, root, +reply}:
          Core.outcome(St.Store.decide(store, key, req, root), reply, jobs, path, store)

@unsafe def Core.outcome(o: St.Outcome, +reply: Chan(Verdict), +jobs: Chan(Job), +path: String, +store: St.Store) -> IO(Unit):
  match o:
    case St.Refuse{c, why}:
      do IO<Unit>:
        ok : Bool <- Chan.send(Verdict, reply, No{c, why})
        Core.loop(jobs, path, store)
    case St.Sign{+es}:
      Core.write(List.length(&2, St.LogEvent, es), es, reply, jobs, path, store)

@unsafe def Core.write(n: Nat, +es: List<&2, St.LogEvent>, +reply: Chan(Verdict), +jobs: Chan(Job), +path: String, +store: St.Store) -> IO(Unit):
  match n:
    case 0n:
      do IO<Unit>:
        ok : Bool <- Chan.send(Verdict, reply, Go{})
        Core.loop(jobs, path, store)
    case 1n+p:
      do IO<Unit>:
        r : Result<&1, &1, U32 & String, Unit> <- F.Log.append_sync(path, St.Log.show(es))
        Core.written(r, es, reply, jobs, path, store)

# If the log write fails, Bulkhead stops: the state on disk is not known,
# and a signer must not run on a state that it cannot trust.
@unsafe def Core.written(r: Result<&1, &1, U32 & String, Unit>, +es: List<&2, St.LogEvent>, +reply: Chan(Verdict),
  +jobs: Chan(Job), +path: String, +store: St.Store) -> IO(Unit):
  match r:
    case Fail{ce}:
      match ce:
        case (code, msg):
          IO.die(Unit, 1, "slashing log write failed, stopping: " ++ msg)
    case Done{u}:
      do IO<Unit>:
        ok : Bool <- Chan.send(Verdict, reply, Go{})
        Core.loop(jobs, path, St.Store.apply_all(es, store))

# Requests
# ========

type Ctx is Data:
  Ctx{keys: List<&2, K.Loaded>, pubkeys: String, net: R.Net}

type Resp is Data:
  Resp{status: U32, ctype: String, body: String}

def Resp.text(status: U32, body: String) -> Resp:
  Resp{status, H.Http.text(), body}

def Keys.index(ls: List<&2, K.Loaded>, +k: S.Pubkey) -> Maybe<&2, U32>:
  match ls:
    case Nil{}:
      None{}
    case Con{l, t}:
      match l:
        case K.Loaded{x, i}:
          Bool.pick(Maybe<&2, U32>, S.Pubkey.is_eq(k, x), Some{i}, Keys.index(t, k))

def Keys.json.items(ls: List<&2, K.Loaded>) -> List<&2, String>:
  match ls:
    case Nil{}:
      []
    case Con{l, t}:
      match l:
        case K.Loaded{x, i}:
          Con{"\"" ++ S.Hex.pubkey(x) ++ "\"", Keys.json.items(t)}

def Keys.json(ls: List<&2, K.Loaded>) -> String:
  "[" ++ String.join(Keys.json.items(ls), ",") ++ "]"

def Ctx.net(c: Ctx) -> R.Net:
  match c:
    case Ctx{ks, pk, n}:
      n

def Sign.reply(r: Result<&1, &1, U32 & String, String>, json: Bool) -> Resp:
  match r:
    case Fail{ce}:
      match ce:
        case (code, msg):
          Resp.text(500, msg)
    case Done{sig}:
      match json:
        case True{}:
          Resp{200, H.Http.json(), "{\"signature\":\"" ++ sig ++ "\"}"}
        case False{}:
          Resp{200, H.Http.text(), sig}

def Sign.verdict(v: Maybe<&1, Verdict>, +json: Bool, +index: U32, +root: S.B32) -> IO(Resp):
  match v:
    case None{}:
      IO.pure(Resp, Resp.text(500, "the core task stopped"))
    case Some{x}:
      match x:
        case No{c, why}:
          IO.pure(Resp, Resp.text(c, why))
        case Go{}:
          do IO<Resp>:
            r : Result<&1, &1, U32 & String, String> <- F.Bls.sign_key(index, S.Hex.b32(root))
            return Sign.reply(r, json)

def Sign.ask(+jobs: Chan(Job), +key: S.Pubkey, +index: U32, req: R.Request, +root: S.B32, +json: Bool) -> IO(Resp):
  do IO<Resp>:
    +reply : Chan(Verdict) <- Chan.new(Verdict, 1)
    ok : Bool <- Chan.send(Job, jobs, Job{key, req, root, reply})
    v : Maybe<&1, Verdict> <- Chan.recv(Verdict, reply)
    Sign.verdict(v, json, index, root)

def Sign.checked(r: Result<&2, &2, String, S.B32>, +jobs: Chan(Job), +key: S.Pubkey, +index: U32, req: R.Request, +json: Bool) -> IO(Resp):
  match r:
    case Fail{e}:
      IO.pure(Resp, Resp.text(400, e))
    case Done{+root}:
      Sign.ask(jobs, key, index, req, root, json)

def Sign.decoded(r: Result<&2, &2, String, R.Request>, +ctx: Ctx, +jobs: Chan(Job), +key: S.Pubkey, +index: U32, +json: Bool) -> IO(Resp):
  match r:
    case Fail{e}:
      IO.pure(Resp, Resp.text(400, e))
    case Done{+req}:
      match ctx:
        case Ctx{ks, pk, n}:
          Sign.checked(R.Request.check(req, R.Net.log_spe(n)), jobs, key, index, req, json)

def Sign.indexed(i: Maybe<&2, U32>, +ctx: Ctx, +jobs: Chan(Job), +key: S.Pubkey, body: String, +json: Bool) -> IO(Resp):
  match i:
    case None{}:
      IO.pure(Resp, Resp.text(404, "no loaded key has this public key"))
    case Some{+index}:
      Sign.decoded(R.Request.decode(body, Ctx.net(ctx)), ctx, jobs, key, index, json)

def Sign.keyed(k: Maybe<&2, S.Pubkey>, +ctx: Ctx, +jobs: Chan(Job), body: String, +json: Bool) -> IO(Resp):
  match k:
    case None{}:
      IO.pure(Resp, Resp.text(404, "no loaded key has this public key"))
    case Some{+key}:
      match ctx:
        case Ctx{+ks, pk, n}:
          Sign.indexed(Keys.index(ks, key), Ctx{ks, pk, n}, jobs, key, body, json)

def Route.path.first(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{h, rest}:
      h

# The path without a query string.
def Route.path(t: String) -> String:
  Route.path.first(H.Http.split(t, 63))

def Route.sign_prefix() -> String:
  "/api/v1/eth2/sign/"

def Route.method(+m: String, want: String, act: IO(Resp)) -> IO(Resp):
  Bool.pick(IO(Resp), String.eq(m, want), act, IO.pure(Resp, Resp.text(405, "method not allowed")))

def Ctx.pubkeys(c: Ctx) -> String:
  match c:
    case Ctx{ks, pk, n}:
      pk

# Connections
# ===========

def Route.go(+path: String, +m: String, +ctx: Ctx, +jobs: Chan(Job), body: String, +json: Bool) -> IO(Resp):
  Bool.pick(IO(Resp), String.eq(path, "/upcheck"), Route.method(m, "GET", IO.pure(Resp, Resp.text(200, "OK"))),
  Bool.pick(IO(Resp), String.eq(path, "/api/v1/eth2/publicKeys"),
    Route.method(m, "GET", IO.pure(Resp, Resp{200, H.Http.json(), Ctx.pubkeys(ctx)})),
  Bool.pick(IO(Resp), String.starts_with(path, Route.sign_prefix()),
    Route.method(m, "POST", Sign.keyed(S.Hex.read_pubkey(String.drop(path, String.length(Route.sign_prefix()))), ctx, jobs, body, json)),
    IO.pure(Resp, Resp.text(404, "not found")))))

def Route.handle(+ctx: Ctx, +jobs: Chan(Job), r: H.HttpReq) -> IO(Resp):
  match r:
    case H.HttpReq{+m, t, v, hs, body}:
      Route.go(Route.path(t), m, ctx, jobs, body, H.Http.wants_json.of(H.Http.find(hs, "accept")))

def Conn.send_resp(r: Resp, close: Bool) -> String:
  match r:
    case Resp{status, ctype, body}:
      H.Http.response(status, ctype, body, close)

# have is the length of buf. The loop parses buf again only when it has
# the characters that the last parse was missing: parsing on each read
# costs time n^2 for a body of n characters.
@unsafe def Conn.loop(sock: Socket, +buf: String, +ctx: Ctx, +jobs: Chan(Job)) -> IO(Unit):
  Conn.parsed(sock, H.Http.parse(buf), buf, String.length(buf), ctx, jobs)

@unsafe def Conn.parsed(sock: Socket, p: H.Parse, +buf: String, +have: Nat, +ctx: Ctx, +jobs: Chan(Job)) -> IO(Unit):
  match p:
    case H.More{missing}:
      Conn.wait(sock, [buf], have, Nat.add(have, missing), ctx, jobs)
    case H.Bad{c, why}:
      do IO<Unit>:
        sent : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send(sock, H.Http.response(c, H.Http.text(), why, True{}))
        Conn.close(sent)
    case H.Got{+req, rest}:
      do IO<Unit>:
        resp : Resp <- Route.handle(ctx, jobs, req)
        +close : Bool = H.Http.closes(req)
        sent : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send(sock, Conn.send_resp(resp, close))
        Conn.after(close, sent, rest, ctx, jobs)

# parts holds the reads so far, the newest first. have is their total
# length, and need is the length that the next parse needs.
@unsafe def Conn.wait(sock: Socket, +parts: List<&2, String>, +have: Nat, +need: Nat, +ctx: Ctx, +jobs: Chan(Job)) -> IO(Unit):
  do IO<Unit>:
    rr : Socket & Result<&1, &1, U32 & String, Maybe<&1, String>> <- TCP.poll(sock, 65536, 60000)
    Conn.read(rr, parts, have, need, ctx, jobs)

@unsafe def Conn.close(sent: Socket & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (s, r) = sent
  Socket.close(s)

@unsafe def Conn.after(close: Bool, sent: Socket & Result<&1, &1, U32 & String, Unit>, +rest: String, +ctx: Ctx, +jobs: Chan(Job)) -> IO(Unit):
  match close:
    case True{}:
      Conn.close(sent)
    case False{}:
      Conn.keep(sent, rest, ctx, jobs)

@unsafe def Conn.keep(sent: Socket & Result<&1, &1, U32 & String, Unit>, +rest: String, +ctx: Ctx, +jobs: Chan(Job)) -> IO(Unit):
  (s, r) = sent
  match r:
    case Fail{e}:
      Socket.close(s)
    case Done{u}:
      Conn.loop(s, rest, ctx, jobs)

def Conn.join(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{h, t}:
      h ++ Conn.join(t)

@unsafe def Conn.next(short: Bool, s: Socket, +parts: List<&2, String>, +have: Nat, +need: Nat, +ctx: Ctx, +jobs: Chan(Job)) -> IO(Unit):
  match short:
    case True{}:
      Conn.wait(s, parts, have, need, ctx, jobs)
    case False{}:
      Conn.loop(s, Conn.join(List.reverse(&2, String, parts)), ctx, jobs)

# An empty read is the end of the stream.
@unsafe def Conn.got(eof: Bool, s: Socket, +parts: List<&2, String>, +have: Nat, +need: Nat, +ctx: Ctx, +jobs: Chan(Job)) -> IO(Unit):
  match eof:
    case True{}:
      Socket.close(s)
    case False{}:
      Conn.next(Nat.is_lt(have, need), s, parts, have, need, ctx, jobs)

@unsafe def Conn.read(rr: Socket & Result<&1, &1, U32 & String, Maybe<&1, String>>, +parts: List<&2, String>, +have: Nat, +need: Nat, +ctx: Ctx, +jobs: Chan(Job)) -> IO(Unit):
  (s, r) = rr
  match r:
    case Fail{e}:
      Socket.close(s)
    case Done{m}:
      match m:
        case None{}:
          Socket.close(s)
        case Some{+data}:
          Conn.got(String.is_empty(data), s, Con{data, parts}, Nat.add(have, String.length(data)), need, ctx, jobs)

@unsafe def Accept.loop(l: Listener, +ctx: Ctx, +jobs: Chan(Job)) -> IO(Unit):
  do IO<Unit>:
    r : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
    Accept.next(r, ctx, jobs)

@unsafe def Accept.next(r: Listener & Result<&1, &1, U32 & String, Socket>, +ctx: Ctx, +jobs: Chan(Job)) -> IO(Unit):
  (l, res) = r
  match res:
    case Fail{e}:
      Accept.loop(l, ctx, jobs)
    case Done{sock}:
      do IO<Unit>:
        IO.spawn(Unit, Conn.loop(sock, "", ctx, jobs))
        Accept.loop(l, ctx, jobs)

# Start
# =====

def Main.run(c: Config) -> IO(Unit):
  match c:
    case Config{net, kdir, lpath, +host, +port}:
      do IO<Unit>:
        +dir : String <- Config.need(String, kdir, "--key-config-path is required")
        +path : String <- Config.need(String, lpath, "--slashing-log is required")
        n : R.Net <- Config.net(net)
        +ks : List<&2, K.Loaded> <- K.Keys.load_dir(dir)
        store : St.Store <- Start.store(path)
        +jobs : Chan(Job) <- Chan.new(Job, 4096)
        IO.spawn(Unit, Core.loop(jobs, path, store))
        l : Listener <- K.Load.ctx(Listener, host, F.Net.listen(host, port))
        IO.print("bulkhead: " ++ Nat.show(List.length(&2, K.Loaded, ks)) ++ " keys, listening on "
          ++ host ++ ":" ++ U32.show(port))
        Accept.loop(l, Ctx{ks, Keys.json(ks), n}, jobs)
def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    c : Config <- Config.need(Config, Config.parse(args, Config.default()), "invalid arguments")
    Main.run(c)

