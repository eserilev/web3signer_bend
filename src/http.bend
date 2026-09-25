# HTTP/1.1 for the signer API: request framing, headers and responses. Pure
# code: src/main.bend does the socket I/O.
#
# Only ASCII requests are accepted. TCP.recv decodes bytes as UTF-8, so the
# length of a String is its byte length only for ASCII. A request with any
# other character gets 400, and the connection closes.
import Base

def Http.max_head() -> Nat:
  16384n

def Http.max_body() -> Nat:
  1048576n

def Http.cr() -> Char:
  Chr{13}

def Http.crlf() -> String:
  SCon{Chr{13}, SCon{Chr{10}, SNil{}}}

type Header is Data:
  Header{name: String, value: String}

type HttpReq is Data:
  HttpReq{method: String, target: String, version: String, headers: List<&2, Header>, body: String}

# More: the buffer has no complete request yet. Got: a request, and the
# bytes after it. Bad: the request is invalid; answer status and close.
type Parse is Data:
  More{}
  Got{req: HttpReq, rest: String}
  Bad{status: U32, reason: String}

# Text
# ====

def Http.ascii(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      match c:
        case Chr{x}:
          U32.is_lt(x, 128) && Http.ascii(t)

def Http.lower(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      SCon{Char.to_lower(c), Http.lower(t)}

def Http.is_space(+c: U32) -> Bool:
  U32.is_eq(c, 32) || U32.is_eq(c, 9)

def Http.trim_left(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          Bool.pick(String, Http.is_space(x), Http.trim_left(t), SCon{Chr{x}, t})

def Http.trim(s: String) -> String:
  String.reverse(Http.trim_left(String.reverse(Http.trim_left(s))))

# A string split at one separator character.
type Parts is Data:
  Parts{done: List<&2, String>, cur: String}

# A match, not Bool.pick, so that cur is reversed only at a separator:
# Bool.pick evaluates both of its values.
def Parts.at(is_sep: Bool, done: List<&2, String>, cur: String, +x: U32) -> Parts:
  match is_sep:
    case True{}:
      Parts{Con{String.reverse(cur), done}, ""}
    case False{}:
      Parts{done, SCon{Chr{x}, cur}}

def Parts.step(+sep: U32, st: Parts, c: Char) -> Parts:
  match st:
    case Parts{done, cur}:
      match c:
        case Chr{+x}:
          Parts.at(U32.is_eq(x, sep), done, cur, x)

def Parts.go(s: String, +sep: U32, st: Parts) -> Parts:
  match s:
    case SNil{}:
      st
    case SCon{c, t}:
      Parts.go(t, sep, Parts.step(sep, st, c))

def Parts.end(st: Parts) -> List<&2, String>:
  match st:
    case Parts{done, cur}:
      List.reverse(&2, String, Con{String.reverse(cur), done})

def Http.split(s: String, +sep: U32) -> List<&2, String>:
  Parts.end(Parts.go(s, sep, Parts{[], ""}))

# The text before the first CRLF CRLF, and the text after it.
type Head is Data:
  Head{head: String, rest: String}
  NoHead{}

# acc holds the head so far, in reverse. After the blank line, found is
# True and each character goes to rest, in reverse.
type HeadScan is Data:
  HeadScan{acc: String, found: Bool, rest: String}

def Http.blank_rev() -> String:
  SCon{Chr{10}, SCon{Chr{13}, SCon{Chr{10}, SCon{Chr{13}, SNil{}}}}}

def Http.head.check(+acc: String) -> HeadScan:
  HeadScan{acc, String.starts_with(acc, Http.blank_rev()), ""}

def Http.head.push(+acc: String, c: Char) -> HeadScan:
  Http.head.check(SCon{c, acc})

def Http.head.step(st: HeadScan, c: Char) -> HeadScan:
  match st:
    case HeadScan{acc, found, rest}:
      match found:
        case True{}:
          HeadScan{acc, True{}, SCon{c, rest}}
        case False{}:
          Http.head.push(acc, c)

def Http.head.go(s: String, st: HeadScan) -> HeadScan:
  match s:
    case SNil{}:
      st
    case SCon{c, t}:
      Http.head.go(t, Http.head.step(st, c))

def Http.head.end(st: HeadScan) -> Head:
  match st:
    case HeadScan{acc, found, rest}:
      match found:
        case True{}:
          Head{String.reverse(String.drop(acc, 4n)), String.reverse(rest)}
        case False{}:
          NoHead{}

def Http.head(s: String) -> Head:
  Http.head.end(Http.head.go(s, HeadScan{"", False{}, ""}))

# Headers
# =======

def Http.header.parts(ps: List<&2, String>) -> Maybe<&2, Header>:
  match ps:
    case Nil{}:
      None{}
    case Con{name, rest}:
      match rest:
        case Nil{}:
          None{}
        case Con{v, more}:
          Some{Header{Http.lower(Http.trim(name)), Http.trim(String.join(Con{v, more}, ":"))}}

def Http.header(line: String) -> Maybe<&2, Header>:
  Http.header.parts(Http.split(line, 58))

def Http.headers(ls: List<&2, String>, acc: List<&2, Header>) -> Maybe<&2, List<&2, Header>>:
  match ls:
    case Nil{}:
      Some{List.reverse(&2, Header, acc)}
    case Con{l, rest}:
      do Maybe<&2, List<&2, Header>>:
        h : Header <- Http.header(l)
        Http.headers(rest, Con{h, acc})

def Http.find(hs: List<&2, Header>, +name: String) -> Maybe<&2, String>:
  match hs:
    case Nil{}:
      None{}
    case Con{h, t}:
      match h:
        case Header{n, v}:
          Bool.pick(Maybe<&2, String>, String.eq(n, name), Some{v}, Http.find(t, name))

def Http.header_of(r: HttpReq, name: String) -> Maybe<&2, String>:
  match r:
    case HttpReq{m, t, v, hs, b}:
      Http.find(hs, name)

def Http.nat.cap(+n: Nat) -> Maybe<&2, Nat>:
  Bool.pick(Maybe<&2, Nat>, Nat.is_lt(Http.max_body(), n), None{}, Some{n})

def Http.nat.digit(ok: Bool, +x: U32, +n: Nat) -> Maybe<&2, Nat>:
  match ok:
    case False{}:
      None{}
    case True{}:
      Http.nat.cap(Nat.add(Nat.mul(n, 10n), U32.to_nat((x - 48 : U32))))

# Decimal digits only, as a Nat no larger than Http.max_body.
def Http.nat.step(acc: Maybe<&2, Nat>, c: Char) -> Maybe<&2, Nat>:
  match acc:
    case None{}:
      None{}
    case Some{+n}:
      match c:
        case Chr{+x}:
          Http.nat.digit(Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), x, n)

def Http.nat.go(s: String, acc: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      acc
    case SCon{c, t}:
      Http.nat.go(t, Http.nat.step(acc, c))

def Http.nat(s: String) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      None{}
    case SCon{c, t}:
      Http.nat.go(SCon{c, t}, Some{0n})

# Requests
# ========

def Http.body.ascii(ok: Bool, r: HttpReq, rest: String) -> Parse:
  match ok:
    case True{}:
      Got{r, rest}
    case False{}:
      Bad{400, "the request body is not ASCII"}

# The request after its head: take Content-Length bytes of body, if the
# buffer has them. Everything after the head must be ASCII first: with any
# other character, a String length is not a byte length.
def Http.body(+m: String, +t: String, +v: String, +hs: List<&2, Header>, +rest: String, cl: Maybe<&2, Nat>) -> Parse:
  match cl:
    case None{}:
      Bad{400, "invalid Content-Length"}
    case Some{+n}:
      Bool.pick(Parse, Bool.not(Http.ascii(rest)), Bad{400, "the request is not ASCII"},
      Bool.pick(Parse, Nat.is_lt(String.length(rest), n), More{},
        Http.body.ascii(Http.ascii(String.take(rest, n)), HttpReq{m, t, v, hs, String.take(rest, n)}, String.drop(rest, n))))

def Http.content_length(+hs: List<&2, Header>) -> Maybe<&2, Nat>:
  Maybe.default(&2, Maybe<&2, Nat>, Maybe.map(&2, String, Maybe<&2, Nat>, s => Http.nat(s), Http.find(hs, "content-length")), Some{0n})

def Http.chunked(+hs: List<&2, Header>) -> Bool:
  Maybe.is_some(&2, String, Http.find(hs, "transfer-encoding"))

def Http.with_headers(+m: String, +t: String, +v: String, hs: Maybe<&2, List<&2, Header>>, +rest: String) -> Parse:
  match hs:
    case None{}:
      Bad{400, "invalid header"}
    case Some{+h}:
      Bool.pick(Parse, Http.chunked(h), Bad{501, "Transfer-Encoding is not supported"},
        Http.body(m, t, v, h, rest, Http.content_length(h)))

def Http.strip_cr.rev(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          Bool.pick(String, U32.is_eq(x, 13), t, SCon{Chr{x}, t})

def Http.strip_cr(s: String) -> String:
  String.reverse(Http.strip_cr.rev(String.reverse(s)))

# Split at LF, then drop the CR at the end of each line.
def Http.lines.strip(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      []
    case Con{l, rest}:
      Con{Http.strip_cr(l), Http.lines.strip(rest)}

def Http.lines(head: String) -> List<&2, String>:
  Http.lines.strip(Http.split(head, 10))

def Http.from_request_line(ps: List<&2, String>, hs: List<&2, String>, +rest: String) -> Parse:
  match ps:
    case [+m, +t, +v]:
      Http.with_headers(m, t, v, Http.headers(hs, []), rest)
    case _:
      Bad{400, "invalid request line"}

def Http.from_lines(ls: List<&2, String>, +rest: String) -> Parse:
  match ls:
    case Nil{}:
      Bad{400, "empty request"}
    case Con{first, hs}:
      Http.from_request_line(Http.split(first, 32), hs, rest)

def Http.from_head(h: Head, +whole: String) -> Parse:
  match h:
    case NoHead{}:
      Bool.pick(Parse, Nat.is_lt(Http.max_head(), String.length(whole)), Bad{431, "the request head is too large"}, More{})
    case Head{+head, rest}:
      Bool.pick(Parse, Http.ascii(head), Http.from_lines(Http.lines(head), rest),
        Bad{400, "the request head is not ASCII"})

# Parses the first request in buf.
def Http.parse(+buf: String) -> Parse:
  Http.from_head(Http.head(buf), buf)

# The request wants the connection closed after the response.
def Http.closes(+r: HttpReq) -> Bool:
  match r:
    case HttpReq{m, t, +v, hs, b}:
      Bool.not(String.eq(v, "HTTP/1.1"))
        || String.eq(Http.lower(Maybe.default(&2, String, Http.find(hs, "connection"), "")), "close")

# Accept
# ======
#
# JSON if an Accept entry is application/json or */*; plain text otherwise.

def Http.accept_entry.first(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{h, t}:
      h

def Http.accept_entry(e: String) -> String:
  Http.lower(Http.trim(Http.accept_entry.first(Http.split(e, 59))))

def Http.accept_one(+e: String) -> Bool:
  String.eq(e, "application/json") || String.eq(e, "*/*")

def Http.accept_any(es: List<&2, String>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Con{e, t}:
      Http.accept_one(Http.accept_entry(e)) || Http.accept_any(t)

def Http.wants_json.of(a: Maybe<&2, String>) -> Bool:
  match a:
    case None{}:
      False{}
    case Some{v}:
      Http.accept_any(Http.split(v, 44))

# Responses
# =========

def Http.wants_json(r: HttpReq) -> Bool:
  match r:
    case HttpReq{m, t, v, hs, b}:
      Http.wants_json.of(Http.find(hs, "accept"))

def Http.reason(+status: U32) -> String:
  Bool.pick(String, U32.is_eq(status, 200), "OK",
  Bool.pick(String, U32.is_eq(status, 400), "Bad Request",
  Bool.pick(String, U32.is_eq(status, 404), "Not Found",
  Bool.pick(String, U32.is_eq(status, 405), "Method Not Allowed",
  Bool.pick(String, U32.is_eq(status, 412), "Precondition Failed",
  Bool.pick(String, U32.is_eq(status, 413), "Payload Too Large",
  Bool.pick(String, U32.is_eq(status, 431), "Request Header Fields Too Large",
  Bool.pick(String, U32.is_eq(status, 501), "Not Implemented",
    "Internal Server Error"))))))))

def Http.close_header(close: Bool) -> String:
  match close:
    case True{}:
      "Connection: close" ++ Http.crlf()
    case False{}:
      ""

def Http.response(+status: U32, ctype: String, +body: String, close: Bool) -> String:
  "HTTP/1.1 " ++ U32.show(status) ++ " " ++ Http.reason(status) ++ Http.crlf()
    ++ "Content-Type: " ++ ctype ++ Http.crlf()
    ++ "Content-Length: " ++ Nat.show(String.length(body)) ++ Http.crlf()
    ++ Http.close_header(close) ++ Http.crlf() ++ body

def Http.text() -> String:
  "text/plain; charset=utf-8"

def Http.json() -> String:
  "application/json; charset=utf-8"
