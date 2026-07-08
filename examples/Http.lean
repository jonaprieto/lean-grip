/-
Copyright 2026 Jonathan Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grip

/-!
# Grip.Examples.Http -- an HTTP/1.1 request-line and header parser

Parses the start-line and header block of an HTTP request into a record:

```
<request> ::= <method> SP <target> SP "HTTP/" <version> CRLF <header>*
<header>  ::= <name> ":" <ows> <value> CRLF
```

This example uses the ergonomic `Parser` (ungraded) face with `do`-notation for the
request line, and the graded `GParser.many` for the header list -- `many` demands an
always-consuming element, which a header (a non-empty name token first) satisfies, so
`many header` is well-typed. `capture` pulls each field out as a `String`.

The body and the terminating blank line are out of scope; this parses through the last
header. (ponytail: header folding / obs-text and chunked bodies are omitted -- add them
when a real transport needs them.)
-/

namespace Grip.Examples.Http

open Grip

/-- A parsed HTTP request start-line plus headers. -/
structure Request where
  /-- The request method, e.g. `GET`. -/
  method : String
  /-- The request target, e.g. `/index.html`. -/
  target : String
  /-- The HTTP version string after `HTTP/`, e.g. `1.1`. -/
  version : String
  /-- The header fields, in order, as `(name, value)` pairs. -/
  headers : List (String × String)
  deriving BEq, Repr

/-- A header-name byte: a visible ASCII character (excludes space, DEL, and non-ASCII)
that is not the `:` separator. -/
@[inline] private def isNameByte (b : UInt8) : Bool :=
  b > Ascii.space && b < 127 && b != Ascii.colon

/-- A version byte: digit or dot. -/
@[inline] private def isVersionByte (b : UInt8) : Bool :=
  Ascii.isDigit b || b == Ascii.dot

/-- Optional whitespace: space or tab only (no line breaks). -/
@[inline] private def ows : GParser flexible Nat :=
  GParser.takeWhile Ascii.isBlank

/-- Carriage-return / line-feed. -/
@[inline] private def crlf : GParser conditional Unit :=
  GParser.seqR (GParser.byte Ascii.cr) (GParser.byte Ascii.lf)

/-- One header line, as `(name, value)`; always consumes (the name is non-empty). -/
private def header : GParser conditional (String × String) :=
  GParser.map2 (·, ·)
    (GParser.capture (GParser.takeWhile1 isNameByte))          -- field name
    (GParser.seqR (GParser.byte Ascii.colon)                   -- ':'
      (GParser.seqR ows
        (GParser.seqL (GParser.capture (GParser.takeWhile (· != Ascii.cr)))  -- value up to CR
          crlf)))

-- Request-line fields, weakened to the ungraded `Parser` face so the `do`-block below
-- binds them directly. `weakenFallible` makes the graded-to-`Parser` step explicit
-- (the same bridge `Grip.Examples.Json` uses).
private def methodP : Parser String :=
  GParser.weakenFallible (GParser.capture (GParser.takeWhile1 Ascii.isUpper))
private def spP : Parser Unit := GParser.weakenFallible (GParser.byte Ascii.space)
private def slashP : Parser Unit := GParser.weakenFallible (GParser.string "HTTP/")
private def targetP : Parser String :=
  GParser.weakenFallible (GParser.capture (GParser.takeWhile1 (· != Ascii.space)))
private def versionP : Parser String :=
  GParser.weakenFallible (GParser.capture (GParser.takeWhile1 isVersionByte))
private def crlfP : Parser Unit := GParser.weakenFallible crlf
private def headersP : Parser (List (String × String)) :=
  GParser.weakenFallible (GParser.many header)

/-- Parse a request start-line and its header block. -/
def request : Parser Request := do
  let method ← methodP
  let _ ← spP
  let target ← targetP
  let _ ← spP
  let _ ← slashP
  let version ← versionP
  let _ ← crlfP
  let headers ← headersP
  return { method, target, version, headers }

/-- Parse an HTTP request from `arr`, or `none` on failure. -/
@[inline] def parse (arr : ByteArray) : Option Request := GParser.run? request arr

-- Acceptance guards -------------------------------------------------------

#guard parse "GET / HTTP/1.1\r\n\r\n".toUTF8
        == some { method := "GET", target := "/", version := "1.1", headers := [] }

#guard parse "GET /index.html HTTP/1.1\r\nHost: example.com\r\n\r\n".toUTF8
        == some { method := "GET", target := "/index.html", version := "1.1",
                  headers := [("Host", "example.com")] }

#guard parse "POST /api HTTP/1.0\r\nContent-Type: application/json\r\nAccept: */*\r\n\r\n".toUTF8
        == some { method := "POST", target := "/api", version := "1.0",
                  headers := [("Content-Type", "application/json"), ("Accept", "*/*")] }

-- Malformed: missing the space after the method.
#guard parse "GET/ HTTP/1.1\r\n".toUTF8 == none

end Grip.Examples.Http
