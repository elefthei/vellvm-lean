/-
Copyright (c) 2012 Raphaël Proust <raphlalou@gmail.com>
Copyright (c) 2012 INRIA - Raphaël Proust <raphlalou@gmail.com>
Copyright (c) 2012 ENS - Raphaël Proust <raphlalou@gmail.com>
Copyright (c) 2014 OCamlPro - Julien Sagot <ju.sagot@gmail.com>
Copyright (c) 2026 U. Penn. Steve Zdancewic <stevez@cis.upenn.edu>

Permission to use, copy, modify, and distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
Adapted for use in Vellvm by Steve Zdancewic (c) 2017.
-/
module

public import Vellvm.Frontend.Lexer

public section
namespace Vellvm.Frontend
open Vellvm.Syntax.LLVMAst

inductive ParseErrorKind where
  | syntaxError | failure (message : String) | invalidAnonymousId (message : String)
  | zeroWidthAssertion
  deriving Inhabited

structure ParseError where
  filename : IRString
  position : Position
  lexeme : IRString
  kind : ParseErrorKind
  deriving Inhabited

inductive EntryPoint where
  | toplevel_entities | test_call | texp | metadata_id
  deriving BEq

/-- `llvm_lexer.mll` wraps failures differently at the file and assertion entry points.
The token text can be arbitrary bytes. `IO.parse_file` adds its own filename prefix. -/
def ParseError.message (e : ParseError) (entry : EntryPoint) : ByteArray :=
  let message := match e.kind with
    | .syntaxError => if entry == .test_call then "Parsing Error Encountered" else "Error token encountered"
    | .failure m => "Failure: " ++ m
    | .invalidAnonymousId m => m
    | .zeroWidthAssertion => "Camlcoq.ml:73: assertion failed"
  match e.kind with
  | .invalidAnonymousId _ | .zeroWidthAssertion => message.toUTF8
  | .failure m => if entry != .toplevel_entities then m.toUTF8 else formatted message
  | .syntaxError => formatted message
where
  formatted (message : String) : ByteArray :=
    s!"Parsing error: line {e.position.line}, column {e.position.column}, token '".toUTF8 ++
      e.lexeme ++ "': ".toUTF8 ++ message.toUTF8 ++ " ".toUTF8

namespace Parser

structure Cursor where
  lexer : Lexer
  /-- At most two pending tokens; `lexer` is just past the last one. -/
  pending : List LocatedToken := []
  lastStart : Position
  lastEnd : Position
  anon : Int := 0
  voidCount : Nat := 0

abbrev P := StateT Cursor (Except ParseError)

private def readNext : P LocatedToken := do
  let s ← get
  match s.lexer.next with
  | .ok (t, l) => set { s with lexer := l }; return t
  | .error e => throw ⟨e.filename, e.startPos, e.lexeme, match e.kind with
      | .failure m => .failure m | .zeroWidthAssertion => .zeroWidthAssertion⟩

private def front : P LocatedToken := do
  if let t :: _ := (← get).pending then return t
  let t ← readNext
  modify fun s ↦ { s with pending := [t] }
  return t

def peek : P Token := return (← front).token

def peekNext : P Token := do
  let t ← front
  if let _ :: u :: _ := (← get).pending then return u.token
  let u ← readNext
  modify fun s ↦ { s with pending := [t, u] }
  return u.token

def pop : P Token := do
  let t ← front
  modify fun s ↦ { s with pending := s.pending.drop 1, lastStart := t.startPos, lastEnd := t.endPos }
  return t.token

def startPos : P Position := return (← front).startPos

def fileMetadata (start : Position) : P (metadata typ) := do
  let s ← get
  return .METADATA_File_info ⟨s.lexer.filename, start.line, start.column, s.lastEnd.line, s.lastEnd.column⟩

private def raiseAt (k : ParseErrorKind) (first last : Position) : P α := do
  let l := (← get).lexer
  throw ⟨l.filename, first, l.input.extract first.offset last.offset, k⟩

def syntaxError : P α := do
  let t ← front
  raiseAt .syntaxError t.startPos t.endPos

def failure (message : String) : P α := do
  let s ← get
  raiseAt (.failure message) s.lexer.lastStart s.lexer.pos

def isFixed : Token → FixedToken → Bool
  | .fixed a, b => a == b
  | _, _ => false

def eat (k : FixedToken) : P Bool := do
  if isFixed (← peek) k then discard pop; return true
  return false

def expect (k : FixedToken) : P Unit := do
  unless ← eat k do syntaxError

def parseInteger : P int_syntax := do
  let .INTEGER n ← peek | syntaxError
  discard pop; return n

def parseString : P IRString := do
  let .STRING s ← peek | syntaxError
  discard pop; return s

def rawId : LexedId → raw_id
  | .Named s => .Name s
  | .Anonymous n => .Anon n

def localId : P raw_id := do
  let .LOCAL i ← peek | syntaxError
  discard pop; return rawId i

def globalId : P raw_id := do
  let .GLOBAL i ← peek | syntaxError
  discard pop; return rawId i

def quoteBytes (s : IRString) : IRString := (ByteArray.empty.push 34 ++ s).push 34

def withParens (p : P α) : P α := do expect .LPAREN; let a ← p; expect .RPAREN; return a

def parseSep1 (p : P α) : P (List α) := do
  let mut rev := [← p]
  while ← eat .COMMA do rev := (← p) :: rev
  return rev.reverse

def parseSep (close : FixedToken) (p : P α) : P (List α) := do
  if ← eat close then return []
  let xs ← parseSep1 p
  expect close
  return xs

private def machineInt (z : Int) : Int := (z + 2^62) % (2^63) - 2^62

/-- OCaml's 63-bit `int_of_string`, shared by numeric block labels and debugger input. -/
def ocamlInt? (s : ByteArray) : Option Int := do
  let first ← s[0]?
  let neg := first == 45
  let start := if neg || first == 43 then 1 else 0
  let mut i := start
  let mut base := 10
  let mut unsigned := false
  if s[i]? == some 48 then
    match (s[i+1]? : Option UInt8) with
    | some 120 | some 88 => base := 16; unsigned := true
    | some 111 | some 79 => base := 8; unsigned := true
    | some 98 | some 66 => base := 2; unsigned := true
    | some 117 | some 85 => unsigned := true
    | _ => pure ()
    if unsigned then i := i + 2
  let digits := i
  let limit := if unsigned then 2^63 - 1 else if neg then 2^62 else 2^62 - 1
  let mut n := 0
  for j in [i:s.size] do
    let c := s[j]!.toNat
    if c == 95 && j > digits then continue
    let d := if 48 ≤ c && c ≤ 57 then c - 48 else if 65 ≤ c && c ≤ 70 then c - 55
      else if 97 ≤ c && c ≤ 102 then c - 87 else 16
    guard (d < base)
    n := n * base + d
    guard (n ≤ limit)
  guard (digits < s.size)
  return machineInt (if neg then -(Int.ofNat n) else Int.ofNat n)

private def boundNumber (n : Int) (atPos : Position) : P raw_id := do
  let s ← get
  if s.anon > n then
    let msg := s!"Unexpected sequential id: expected >= {s.anon % (2^63)} but found {n % (2^63)}"
    throw ⟨s.lexer.filename, atPos, .empty, .invalidAnonymousId msg⟩
  set { s with anon := machineInt (n+1) }
  return .Anon n

def boundId (id : Option LexedId) (atPos : Position) : P raw_id := do
  match id with
  | some (.Named s) => return .Name s
  | some (.Anonymous n) => boundNumber n atPos
  | none => boundNumber (← get).anon atPos

def boundLabel (label : Option IRString) (atPos : Position) : P raw_id := do
  match label with
  | none => boundId none atPos
  | some l => match ocamlInt? l with
    | some n => boundNumber n atPos
    | none => return .Name l

def voidId : P instr_id := do
  let s ← get
  set { s with voidCount := s.voidCount + 1 }
  return .IVoid s.voidCount

private def hexNibble : Nat → Hexadecimal.uint → Hexadecimal.uint
  | 0 => .D0 | 1 => .D1 | 2 => .D2 | 3 => .D3 | 4 => .D4 | 5 => .D5 | 6 => .D6 | 7 => .D7
  | 8 => .D8 | 9 => .D9 | 10 => .Da | 11 => .Db | 12 => .Dc | 13 => .Dd | 14 => .De | _ => .Df

def byteToI8 (b : UInt8) : texp typ :=
  (.TYPE_I ⟨8, by decide⟩, .EXP_Integer (.IntHexadecimal (.Pos
    (hexNibble (b.toNat / 16) (hexNibble (b.toNat % 16) .Nil)))))

def i8ToByte : texp typ → Except String UInt8
  | (.TYPE_I sz, .EXP_Integer (.IntHexadecimal (.Pos u))) => do
    unless sz.val == 8 do throw "i8_to_byte failed with non-byte type annotation"
    -- OCaml first wraps through int64, then through its signed 63-bit machine int.
    let n := u.toNat % (2 ^ 63)
    unless n < 256 do throw "Char.chr"
    return n.toUInt8
  | _ => .error "i8_to_byte failed with incorrect type/value"

/-- Run a start production with its lexer histogram; partial entry points need not request EOF. -/
def run (p : P α) (l : Lexer) : Except ParseError (α × Histogram) := do
  let (a, s) ← p.run { lexer := l, lastStart := l.pos, lastEnd := l.pos }
  return (a, s.lexer.histogram)

end Parser
end Vellvm.Frontend
