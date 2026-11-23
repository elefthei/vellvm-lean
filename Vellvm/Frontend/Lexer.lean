/-
Copyright (c) 2012 Raphaël Proust <raphlalou@gmail.com>
Copyright (c) 2012 INRIA - Raphaël Proust <raphlalou@gmail.com>
Copyright (c) 2012 ENS - Raphaël Proust <raphlalou@gmail.com>

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

public import Vellvm.Frontend.Token
public import Std.Data.HashMap

public section
namespace Vellvm.Frontend
open Vellvm.Syntax.LLVMAst

inductive LexErrorKind where
  | failure (message : String)
  | zeroWidthAssertion
  deriving Inhabited

structure LexError where
  filename : IRString
  /-- Actual offending byte, or the end of input. -/
  position : Position
  /-- OCamllex retains the previous successful position on an unmatched byte. -/
  startPos : Position
  lexeme : ByteArray
  kind : LexErrorKind
  deriving Inhabited

abbrev Histogram := Std.HashMap String Nat

/-- Rows are unordered in the oracle. The output driver adds the final newline. -/
def histogramText (histogram : Histogram) : String :=
  String.intercalate "\n" (histogram.toList.map fun (word, n) ↦ s!"{word}, {n}")

structure Lexer where
  input : ByteArray
  filename : IRString
  pos : Position
  lastStart : Position
  histogram : Histogram := {}
  deriving Inhabited

def Lexer.init (input filename : ByteArray) (line : Nat := 1) : Lexer :=
  { input, filename, pos := { line }, lastStart := {} }

private abbrev Code := Nat

/-- Sentinel 256 is not a byte, so it never matches a byte class, even in binary input. -/
private def byte (s : ByteArray) (i : Nat) : Code :=
  if h : i < s.size then s[i].toNat else 256

private def digit (c : Code) := 48 ≤ c && c ≤ 57
private def hex (c : Code) := digit c || (65 ≤ c && c ≤ 70) || (97 ≤ c && c ≤ 102)
private def hexValue (c : Code) := if c ≤ 57 then c - 48 else if c ≤ 70 then c - 55 else c - 87
private def alpha (c : Code) := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)
private def alnum (c : Code) := digit c || alpha c
private def kwChar (c : Code) := alnum c || c == 36 || c == 46 || c == 95
private def idChar (c : Code) := kwChar c || c == 45
private def ws (c : Code) := c == 32 || c == 9
private def eol (c : Code) := c == 13 || c == 10
private def sign (c : Code) := c == 43 || c == 45

private def scan (s : ByteArray) (i : Nat) (p : Code → Bool) : Nat :=
  if h : i < s.size then
    if p s[i].toNat then scan s (i+1) p else i
  else i
termination_by s.size - i

private def Position.atOffset (p : Position) (i : Nat) : Position :=
  { p with offset := i, column := p.column + (i - p.offset) }

private def Lexer.advance (l : Lexer) (i : Nat) : Lexer :=
  { l with lastStart := l.pos, pos := l.pos.atOffset i }

private def eolEnd (s : ByteArray) (i : Nat) : Nat :=
  let a := byte s i
  let b := byte s (i+1)
  if eol b && a != b then i+2 else i+1

private def Lexer.newline (l : Lexer) : Lexer :=
  { l with lastStart := l.pos, pos := ⟨eolEnd l.input l.pos.offset, l.pos.line+1, 0⟩ }

private def Lexer.emit (l : Lexer) (i : Nat) (t : Token) : LocatedToken × Lexer :=
  let l := l.advance i
  (⟨t, l.lastStart, l.pos⟩, l)

private def Lexer.emptyMatch (l : Lexer) : LexError :=
  ⟨l.filename, l.pos, l.lastStart, .empty, .failure "lexing: empty token"⟩

private def Lexer.badToken (l : Lexer) (i : Nat) (k : LexErrorKind) : LexError :=
  ⟨l.filename, l.pos, l.pos, l.input.extract l.pos.offset i, k⟩

private def compareWord (s : ByteArray) (start stop : Nat) (word : String) : Ordering :=
  Id.run do
    for n in [:min (stop-start) word.utf8ByteSize] do
      let p := String.Pos.Raw.mk n
      if h : p < word.rawEndPos then
        let o := compare (byte s (start+n)) (word.getUTF8Byte p h).toNat
        if o != .eq then return o
    return compare (stop-start) word.utf8ByteSize

/-- Search the generated sorted table without copying a candidate lexeme. -/
private def lookupWord (s : ByteArray) (start stop : Nat) (table : Array (String × FixedToken)) :
    Option (String × FixedToken) := loop 0 table.size
where
  loop (lo hi : Nat) :=
    if h : lo < hi then
      let mid := (lo+hi)/2
      let entry := table[mid]!
      match compareWord s start stop entry.1 with
      | .eq => some entry
      | .lt => loop lo mid
      | .gt => loop (mid+1) hi
    else none
  termination_by hi-lo
  decreasing_by all_goals omega

private def decDigits (s : ByteArray) (lo hi : Nat) : Decimal.uint :=
  (hi-lo).fold (fun n _ rest ↦
    match byte s (hi-1-n) with
    | 48 => .D0 rest | 49 => .D1 rest | 50 => .D2 rest | 51 => .D3 rest
    | 52 => .D4 rest | 53 => .D5 rest | 54 => .D6 rest | 55 => .D7 rest
    | 56 => .D8 rest | _ => .D9 rest) .Nil

private def hexDigits (s : ByteArray) (lo hi : Nat) : Hexadecimal.uint :=
  (hi-lo).fold (fun n _ rest ↦
    match hexValue (byte s (hi-1-n)) with
    | 0 => .D0 rest | 1 => .D1 rest | 2 => .D2 rest | 3 => .D3 rest
    | 4 => .D4 rest | 5 => .D5 rest | 6 => .D6 rest | 7 => .D7 rest
    | 8 => .D8 rest | 9 => .D9 rest | 10 => .Da rest | 11 => .Db rest
    | 12 => .Dc rest | 13 => .Dd rest | 14 => .De rest | _ => .Df rest) .Nil

private def signedDigits (s : ByteArray) (neg : Bool) (lo hi : Nat) : Decimal.int :=
  let digits := decDigits s lo hi
  if neg then .Neg digits else .Pos digits

/-- Only IDs and type widths pass through the pinned 64-bit OCaml `int_of_string`. -/
private def machineNat (l : Lexer) (lo hi : Nat) : Except LexError Nat := do
  let mut n := 0
  for i in [lo:hi] do
    n := n * 10 + (byte l.input i - 48)
    if n > 4611686018427387903 then throw (l.badToken hi (.failure "int_of_string"))
  return n

/-- LLVM c-string semantic action; ordinary STRING and quoted identifiers keep their escapes. -/
def unescape (s : ByteArray) : ByteArray := Id.run do
  let first := scan s 0 (· != 92)
  if first == s.size then return s
  let mut out := s.extract 0 first
  let mut i := first
  repeat
    if i >= s.size then return out
    let c := byte s i
    if c == 92 then
      let a := byte s (i+1)
      if a == 92 then
        out := out.push 92
        i := i+2
        continue
      let b := byte s (i+2)
      if hex a && hex b then
        out := out.push (hexValue a * 16 + hexValue b).toUInt8
        i := i+3
        continue
    out := out.push c.toUInt8
    i := i+1
  return out

/-- Inverse byte spelling used by the LLVM printer; hex digits in escapes are uppercase. -/
def escape (s : ByteArray) : ByteArray := Id.run do
  let needsEscape := fun c : Code ↦ c < 32 || c >= 127 || c == 34 || c == 92
  let first := scan s 0 (! needsEscape ·)
  if first == s.size then return s
  let mut out := s.extract 0 first
  for i in [first:s.size] do
    let c := byte s i
    let nibble := fun d : Nat ↦ (if d < 10 then d+48 else d+55).toUInt8
    if c == 92 then out := (out.push 92).push 92
    else if needsEscape c then out := ((out.push 92).push (nibble (c/16))).push (nibble (c%16))
    else out := out.push c.toUInt8
  return out

private def quoted (l : Lexer) (id : Bool) : Except LexError (ByteArray × Lexer) := do
  let start := l.pos.offset
  let stop := scan l.input (start+1) (· != 34)
  -- The string sublexer consumes *all* bytes except quote, without a Lexing.new_line action.
  let atQuote := (l.advance (stop-1)).advance stop
  if stop == l.input.size then throw atQuote.emptyMatch
  let text := if id then l.input.extract start (stop+1) else l.input.extract (start+1) stop
  return (text, atQuote.advance (stop+1))

private def lexId (l : Lexer) : Except LexError (LexedId × Lexer) := do
  let start := l.pos.offset
  let c := byte l.input start
  if c == 34 then
    let (name, l) ← quoted l true
    return (.Named name, l)
  if digit c then
    let stop := scan l.input (start+1) digit
    return (.Anonymous (← machineNat l start stop), l.advance stop)
  if idChar c then
    let stop := scan l.input (start+1) idChar
    return (.Named (l.input.extract start stop), l.advance stop)
  throw l.emptyMatch

/-- Scan the bodies discarded by `#dbg`/module summaries and retained verbatim by `!DI`.
The upstream sublexers count parentheses even inside quotes, and silently accept EOF. -/
private def balanced (l : Lexer) : Lexer := Id.run do
  let mut l := l
  let mut depth := 1
  repeat
    let i := l.pos.offset
    let c := byte l.input i
    if c == 256 || (c == 41 && depth == 1) then return l
    if c == 40 then
      depth := depth+1
      l := l.advance (i+1)
    else if c == 41 then
      depth := depth-1
      l := l.advance (i+1)
    else if eol c then l := l.newline
    else l := l.advance (scan l.input (i+1) (fun b ↦ !eol b && b != 40 && b != 41))
  return l

private def skipGroup (l : Lexer) : Lexer :=
  let r := balanced l
  if r.pos.offset < r.input.size then r.advance (r.pos.offset+1) else r

private def skipTrivia (lexer : Lexer) : Lexer := Id.run do
  let mut l := lexer
  repeat
    let s := l.input
    let i := l.pos.offset
    let c := byte s i
    if ws c then l := l.advance (scan s (i+1) ws)
    else if eol c then l := l.newline
    else if c == 59 then -- comment
      let nl := scan s (i+1) (!eol ·)
      l := l.advance nl
      if nl != s.size then l := l.newline
    else if c == 35 && byte s (i+1) == 100 && byte s (i+2) == 98 && byte s (i+3) == 103 then
      let stop := scan s (i+4) kwChar
      if byte s stop != 40 then return l
      l := skipGroup (l.advance (stop+1))
    else if c == 94 then -- ^...=...: summary
      let field := fun b ↦ alnum b || ws b
      let eqPos := scan s (i+1) field
      if byte s eqPos != 61 then return l
      let colon := scan s (eqPos+1) field
      if byte s colon != 58 then return l
      let stop := scan s (colon+1) (fun b ↦ !eol b && b != 40)
      if stop == s.size then return l.advance stop
      if byte s stop == 40 then l := skipGroup (l.advance (stop+1))
      -- gobble_module's unparenthesized eol branch intentionally omits Lexing.new_line.
      else l := (l.advance stop).advance (eolEnd s stop)
    else return l
  return l

private def hexFormat : Code → float_hex_type × Nat
  | 75 => (.FH_K, 20) | 76 => (.FH_L, 32) | 77 => (.FH_M, 32)
  | 72 => (.FH_H, 4) | 82 => (.FH_R, 4) | _ => (.FH_X, 0)

private abbrev LexResult := Except LexError (LocatedToken × Lexer)

/-- Resolve overlaps by longest match, then source rule order (notably `i8`, `0x`, and `...`). -/
private def wordOrNumber (l : Lexer) : LexResult := do
  let s := l.input
  let i := l.pos.offset
  let c := byte s i
  let wordEnd := scan s i kwChar
  let labelEnd := if byte s wordEnd == 45 then scan s (wordEnd+1) idChar else wordEnd
  if labelEnd > i && byte s labelEnd == 58 then
    let t := match lookupWord s i labelEnd colonKeywordTable with
      | some (_, k) => Token.fixed k
      | none => .LABEL (s.extract i labelEnd)
    return l.emit (labelEnd+1) t
  if c == 46 && byte s (i+1) == 46 && byte s (i+2) == 46 && wordEnd == i+3 then
    return l.emit wordEnd (.fixed .DOTDOTDOT)
  if c == 105 || c == 98 then -- iN, bN
    let stop := scan s (i+1) digit
    if stop > i+1 && stop == wordEnd then
      let n ← machineNat l (i+1) stop
      if h : 0 < n then
        let w : Positive := ⟨n,h⟩
        return l.emit stop (if c == 105 then .I w else .B w)
      throw (l.badToken stop .zeroWidthAssertion)
  if (c == 115 || c == 117) && byte s (i+1) == 48 && byte s (i+2) == 120 then -- s0x, u0x
    let lo := i+3
    let stop := scan s lo hex
    if stop > lo && stop == wordEnd then
      let ds := hexDigits s lo stop
      return l.emit stop (.INTEGER (.IntHexadecimal (if c == 115 then .Neg ds else .Pos ds)))
  if c == 48 && byte s (i+1) == 120 then -- 0x[KLMHR]?
    let (tag, width) := hexFormat (byte s (i+2))
    let lo := if width == 0 then i+2 else i+3
    let stop := scan s lo hex
    if stop > lo && stop == wordEnd then
      if width != 0 && stop-lo != width then
        let ds := String.fromUTF8! (s.extract lo stop) -- scanned hex is ASCII
        throw (l.badToken stop (.failure ("got ill-sized hex literal: " ++ ds)))
      return l.emit stop (.FLOAT (.FS_hex tag (hexDigits s lo stop)))
  if digit c || sign c then
    let lo := if sign c then i+1 else i
    let whole := scan s lo digit
    if whole > lo then
      if byte s whole == 46 then
        let fracEnd := scan s (whole+1) digit
        let e := byte s fracEnd
        if e == 69 || e == 101 then
          let es := byte s (fracEnd+1)
          let expStart := if sign es then fracEnd+2 else fracEnd+1
          let expEnd := scan s expStart digit
          if expEnd > expStart && expEnd >= wordEnd then
            let d := Decimal.DecimalExp (signedDigits s (c == 45) lo whole)
              (decDigits s (whole+1) fracEnd) (signedDigits s (es == 45) expStart expEnd)
            return l.emit expEnd (.FLOAT (.FS_decimal d))
        if fracEnd >= wordEnd then
          let d := Decimal.Decimal (signedDigits s (c == 45) lo whole) (decDigits s (whole+1) fracEnd)
          return l.emit fracEnd (.FLOAT (.FS_decimal d))
      else if whole >= wordEnd then
        return l.emit whole (.INTEGER (.IntDecimal (signedDigits s (c == 45) lo whole)))
  if wordEnd > i then
    if let some (word, k) := lookupWord s i wordEnd keywordTable then
      let l := { l with histogram := l.histogram.alter word fun n ↦ some (n.getD 0 + 1) }
      return l.emit wordEnd (.fixed k)
    return l.emit wordEnd (.KW_UNKNOWN (s.extract i wordEnd))
  throw l.emptyMatch

/-- Consume a token on demand. Reaching EOF again returns an empty EOF at the same position. -/
def Lexer.next (lexer : Lexer) : Except LexError (LocatedToken × Lexer) := do
  let l := skipTrivia lexer
  let s := l.input
  let i := l.pos.offset
  let fixed := fun (k : FixedToken) ↦ l.emit (i+1) (.fixed k)
  match byte s i with
  | 256 => return l.emit i (.fixed .EOF)
  | 61 => return fixed .EQ
  | 44 => return fixed .COMMA
  | 40 => return fixed .LPAREN
  | 41 => return fixed .RPAREN
  | 123 => return fixed .LCURLY
  | 125 => if byte s (i+1) == 62 then return l.emit (i+2) (.fixed .RCURLYGT) else return fixed .RCURLY
  | 91 => return fixed .LSQUARE
  | 93 => return fixed .RSQUARE
  | 60 => if byte s (i+1) == 123 then return l.emit (i+2) (.fixed .LTLCURLY) else return fixed .LT
  | 62 => return fixed .GT
  | 58 => return fixed .COLON
  | 42 => return fixed .STAR
  | 64 | 37 =>
    let (id, r) ← lexId (l.advance (i+1))
    let t := if byte s i == 64 then Token.GLOBAL id else .LOCAL id
    return (⟨t, r.lastStart, r.pos⟩, r)
  | 34 =>
    let (text, r) ← quoted l false
    return (⟨.STRING text, r.lastStart, r.pos⟩, r)
  | 33 =>
    if byte s (i+1) == 68 && byte s (i+2) == 73 then
      let stop := scan s (i+3) kwChar
      if byte s stop == 40 then
        let r := balanced (l.advance (stop+1))
        let close := r.pos.offset
        if close == s.size then return r.emit close (.fixed .EOF)
        return r.emit (close+1) (.METADATA_DEBUG (s.extract (i+3) stop) (s.extract (stop+1) close))
    let c := byte s (i+1)
    if idChar c && !digit c then
      let stop := scan s (i+2) idChar
      return l.emit stop (.METADATA_NAME (s.extract (i+1) stop))
    return fixed .BANG
  | 35 =>
    let stop := scan s (i+1) digit
    if stop == i+1 then throw l.emptyMatch
    return l.emit stop (.ATTR_GRP_ID (Int.ofNat (← machineNat l (i+1) stop)))
  | _ => wordOrNumber l

end Vellvm.Frontend
