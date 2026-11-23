/-
 *                     Vellvm - the Verified LLVM project
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>
 *   Distributed under the GNU General Public License, version 3 or later.
-/
import Vellvm.CLI.Run

namespace Vellvm.CLI
open Frontend Syntax Syntax.LLVMAst Syntax.RawIdMaps Semantics
attribute [local instance] P

private def helpText := "Vellvm Debugger Commands:  \n" ++
  "\t n : run until next breakpoint\n\t s : step\n\t c : continue\n\t q : quit\n" ++
  "\t pg : print global values\n\t pl : print local values\n\t pb : print breakpoints\n" ++
  "\t bt : print stack trace\n\t st : print stack trace\n" ++
  "\t rb n: remove breakpoint number n\n\t b n : add breakpoint with number n\n" ++
  "\t h : display this help message\n\n"

/-- `read_line` removes just LF. A byte read neither decodes filenames nor reads past a command. -/
private def readLine (input : IO.FS.Stream) : Platform.Action IRString := do
  let mut line := ByteArray.empty
  repeat
    let byte ← input.read 1
    let some c := byte[0]? | do
      if line.isEmpty then throw (.exception "End_of_file".toUTF8)
      return line
    if c == 10 then return line
    line := line.push c

private def readInt (input : IO.FS.Stream) : Platform.Action Int := do
  let some n := Parser.ocamlInt? (← readLine input) | Platform.fail "int_of_string"
  return n

private structure Breakpoint where
  id : Nat
  file : IRString
  line : Int

private structure Breakpoints where
  buckets : Array (List Breakpoint) := Array.replicate 16 []
  count : Nat := 0
  nextId : Nat := 0

/-- OCaml `Hashtbl.to_seq` visits buckets in index order, newest key first within a bucket.
Its hash of an integer mixes the tagged machine word, not the untagged breakpoint number. -/
private def bucketIndex (id size : Nat) : Nat :=
  let word := id.toUInt64 * 2 + 1
  let d := (word ^^^ (word >>> 32)).toUInt32 * 0xcc9e2d51
  let h := ((d <<< 15) ||| (d >>> 17)) * 0x1b873593
  let h := ((h <<< 13) ||| (h >>> 19)) * 5 + 0xe6546b64
  let h := (h ^^^ (h >>> 16)) * 0x85ebca6b
  let h := (h ^^^ (h >>> 13)) * 0xc2b2ae35
  ((h ^^^ (h >>> 16)) &&& 0x3fffffff).toNat &&& (size - 1)

private def Breakpoints.add (t : Breakpoints) (file : IRString) (line : Int) : Breakpoints := Id.run do
  let size := t.buckets.size
  let bp : Breakpoint := ⟨t.nextId, file, line⟩
  let mut buckets := t.buckets.modify (bucketIndex bp.id size) (bp :: ·)
  if t.count + 1 > 2 * size then
    let mut larger := Array.replicate (2 * size) []
    for bucket in buckets, i in [:size] do
      let (lo, hi) := bucket.partition fun b ↦ bucketIndex b.id (2 * size) == i
      larger := (larger.set! i lo).set! (i + size) hi
    buckets := larger
  return ⟨buckets, t.count + 1, t.nextId + 1⟩

private def Breakpoints.remove (t : Breakpoints) (id : Int) : Breakpoints := Id.run do
  if id < 0 then return t
  let i := bucketIndex id.toNat t.buckets.size
  let old := t.buckets[i]!
  unless old.any (fun bp ↦ bp.id == id.toNat) do return t
  return { t with buckets := t.buckets.set! i (old.eraseP (fun bp ↦ bp.id == id.toNat)),
                  count := t.count - 1 }

/-- Match the source's anchored `[file:line.col-line.col]` regexp on bytes. In Str, `$`
also matches immediately before LF. Convert the numbers only after the whole regexp matches. -/
private def atBreakpoint (t : Breakpoints) (snap : Snapshot) : Platform.Action Bool := do
  let text := location snap
  let some colon := text.findIdx? (· == 58) | return false
  let mut i := colon + 1
  let mut line := 0
  let mut overflow := false
  for sep in #[46, 45, 46, 93] do
    let start := i
    let mut n := 0
    while let some c := text[i]? do
      if c < 48 || c > 57 then break
      unless overflow do
        n := 10 * n + (c.toNat - 48)
        overflow := n >= 2^62
      i := i + 1
    if i == start || text[i]? != some sep then return false
    if start == colon + 1 then line := n
    i := i + 1
  if i != text.size && text[i]? != some 10 then return false
  if overflow then Platform.fail "int_of_string"
  let file := text.extract 1 colon
  return t.buckets.any fun bucket ↦ bucket.any fun bp ↦ bp.line == Int.ofNat line && bp.file == file

private inductive Motion where | step | next | cont deriving BEq

/-- `next` waits for the *same* stack depth, even when stepping out of the current frame.
`continue` checks for a breakpoint only at a location where `next` itself could stop. -/
private def advance (cur : Cursor σ S) (how : Motion) (bps : Breakpoints) :
    Platform.Action (Cursor σ S ⊕ Result) := do
  let depth := if how == .step then 0 else cur.snapshot.frames.length
  let mut cur := cur
  repeat
    let prev := cur.snapshot.loc
    match ← cur.singleStep true with
    | .inr res => return .inr res
    | .inl next =>
      cur := next
      if sameLocation prev next.snapshot.loc then continue
      if how == .step then return .inl next
      if next.snapshot.frames.length != depth then continue
      if how == .next then return .inl next
      if ← atBreakpoint bps next.snapshot then return .inl next

private def printVars (out : IO.FS.Stream) (vars : rmap Value) : IO Unit := do
  for (key, value) in RM.elements vars do
    out.write ((ShowAST.show_raw_id key ++ " -> ".toUTF8 ++ DynamicValues.show_dvalue value).push 10)

private def interact (cur : Cursor σ S) : Platform.Action Result := do
  let input ← IO.getStdin
  let out ← IO.getStdout
  let mut cur := cur
  let mut bps : Breakpoints := {}
  repeat
    out.putStr "(vellvm)> "
    out.flush
    let cmd := (String.fromUTF8? (← readLine input)).getD ""
    match cmd with
    | "n" | "s" | "c" =>
      let how := if cmd == "s" then Motion.step else if cmd == "n" then .next else .cont
      match ← advance cur how bps with
      | .inr res => return res
      | .inl next => cur := next
    | "q" => return .error (.failed "Quitting".toUTF8)
    | "pg" => printVars out cur.snapshot.globals
    | "pl" | "bt" | "st" =>
      let mut i := 0
      for frame in cur.snapshot.frames do
        let loc := frame.loc.getD "_".toUTF8
        if cmd == "pl" then
          out.write (s!"Stack frame #{i} (".toUTF8 ++ loc ++ "):\n".toUTF8)
          printVars out frame.vars
        else
          out.write ((s!"#{i}: ".toUTF8 ++ loc).push 10)
        i := i + 1
    | "b" =>
      let file ← readLine input
      let line ← readInt input
      out.putStr s!"Added breakpoint {bps.nextId}\n"
      bps := bps.add file line
    | "rb" => bps := bps.remove (← readInt input)
    | "pb" =>
      for bucket in bps.buckets do
        for bp in bucket do
          out.write (s!"{bp.id} -> ".toUTF8 ++ bp.file ++ s!":{bp.line}.-.\n".toUTF8)
    | "h" => out.putStr helpText
    | _ => out.putStr "Invalid command.\n"

def debugger (argv : List IRString) (prog : Driver.Program) : Platform.Action Result :=
  withMain argv prog fun cur ↦ interact cur

end Vellvm.CLI
