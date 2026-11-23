/-
 *                     Vellvm - the Verified LLVM project
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>
 *   Distributed under the GNU General Public License, version 3 or later.
-/
import Vellvm.Frontend.Driver
import Vellvm.Tree.Logged
import Vellvm.Semantics.LLVMEvents
import Vellvm.Semantics.TopLevel.Interpreter
import Vellvm.Semantics.DynamicValues.Show
import Vellvm.Semantics.Implementations.ParamsV
import Vellvm.Semantics.Implementations.IPtrInfinite
import Vellvm.Syntax.ReprAST

namespace Vellvm.CLI
open Frontend Platform Syntax Syntax.LLVMAst Syntax.RawIdMaps
open Tree Semantics Semantics.Interfaces.Params Semantics.DynamicValues
open Semantics.Implementations.IPtrInfinite Semantics.LLVMEvents Semantics.Instrumentation

abbrev P := @Implementations.ParamsV.ParamsV IPZ IPZTheory
attribute [local instance] P
abbrev Value := @dvalue P

inductive ExitCondition where
  | uninterpretedCall (message : IRString)
  | outOfMemory (loc : IRString)
  | undefinedBehavior (loc : IRString)
  | failed (loc : IRString)
  | llvmException (loc : IRString)
  | stuck (loc : IRString)

def ExitCondition.describe : ExitCondition → IRString
  | .uninterpretedCall m => "Uninterpreted Call: ".toUTF8 ++ m
  | .outOfMemory m => "Out Of Memory: ".toUTF8 ++ m
  | .undefinedBehavior m => "Undefined Behavior: ".toUTF8 ++ m
  | .failed m => "Failed: ".toUTF8 ++ m
  | .llvmException m => "LLVM Level Exception: ".toUTF8 ++ m
  | .stuck m => "Internal stuck state: ".toUTF8 ++ m

abbrev Result := Except ExitCondition Value

structure Frame where
  vars : rmap Value := RM.empty _
  exc : Option Value := none
  /-- The initial frame has no caller; a push can have a caller of unknown location. -/
  caller : Option (Option file_info) := none

def Frame.loc (frame : Frame) := frame.caller.map AstLib.location_string

structure Snapshot where
  loc : Option file_info := none
  globals : rmap Value := RM.empty _
  locals : rmap Value := RM.empty _
  frames : List Frame := [{}]

def location (snap : Snapshot) := AstLib.location_string snap.loc

def sameLocation (a b : Option file_info) : Bool :=
  withPtrEq a b (fun _ ↦ match a, b with
    | some x, some y => x.start_line == y.start_line && x.start_col == y.start_col &&
      x.end_line == y.end_line && x.end_col == y.end_col && x.filename == y.filename
    | none, none => true
    | _, _ => false) (by rintro rfl; cases a <;> simp)

private def writeNow (stream : IO.FS.Stream) (bytes : ByteArray) : IO Unit := do
  stream.write bytes
  stream.flush

private def update (snap : Snapshot) (debug : Bool) : TraceRequest → Action Snapshot
  | .setLoc loc => do
    let s := { snap with loc }
    if debug && !sameLocation loc snap.loc then writeNow (← IO.getStdout) ((location s).push 10)
    return s
  | .diagnostic bytes => do
    writeNow (← IO.getStdout) ((location snap ++ ": ".toUTF8 ++ bytes).push 10)
    return snap
  | .globals globals => pure { snap with globals }
  | .locals locals => pure { snap with locals }
  | .framePush vars exc =>
    pure { snap with frames := ⟨vars, exc, some snap.loc⟩ :: snap.frames }
  | .frameSet vars exc => do
    let f :: rest := snap.frames | fail "Empty stack, can't set"
    return { snap with frames := { f with vars, exc } :: rest }
  | .framePop => do
    let _ :: rest := snap.frames | fail "tl"
    return { snap with frames := rest }

/-- Keep the producer's transition function and current state. There is no tree unfolding or fuel. -/
structure Cursor (σ S : Type) where
  next : S → CTree.CTreeF (MCFGEbot ⊕ₑ Trace) NoChoice (Value × σ) S
  state : S
  snapshot : Snapshot

private def cursor {σ} (p : Logged MCFGEbot NoChoice (Value × σ)) : Cursor σ p.S :=
  ⟨p.next, p.initial, {}⟩

private def byteList (bs : List VellvmIntegers.int8) : ByteArray :=
  bs.foldl (fun out b ↦ out.push b.bits.toNat.toUInt8) .empty

def Cursor.singleStep (cur : Cursor σ S) (debug : Bool) : Action (Cursor σ S ⊕ Result) := do
  let advance := fun (s : S) ↦ Sum.inl { cur with state := s }
  let stop := fun e ↦ Sum.inr (.error e : Result)
  match cur.next cur.state with
  | .ret (v, _) => return .inr (.ok v)
  | .stuck => return stop (.stuck (location cur.snapshot))
  | .guard s | .step s => return advance s
  | .br b _ => nomatch b
  | .vis (.inr r) k =>
    let snapshot ← update cur.snapshot debug r
    return .inl { cur with state := k (), snapshot }
  | .vis (.inl (.inl (.ExternalCall ty _ args))) _ =>
    return stop (.uninterpretedCall (location cur.snapshot ++ ": Call with return type ".toUTF8 ++
      ReprAST.repr_dtyp ty ++ s!", {args.length} dvalues.".toUTF8))
  | .vis (.inl (.inl (.IO_stdout bs))) k =>
    writeNow (← IO.getStdout) (byteList bs)
    return advance (k ())
  | .vis (.inl (.inl (.IO_stderr bs))) k =>
    writeNow (← IO.getStderr) (byteList bs)
    return advance (k ())
  | .vis (.inl (.inr (.inl _))) _ => return stop (.outOfMemory (location cur.snapshot))
  | .vis (.inl (.inr (.inr (.inl _)))) _ => return stop (.llvmException (location cur.snapshot))
  | .vis (.inl (.inr (.inr (.inr (.inl _))))) _ =>
    return stop (.undefinedBehavior (location cur.snapshot))
  | .vis (.inl (.inr (.inr (.inr (.inr (.inl (.Debug _))))))) k =>
    if debug then writeNow (← IO.getStdout) (("DEBUG: ".toUTF8 ++ location cur.snapshot).push 10)
    return advance (k ())
  | .vis (.inl (.inr (.inr (.inr (.inr (.inr _)))))) _ =>
    return stop (.failed (location cur.snapshot))

def Cursor.run (cur : Cursor σ S) (debug : Bool)
    (saveLoc : Option (IO.Ref (Option file_info)) := none) : Action Result := do
  let mut cur := cur
  repeat
    match ← cur.singleStep debug with
    | .inl next => cur := next
    | .inr res =>
      if let some ref := saveLoc then ref.set cur.snapshot.loc
      return res

def withMain (argv : List IRString) (prog : Driver.Program)
    (drive : {σ S : Type} → Cursor σ S → Action α) : Action α :=
  drive (cursor (TopLevel.Worker.interpreter_param (M := Logged (Pa := P)) argv prog))

def runCall (lastLoc : IO.Ref (Option file_info)) (debug : Bool) (ty : DynamicTypes.dtyp)
    (entry : raw_id) (args : List (DynamicTypes.dtyp × Value)) (prog : Driver.Program) : Action Result := do
  let p := TopLevel.Worker.interpreter_gen (M := Logged (Pa := P)) ty entry (pure args) prog
  let cur := cursor p
  let loc ← lastLoc.get
  ({ cur with snapshot := { cur.snapshot with loc } }).run debug (some lastLoc)

end Vellvm.CLI
