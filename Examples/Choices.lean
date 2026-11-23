import Vellvm.Frontend.Parser
import Vellvm.Semantics.Implementations.IPtrFinite
import Vellvm.Semantics.Implementations.IPtrInfinite
import Vellvm.Semantics.TopLevel.Interpreter
import Vellvm.Semantics.Operations.Freeze

namespace Examples.Choices
open ITree (Effect)
open Vellvm Vellvm.Tree Vellvm.Semantics Vellvm.Syntax.DynamicTypes
open Interfaces.Params Interfaces.IPtr Implementations.ParamsV Implementations.Memory
open Implementations.IPtrInfinite Implementations.IPtrFinite
open DynamicValues LLVMEvents InterpretationStack Utils.IntMaps

private abbrev width : Positive := ⟨8, by decide⟩
private abbrev i8 : dtyp := DTYPE_I width
private def byteVal [Params] (z : Int) : dvalue :=
  DVALUE_Base (DVALUE_I width (Numeric.Integers.repr z))

/-- Try the requested address against the entire interval, including its last byte. -/
private def atAddress (m : IntMap α) (n a : Nat) (k : Int) : Option {k // AllocationLegal m n a k} :=
  if h : 0 < k ∧ (a = 0 ∨ k % (a : Int) = 0) ∧
      ∀ j : Fin n, (lookup (k + (j.val : Int)) m).isNone = true then
    some ⟨k, h.1, h.2.1, by
      intro i hi hlt ⟨v, hv⟩
      have absent := h.2.2 ⟨i.toNat, by omega⟩
      change (lookup (k + (i.toNat : Int)) m).isNone = true at absent
      rw [Int.toNat_of_nonneg hi, (lookup_mapsTo _ _ _).mpr hv] at absent
      cases absent⟩
  else none

private abbrev Schedule (B : Effect) := (c : B.I) → IO (Option (B.O c))

section
variable [IP : IPtr] [T : IPtrTheory]

private def referenceAnswer (c : ChoiceRequest (@ParamsV IP T)) : (Choice ParamsV).O c :=
  ⟨c.reference, c.reference_legal rfl⟩

private def schedule (one := false) (address : Option Int := none) (skip : Nat := 0)
    (draws : Option (IO.Ref Nat) := none) : Schedule (Choice (@ParamsV IP T))
  | .draw dt v ok => do
    if let some count := draws then count.modify (· + 1)
    if one then
      if ht : dt = i8 then
        return some ⟨byteVal 1, by
          subst dt
          exact ⟨by simp [byteVal, i8, dvalue_is_canonical, dvalue_base_canonical,
                          dvalue_base_has_dtyp_base] <;> decide,
                 by simp [byteVal, dvalue_well_defined, dvalue_base_well_defined],
                 by simp [byteVal, allPointers]⟩⟩
    return some (referenceAnswer (.draw dt v ok))
  | .nextKey bytes n a => do
    if let some k := address then return atAddress bytes n a k
    return some (referenceAnswer (.nextKey bytes n a))
  | .fresh high => pure <| some ⟨Nat.succ (Nat.add high skip),
      Nat.lt_succ_of_le (Nat.le_add_right high skip)⟩
  | .exposed => pure (some ⟨none, rfl⟩)
end

private inductive Stop where
  | refused | oom | failure
  deriving BEq, Repr

/-- No fuel: consume one producer head and resume its stored state. -/
private def drive [Params] {B : Effect} (pick : Schedule B) (p : Producer MCFGEbot B X) :
    IO (Except Stop X) := do
  let mut s := p.initial
  repeat
    match p.next s with
    | .ret x => return .ok x
    | .guard s' | .step s' => s := s'
    | .stuck => throw (IO.userError "unexpected stuck producer")
    | .br c k =>
      let some a ← pick c | return .error .refused
      s := k a
    | .vis (.inl _) _ => throw (IO.userError "unexpected external call or IO")
    | .vis (.inr (.inl _)) _ => return .error .oom
    | .vis (.inr (.inr (.inl _))) _ => throw (IO.userError "unexpected LLVM exception")
    | .vis (.inr (.inr (.inr (.inl _)))) _ => throw (IO.userError "unexpected UB")
    | .vis (.inr (.inr (.inr (.inr (.inl (.Debug ())))))) k => s := k ()
    | .vis (.inr (.inr (.inr (.inr (.inr _))))) _ => return .error .failure

private def returned (label : String) : Except Stop X → IO X
  | .ok x => pure x
  | .error e => throw (IO.userError s!"{label}: unexpected {repr e}")

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

private def stopped (label : String) (expected : Stop) : Except Stop X → IO Unit
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly returned")
  | .error actual => check s!"{label}: expected {repr expected}, got {repr actual}" (actual == expected)

private def model [Pa : Params] (t : Producer MCFGEtop NoChoice X) (s : FusedS) :=
  InterpretationStack.Worker.interp_mcfgWith branchingChooser t s

section
variable [IP : IPtr] [T : IPtrTheory]

private def alloc (init : FusedS) (size align : Nat) :=
  model (LLVMEvents.Worker.alloca i8 size (some align)) init

private def checkAllocated (label : String) (addr : Int) (keys : List Int) (r : Res dvalue) : IO Unit := do
  check s!"{label}: wrong pointer" (dvalue_ptr_address r.1 == some addr)
  check s!"{label}: wrong occupied bytes" ((IM.elements r.2.1.state_memory_stack.Memory_stack_memory).map Prod.fst == keys)

private def largeKey (init : FusedS) (fits : Bool) : IO Unit := do
  let k : Int := 2^64
  let result ← drive (schedule (address := some k)) (alloc init 1 1)
  if fits then checkAllocated "IPZ" k [k] (← returned "IPZ" result)
  else stopped "IP64Bit" .oom result
end

section
attribute [local instance] IPZ

private def memoryCases (init : FusedS) : IO Unit := do
  let occupied := add 5 (MemoryBytes.poison_memory_byte, some 4) memory_empty
  let st : State := ⟨{empty_memory_stack with Memory_stack_memory := occupied}, (4 : Nat)⟩
  let start := (st, init.2)
  let request := alloc start 2 4
  stopped "occupied last byte" .refused (← drive (schedule (address := some 4)) request)
  for (key, proposed) in [(8, none), (12, some 12)] do
    let r ← returned "aligned allocation" (← drive (schedule (address := proposed)) request)
    checkAllocated "aligned allocation" key [5, key, key+1] r
    check "allocation did not update provenance" (Nat.beq r.2.1.state_provenance 5)
  let zero ← returned "zero size/alignment" (← drive (schedule (address := some 5)) (alloc start 0 0))
  checkAllocated "zero size/alignment" 5 [5] zero
  let saved := lookup 5 zero.2.1.state_memory_stack.Memory_stack_memory
  let some (b, aid) := saved | throw (IO.userError "zero-sized allocation removed an occupied byte")
  check "zero-sized allocation overwrote the occupied byte"
    (DVALUE_Base (DVALUE_B width b) == DVALUE_Base (DVALUE_B width MemoryBytes.poison_memory_byte)
      && (show Option Nat from aid) == some 4)
  for (skip, expected) in [(0, 5), (2, 7)] do
    let readAfter : Handlers.Memory.ConcreteMem (Nat × Nat) :=
      .Mchoose .Cfresh_prov fun p ↦ .Mget fun now ↦ .Mret (p, now.state_provenance)
    let p : Producer MCFGEbot (Choice ParamsV) _ :=
      Handlers.Memory.Worker.memM_interpWith branchingChooser readAfter st
    let ((chosen, seen), after) ← returned "fresh provenance" (← drive (schedule (skip := skip)) p)
    check "fresh provenance not stored before the continuation"
      (chosen == expected && seen == expected && Nat.beq after.state_provenance expected)

private def drawCases (init : FusedS) : IO Unit := do
  let draws ← IO.mkRef 0
  let badType := DTYPE_Array false 0 DTYPE_Label
  stopped "Draw [0 x label]" .failure (← drive (schedule (draws := some draws))
    (model (LLVMEvents.Worker.draw badType) init))
  check "Draw [0 x label] offered a branch" ((← draws.get) == 0)
  let ptrBit : memory_bit := Bit_ptr ((37 : Int), some [9]) 11
  let mixed (b : memory_bit) : dvalue := DVALUE_Base (DVALUE_B width
    (.BYTE_Mixed (b :: ptrBit :: List.replicate 6 (Z_to_memory_bit 0))))
  for (one, z) in [(false, 0), (true, 1)] do
    draws.set 0
    let p := model (Operations.Freeze.Worker.freeze (DTYPE_B width) (mixed Bit_psn)) init
    let (v, _) ← returned "mixed-byte freeze" (← drive (schedule one (draws := some draws)) p)
    check "mixed-byte freeze changed pointer, provenance, bit index or nonpoison bits"
      (v == mixed (Z_to_memory_bit z) && (← draws.get) == 1)

private abbrev Ptr := Int × Option (List Nat)
private abbrev Env := List (Syntax.LLVMAst.raw_id × dvalue)
private abbrev FrameView := Env × Option dvalue × Option IRString

private def frames : Framestack → List (List Ptr)
  | .Singleton f => [f]
  | .Snoc rest f => f :: frames rest

/-- Compare every semantic state component, including byte contents and pointer provenance. -/
private def stateView (s : FusedS) :
    List (Int × dvalue × Option Nat) × List (List Ptr) × List (Int × List Ptr) ×
    Nat × FrameView × List FrameView × Env :=
  let (m, (sf, stk), gs) := s
  let frame (f : Handlers.Stack.stack_frame) :=
    (Syntax.RawIdMaps.RM.elements f.stack_vars, f.stack_exc, f.stack_loc)
  let ms := m.state_memory_stack
  let bytes := (IM.elements ms.Memory_stack_memory).map fun (e : Int × byte) ↦
    (e.1, DVALUE_Base (DVALUE_B width e.2.1), e.2.2)
  (bytes, frames ms.Memory_stack_frame_stack, IM.elements ms.Memory_stack_heap,
    m.state_provenance, frame sf, stk.map frame, Syntax.RawIdMaps.RM.elements gs)

private def programCases (prog : TopLevel.ll_toplevel_entities) : IO Unit := do
  for (name, reused) in [("frozen", false), ("reused", true)] do
    let entry := Syntax.LLVMAst.raw_id.Name name.toUTF8
    let plain := TopLevel.Worker.interpreter_gen (M := Producer) i8 entry (pure []) prog
    let (v, state) ← returned name (← drive (B := NoChoice) (fun c ↦ nomatch c) plain)
    check s!"@{name}: deterministic interpreter did not return i8 0" (v == byteVal 0)
    let openProg := TopLevel.Worker.open_program (M := Producer) i8 entry (pure []) prog
    let p := model openProg TopLevel.initialState
    for one in [false, true] do
      let draws ← IO.mkRef 0
      let (v, state') ← returned name (← drive (schedule one (draws := some draws)) p)
      let expected := if one && !reused then 1 else 0
      check s!"@{name}: expected i8 {expected} and exactly one draw"
        (v == byteVal expected && (← draws.get) == 1)
      check s!"@{name}: freeze changed the final state" (stateView state' == stateView state)

def run : IO Unit := do
  let path := "Examples/choices.ll"
  let (prog, _) ← match Frontend.Parser.toplevel_entities (← IO.FS.readBinFile path) path.toUTF8 with
    | .ok parsed => pure parsed
    | .error e => throw (IO.userError s!"{path}:{e.position.line}:{e.position.column}: parse error")
  programCases (TopLevel.link_all [] prog)
  drawCases TopLevel.initialState
  memoryCases TopLevel.initialState
  largeKey (IP := IPZ) TopLevel.initialState true
  largeKey (IP := IP64Bit) (@TopLevel.initialState (@ParamsV IP64Bit IP64BitTheory)) false
  IO.println "freeze and memory choice checks passed"
end
end Examples.Choices

def main : IO Unit := Examples.Choices.run
