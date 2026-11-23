module

public import Vellvm.Semantics.DynamicValues.Core
public import Vellvm.Semantics.LLVMEvents
public import Vellvm.Semantics.Simulation

@[expose] public section
namespace Vellvm.Semantics.Operations.Freeze
open ITree (Effect Subeffect)
open Vellvm.Tree Interfaces.Params DynamicValues Syntax.DynamicTypes LLVMEvents

variable [Pa : Params]

def freeze_bits (z : Int) (i : Nat) : List memory_bit → List memory_bit
  | [] => []
  | .Bit_psn :: bs => Z_to_memory_bit (if z.testBit i then 1 else 0) :: freeze_bits z (i+1) bs
  | b :: bs => b :: freeze_bits z (i+1) bs

/-- A draw changes precisely the poison positions, without altering pointer identity or bit index. -/
theorem getElem?_freeze_bits (z : Int) (i j : Nat) (bs : List memory_bit) :
    (freeze_bits z i bs)[j]? = (bs[j]?).map (fun
      | .Bit_psn => Z_to_memory_bit (if z.testBit (i+j) then 1 else 0)
      | bit => bit) := by
  induction j generalizing i bs with
  | zero =>
    cases bs with
    | nil => rfl
    | cons b bs => cases b <;> rfl
  | succ j ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      cases b <;> simpa only [freeze_bits, List.getElem?_cons_succ, Nat.add_assoc, Nat.add_comm 1 j]
        using ih (i+1) bs

def freeze_mixed_bits (sz : Positive) (z : Int) (bits : List memory_bit) : dvalue_bv sz :=
  let frozen := freeze_bits z 0 bits
  if frozen.all is_int_bit then .BYTE_I (Numeric.Integers.repr (int_bits_to_Z frozen))
  else .BYTE_Mixed frozen

namespace Worker
variable {M : Effect → Effect → Type → Type v} [Runtime M]
variable {E B : Effect} [DrawE -< E]

def freeze_base (dt : dtyp) (dv : dvalue_base) : M E B dvalue :=
  match dv with
  | .DVALUE_Poison => LLVMEvents.Worker.draw dt
  | .DVALUE_B sz (.BYTE_Mixed bits) =>
    if bits.any is_poison_bit then do
      let x ← LLVMEvents.Worker.draw (DTYPE_I sz)
      let z := match x with
        | .DVALUE_Base (.DVALUE_I _ i) => Numeric.Integers.unsigned i
        | _ => 0
      pure (DVALUE_Base (DVALUE_B sz (freeze_mixed_bits sz z bits)))
    else pure (DVALUE_Base dv)
  | _ => pure (DVALUE_Base dv)

variable [Instrumentation.Diagnostics M] [FailureE -< E]

mutual
  def freeze (dt : dtyp) (dv : dvalue) : M E B dvalue :=
    match dv with
    | .DVALUE_Base b => freeze_base dt b
    | .DVALUE_Struct _ fields =>
      match dt with
      | .DTYPE_Struct p ts => do pure (DVALUE_Struct p (← freezeFields ts fields []))
      | _ => LLVMEvents.Worker.«raise» "freeze: type mismatch non-struct type".toUTF8
    | .DVALUE_Array _ elts =>
      match dt with
      | .DTYPE_Array v _ t => do pure (DVALUE_Array v (← freezeElts t elts []))
      | _ => LLVMEvents.Worker.«raise» "freeze: type mismatch non-array type".toUTF8
  termination_by structural dv

  def freezeFields (ts : List dtyp) (vs acc : List dvalue) : M E B (List dvalue) :=
    match vs, ts with
    | [], [] => pure acc.reverse
    | v :: vs, t :: ts => do freezeFields ts vs ((← freeze t v) :: acc)
    | _, _ => LLVMEvents.Worker.«raise» "freeze_fields: mismatched field types and values".toUTF8
  termination_by structural vs

  def freezeElts (t : dtyp) (vs acc : List dvalue) : M E B (List dvalue) :=
    match vs with
    | [] => pure acc.reverse
    | v :: vs => do freezeElts t vs ((← freeze t v) :: acc)
  termination_by structural vs
end

variable {N : Effect → Effect → Type → Type w} [Runtime N] [Instrumentation.Diagnostics N]
variable [Instrumentation.Snapshots M] [Instrumentation.Snapshots N] (s : Simulation M N)

theorem freeze_base_congr (dt : dtyp) (dv : dvalue_base) :
    s.R (E := E) (B := B) (freeze_base dt dv) (freeze_base dt dv) := by
  cases dv with
  | DVALUE_Poison => exact s.emit (E := DrawE) (Draw dt)
  | DVALUE_B sz bv =>
    cases bv with
    | BYTE_Mixed bits =>
      simp only [freeze_base]
      split
      · apply s.bind
        · exact s.emit (E := DrawE) (Draw (DTYPE_I sz))
        · exact fun _ ↦ s.pure _
      · exact s.pure _
    | _ => exact s.pure _
  | _ => exact s.pure _

mutual
  theorem freeze_congr (dt : dtyp) (dv : dvalue) :
      s.R (E := E) (B := B) (freeze dt dv) (freeze dt dv) := by
    cases dv with
    | DVALUE_Base b => exact freeze_base_congr s dt b
    | DVALUE_Struct _ fields =>
      cases dt with
      | DTYPE_Struct p ts =>
        exact s.bind (freezeFields_congr ts fields []) (fun _ ↦ s.pure _)
      | _ => exact s.«raise» _
    | DVALUE_Array _ elts =>
      cases dt with
      | DTYPE_Array v _ t =>
        exact s.bind (freezeElts_congr t elts []) (fun _ ↦ s.pure _)
      | _ => exact s.«raise» _
  termination_by structural dv

  theorem freezeFields_congr (ts : List dtyp) (vs acc : List dvalue) :
      s.R (E := E) (B := B) (freezeFields ts vs acc) (freezeFields ts vs acc) := by
    cases vs with
    | nil => cases ts with
      | nil => exact s.pure _
      | cons _ _ => exact s.«raise» _
    | cons v vs => cases ts with
      | nil => exact s.«raise» _
      | cons t ts =>
        exact s.bind (freeze_congr t v) (fun x ↦ freezeFields_congr ts vs (x :: acc))
  termination_by structural vs

  theorem freezeElts_congr (t : dtyp) (vs acc : List dvalue) :
      s.R (E := E) (B := B) (freezeElts t vs acc) (freezeElts t vs acc) := by
    cases vs with
    | nil => exact s.pure _
    | cons v vs =>
      exact s.bind (freeze_congr t v) (fun x ↦ freezeElts_congr t vs (x :: acc))
  termination_by structural vs
end
end Worker

variable {E B : Effect}

def freeze_base [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (dt : dtyp) (dv : dvalue_base) : CTree.CTree E B dvalue := Worker.freeze_base dt dv

def freeze [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (dt : dtyp) (dv : dvalue) : CTree.CTree E B dvalue := Worker.freeze dt dv

end Vellvm.Semantics.Operations.Freeze
