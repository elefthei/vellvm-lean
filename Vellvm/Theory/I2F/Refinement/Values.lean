module

public import Vellvm.Theory.I2F.Refinement.Params
public import Vellvm.Semantics.DynamicValues.Basic
public import Vellvm.Utils.RelationsUtil
public import Mathlib.Data.List.Forall2

@[expose] public section
namespace Vellvm.Theory.I2F.Refinement
open Semantics.DynamicValues Semantics.Interfaces.Pointer Syntax.DynamicTypes Numeric.Integers

def I2F_Iptr (z : PInf.IPTR.iptr) (i : PFin.IPTR.iptr) : Prop := z = unsigned i

def I2F_Addr (p : PInf.PTR.ptr) (q : PFin.PTR.ptr) : Prop := I2F_Iptr p.1 q.1 ∧ p.2 = q.2

inductive I2F_memory_bit : @memory_bit PInf → @memory_bit PFin → Prop where
  | I2F_Bit_ptr (p p' idx) : I2F_Addr p p' →
      I2F_memory_bit (@Bit_ptr PInf p idx) (@Bit_ptr PFin p' idx)
  | I2F_Bit_psn : I2F_memory_bit (@Bit_psn PInf) (@Bit_psn PFin)
  | I2F_Bit_bit (b) : I2F_memory_bit (@Bit_bit PInf b) (@Bit_bit PFin b)
export I2F_memory_bit (I2F_Bit_ptr I2F_Bit_psn I2F_Bit_bit)

inductive I2F_dvalue_bv {sz : Positive} : @dvalue_bv PInf sz → @dvalue_bv PFin sz → Prop where
  | I2F_BYTE_I (i : bit_int sz) : I2F_dvalue_bv (@BYTE_I PInf sz i) (@BYTE_I PFin sz i)
  | I2F_BYTE_Pointer (p p' n) : I2F_Addr p p' →
      I2F_dvalue_bv (@BYTE_Pointer PInf sz p n) (@BYTE_Pointer PFin sz p' n)
  | I2F_BYTE_Mixed {bits bits'} : List.Forall₂ I2F_memory_bit bits bits' →
      I2F_dvalue_bv (@BYTE_Mixed PInf sz bits) (@BYTE_Mixed PFin sz bits')
export I2F_dvalue_bv (I2F_BYTE_I I2F_BYTE_Pointer I2F_BYTE_Mixed)

inductive I2F_dvalue_base : @dvalue_base PInf → @dvalue_base PFin → Prop where
  | I2F_dvalue_Pointer (p p') : I2F_Addr p p' →
      I2F_dvalue_base (@DVALUE_Pointer PInf p) (@DVALUE_Pointer PFin p')
  | I2F_dvalue_Int {sz} (i : bit_int sz) : I2F_dvalue_base (@DVALUE_I PInf sz i) (@DVALUE_I PFin sz i)
  | I2F_dvalue_Ptr {p p'} : I2F_Iptr p p' → I2F_dvalue_base (@DVALUE_Iptr PInf p) (@DVALUE_Iptr PFin p')
  | I2F_dvalue_Double (d) : I2F_dvalue_base (@DVALUE_Double PInf d) (@DVALUE_Double PFin d)
  | I2F_dvalue_Float (f) : I2F_dvalue_base (@DVALUE_Float PInf f) (@DVALUE_Float PFin f)
  | I2F_dvalue_Poison : I2F_dvalue_base (@DVALUE_Poison PInf) (@DVALUE_Poison PFin)
  | I2F_dvalue_None : I2F_dvalue_base (@DVALUE_None PInf) (@DVALUE_None PFin)
  | I2F_dvalue_B {sz} {bv : @dvalue_bv PInf sz} {bv' : @dvalue_bv PFin sz} :
      I2F_dvalue_bv bv bv' → I2F_dvalue_base (@DVALUE_B PInf sz bv) (@DVALUE_B PFin sz bv')
export I2F_dvalue_base (I2F_dvalue_Pointer I2F_dvalue_Int I2F_dvalue_Ptr I2F_dvalue_Double
  I2F_dvalue_Float I2F_dvalue_Poison I2F_dvalue_None I2F_dvalue_B)

inductive I2F_dvalue : @dvalue PInf → @dvalue PFin → Prop where
  | I2F_dvalue_Base {b b'} : I2F_dvalue_base b b' →
      I2F_dvalue (@DVALUE_Base PInf b) (@DVALUE_Base PFin b')
  | I2F_dvalue_Struct (p) {s1 s2} : List.Forall₂ I2F_dvalue s1 s2 →
      I2F_dvalue (@DVALUE_Struct PInf p s1) (@DVALUE_Struct PFin p s2)
  | I2F_dvalue_Array (v) {s1 s2} : List.Forall₂ I2F_dvalue s1 s2 →
      I2F_dvalue (@DVALUE_Array PInf v s1) (@DVALUE_Array PFin v s2)
export I2F_dvalue (I2F_dvalue_Base I2F_dvalue_Struct I2F_dvalue_Array)

abbrev I2F_exc_dvalue := Sum.LiftRel I2F_dvalue I2F_dvalue

def I2F_targs : List (dtyp × @dvalue PInf) → List (dtyp × @dvalue PFin) → Prop :=
  List.Forall₂ (Utils.RelationsUtil.prod_rel Eq I2F_dvalue)

theorem I2F_Addr_ptr_aligned_to (p : PInf.PTR.ptr) (p' : PFin.PTR.ptr) (align : Nat)
    (h : I2F_Addr p p') : @ptr_aligned_to PInf.PROV PInf.PTR PInf.P2I p align =
      @ptr_aligned_to PFin.PROV PFin.PTR PFin.P2I p' align := by
  unfold ptr_aligned_to
  rw [show PInf.P2I.ptr_to_int p = PFin.P2I.ptr_to_int p' from h.1]

theorem I2F_dvalue_ind {P : @dvalue PInf → @dvalue PFin → Prop}
    (hb : ∀ b b', I2F_dvalue_base b b' → P (@DVALUE_Base PInf b) (@DVALUE_Base PFin b'))
    (hs : ∀ p s1 s2, List.Forall₂ I2F_dvalue s1 s2 → List.Forall₂ P s1 s2 →
      P (@DVALUE_Struct PInf p s1) (@DVALUE_Struct PFin p s2))
    (ha : ∀ v s1 s2, List.Forall₂ I2F_dvalue s1 s2 → List.Forall₂ P s1 s2 →
      P (@DVALUE_Array PInf v s1) (@DVALUE_Array PFin v s2))
    {d d0} (h : I2F_dvalue d d0) : P d d0 :=
  I2F_dvalue.rec (motive_1 := fun x y _ ↦ P x y) (motive_2 := fun xs ys _ ↦ List.Forall₂ P xs ys)
    (fun {_ _} ↦ hb _ _) (fun p {_ _} ↦ hs p _ _) (fun v {_ _} ↦ ha v _ _)
    .nil (fun _ _ ih iht ↦ .cons ih iht) h

theorem I2F_targs_fst {args1 args2} (h : I2F_targs args1 args2) :
    args1.map Prod.fst = args2.map Prod.fst := by
  induction h with
  | nil => rfl
  | cons hxy _ ih => exact congrArg₂ List.cons hxy.1 ih

theorem I2F_targs_snd {args1 args2} (h : I2F_targs args1 args2) :
    List.Forall₂ I2F_dvalue (args1.map Prod.snd) (args2.map Prod.snd) := by
  induction h with
  | nil => exact .nil
  | cons hxy _ ih => exact .cons hxy.2 ih

end Vellvm.Theory.I2F.Refinement
