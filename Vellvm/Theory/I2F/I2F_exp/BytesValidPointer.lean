import Vellvm.Theory.I2F.I2F_exp.BytesBasic
import Vellvm.Theory.I2F.Refinement.EOU
import Mathlib.Tactic.Tauto

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof

private theorem ptr_eq_iff {p q p' q'} (hp : I2F_Addr p p') (hq : I2F_Addr q q') :
    p = q ↔ p' = q' := by
  constructor
  · rintro rfl
    exact Prod.ext (bit_int.ext_unsigned (hp.1.symm.trans hq.1)) (hp.2.symm.trans hq.2)
  · rintro rfl
    exact Prod.ext (hp.1.trans hq.1.symm) (hp.2.trans hq.2.symm)

theorem I2F_EOUP_valid_pointer_bits : ∀ {p p'} base off {bs bs'}, I2F_Addr p p' → List.Forall₂ I2F_memory_bit bs bs' →
    I2F_EOUP Eq (@valid_pointer_bits PInf p base off bs) (@valid_pointer_bits PFin p' base off bs') := by
  intro p q base off bs cs hp h
  induction h generalizing off with
  | nil => exact .I2F_EOUP_ret _ _ rfl
  | cons hb ht ih =>
    cases hb with
    | I2F_Bit_psn => exact .I2F_EOUP_poison
    | I2F_Bit_bit => exact .I2F_EOUP_ret _ _ rfl
    | I2F_Bit_ptr x y j hxy =>
      have he := ptr_eq_iff hp hxy
      simp only [valid_pointer_bits]
      cases PInf.PTR.eq_dec_ptr p x <;> cases PFin.PTR.eq_dec_ptr q y
      · by_cases hj : (j == base + off) = true <;> simp only [hj, if_true, if_false] <;>
          first | exact ih _ | exact .I2F_EOUP_ret _ _ rfl
      · exfalso; tauto
      · exfalso; tauto
      · exact .I2F_EOUP_ret _ _ rfl

theorem I2F_EOUP_valid_pointer_byte : ∀ {p p'} i {bs bs'}, I2F_Addr p p' → I2F_memory_byte bs bs' →
    I2F_EOUP Eq (@valid_pointer_byte PInf p i bs) (@valid_pointer_byte PFin p' i bs') := by
  intro p q i b c hp hb
  cases hb with
  | I2F_BYTE_I => exact .I2F_EOUP_ret _ _ rfl
  | I2F_BYTE_Mixed h => exact I2F_EOUP_valid_pointer_bits _ _ hp h
  | I2F_BYTE_Pointer x y j hxy =>
    have he := ptr_eq_iff hp hxy
    simp only [valid_pointer_byte]
    split <;> split <;> first | exact .I2F_EOUP_ret _ _ rfl | (exfalso; tauto)

theorem I2F_EOUP_valid_pointer_bytes : ∀ {p p'} i {bs bs'}, I2F_Addr p p' → List.Forall₂ I2F_memory_byte bs bs' →
    I2F_EOUP Eq (@valid_pointer_bytes PInf p i bs) (@valid_pointer_bytes PFin p' i bs') := by
  intro p q i bs cs hp h
  induction h generalizing i with
  | nil => exact .I2F_EOUP_ret _ _ rfl
  | cons hb _ ih =>
    refine I2F_EOUP_bind _ _ (I2F_EOUP_valid_pointer_byte i hp hb) fun x y e ↦ ?_
    cases e; cases x <;> first | apply ih | exact .I2F_EOUP_ret _ _ rfl

end Vellvm.Theory.I2F.I2F_exp
