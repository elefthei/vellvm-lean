import Vellvm.Theory.I2F.I2F_exp.BytesBasic

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u

theorem in_bounds_case : ∀ (k : Positive) (x : Int), x ≤ @max_unsigned k → 0 ≤ x → x = unsigned (@repr k x) := fun _ _ hi lo ↦ (unsigned_repr _ ⟨lo, hi⟩).symm

theorem unsigned_inj : ∀ (sz : Positive) (x y : bit_int sz), unsigned x = unsigned y → x = y := fun _ _ _ h ↦ bit_int.ext_unsigned h

theorem I2F_memory_byte_to_memory_bits : ∀ {b b'}, I2F_memory_byte b b' →
    List.Forall₂ I2F_memory_bit (@memory_byte_to_memory_bits PInf b) (@memory_byte_to_memory_bits PFin b') := by
  intro _ _ h
  cases h with
  | I2F_BYTE_I => exact List.rel_reverse (Forall2_rev_loop_acc _ _ _ (fun _ ↦ I2F_Bit_bit _) _ _ _ _ .nil)
  | I2F_BYTE_Pointer p q i hp => exact List.rel_reverse (Forall2_rev_loop_acc _ _ _ (fun j ↦ I2F_Bit_ptr p q j hp) _ _ _ _ .nil)
  | I2F_BYTE_Mixed hb => exact hb

theorem I2F_get_bits_of_memory_byte_list : ∀ {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' → ∀ n {acc acc'}, List.Forall₂ I2F_memory_bit acc acc' →
    List.Forall₂ I2F_memory_bit (@get_bits_of_memory_byte_list PInf n bs acc) (@get_bits_of_memory_byte_list PFin n bs' acc') := by
  intro _ _ h
  induction h with
  | nil =>
    intro n acc acc' ha
    simp only [get_bits_of_memory_byte_list]
    split
    · exact ha
    · exact Forall2_rev_loop_acc _ _ _ (fun _ ↦ I2F_Bit_psn) _ _ _ _ ha
  | cons hb _ ih =>
    intro n acc acc' ha
    have hr := I2F_memory_byte_to_memory_bits hb
    simp only [get_bits_of_memory_byte_list]
    split
    · exact Forall2_rev_append _ _ _ (List.forall₂_take n hr) _ _ ha
    · exact ih _ (Forall2_rev_append _ _ _ hr _ _ ha)

end Vellvm.Theory.I2F.I2F_exp
