import Vellvm.Theory.I2F.I2F_exp.BytesSlice
import Vellvm.Theory.I2F.I2F_exp.Freeze

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof

theorem I2F_mixed_fallback : ∀ (sz : Positive) {bs cs}, List.Forall₂ I2F_memory_byte bs cs → I2F_dvalue_bv
    (@BYTE_Mixed PInf sz (@get_bits_of_memory_byte_list PInf sz.val bs []).reverse) (@BYTE_Mixed PFin sz (@get_bits_of_memory_byte_list PFin sz.val cs []).reverse) := fun sz {_ _} h ↦ I2F_BYTE_Mixed (List.rel_reverse (I2F_get_bits_of_memory_byte_list h sz.val .nil))

theorem I2F_existsb_ptr_bits : ∀ (sz : Positive) {bs cs}, List.Forall₂ I2F_memory_byte bs cs → 
    (@get_bits_of_memory_byte_list PInf sz.val bs []).reverse.any (@is_ptr_bit PInf) =
    (@get_bits_of_memory_byte_list PFin sz.val cs []).reverse.any (@is_ptr_bit PFin) := by
  intro sz bs cs h
  have aux {xs ys} (hr : List.Forall₂ I2F_memory_bit xs ys) :
      xs.any (@is_ptr_bit PInf) = ys.any (@is_ptr_bit PFin) := by
    induction hr with
    | nil => rfl
    | cons hb _ ih => simp only [List.any_cons, I2F_is_ptr_bit hb, ih]
  exact aux (List.rel_reverse (I2F_get_bits_of_memory_byte_list h sz.val .nil))

theorem I2F_memory_bytes_to_bits_value : ∀ (sz : Positive) {bs cs}, List.Forall₂ I2F_memory_byte bs cs → I2F_dvalue_bv
    (@memory_bytes_to_bits_value PInf sz bs) (@memory_bytes_to_bits_value PFin sz cs) := by
  intro sz bs cs h
  have hb := List.rel_reverse (I2F_get_bits_of_memory_byte_list h sz.val .nil)
  simp only [memory_bytes_to_bits_value]
  rw [I2F_existsb_ptr_bits sz h, I2F_existsb_poison_bits hb]
  split
  · exact I2F_BYTE_Mixed hb
  · have hr := I2F_EOUP_no_cut_inv Eq (I2F_memory_bytes_to_int sz h)
        (@no_cut_memory_bytes_to_int PInf sz bs) (@no_cut_memory_bytes_to_int PFin sz cs)
    rcases hr with ⟨x,y,hx,hy,rfl⟩ | ⟨hx,hy⟩ | ⟨_,_,hx,hy⟩ <;>
      rw [hx,hy] <;> first | exact I2F_BYTE_I _ | (rw [I2F_int_bits_to_Z hb]; exact I2F_BYTE_I _)

theorem I2F_memory_bytes_to_byte_value : ∀ (sz : Positive) {bs cs}, List.Forall₂ I2F_memory_byte bs cs → I2F_EOU I2F_dvalue_bv
    (@memory_bytes_to_byte_value PInf sz bs) (@memory_bytes_to_byte_value PFin sz cs) := by
  intro sz bs cs h
  have hs := I2F_memory_bytes_to_pointer_slice h
  unfold memory_bytes_to_byte_value
  cases hl : @memory_bytes_to_pointer_slice PInf bs with
  | none => cases hr : @memory_bytes_to_pointer_slice PFin cs <;> simp only [hl,hr] at hs <;>
      first | exact False.elim hs | exact .I2F_EOU_ret _ _ (I2F_memory_bytes_to_bits_value sz h)
  | some x =>
    obtain ⟨p,i⟩ := x
    cases hr : @memory_bytes_to_pointer_slice PFin cs with
    | none => simp only [hl,hr] at hs
    | some y =>
      obtain ⟨q,j⟩ := y
      simp only [hl,hr] at hs
      obtain ⟨hp,rfl⟩ := hs
      dsimp only
      cases pointer_chunk_aligned sz i <;> first
        | exact .I2F_EOU_ret _ _ (I2F_BYTE_Pointer _ _ _ hp)
        | exact .I2F_EOU_ret _ _ (I2F_memory_bytes_to_bits_value sz h)

end Vellvm.Theory.I2F.I2F_exp
