import Vellvm.Theory.I2F.I2F_exp.BytesWriterBase
import Vellvm.Theory.I2F.I2F_exp.Freeze
import Vellvm.Semantics.MemoryBytes

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof

theorem I2F_dvalue_bv_all_poison : ∀ {sz} {b b'}, @I2F_dvalue_bv sz b b' → @dvalue_bv_all_poison PInf sz b = @dvalue_bv_all_poison PFin sz b' := by
  intro sz b c h
  cases h <;> first | rfl | apply I2F_all_poison_bits; assumption

theorem I2F_memory_byte_of_bits : ∀ {bs cs}, List.Forall₂ I2F_memory_bit bs cs → I2F_memory_byte (@memory_byte_of_bits PInf bs) (@memory_byte_of_bits PFin cs) := by
  intro bs cs h
  unfold memory_byte_of_bits
  rw [I2F_forallb_int_bits h, I2F_int_bits_to_Z h]
  split <;> first | exact I2F_BYTE_I _ | exact I2F_BYTE_Mixed h

theorem I2F_acc_bits_to_memory_bytes : ∀ n {bs cs xs ys}, List.Forall₂ I2F_memory_bit bs cs → List.Forall₂ I2F_memory_byte xs ys →
    List.Forall₂ I2F_memory_byte (@acc_bits_to_memory_bytes PInf n bs xs) (@acc_bits_to_memory_bytes PFin n cs ys) := by
  intro n
  induction n with
  | zero => intros; assumption
  | succ n ih =>
    intro bs cs xs ys h ha
    exact ih (List.forall₂_drop 8 h) (.cons (I2F_memory_byte_of_bits (List.forall₂_take 8 h)) ha)

theorem I2F_acc_packed_bits_to_memory_bytes : ∀ n {bs cs xs ys}, List.Forall₂ I2F_memory_bit bs cs → List.Forall₂ I2F_memory_byte xs ys →
    List.Forall₂ I2F_memory_byte (@acc_packed_bits_to_memory_bytes PInf n bs xs) (@acc_packed_bits_to_memory_bytes PFin n cs ys) := by
  intro n bs cs xs ys h ha
  unfold acc_packed_bits_to_memory_bytes
  rw [h.length_eq]
  exact I2F_acc_bits_to_memory_bytes n (List.rel_append h (Forall2_repeat _ _ _ _ (I2F_Bit_bit _))) ha

theorem I2F_packed_elt_bits : ∀ m {x y}, I2F_dvalue x y → I2F_EOU (List.Forall₂ I2F_memory_bit) (@packed_elt_bits PInf m x) (@packed_elt_bits PFin m y) := by
  intro m x y h
  cases h with
  | I2F_dvalue_Struct | I2F_dvalue_Array => exact .I2F_EOU_error _ _
  | I2F_dvalue_Base hb =>
    cases hb with
    | I2F_dvalue_Int => exact .I2F_EOU_ret _ _ (List.rel_reverse (Forall2_rev_loop_acc _ _ _ (fun _ ↦ I2F_Bit_bit _) _ _ _ _ .nil))
    | I2F_dvalue_Poison => exact .I2F_EOU_ret _ _ (Forall2_repeat _ _ _ _ I2F_Bit_psn)
    | I2F_dvalue_B hv =>
      cases hv with
      | I2F_BYTE_I => exact .I2F_EOU_ret _ _ (List.rel_reverse (Forall2_rev_loop_acc _ _ _ (fun _ ↦ I2F_Bit_bit _) _ _ _ _ .nil))
      | I2F_BYTE_Pointer p q i hp => exact .I2F_EOU_ret _ _ (List.rel_reverse (Forall2_rev_loop_acc _ _ _ (fun j ↦ I2F_Bit_ptr p q j hp) _ _ _ _ .nil))
      | I2F_BYTE_Mixed h => exact .I2F_EOU_ret _ _ h
    | _ => exact .I2F_EOU_error _ _

theorem I2F_packed_vector_bytes : ∀ m t {xs ys} o ta {bs cs}, List.Forall₂ I2F_dvalue xs ys → List.Forall₂ I2F_memory_byte bs cs →
    I2F_EOU I2F_ser_state (@writePacked PInf m t xs o ta bs) (@writePacked PFin m t ys o ta cs) := by
  intro m t xs ys o ta bs cs h ha
  refine I2F_EOU_bind _ _ (I2F_EOU_map_monad2 _ _ h fun _ _ hr ↦ I2F_packed_elt_bits m hr) ?_
  intro ls rs hl
  exact .I2F_EOU_ret _ _ (I2F_accumulate_padding _ ta
    (I2F_acc_packed_bits_to_memory_bytes _ (Forall2_concat _ _ _ hl) ha))

end Vellvm.Theory.I2F.I2F_exp
