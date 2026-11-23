import Vellvm.Theory.I2F.I2F_exp.BytesByteValue
import Vellvm.Theory.I2F.I2F_exp.BytesPack
import Vellvm.Theory.MemoryBytesFacts.Aggregate
import Vellvm.Theory.MemoryBytesFacts.Mixed

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof

theorem I2F_packed_bits_to_dvalue : ∀ t m {bs cs}, List.Forall₂ I2F_memory_bit bs cs → I2F_dvalue (@packed_bits_to_dvalue PInf t m bs) (@packed_bits_to_dvalue PFin t m cs) := by
  intro t m bs cs h
  have hp := I2F_all_poison_bits h
  unfold all_poison_bits at hp
  have hz := I2F_memory_bits_to_Z h
  have same : @memory_bits_to_Z PInf bs = @memory_bits_to_Z PFin cs := by
    rcases @Theory.MemoryBytesFacts.memory_bits_to_Z_total PInf bs with h₁ | ⟨x,h₁⟩ <;>
      rcases @Theory.MemoryBytesFacts.memory_bits_to_Z_total PFin cs with h₂ | ⟨y,h₂⟩ <;>
      rw [h₁,h₂] at hz ⊢ <;> cases hz <;> subst_vars <;> rfl
  cases t <;> simp only [packed_bits_to_dvalue]
  all_goals first
    | rw [hp,I2F_forallb_int_bits h,I2F_int_bits_to_Z h]
      cases cs.all (@is_poison_bit PFin) <;> cases cs.all (@is_int_bit PFin) <;>
        first | exact I2F_dvalue_Base I2F_dvalue_Poison |
          exact I2F_dvalue_Base (I2F_dvalue_B (I2F_BYTE_I _)) |
          exact I2F_dvalue_Base (I2F_dvalue_B (I2F_BYTE_Mixed h))
    | rw [same]
      rcases @Theory.MemoryBytesFacts.memory_bits_to_Z_total PFin cs with e | ⟨z,e⟩ <;>
        rw [e] <;> first | exact I2F_dvalue_Base I2F_dvalue_Poison |
          exact I2F_dvalue_Base (I2F_dvalue_Int _)

theorem I2F_packed_bits_to_elts : ∀ t m n {bs cs}, List.Forall₂ I2F_memory_bit bs cs → List.Forall₂ I2F_dvalue (@packed_bits_to_elts PInf t m n bs) (@packed_bits_to_elts PFin t m n cs) := by
  intro t m n
  induction n with
  | zero => intros; exact .nil
  | succ n ih => intro bs cs h; exact .cons (I2F_packed_bits_to_dvalue t m (List.forall₂_take _ h)) (ih (List.forall₂_drop _ h))

theorem I2F_packed_vector_elts : ∀ t m n {bs cs}, List.Forall₂ I2F_memory_byte bs cs → List.Forall₂ I2F_dvalue (@Theory.MemoryBytesFacts.packed_vector_elts PInf t m n bs) (@Theory.MemoryBytesFacts.packed_vector_elts PFin t m n cs) := fun t m n {_ _} h ↦ I2F_packed_bits_to_elts t m n (List.rel_reverse (I2F_get_bits_of_memory_byte_list h _ .nil))

theorem I2F_memory_bytes_to_dvalue_base : ∀ t {bs cs}, List.Forall₂ I2F_memory_byte bs cs → I2F_EOU I2F_dvalue_base (@memory_bytes_to_dvalue_base PInf bs t) (@memory_bytes_to_dvalue_base PFin cs t) := by
  intro t bs cs h
  have hm := I2F_EOUP_map_monad2 (@memory_byte_to_Z PInf) (@memory_byte_to_Z PFin) h
    (fun _ _ hb ↦ I2F_memory_byte_to_Z hb)
  cases t with
  | DTYPE_I sz =>
    exact I2F_absorb_pois Eq _ _ _ _ (I2F_memory_bytes_to_int sz h)
      (fun _ _ e ↦ e ▸ I2F_EOU_ret _ _ (I2F_dvalue_Int _))
  | DTYPE_Iptr =>
    refine I2F_absorb_pois _ _ _ _ _ hm fun x y e ↦ ?_
    cases Forall2_eq _ _ e
    exact I2F_EOU_bind _ _ (I2F_from_Z _) fun _ _ hi ↦ .I2F_EOU_ret _ _ (I2F_dvalue_Ptr hi)
  | DTYPE_Pointer =>
    exact I2F_absorb_pois _ _ _ _ _ (I2F_EOUP_memory_bytes_to_pointer h)
      (fun _ _ hp ↦ I2F_EOU_ret _ _ (I2F_dvalue_Pointer _ _ hp))
  | DTYPE_FP f =>
    cases f <;> first | exact .I2F_EOU_error _ _ |
      (apply I2F_absorb_pois _ _ _ _ _ hm; intro x y e; cases Forall2_eq _ _ e; repeat constructor)
  | DTYPE_B sz =>
    simp only [memory_bytes_to_dvalue_base, I2F_all_poison_bytes h]
    split
    · exact .I2F_EOU_ret _ _ I2F_dvalue_Poison
    · refine I2F_EOU_bind _ _ (I2F_memory_bytes_to_byte_value sz h) fun x y hv ↦ ?_
      rw [I2F_dvalue_bv_all_poison hv]; split <;> first | exact .I2F_EOU_ret _ _ I2F_dvalue_Poison |
        exact .I2F_EOU_ret _ _ (I2F_dvalue_B hv)
  | _ => exact .I2F_EOU_error _ _

end Vellvm.Theory.I2F.I2F_exp
