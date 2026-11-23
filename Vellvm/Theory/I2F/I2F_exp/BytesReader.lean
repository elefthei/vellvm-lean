import Vellvm.Theory.I2F.I2F_exp.BytesReaderBase
import Vellvm.Theory.I2F.I2F_exp.Values
import Vellvm.Theory.I2F.I2F_exp.BytesReaderLoops

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof
theorem I2F_memory_bytes_to_dvalue : ∀ t, ∀ {bs cs}, List.Forall₂ I2F_memory_byte bs cs → I2F_EOU I2F_dvalue (@memory_bytes_to_dvalue PInf bs t) (@memory_bytes_to_dvalue PFin cs t) := by
  apply dtyp_ind
  · intro t bs cs h
    simp only [memory_bytes_to_dvalue]
    exact I2F_EOU_bind _ _ (I2F_memory_bytes_to_dvalue_base t (List.forall₂_take _ h))
      fun _ _ hb ↦ .I2F_EOU_ret _ _ (I2F_dvalue_Base hb)
  · intro p ts ih bs cs h
    have hs := I2F_poison_split h
    simp only [Theory.MemoryBytesFacts.read_struct_unfold]
    cases hx : @poison_split PInf bs with | mk n xs =>
      cases hy : @poison_split PFin cs with | mk m ys =>
        rw [hx,hy] at hs; obtain ⟨e,hr⟩ := hs; change n = m at e; subst m
        change List.Forall₂ I2F_memory_byte xs ys at hr
        cases hr with
        | nil => exact .I2F_EOU_ret _ _ (I2F_poison_of_dtyp _)
        | cons =>
          exact I2F_EOU_bind _ _ (readStructRel ts ih _ _ _ h)
            fun _ _ hv ↦ .I2F_EOU_ret _ _ (I2F_canonicalize_agg _ hv)
  · intro v sz t ih bs cs h
    have hs := I2F_poison_split h
    simp only [Theory.MemoryBytesFacts.read_array_unfold]
    cases hx : @poison_split PInf bs with | mk n xs =>
      cases hy : @poison_split PFin cs with | mk m ys =>
        rw [hx,hy] at hs; obtain ⟨e,hr⟩ := hs; change n = m at e; subst m
        change List.Forall₂ I2F_memory_byte xs ys at hr
        cases hr with
        | nil => exact .I2F_EOU_ret _ _ (I2F_poison_of_dtyp _)
        | cons =>
          dsimp only
          split
          · exact .I2F_EOU_ret _ _ (I2F_canonicalize_agg _ (I2F_packed_vector_elts _ _ sz h))
          · exact I2F_EOU_bind _ _ (readArrayRel t ih _ _ _ _ h)
              fun _ _ hv ↦ .I2F_EOU_ret _ _ (I2F_canonicalize_agg _ hv)

end Vellvm.Theory.I2F.I2F_exp
