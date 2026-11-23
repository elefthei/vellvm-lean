import Vellvm.Theory.I2F.I2F_exp.BytesBits
import Vellvm.Theory.I2F.Refinement.EOU
import Vellvm.Theory.MemoryBytesFacts.Writer

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u v

theorem I2F_absorb_pois : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (c : EOUP A) (d : EOUP B)
    (f : A → EOU (@dvalue_base PInf)) (g : B → EOU (@dvalue_base PFin)), I2F_EOUP R c d →
    (∀ a b, R a b → I2F_EOU I2F_dvalue_base (f a) (g b)) →
    I2F_EOU I2F_dvalue_base (@absorb_pois PInf A c f) (@absorb_pois PFin B d g) := by
  intro A B R c d f g hc hk
  cases hc with
  | I2F_EOUP_ret a b h => exact hk a b h
  | I2F_EOUP_poison => exact .I2F_EOU_ret _ _ I2F_dvalue_Poison
  | I2F_EOUP_error => exact .I2F_EOU_error _ _
  | I2F_EOUP_ub => exact .I2F_EOU_ub _ _
  | I2F_EOUP_oom => exact .I2F_EOU_oom _ _

theorem I2F_memory_bit_to_bit : ∀ {b b'}, I2F_memory_bit b b' → I2F_EOUP Eq (@memory_bit_to_bit PInf  b) (@memory_bit_to_bit PFin  b') := by
  intro _ _ h
  cases h with
  | I2F_Bit_ptr p q i hp => exact .I2F_EOUP_ret _ _ (congrArg (fun z ↦ extract_bit_Z z i) hp.1)
  | I2F_Bit_psn => exact .I2F_EOUP_poison
  | I2F_Bit_bit _ => exact .I2F_EOUP_ret _ _ rfl

theorem I2F_memory_bits_to_Z : ∀ {bs bs'}, List.Forall₂ I2F_memory_bit bs bs' → I2F_EOUP Eq (@memory_bits_to_Z PInf  bs) (@memory_bits_to_Z PFin  bs') := by
  intro _ _ h
  refine I2F_EOUP_bind _ _ (I2F_EOUP_map_monad2 _ _ h fun _ _ hb ↦ I2F_memory_bit_to_bit hb) ?_
  intro xs ys hxy
  cases Forall2_eq _ _ hxy
  exact .I2F_EOUP_ret _ _ rfl

theorem I2F_memory_byte_to_Z : ∀ {b b'}, I2F_memory_byte b b' → I2F_EOUP Eq (@memory_byte_to_Z PInf  b) (@memory_byte_to_Z PFin  b') := by
  intro _ _ h
  cases h with
  | I2F_BYTE_I _ => exact .I2F_EOUP_ret _ _ rfl
  | I2F_BYTE_Pointer p q i hp => exact .I2F_EOUP_ret _ _ (congrArg (fun z ↦ extract_byte_Z z i) hp.1)
  | I2F_BYTE_Mixed h => exact I2F_memory_bits_to_Z h

theorem I2F_concat_bytes_Z_mixed : ∀ n {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' → I2F_EOUP Eq (@concat_bytes_Z_mixed PInf n bs) (@concat_bytes_Z_mixed PFin n bs') := by
  intro n _ _ h
  induction h with
  | nil => exact .I2F_EOUP_ret _ _ rfl
  | cons hb ht ih =>
    cases ht with
    | nil =>
      have hbits := List.forall₂_take n (I2F_memory_byte_to_memory_bits hb)
      cases hb <;> first | exact .I2F_EOUP_ret _ _ rfl | exact I2F_memory_bits_to_Z hbits
    | cons =>
      rw [@Theory.MemoryBytesFacts.concat_bytes_Z_mixed_cons2 PInf, @Theory.MemoryBytesFacts.concat_bytes_Z_mixed_cons2 PFin]
      refine I2F_EOUP_bind _ _ (I2F_memory_byte_to_Z hb) fun _ _ e ↦ ?_
      cases e
      refine I2F_EOUP_bind _ _ ih fun _ _ e ↦ ?_
      cases e; exact .I2F_EOUP_ret _ _ rfl

theorem I2F_memory_bytes_to_int : ∀ sz {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' → I2F_EOUP Eq (@memory_bytes_to_int PInf sz bs) (@memory_bytes_to_int PFin sz bs') := by
  intro sz _ _ h
  simp only [memory_bytes_to_int]
  split
  · exact I2F_concat_bytes_Z_mixed _ h
  · refine I2F_EOUP_bind _ _ (I2F_EOUP_map_monad2 _ _ h fun _ _ hb ↦ I2F_memory_byte_to_Z hb) ?_
    intro xs ys hxy
    cases Forall2_eq _ _ hxy
    exact .I2F_EOUP_ret _ _ rfl

end Vellvm.Theory.I2F.I2F_exp
