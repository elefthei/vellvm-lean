import Vellvm.Theory.I2F.I2F_exp.BytesDigits
import Vellvm.Theory.I2F.I2F_exp.BytesNoCut
import Vellvm.Theory.I2F.I2F_exp.BytesAddress

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u v
open Vellvm.Semantics.Interfaces.Sizeof

theorem I2F_EOUP_fmap_NoPois : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) (c : EOU A) (d : EOU B),
    I2F_EOU R c d → I2F_EOUP R ((some <$> c) : EOU (Option A)) ((some <$> d) : EOU (Option B)) := by intro A B R c d h; cases h <;> constructor <;> assumption

theorem I2F_EOUP_memory_bytes_to_address_ptr : ∀ {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' → I2F_EOUP I2F_Addr (@memory_bytes_to_address_ptr PInf  bs) (@memory_bytes_to_address_ptr PFin  bs') := by
  intro _ _ h
  refine I2F_EOUP_bind _ _ (I2F_EOUP_map_monad2 _ _ h fun _ _ hb ↦ I2F_memory_byte_to_Z hb) ?_
  intro xs ys hxy
  cases Forall2_eq _ _ hxy
  exact I2F_EOUP_fmap_NoPois _ _ _ (I2F_int_to_ptr _ _)

theorem I2F_EOUP_no_cut_inv : ∀ {A : Type u} {B : Type v} (R : A → B → Prop) {c : EOUP A} {d : EOUP B},
    I2F_EOUP R c d → no_cut c → no_cut d →
    (∃ a b, c = raise_ret (some a) ∧ d = raise_ret (some b) ∧ R a b) ∨
    (c = raise_ret none ∧ d = raise_ret none) ∨ (∃ s t, c = raise_error s ∧ d = raise_error t) := by
  intro A B R c d h hc hd
  cases h with
  | I2F_EOUP_ret a b hab => exact .inl ⟨a,b,rfl,rfl,hab⟩
  | I2F_EOUP_poison => exact .inr (.inl ⟨rfl,rfl⟩)
  | I2F_EOUP_error s t => exact .inr (.inr ⟨s,t,rfl,rfl⟩)
  | I2F_EOUP_ub => exact False.elim hc
  | I2F_EOUP_oom => exact False.elim hd

end Vellvm.Theory.I2F.I2F_exp
