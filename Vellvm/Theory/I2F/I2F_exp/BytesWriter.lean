import Vellvm.Theory.I2F.I2F_exp.BytesWriterEquations
import Vellvm.Theory.I2F.I2F_exp.BytesPack

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof

private theorem padState (ta : Option Nat) {x y} (h : I2F_ser_state x y) :
    I2F_ser_state (@accumulate_padding PInf x.1 ta x.2) (@accumulate_padding PFin y.1 ta y.2) := by
  rcases x with ⟨i,xs⟩; rcases y with ⟨j,ys⟩; obtain ⟨e,hs⟩ := h
  change i = j at e; subst j; exact I2F_accumulate_padding i ta hs

theorem I2F_accumulate_struct_bytes : ∀ {fs gs}, List.Forall₂ (fun a b ↦ ∀ dt o ta {xs ys}, List.Forall₂ I2F_memory_byte xs ys →
        I2F_EOU I2F_ser_state (@acc_dvalue_to_memory_bytes_h PInf dt a o ta xs) (@acc_dvalue_to_memory_bytes_h PFin dt b o ta ys)) fs gs →
    ∀ ts ta pad o {bs cs}, List.Forall₂ I2F_memory_byte bs cs → I2F_EOU I2F_ser_state
      (@accumulate_struct_bytes PInf ta pad fs ts o bs) (@accumulate_struct_bytes PFin ta pad gs ts o cs) := by
  intro fs gs h
  induction h with
  | nil =>
    intro ts ta pad o bs cs ha
    cases ts with
    | nil =>
      rw [@acc_struct_nil PInf, @acc_struct_nil PFin]
      have hr := I2F_accumulate_padding o pad ha
      exact I2F_EOU_ret _ _ (padState ta hr)
    | cons => rw [@acc_struct_nil_cons PInf, @acc_struct_nil_cons PFin]; exact .I2F_EOU_error _ _
  | cons hf _ ih =>
    intro ts ta pad o bs cs ha
    cases ts with
    | nil => rw [@acc_struct_cons_nil PInf, @acc_struct_cons_nil PFin]; exact .I2F_EOU_error _ _
    | cons t ts =>
      simp only [acc_struct_cons]
      have hp := I2F_accumulate_padding o (pad.map fun _ ↦ (@dtyp_alignment PInf.SIZE t).preferred_alignment) ha
      refine I2F_EOU_bind _ _ (hf t 0 none hp.2) ?_
      rintro ⟨i,xs⟩ ⟨j,ys⟩ ⟨e,hs⟩
      change i = j at e; subst j
      have eoff := hp.1
      simp only [Prod.fst, Prod.snd] at hs ⊢
      rw [eoff]
      exact ih ts ta pad _ (I2F_accumulate_poison_bytes _ hs)

theorem I2F_accumulate_array_bytes : ∀ {es fs}, List.Forall₂ (fun a b ↦ ∀ dt o ta {xs ys}, List.Forall₂ I2F_memory_byte xs ys →
        I2F_EOU I2F_ser_state (@acc_dvalue_to_memory_bytes_h PInf dt a o ta xs) (@acc_dvalue_to_memory_bytes_h PFin dt b o ta ys)) es fs →
    ∀ v t ta o {bs cs}, List.Forall₂ I2F_memory_byte bs cs → I2F_EOU I2F_ser_state
      (@accumulate_array_bytes PInf ta v t es o bs) (@accumulate_array_bytes PFin ta v t fs o cs) := by
  intro es fs h
  induction h with
  | nil => intro v t ta o bs cs ha; exact .I2F_EOU_ret _ _ (I2F_accumulate_padding o ta ha)
  | cons hf _ ih =>
    intro v t ta o bs cs ha
    simp only [acc_array_cons]
    refine I2F_EOU_bind _ _ (hf t 0 none ha) ?_
    rintro ⟨i,xs⟩ ⟨j,ys⟩ ⟨e,hs⟩
    change i = j at e; subst j
    exact ih v t ta _ (I2F_accumulate_poison_bytes _ hs)

theorem I2F_acc_dvalue_to_memory_bytes_h : ∀ {a b}, I2F_dvalue a b → (fun a b ↦ ∀ dt o ta {xs ys}, List.Forall₂ I2F_memory_byte xs ys →
        I2F_EOU I2F_ser_state (@acc_dvalue_to_memory_bytes_h PInf dt a o ta xs) (@acc_dvalue_to_memory_bytes_h PFin dt b o ta ys)) a b := by
  intro a b h
  apply I2F_dvalue_ind (P := fun x y ↦ ∀ dt o ta {xs ys}, List.Forall₂ I2F_memory_byte xs ys →
    I2F_EOU I2F_ser_state (@acc_dvalue_to_memory_bytes_h PInf dt x o ta xs) (@acc_dvalue_to_memory_bytes_h PFin dt y o ta ys)) _ _ _ h
  · intro x y hb dt o ta xs ys hs
    cases dt with
    | DTYPE_Base t => simp only [ser_Base_eq]; exact .I2F_EOU_ret _ _ (padState ta (I2F_acc_memory_bytes_of_dvalue_base t hb o hs))
    | DTYPE_Struct | DTYPE_Array => cases hb <;> simp only [acc_dvalue_to_memory_bytes_h] <;>
        first | exact .I2F_EOU_error _ _ | exact .I2F_EOU_ret _ _ (padState ta (I2F_accumulate_padding_bytes o _ hs))
  · intro p xs ys _ ih dt o ta bs cs hbs
    cases dt <;> first | (simp only [ser_Struct_eq]; apply I2F_accumulate_struct_bytes ih; exact hbs) |
      (simp only [acc_dvalue_to_memory_bytes_h]; exact .I2F_EOU_error _ _)
  · intro p xs ys hr ih dt o ta bs cs hbs
    cases dt <;> first | (simp only [ser_Array_eq]; split <;> first | apply I2F_packed_vector_bytes _ _ _ _ hr hbs | apply I2F_accumulate_array_bytes ih; exact hbs) |
      (simp only [acc_dvalue_to_memory_bytes_h]; exact .I2F_EOU_error _ _)

theorem I2F_memory_dvalue_to_memory_bytes : ∀ t {a b}, I2F_dvalue a b → ∀ ta, I2F_EOU (List.Forall₂ I2F_memory_byte)
    (@dvalue_to_memory_bytes PInf t a ta) (@dvalue_to_memory_bytes PFin t b ta) := by
  intro t a b h ta
  refine I2F_EOU_bind _ _ (I2F_acc_dvalue_to_memory_bytes_h h t 0 ta .nil) ?_
  intro x y hs
  exact .I2F_EOU_ret _ _ (List.rel_reverse hs.2)

end Vellvm.Theory.I2F.I2F_exp
